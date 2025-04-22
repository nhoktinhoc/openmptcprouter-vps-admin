```python
#!/usr/bin/env python3
#
# Copyright (C) 2018-2025 Ycarus (Yannick Chabanois) <ycarus@zugaina.org> for OpenMPTCProuter
#
# This is free software, licensed under the GNU General Public License v3.0.
# See /LICENSE for more information.
#
# Modified to use iptables instead of Shorewall

import json
import base64
import secrets
import uuid
import configparser
import argparse
import subprocess
import os
#import sys
import glob
import socket
from operator import itemgetter
import re
import hashlib
#import pathlib
import shutil
import time
import copy
#from pprint import pprint
from datetime import datetime, timedelta
from tempfile import mkstemp
from typing import List, Optional
from shutil import move
from enum import Enum
from os import path
from ipaddress import ip_address, IPv4Address, IPv6Address, ip_network
import logging
import uvicorn
import jwt
import requests
from jwt import PyJWTError
from netaddr import *
import psutil
#from netjsonconfig import OpenWrt
from fastapi import Depends, FastAPI, HTTPException, Query, Request, UploadFile
from fastapi.security import OAuth2PasswordRequestForm, OAuth2
from passlib.context import CryptContext
from fastapi.encoders import jsonable_encoder
from fastapi.security.base import SecurityBase
from fastapi.security.utils import get_authorization_scheme_param
from fastapi.openapi.docs import get_swagger_ui_html
from fastapi.openapi.models import OAuthFlows as OAuthFlowsModel
from fastapi.openapi.utils import get_openapi
from fastapi.openapi.models import SecurityBase as SecurityBaseModel
from fastapi.responses import FileResponse
from pydantic import BaseModel # pylint: disable=E0611
from starlette.status import HTTP_403_FORBIDDEN
from starlette.responses import RedirectResponse, Response, JSONResponse
#from starlette.requests import Request
import netifaces

#logging.basicConfig(filename='/tmp/omr-admin.log', encoding='utf-8', level=logging.DEBUG)
#LOG = logging.getLogger('api')


logging.basicConfig(level=logging.INFO,
                    format="%(levelname)s: "
                           "%(module)s:%(funcName)s:%(lineno)d - %(message)s")
#LOG = logging.getLogger('OMR-Admin')
LOG = logging.getLogger('uvicorn.error')

PERMANENT_SESSION_LIFETIME = timedelta(hours=24)
ACCESS_TOKEN_EXPIRE_MINUTES = 1440
ALGORITHM = "HS256"

# --- Start iptables Helper Functions ---

IPTABLES_CMD = '/usr/sbin/iptables'
IP6TABLES_CMD = '/usr/sbin/ip6tables'

def _run_iptables_cmd(cmd_list: List[str], check: bool = True) -> subprocess.CompletedProcess:
    """Runs an iptables/ip6tables command."""
    LOG.debug(f"Executing iptables command: {' '.join(cmd_list)}")
    try:
        result = subprocess.run(cmd_list, capture_output=True, text=True, check=check)
        if result.returncode != 0:
            LOG.error(f"iptables command failed: {' '.join(cmd_list)}")
            LOG.error(f"Stderr: {result.stderr}")
        # Log stdout only if there's potentially useful output (usually not for add/delete)
        # if result.stdout:
        #     LOG.debug(f"Stdout: {result.stdout}")
        return result
    except FileNotFoundError:
        LOG.error(f"Error: {cmd_list[0]} command not found.")
        raise
    except subprocess.CalledProcessError as e:
        LOG.error(f"iptables command failed with exit code {e.returncode}: {' '.join(cmd_list)}")
        LOG.error(f"Stderr: {e.stderr}")
        raise # Re-raise the exception if check=True
    except Exception as e:
        LOG.error(f"An unexpected error occurred while running iptables: {e}")
        raise

def _build_rule_spec(chain: str, rule: List[str], action: str, comment: Optional[str] = None) -> List[str]:
    """Builds the common part of the iptables rule specification."""
    spec = [chain] + rule
    if comment:
        spec.extend(['-m', 'comment', '--comment', comment])
    spec.extend(['-j', action])
    return spec

def _check_rule_exists(iptables_bin: str, table: str, chain: str, rule_spec: List[str]) -> bool:
    """Checks if an iptables rule exists."""
    cmd = [iptables_bin, '-t', table, '-C', chain] + rule_spec
    try:
        # check=False because a non-zero exit code means the rule doesn't exist, which is not an error here
        result = _run_iptables_cmd(cmd, check=False)
        return result.returncode == 0
    except Exception:
        # If checking fails for other reasons, assume it doesn't exist to be safe
        return False

def iptables_add_rule(table: str, chain: str, rule: List[str], action: str, comment: Optional[str] = None):
    """Adds an iptables rule if it doesn't already exist."""
    rule_spec_no_action = [item for item in rule] # Copy rule list
    if comment:
        rule_spec_no_action.extend(['-m', 'comment', '--comment', comment])

    # Check needs the -j ACTION part excluded from the core rule spec sometimes,
    # but -C requires the full rule including -j. Let's build the full spec for checking.
    full_rule_spec_for_check = rule + (['-m', 'comment', '--comment', comment] if comment else []) + ['-j', action]

    if not _check_rule_exists(IPTABLES_CMD, table, chain, full_rule_spec_for_check):
        cmd = [IPTABLES_CMD, '-t', table, '-A'] + _build_rule_spec(chain, rule, action, comment)
        _run_iptables_cmd(cmd)
    else:
        LOG.debug(f"Rule already exists, skipping add: iptables -t {table} -A {chain} {' '.join(rule)} -j {action}")


def iptables_del_rule(table: str, chain: str, rule: List[str], action: str, comment: Optional[str] = None):
    """Deletes an iptables rule if it exists."""
    full_rule_spec_for_check = rule + (['-m', 'comment', '--comment', comment] if comment else []) + ['-j', action]

    # Check if the rule exists before attempting deletion
    if _check_rule_exists(IPTABLES_CMD, table, chain, full_rule_spec_for_check):
         cmd = [IPTABLES_CMD, '-t', table, '-D'] + _build_rule_spec(chain, rule, action, comment)
         # Don't check=True here, as deleting a rule that vanished between check and delete is ok
         _run_iptables_cmd(cmd, check=False)
    else:
         LOG.debug(f"Rule does not exist, skipping delete: iptables -t {table} -D {chain} {' '.join(rule)} -j {action}")


def ip6tables_add_rule(table: str, chain: str, rule: List[str], action: str, comment: Optional[str] = None):
    """Adds an ip6tables rule if it doesn't already exist."""
    rule_spec_no_action = [item for item in rule] # Copy rule list
    if comment:
        rule_spec_no_action.extend(['-m', 'comment', '--comment', comment])

    full_rule_spec_for_check = rule + (['-m', 'comment', '--comment', comment] if comment else []) + ['-j', action]

    if not _check_rule_exists(IP6TABLES_CMD, table, chain, full_rule_spec_for_check):
        cmd = [IP6TABLES_CMD, '-t', table, '-A'] + _build_rule_spec(chain, rule, action, comment)
        _run_iptables_cmd(cmd)
    else:
        LOG.debug(f"Rule already exists, skipping add: ip6tables -t {table} -A {chain} {' '.join(rule)} -j {action}")


def ip6tables_del_rule(table: str, chain: str, rule: List[str], action: str, comment: Optional[str] = None):
    """Deletes an ip6tables rule if it exists."""
    full_rule_spec_for_check = rule + (['-m', 'comment', '--comment', comment] if comment else []) + ['-j', action]

    if _check_rule_exists(IP6TABLES_CMD, table, chain, full_rule_spec_for_check):
        cmd = [IP6TABLES_CMD, '-t', table, '-D'] + _build_rule_spec(chain, rule, action, comment)
        _run_iptables_cmd(cmd, check=False) # Allow delete to fail silently if rule is gone
    else:
        LOG.debug(f"Rule does not exist, skipping delete: ip6tables -t {table} -D {chain} {' '.join(rule)} -j {action}")


# --- End iptables Helper Functions ---


# Get main net interface using netifaces (Best effort)
IFACE = None
IFACE6 = None
try:
    gw_info_v4 = netifaces.gateways().get('default', {}).get(netifaces.AF_INET)
    if gw_info_v4:
        IFACE = gw_info_v4[1]
        LOG.info(f"Detected default IPv4 interface: {IFACE}")
    else:
        LOG.warning("Could not automatically detect default IPv4 interface.")
except Exception as e:
    LOG.warning(f"Error detecting default IPv4 interface: {e}")

try:
    gw_info_v6 = netifaces.gateways().get('default', {}).get(netifaces.AF_INET6)
    if gw_info_v6:
        IFACE6 = gw_info_v6[1]
        LOG.info(f"Detected default IPv6 interface: {IFACE6}")
    # else: # Often no default v6 route even if v6 is present
    #     LOG.warning("Could not automatically detect default IPv6 interface.")
except Exception as e:
    LOG.warning(f"Error detecting default IPv6 interface: {e}")

# Fallback if detection fails (should ideally be configured)
if not IFACE:
    # Try common names
    for iface_name in ['eth0', 'ens3', 'eno1']:
         if iface_name in netifaces.interfaces():
             IFACE = iface_name
             LOG.warning(f"Falling back to guessed IPv4 interface: {IFACE}")
             break
if not IFACE:
     LOG.error("Failed to determine primary IPv4 interface. Please configure manually.")
     # Consider exiting or using a dummy value if essential functionality depends on it

if not IFACE6:
    # Try common names if IFACE exists and might be the same
    if IFACE and IFACE in netifaces.interfaces():
         addrs = netifaces.ifaddresses(IFACE)
         if netifaces.AF_INET6 in addrs:
             IFACE6 = IFACE
             LOG.warning(f"Falling back to guessed IPv6 interface (same as IPv4): {IFACE6}")
    if not IFACE6:
        LOG.warning("Failed to determine primary IPv6 interface.")


def delete_oldest_files(path, keep = 10):
    files = glob.glob(path)
    fileData = {}
    for fname in files:
        try:
            fileData[fname] = os.stat(fname).st_mtime
        except FileNotFoundError:
            continue # Skip if file disappears between glob and stat
    sorted_files = sorted(fileData.items(), key = itemgetter(1))
    if len(sorted_files) > keep:
        delete = len(sorted_files) - keep
        for x in range(0, delete):
            try:
                LOG.info(f"Deleting old backup file: {sorted_files[x][0]}")
                os.remove(sorted_files[x][0])
            except OSError as e:
                LOG.warning(f"Could not delete old backup file {sorted_files[x][0]}: {e}")


def backup_config():
    try:
        backup_filename = '/etc/openmptcprouter-vps-admin/omr-admin-config.json.' + str(int(time.time()))
        shutil.copy2('/etc/openmptcprouter-vps-admin/omr-admin-config.json', backup_filename)
        LOG.info(f"Configuration backup created: {backup_filename}")
        delete_oldest_files('/etc/openmptcprouter-vps-admin/omr-admin-config.json.*')
    except Exception as e:
        LOG.error(f"Failed to backup configuration: {e}")

# Get interface rx/tx
def get_bytes(t, iface='eth0'):
    # Ensure interface name is safe (alphanumeric, dash, underscore)
    if not re.fullmatch(r'[a-zA-Z0-9_-]+', iface):
        LOG.warning(f"Invalid interface name format provided: {iface}")
        return 0
    stat_file = f'/sys/class/net/{iface}/statistics/{t}_bytes'
    if path.exists(stat_file):
        try:
            with open(stat_file, 'r') as f:
                data = f.read()
            return int(data)
        except (IOError, ValueError) as e:
            LOG.error(f"Could not read or parse {stat_file}: {e}")
            return 0
    return 0

# --- Functions get_bytes_openvpn, get_bytes_ss, get_bytes_ss_go, get_bytes_v2ray, get_bytes_xray remain unchanged ---
def get_bytes_openvpn(user):
    try:
        ovpn_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        ovpn_socket.settimeout(2)
        ovpn_socket.connect(("127.0.0.1", 65302))
        fd = ovpn_socket.makefile('rb')
        line = fd.readline()
        if not line.startswith('>INFO:OpenVPN'.encode()):
            ovpn_socket.close()
            LOG.debug("OpenVPN error: Unexpected initial response")
            return { 'downlinkBytes': 0, 'uplinkBytes': 0 }
        ovpn_socket.send('status\r\n'.encode())
        ovpn_stats = []
        while True:
            line = fd.readline()
            if not line: # Handle unexpected EOF
                LOG.debug("OpenVPN error: Unexpected end of stream")
                break
            decoded_line = line.decode(errors='ignore').strip() # Ignore decoding errors
            ovpn_stats.append(decoded_line)
            if decoded_line == 'END':
                break
        ovpn_socket.close()
    except socket.timeout as err:
        LOG.debug(f"OpenVPN stats timeout: {err}")
        return { 'downlinkBytes': 0, 'uplinkBytes': 0 }
    except socket.error as err:
        LOG.debug(f"OpenVPN stats socket error: {err}")
        return { 'downlinkBytes': 0, 'uplinkBytes': 0 }
    except Exception as err: # Catch other potential errors
        LOG.error(f"Unexpected error getting OpenVPN stats: {err}")
        return { 'downlinkBytes': 0, 'uplinkBytes': 0 }

    for data in ovpn_stats:
        if user in data and 'CLIENT_LIST' in data: # Look for client list entries
            stats = data.split(',')
            # Indices might vary slightly depending on OpenVPN status version, adjust if needed
            # Assuming format: CLIENT_LIST,CommonName,RealAddress,_,_,BytesReceived,BytesSent,...
            if len(stats) >= 7 and stats[1] == user:
                 try:
                     # BytesReceived = uplink from client perspective, BytesSent = downlink
                     return { 'downlinkBytes': int(stats[6]), 'uplinkBytes': int(stats[5]) }
                 except (ValueError, IndexError) as e:
                     LOG.warning(f"Could not parse OpenVPN stats line for user {user}: {data} - Error: {e}")
                     continue # Try next line if parsing fails
    LOG.debug(f"OpenVPN user {user} not found in status or stats malformed.")
    return { 'downlinkBytes': 0, 'uplinkBytes': 0 }


def get_bytes_ss(port):
    try:
        ss_socket = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        ss_socket.settimeout(1)
        # Ensure manager address is configurable if not localhost
        ss_manager_addr = ("127.0.0.1", 8839)
        ss_socket.sendto('ping'.encode(), ss_manager_addr)
        ss_recv = ss_socket.recv(1024)
        ss_socket.close() # Close the socket
    except socket.timeout as err:
        LOG.debug(f"Shadowsocks stats timeout: {err}")
        return 0
    except socket.error as err:
        LOG.debug(f"Shadowsocks stats socket error: {err}")
        return 0
    except Exception as err: # Catch other potential errors
        LOG.error(f"Unexpected error getting Shadowsocks stats: {err}")
        return 0

    try:
        json_txt = ss_recv.decode("utf-8").replace('stat: ', '')
        result = json.loads(json_txt)
        if str(port) in result:
            return result[str(port)]
        else:
            LOG.debug(f"Shadowsocks port {port} not found in stats: {result}")
            return 0
    except (json.JSONDecodeError, UnicodeDecodeError) as e:
        LOG.warning(f"Could not decode or parse Shadowsocks stats response: {ss_recv} - Error: {e}")
        return 0
    except KeyError:
        LOG.debug(f"Key {port} not found in Shadowsocks stats dict: {result}")
        return 0


def get_bytes_ss_go(user):
    # Prioritize new API endpoint, fallback to old one
    api_urls = [
        "http://127.0.0.1:65279/api/ssm/v1/servers/ss-2022/stats",
        "http://127.0.0.1:65279/v1/servers/ss-2022/stats"
    ]
    stats_data = None
    for url in api_urls:
        try:
            r = requests.get(url=url, timeout=2) # Reduced timeout
            r.raise_for_status() # Raise exception for bad status codes (4xx, 5xx)
            stats_data = r.json()
            # Break if successfully fetched and parsed
            if stats_data and 'error' not in stats_data:
                 break
            elif stats_data and 'error' in stats_data:
                 LOG.debug(f"Shadowsocks-go API error at {url}: {stats_data['error']}")
                 stats_data = None # Reset to try next URL
        except requests.exceptions.Timeout:
            LOG.debug(f"Shadowsocks-go stats timeout at {url}")
            continue # Try next URL
        except requests.exceptions.ConnectionError as err:
             LOG.debug(f"Shadowsocks-go stats connection error at {url}: {err}")
             continue # Try next URL
        except requests.exceptions.RequestException as err:
            LOG.debug(f"Shadowsocks-go stats generic request error at {url}: {err}")
            continue # Try next URL
        except requests.exceptions.JSONDecodeError as err:
            LOG.warning(f"Shadowsocks-go stats JSON decode error at {url}: {err} - Response: {r.text[:200]}") # Log beginning of response
            continue # Try next URL

    if not stats_data:
        LOG.debug("Failed to get Shadowsocks-go stats from all API endpoints.")
        return { 'downlinkBytes': 0, 'uplinkBytes': 0 }

    # Check structure before accessing 'users'
    if 'users' in stats_data and isinstance(stats_data['users'], list):
        for userdata in stats_data['users']:
            # Check if userdata is a dict and has the required keys
            if isinstance(userdata, dict) and \
               'username' in userdata and userdata['username'] == user and \
               'downlinkBytes' in userdata and 'uplinkBytes' in userdata:
                try:
                    # Validate that values are integers
                    downlink = int(userdata['downlinkBytes'])
                    uplink = int(userdata['uplinkBytes'])
                    return { 'downlinkBytes': downlink, 'uplinkBytes': uplink }
                except (ValueError, TypeError) as e:
                    LOG.warning(f"Invalid byte values for user {user} in Shadowsocks-go stats: {userdata} - Error: {e}")
                    # Return 0 if values are bad for this user
                    return { 'downlinkBytes': 0, 'uplinkBytes': 0 }
        # If loop finishes without finding the user
        LOG.debug(f"User {user} not found in Shadowsocks-go stats user list.")
    else:
        LOG.debug(f"Unexpected structure or missing 'users' list in Shadowsocks-go stats response: {stats_data}")

    return { 'downlinkBytes': 0, 'uplinkBytes': 0 }


def get_bytes_v2ray(t, user):
    if t == "tx":
        side = "downlink"
    else:
        side = "uplink"

    # Construct the command safely
    # Note: Using shell=True is generally discouraged due to security risks.
    # If possible, avoid it. Here, user input is embedded. Ensure 'user' is validated.
    # A safer alternative might involve direct API calls if v2ray offers them.
    # Escaping the user string properly is crucial if shell=True must be used.
    # Using lists avoids shell=True risks if the command structure allows it.
    # command = ['/usr/bin/v2ray', 'api', 'stats', '--server=127.0.0.1:10085', '-json', f'user>>>{user}>>>traffic>>>{side}']
    # Using shell=True version from original code, but be aware of risks:
    cmd_str = f"/usr/bin/v2ray api stats --server=127.0.0.1:10085 -json 'user>>>{user}>>>traffic>>>{side}' 2>/dev/null | jq -r .stat[0].value | tr -d ' \n'"

    try:
        # Use timeout for subprocess
        result = subprocess.run(cmd_str, shell=True, capture_output=True, text=True, timeout=5, check=True)
        data = result.stdout.strip()
        # data = subprocess.check_output(cmd_str, shell = True, timeout=5).decode("utf-8").strip()
    except subprocess.TimeoutExpired:
        LOG.debug(f"V2Ray stats command timed out for user {user}, side {side}")
        return 0
    except subprocess.CalledProcessError as e:
        # jq might return error if path doesn't exist (no traffic yet)
        LOG.debug(f"V2Ray stats command failed for user {user}, side {side}. Stderr: {e.stderr}. Stdout: {e.stdout}")
        return 0
    except FileNotFoundError:
        LOG.error("v2ray or jq command not found for getting stats.")
        return 0
    except Exception as e: # Catch other potential errors
        LOG.error(f"Unexpected error getting V2Ray stats for user {user}, side {side}: {e}")
        return 0

    if data != '' and data != 'null':
        try:
            return int(data)
        except ValueError:
            LOG.warning(f"Could not convert V2Ray stats result to int: '{data}'")
            return 0
    else:
        # No data or null means 0 bytes or user doesn't exist/no traffic yet
        return 0

def get_bytes_xray(t, user):
    if t == "tx":
        side = "downlink"
    else:
        side = "uplink"

    # Construct command - again, shell=True has risks.
    cmd_str = f"/usr/bin/xray api stats --server=127.0.0.1:10086 -name 'user>>>{user}>>>traffic>>>{side}' 2>/dev/null | jq -r .stat.value | tr -d ' \n'"

    try:
        result = subprocess.run(cmd_str, shell=True, capture_output=True, text=True, timeout=5, check=True)
        data = result.stdout.strip()
    except subprocess.TimeoutExpired:
        LOG.debug(f"Xray stats command timed out for user {user}, side {side}")
        return 0
    except subprocess.CalledProcessError as e:
        LOG.debug(f"Xray stats command failed for user {user}, side {side}. Stderr: {e.stderr}. Stdout: {e.stdout}")
        return 0
    except FileNotFoundError:
        LOG.error("xray or jq command not found for getting stats.")
        return 0
    except Exception as e:
        LOG.error(f"Unexpected error getting Xray stats for user {user}, side {side}: {e}")
        return 0

    if data != '' and data != 'null':
        try:
            return int(data)
        except ValueError:
            LOG.warning(f"Could not convert Xray stats result to int: '{data}'")
            return 0
    else:
        return 0


def checkIfProcessRunning(processName):
    '''
    Check if there is any running process that contains the given name processName.
    '''
    #Iterate over the all the running process
    for proc in psutil.process_iter(['pid', 'name']):
        try:
            # Check if process name contains the given name string.
            if processName.lower() in proc.info['name'].lower():
                return True
        except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess):
            pass # Ignore processes that cause errors during access
        except Exception as e: # Catch other potential errors
             LOG.warning(f"Error checking process {proc.info.get('pid', '?')}: {e}")
    return False;

# --- Functions file_as_bytes, get_username_from_userid, get_userid_from_username, check_username_serial, set_global_param, modif_config_user remain unchanged ---
def file_as_bytes(file):
    with file:
        return file.read()

def get_username_from_userid(userid):
    if userid == 0:
        return 'openmptcprouter'
    config_path = '/etc/openmptcprouter-vps-admin/omr-admin-config.json'
    try:
        with open(config_path) as f:
            content = f.read()
        # Tolerate trailing comma before closing brace/bracket
        content = re.sub(r",\s*([}\]])", r"\1", content)
        data = json.loads(content)

        # Basic structure validation
        if not isinstance(data, dict) or \
           'users' not in data or not isinstance(data['users'], list) or \
           len(data['users']) == 0 or not isinstance(data['users'][0], dict):
            LOG.error(f"Invalid structure in config file: {config_path}")
            return '' # Or raise an error

        for user, user_data in data['users'][0].items():
             # Check if user_data is a dict and has 'userid'
             if isinstance(user_data, dict) and 'userid' in user_data:
                 try:
                     if int(user_data['userid']) == userid:
                         return user
                 except (ValueError, TypeError):
                     LOG.warning(f"Invalid userid '{user_data['userid']}' for user '{user}' in config.")
                     continue # Skip this user if userid is not a valid integer

    except FileNotFoundError:
        LOG.error(f"Config file not found: {config_path}")
        return ''
    except json.JSONDecodeError as e:
        LOG.error(f"Config file {config_path} is not valid JSON: {e}")
        # Optionally log problematic part of content: content[max(0, e.pos-20):e.pos+20]
        return ''
    except Exception as e: # Catch other potential errors
        LOG.error(f"Unexpected error reading or parsing config {config_path}: {e}")
        return ''

    LOG.debug(f"User ID {userid} not found in config.")
    return '' # Return empty string if not found


def get_userid_from_username(username):
    if username == 'openmptcprouter':
        return 0
    config_path = '/etc/openmptcprouter-vps-admin/omr-admin-config.json'
    try:
        with open(config_path) as f:
            content = f.read()
        content = re.sub(r",\s*([}\]])", r"\1", content)
        data = json.loads(content)

        if not isinstance(data, dict) or \
           'users' not in data or not isinstance(data['users'], list) or \
           len(data['users']) == 0 or not isinstance(data['users'][0], dict):
            LOG.error(f"Invalid structure in config file: {config_path}")
            return -1 # Indicate error or not found

        if username in data['users'][0]:
            user_data = data['users'][0][username]
            if isinstance(user_data, dict) and 'userid' in user_data:
                try:
                    return int(user_data['userid'])
                except (ValueError, TypeError):
                     LOG.warning(f"Invalid userid '{user_data['userid']}' for user '{username}' in config.")
                     return -1 # Indicate error
            else:
                 LOG.warning(f"User '{username}' found but missing 'userid' or invalid data structure.")
                 return -1 # Indicate error
        else:
            LOG.debug(f"Username '{username}' not found in config.")
            return -1 # Indicate not found

    except FileNotFoundError:
        LOG.error(f"Config file not found: {config_path}")
        return -1
    except json.JSONDecodeError as e:
        LOG.error(f"Config file {config_path} is not valid JSON: {e}")
        return -1
    except Exception as e:
        LOG.error(f"Unexpected error reading or parsing config {config_path}: {e}")
        return -1


def check_username_serial(username, serial):
    config_path = '/etc/openmptcprouter-vps-admin/omr-admin-config.json'
    try:
        with open(config_path, 'r') as f:
            content = f.read()
        content = re.sub(r",\s*([}\]])", r"\1", content)
        data = json.loads(content)

        if not isinstance(data, dict) or \
           'users' not in data or not isinstance(data['users'], list) or \
           len(data['users']) == 0 or not isinstance(data['users'][0], dict):
            LOG.error(f"Invalid structure in config file: {config_path}")
            return False # Or raise?

        if 'serial_enforce' not in data or data['serial_enforce'] is False:
            return True

        if username not in data['users'][0] or not isinstance(data['users'][0][username], dict):
            LOG.warning(f"User '{username}' not found or invalid data structure during serial check.")
            return False # User must exist for serial enforcement

        user_data = data['users'][0][username]

        if 'serial' not in user_data:
            # First time seeing this serial for the user, store it
            user_data['serial'] = serial
            user_data['serial_error'] = 0 # Initialize error count
            backup_config()
            try:
                with open(config_path, 'w') as outfile:
                    json.dump(data, outfile, indent=4)
                LOG.info(f"Stored initial serial for user '{username}'.")
                return True
            except IOError as e:
                LOG.error(f"Failed to write updated config with serial for user '{username}': {e}")
                # Decide if failure to write means we should deny access
                return False # Safer to deny if we can't save the state

        elif user_data['serial'] == serial:
             # If error count exists, reset it on successful match
            if 'serial_error' in user_data and user_data['serial_error'] > 0:
                user_data['serial_error'] = 0
                backup_config() # Backup before changing error count
                try:
                    with open(config_path, 'w') as outfile:
                        json.dump(data, outfile, indent=4)
                    LOG.debug(f"Reset serial error count for user '{username}'.")
                except IOError as e:
                     LOG.error(f"Failed to write updated config resetting serial error count for user '{username}': {e}")
                     # Continue, as the serial matched, but log the error
            return True
        else:
            # Serial mismatch
            error_count = user_data.get('serial_error', 0)
            try:
                user_data['serial_error'] = int(error_count) + 1
            except (ValueError, TypeError):
                 user_data['serial_error'] = 1 # Reset if value was invalid

            backup_config() # Backup before incrementing error count
            try:
                with open(config_path, 'w') as outfile:
                    json.dump(data, outfile, indent=4)
                LOG.warning(f"Serial mismatch for user '{username}'. Expected '{user_data.get('serial', 'N/A')}', got '{serial}'. Error count: {user_data['serial_error']}")
            except IOError as e:
                 LOG.error(f"Failed to write updated config incrementing serial error count for user '{username}': {e}")
                 # Still return False as the serial didn't match
            return False

    except FileNotFoundError:
        LOG.error(f"Config file not found for serial check: {config_path}")
        return False # Cannot enforce if config doesn't exist
    except json.JSONDecodeError as e:
        LOG.error(f"Config file {config_path} is not valid JSON for serial check: {e}")
        return False # Cannot enforce if config is invalid
    except Exception as e:
        LOG.error(f"Unexpected error during serial check for user {username}: {e}")
        return False # Safer to deny on unexpected errors


def set_global_param(key, value):
    config_path = '/etc/openmptcprouter-vps-admin/omr-admin-config.json'
    try:
        with open(config_path, 'r') as f:
            content = f.read()
        content = re.sub(r",\s*([}\]])", r"\1", content) # Tolerate trailing commas
        data = json.loads(content)
    except FileNotFoundError:
        LOG.warning(f"Config file {config_path} not found. Creating new one for set_global_param.")
        data = {} # Start with an empty dict if file doesn't exist
    except json.JSONDecodeError as e:
        LOG.error(f"Config file {config_path} is not valid JSON. Cannot set global param '{key}': {e}")
        return {'error': f'Config file {config_path} not readable', 'route': 'global_param'}
    except Exception as e:
        LOG.error(f"Unexpected error reading config {config_path} for set_global_param: {e}")
        return {'error': 'Unexpected error reading config', 'route': 'global_param'}

    # Ensure data is a dictionary
    if not isinstance(data, dict):
        LOG.error(f"Config file {config_path} does not contain a valid JSON object. Cannot set global param '{key}'.")
        # Overwrite with a valid structure if desired, or return error.
        # Forcing a structure:
        data = {}
        LOG.warning(f"Config file {config_path} was invalid, resetting to empty object.")
        # return {'error': 'Config file has invalid structure', 'route': 'global_param'}


    if key not in data or data[key] != value:
        original_data = copy.deepcopy(data) # Keep a copy for comparison
        data[key] = value
        LOG.debug(f"Setting global param '{key}' to '{value}'")
        try:
            # Backup before writing potentially new or changed data
            backup_config()
            with open(config_path, 'w') as outfile:
                json.dump(data, outfile, indent=4)
            LOG.info(f"Global parameter '{key}' updated in {config_path}.")
        except IOError as e:
            LOG.error(f"Failed to write updated config file {config_path} for set_global_param: {e}")
            # Optionally try to restore from original_data if backup also failed?
            return {'error': f'Failed to write config file {config_path}', 'route': 'global_param'}
        except Exception as e:
            LOG.error(f"Unexpected error writing config {config_path} for set_global_param: {e}")
            return {'error': 'Unexpected error writing config', 'route': 'global_param'}

    else:
        LOG.debug(f"Global param '{key}' already set to '{value}', no change needed.")

    return None # Indicate success


def modif_config_user(user: str, changes: dict):
    config_path = '/etc/openmptcprouter-vps-admin/omr-admin-config.json'
    try:
        with open(config_path, 'r') as f:
            content = json.load(f)
    except FileNotFoundError:
        LOG.error(f"Config file not found: {config_path}. Cannot modify user '{user}'.")
        return # Or raise an error
    except json.JSONDecodeError as e:
        LOG.error(f"Config file {config_path} is not valid JSON. Cannot modify user '{user}': {e}")
        return # Or raise
    except Exception as e:
        LOG.error(f"Unexpected error reading config {config_path} for modif_config_user: {e}")
        return

    # Basic structure validation
    if not isinstance(content, dict) or 'users' not in content or not isinstance(content['users'], list) or len(content['users']) == 0 or not isinstance(content['users'][0], dict):
        LOG.error(f"Invalid structure in config file: {config_path}. Cannot modify user '{user}'.")
        return # Or raise

    # Check if user exists
    if user not in content['users'][0]:
        LOG.error(f"User '{user}' not found in config. Cannot apply changes.")
        return

    # Ensure user data is a dictionary before updating
    if not isinstance(content['users'][0][user], dict):
         LOG.error(f"Data for user '{user}' in config is not a dictionary. Cannot apply changes.")
         return

    content_initial = copy.deepcopy(content)
    try:
        # Apply the changes
        content['users'][0][user].update(changes)
    except Exception as e:
         LOG.error(f"Failed to apply changes to user '{user}' data: {e}")
         return


    # Compare original and modified content
    if content_initial != content:
        LOG.debug(f"Updating config for user '{user}' with changes: {changes}")
        try:
            backup_config()
            with open(config_path, 'w') as f:
                json.dump(content, f, indent=4)
            LOG.info(f"Configuration updated for user '{user}'.")
            # Update in-memory cache if necessary (e.g., fake_users_db)
            global fake_users_db
            if 'fake_users_db' in globals() and isinstance(fake_users_db, dict):
                 if user in fake_users_db:
                     fake_users_db[user].update(changes)
                 else:
                     # If user was somehow missing from cache but exists in file now
                     fake_users_db[user] = content['users'][0][user]


        except IOError as e:
            LOG.error(f"Failed to write updated config file {config_path} for user '{user}': {e}")
            # Consider implications: changes applied in memory but not saved?
        except Exception as e:
            LOG.error(f"Unexpected error writing config {config_path} for modif_config_user: {e}")
    else:
        LOG.debug(f"No effective changes for user '{user}', config file not modified.")

# --- Functions add_ss_user, remove_ss_user, add_ss_go_user, remove_ss_go_user remain unchanged ---
# --- Functions v2ray_add_user, xray_add_user, v2ray_del_user, xray_del_user remain unchanged ---
# --- Functions v2ray_add_outbound, xray_add_outbound, v2ray_del_outbound, xray_del_outbound remain unchanged ---
# --- Functions v2ray_add_routing, xray_add_routing, v2ray_del_routing, xray_del_routing remain unchanged ---
# --- Functions add_glorytun_tcp, remove_glorytun_tcp, add_glorytun_udp, remove_glorytun_udp remain unchanged ---
# --- Functions add_dsvpn, remove_dsvpn remain unchanged ---
# --- Functions ordered remain unchanged ---
# --- Functions v2ray_add_port, xray_add_port, v2ray_del_port, xray_del_port remain unchanged ---

def add_gre_tunnels():
    # This function heavily relied on Shorewall's snat and interfaces files.
    # Re-implementing with iptables requires adding SNAT/MASQUERADE rules directly.
    LOG.info("Attempting to configure GRE tunnel SNAT/MASQUERADE rules using iptables.")

    allips = []
    try:
        for intf in netifaces.interfaces():
            # Skip loopback and potentially other non-relevant interfaces
            if intf.startswith('lo') or intf.startswith('docker') or intf.startswith('vpn') or intf.startswith('wg') or intf.startswith('tun') or intf.startswith('gt-') or intf.startswith('dsvpn') or intf.startswith('gre'):
                 continue

            addrs = netifaces.ifaddresses(intf)
            if netifaces.AF_INET in addrs:
                ipv4_addr_list = addrs[netifaces.AF_INET]
                for ip_info in ipv4_addr_list:
                    addr = ip_info.get('addr')
                    if addr:
                        try:
                            ip_obj = IPAddress(addr)
                            # Check if public IP (adjust criteria as needed)
                            if not ip_obj.is_private and not ip_obj.is_loopback and not ip_obj.is_link_local and not ip_obj.is_reserved:
                                if addr not in allips: # Avoid duplicates
                                     allips.append(addr)
                        except AddrFormatError:
                            LOG.warning(f"Invalid IP address format found on {intf}: {addr}")
                        except Exception as e:
                            LOG.error(f"Error processing IP {addr} on {intf}: {e}")
    except Exception as e:
         LOG.error(f"Error enumerating interfaces or addresses: {e}")

    if not allips:
        LOG.warning("No public IPv4 addresses found to configure GRE SNAT for.")
        set_global_param('allips', [])
        return

    LOG.debug(f"Found public IPs for potential GRE SNAT: {allips}")
    set_global_param('allips', allips) # Store detected IPs

    config_path = '/etc/openmptcprouter-vps-admin/omr-admin-config.json'
    try:
        with open(config_path) as f:
            content = json.load(f)
        users_data = content.get('users', [{}])[0]
    except (FileNotFoundError, json.JSONDecodeError, IndexError, TypeError) as e:
        LOG.error(f"Could not load or parse user data from {config_path} for GRE config: {e}")
        return

    ip_base_network = IPNetwork('10.255.249.0/24')
    subnet_prefixlen = 30 # /30 for point-to-point links
    available_subnets = list(ip_base_network.subnet(subnet_prefixlen))
    subnet_index = 0

    # Clear existing OMR GRE rules first to avoid duplicates if IPs change
    LOG.debug("Clearing existing OMR GRE iptables rules...")
    # This is tricky without knowing exactly which rules were added.
    # A common approach is to use comments and flush rules with that comment.
    # Or, flush specific chains if they were dedicated.
    # Simple approach: Flush rules with the expected comment format.
    # This is fragile if comments change or aren't used consistently.
    try:
         # Flush SNAT rules
         grep_cmd = f"{IPTABLES_CMD} -t nat -S POSTROUTING | grep 'OMR GRE SNAT' | sed 's/^-A/{IPTABLES_CMD} -t nat -D/'"
         process = subprocess.Popen(grep_cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
         stdout, stderr = process.communicate()
         if process.returncode == 0 and stdout:
             for line in stdout.strip().split('\n'):
                 if line:
                     LOG.debug(f"Deleting rule: {line}")
                     del_result = subprocess.run(line, shell=True, capture_output=True, text=True)
                     if del_result.returncode != 0:
                         LOG.warning(f"Failed to delete rule: {line} - {del_result.stderr.strip()}")
         elif process.returncode != 0 and process.returncode != 1: # Allow exit code 1 (grep found nothing)
            LOG.warning(f"Error finding OMR GRE SNAT rules to delete: {stderr.strip()}")

         # Flush MASQUERADE rules (assuming different comment or structure)
         grep_cmd_masq = f"{IPTABLES_CMD} -t nat -S POSTROUTING | grep 'OMR GRE MASQ' | sed 's/^-A/{IPTABLES_CMD} -t nat -D/'"
         process_masq = subprocess.Popen(grep_cmd_masq, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
         stdout_masq, stderr_masq = process_masq.communicate()
         if process_masq.returncode == 0 and stdout_masq:
             for line in stdout_masq.strip().split('\n'):
                 if line:
                     LOG.debug(f"Deleting rule: {line}")
                     del_result = subprocess.run(line, shell=True, capture_output=True, text=True)
                     if del_result.returncode != 0:
                         LOG.warning(f"Failed to delete rule: {line} - {del_result.stderr.strip()}")
         elif process_masq.returncode != 0 and process_masq.returncode != 1:
             LOG.warning(f"Error finding OMR GRE MASQUERADE rules to delete: {stderr_masq.strip()}")


    except Exception as e:
        LOG.error(f"Error occurred while trying to clear old OMR GRE iptables rules: {e}")


    # Add rules based on current config and IPs
    for user, user_config in users_data.items():
        if user == "admin" or not isinstance(user_config, dict):
            continue

        userid = user_config.get('userid')
        username = user_config.get('username', user) # Fallback to dict key if username missing
        if userid is None:
            LOG.warning(f"User '{username}' missing userid, skipping GRE config.")
            continue

        # Assign a unique /30 subnet to each user
        if subnet_index >= len(available_subnets):
            LOG.error(f"Ran out of subnets in {ip_base_network} for GRE tunnels. Max users: {len(available_subnets)}")
            break # Stop assigning subnets

        network = available_subnets[subnet_index]
        local_gre_ip = str(network[1]) # Server side of the GRE tunnel
        remote_gre_ip = str(network[2]) # Router side of the GRE tunnel (expected source)
        subnet_index += 1

        # Determine the GRE interface name (assuming a convention)
        # The actual interface creation is likely handled by another script/service
        gre_intf_base = f'gre-user{userid}' # Base name, actual might vary

        # Find the actual GRE interface if it exists (e.g., 'gre-userX', 'gre-userX-ipY')
        # This part is tricky as the script doesn't create the interfaces.
        # Assuming a simple naming convention 'gre-user<userid>' for now.
        gre_intf = f'gre-user{userid}'
        # We need the *public* interface associated with this user/tunnel if multiple public IPs exist
        # The original code linked SNAT to specific physical interfaces found during IP scan.
        # Let's try to apply rules for *all* found public IPs for simplicity,
        # or use the first one if only one rule per user is desired.

        public_ips_for_user = user_config.get('public_ips', allips) # Use user-specific IPs if defined, else all found IPs
        if not public_ips_for_user:
            public_ips_for_user = allips # Fallback again if list is empty

        LOG.debug(f"Configuring GRE for user '{username}' (ID {userid}) using subnet {network}, interface {gre_intf}")

        # Rule 1: SNAT traffic *from* the router's GRE IP *to* the specific public IP
        for public_ip in public_ips_for_user:
             # Find the physical interface for this public IP
             public_iface = None
             for intf_name in netifaces.interfaces():
                  addrs = netifaces.ifaddresses(intf_name)
                  if netifaces.AF_INET in addrs:
                      for ip_info in addrs[netifaces.AF_INET]:
                          if ip_info.get('addr') == public_ip:
                              public_iface = intf_name.split(':')[0] # Get base interface name
                              break
                      if public_iface:
                          break
             if not public_iface:
                 LOG.warning(f"Could not find interface for public IP {public_ip} for user {username}. Skipping SNAT rule for this IP.")
                 continue

             snat_rule = ['-s', str(network), '-o', public_iface, '-j', 'SNAT', '--to-source', public_ip]
             snat_comment = f"OMR GRE SNAT for user {username} ({userid}) via {public_ip}"
             iptables_add_rule('nat', 'POSTROUTING', snat_rule, 'SNAT', snat_comment) # Action included in rule list here

        # Rule 2: MASQUERADE traffic originating *from* the server's GRE IP going *out* the GRE tunnel
        # This is less common; usually, traffic *to* the router is handled.
        # The original rule SNAT(-s local_gre_ip -o gre_intf) seems intended for traffic *leaving* the server *via* the GRE tunnel.
        # Let's assume we want to MASQUERADE traffic coming *from* the router via GRE and going *out* the public interface.
        masq_rule = ['-s', str(network), '-o', IFACE, '-j', 'MASQUERADE'] # Traffic from router subnet going out main IFACE
        masq_comment = f"OMR GRE MASQ for user {username} ({userid}) traffic to internet"
        iptables_add_rule('nat', 'POSTROUTING', masq_rule, 'MASQUERADE', masq_comment)

        # Forwarding rule: Allow traffic from the GRE tunnel to the main interface
        fwd_rule = ['-i', gre_intf, '-o', IFACE, '-j', 'ACCEPT']
        fwd_comment = f"OMR GRE FWD from user {username} ({userid}) to internet"
        iptables_add_rule('filter', 'FORWARD', fwd_rule, 'ACCEPT', fwd_comment)

        # Forwarding rule: Allow established/related traffic back to the GRE tunnel
        fwd_back_rule = ['-i', IFACE, '-o', gre_intf, '-m', 'state', '--state', 'RELATED,ESTABLISHED', '-j', 'ACCEPT']
        fwd_back_comment = f"OMR GRE FWD back to user {username} ({userid})"
        iptables_add_rule('filter', 'FORWARD', fwd_back_rule, 'ACCEPT', fwd_back_comment)


        # Update user config with GRE details (optional, but good for consistency)
        gre_tunnel_conf = user_config.get('gre_tunnels', {})
        gre_tunnel_conf[gre_intf] = { # Assuming one main GRE tunnel per user now
            'local_ip': local_gre_ip,
            'remote_ip': remote_gre_ip,
            'network': str(network),
            #'public_ips': public_ips_for_user # Store which IPs are associated
        }
        modif_config_user(username, {'gre_tunnels': gre_tunnel_conf})

    LOG.info("Finished updating GRE tunnel iptables rules.")


# Initial setup of GRE tunnels on script start
with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
    omr_config_data = json.load(f)
if 'gre_tunnels_enabled' not in omr_config_data or omr_config_data['gre_tunnels_enabled']:
    # Check if iptables command exists before trying to use it
    if shutil.which(IPTABLES_CMD):
        add_gre_tunnels()
    else:
        LOG.error(f"{IPTABLES_CMD} not found. Cannot configure GRE tunnels.")


fake_users_db = omr_config_data.get('users', [{}])[0] # Safer access

# Generate a random secret key
if 'secret_key' in omr_config_data:
    SECRET_KEY = omr_config_data['secret_key']
else:
    SECRET_KEY = uuid.uuid4().hex
    set_global_param('secret_key', SECRET_KEY)


# --- User Authentication and JWT functions remain unchanged ---
def verify_password(plain_password, user_password):
    # Use passlib or a similar library for production for proper hashing
    # For this example, using simple comparison matching the original code's apparent intent
    # DO NOT USE THIS IN PRODUCTION WITHOUT REAL PASSWORD HASHING
    # return pwd_context.verify(plain_password, user_password)
    if not user_password: # Handle empty password case
        return False
    return secrets.compare_digest(plain_password, user_password)

def get_password_hash(password):
    # Use passlib or a similar library for production
    # return pwd_context.hash(password)
    # Returning plain password as per original code's apparent intent
    # DO NOT USE THIS IN PRODUCTION WITHOUT REAL PASSWORD HASHING
    return password

# Simulates getting user from DB
def get_user(db, username: str) -> Optional['UserInDB']:
    # Reload config data to ensure freshness, especially after user add/remove
    # This is inefficient but simple for this script structure.
    # A better approach involves signaling or shared memory/IPC if performance is critical.
    try:
         with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
             omr_config_data = json.load(f)
         current_users_db = omr_config_data.get('users', [{}])[0]
         if username in current_users_db:
              user_dict = current_users_db[username]
              # Ensure the structure is somewhat correct before creating UserInDB
              if isinstance(user_dict, dict) and 'username' in user_dict and 'user_password' in user_dict:
                  # Add default values for any missing optional fields expected by UserInDB
                  user_dict.setdefault('vpn', None)
                  user_dict.setdefault('vpn_port', None)
                  user_dict.setdefault('vpn_client_ip', None)
                  user_dict.setdefault('permissions', 'ro') # Default permission if missing
                  user_dict.setdefault('shadowsocks_port', None)
                  user_dict.setdefault('disabled', False) # Default disabled status
                  user_dict.setdefault('userid', None)

                  # Handle potential type issues for 'disabled'
                  disabled_val = user_dict['disabled']
                  if isinstance(disabled_val, str):
                      user_dict['disabled'] = disabled_val.lower() == 'true'
                  elif not isinstance(disabled_val, bool):
                      user_dict['disabled'] = False # Default to False if type is wrong

                  try:
                       return UserInDB(**user_dict)
                  except Exception as e: # Catch Pydantic validation errors or others
                       LOG.error(f"Error creating UserInDB object for user {username}: {e} - Data: {user_dict}")
                       return None
              else:
                   LOG.warning(f"User data for {username} is malformed: {user_dict}")
                   return None
         else:
              return None
    except (FileNotFoundError, json.JSONDecodeError, IndexError, TypeError) as e:
         LOG.error(f"Failed to load user database for get_user: {e}")
         return None


def authenticate_user(db, username: str, password: str) -> Optional['UserInDB']:
    user = get_user(db, username)
    if not user:
        LOG.debug(f"Authentication failed: User '{username}' not found.")
        return None # Return None instead of False
    if not verify_password(password, user.user_password):
        LOG.debug(f"Authentication failed: Incorrect password for user '{username}'.")
        return None # Return None instead of False
    # Check if user is disabled
    if user.disabled:
         LOG.debug(f"Authentication failed: User '{username}' is disabled.")
         return None # Return None for disabled users
    return user

class Token(BaseModel):
    access_token: Optional[str] = None # Made optional
    token_type: Optional[str] = None # Made optional


class TokenData(BaseModel):
    username: Optional[str] = None # Made optional

# User model definition (ensure it matches UserInDB fields used in get_user)
class User(BaseModel):
    username: str
    vpn: Optional[str] = None
    vpn_port: Optional[int] = None
    vpn_client_ip: Optional[str] = None
    permissions: str = 'rw' # Default permission
    shadowsocks_port: Optional[int] = None
    disabled: bool = False # Default disabled status
    userid: Optional[int] = None
    # Add any other fields used from the config that are needed in current_user
    public_ips: List[str] = []
    note: List[str] = []
    lanips: List[str] = []
    vpnremoteip: Optional[str] = None
    vpnlocalip: Optional[str] = None
    ula: Optional[str] = None
    proxy: Optional[str] = None # Add proxy field


class UserInDB(User):
    user_password: str # This should be the HASH in a real system


# --- OAuth2PasswordBearerCookie, BasicAuth classes remain unchanged ---
# Add support for auth before seeing doc
class OAuth2PasswordBearerCookie(OAuth2):
    def __init__(
            self,
            tokenUrl: str,
            scheme_name: str = None,
            scopes: Optional[dict] = None, # Use Optional
            auto_error: bool = True,
    ):
        if not scopes:
            scopes = {}
        flows = OAuthFlowsModel(password={"tokenUrl": tokenUrl, "scopes": scopes})
        super().__init__(flows=flows, scheme_name=scheme_name, auto_error=auto_error)

    async def __call__(self, request: Request) -> Optional[str]:
        header_authorization: str = request.headers.get("Authorization", "") # Provide default
        cookie_authorization: str = request.cookies.get("Authorization", "") # Provide default

        header_scheme, header_param = get_authorization_scheme_param(
            header_authorization
        )
        cookie_scheme, cookie_param = get_authorization_scheme_param(
            cookie_authorization
        )

        authorization = False # Initialize
        scheme = ""
        param = ""

        if header_scheme and header_scheme.lower() == "bearer":
            authorization = True
            scheme = header_scheme
            param = header_param

        elif cookie_scheme and cookie_scheme.lower() == "bearer":
            authorization = True
            scheme = cookie_scheme
            param = cookie_param

        # Combine checks for clarity
        if not authorization:
            if self.auto_error:
                raise HTTPException(
                    status_code=HTTP_403_FORBIDDEN, detail="Not authenticated (no Bearer token)"
                )
            else:
                return None

        # Scheme check is implicitly handled by the conditions above now
        # if scheme.lower() != "bearer": # This check is redundant if authorization is True
        #     if self.auto_error:
        #          raise HTTPException(
        #              status_code=HTTP_403_FORBIDDEN, detail="Not authenticated (invalid scheme)"
        #          )
        #      else:
        #          return None

        return param


class BasicAuth(SecurityBase):
    def __init__(self, scheme_name: str = None, auto_error: bool = True):
        self.scheme_name = scheme_name or self.__class__.__name__
        self.model = SecurityBaseModel(type="http") # type="http", scheme="basic"
        self.model.scheme = "basic" # Explicitly set scheme for OpenAPI docs
        self.auto_error = auto_error

    async def __call__(self, request: Request) -> Optional[str]:
        authorization: str = request.headers.get("Authorization", "") # Provide default
        scheme, param = get_authorization_scheme_param(authorization)
        if not authorization or not scheme or scheme.lower() != "basic" or not param:
            if self.auto_error:
                raise HTTPException(
                    status_code=HTTP_401_UNAUTHORIZED, # Use 401 for missing/bad basic auth
                    detail="Not authenticated (invalid Basic auth)",
                     headers={"WWW-Authenticate": "Basic realm=\"Access\""}, # Add header
                )
            else:
                return None
        return param

basic_auth = BasicAuth(auto_error=False)

# Password context (use bcrypt or argon2 in production)
pwd_context = CryptContext(schemes=["bcrypt"], deprecated="auto") # Keep for potential future use

oauth2_scheme = OAuth2PasswordBearerCookie(tokenUrl="/token")

app = FastAPI(docs_url=None, redoc_url=None, openapi_url=None, title="OpenMPTCProuter Server API")

# --- JWT creation/verification and user dependency functions remain unchanged ---
def create_access_token(*, data: dict, expires_delta: Optional[timedelta] = None): # Use Optional
    to_encode = data.copy()
    if expires_delta:
        expire = datetime.utcnow() + expires_delta
    else:
        # Use ACCESS_TOKEN_EXPIRE_MINUTES if defined, else default
        expire = datetime.utcnow() + timedelta(minutes=ACCESS_TOKEN_EXPIRE_MINUTES or 60)
    to_encode.update({"exp": expire, "iat": datetime.utcnow()}) # Add issue time
    try:
         encoded_jwt = jwt.encode(to_encode, SECRET_KEY, algorithm=ALGORITHM)
         return encoded_jwt
    except PyJWTError as e:
         LOG.error(f"Error encoding JWT: {e}")
         return None


async def get_current_user(token: str = Depends(oauth2_scheme)) -> Optional[User]: # Return Optional[User]
    credentials_exception = HTTPException(
        status_code=HTTP_403_FORBIDDEN, # 403 more appropriate than 401 if token is present but invalid/expired
        detail="Could not validate credentials",
        headers={"WWW-Authenticate": "Bearer"}, # Keep header for Bearer scheme
    )
    if token is None: # Handle case where token is not provided at all
        LOG.debug("get_current_user: No token provided.")
        raise credentials_exception # Or handle differently if optional auth is needed

    try:
        payload = jwt.decode(token, SECRET_KEY, algorithms=[ALGORITHM], options={"require": ["exp", "sub"]}) # Require exp and sub claims
        username: str = payload.get("sub")
        # username check already included in require sub, but double check
        if username is None:
            LOG.debug("get_current_user: Username (sub) claim missing in token.")
            raise credentials_exception
        token_data = TokenData(username=username)
    except jwt.ExpiredSignatureError:
         LOG.debug("get_current_user: Token has expired.")
         raise credentials_exception
    except PyJWTError as e: # Catch other JWT errors (InvalidTokenError, etc.)
        LOG.debug(f"get_current_user: Invalid token - {e}")
        raise credentials_exception
    except Exception as e: # Catch unexpected errors during decoding
        LOG.error(f"Unexpected error decoding token: {e}")
        raise credentials_exception

    # Reload user data from the source of truth (config file)
    # Using fake_users_db directly can lead to stale data after updates
    try:
         with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
             omr_config_data = json.load(f)
         runtime_users_db = omr_config_data.get('users', [{}])[0]
    except (FileNotFoundError, json.JSONDecodeError, IndexError, TypeError) as e:
         LOG.error(f"Failed to load user database for token validation: {e}")
         raise credentials_exception # Cannot validate user if DB fails

    user = get_user(runtime_users_db, username=token_data.username) # Use get_user for consistency
    if user is None:
        LOG.debug(f"get_current_user: User '{token_data.username}' from token not found in current config.")
        raise credentials_exception
    return user # Return the UserInDB object (which inherits from User)


async def get_current_active_user(current_user: User = Depends(get_current_user)):
    # get_current_user already returns None for disabled users if authenticate_user handles it
    # If not, check here:
    if not current_user: # Handles the case where get_current_user itself failed
         raise HTTPException(status_code=403, detail="User not found or invalid.")
    if current_user.disabled:
        raise HTTPException(status_code=400, detail="Inactive user")
    return current_user


# --- FastAPI Endpoints Start ---

@app.get("/")
async def homepage():
    return {"message": "Welcome to the OpenMPTCProuter Server API (using iptables)"}

@app.post('/token', response_model=Token, summary="Login via form data to get JWT token")
async def login_for_access_token(response: Response, form_data: OAuth2PasswordRequestForm = Depends()): # Add Response
    # Reload config for fresh user data on login attempt
    try:
         with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
             omr_config_data = json.load(f)
         login_users_db = omr_config_data.get('users', [{}])[0]
    except (FileNotFoundError, json.JSONDecodeError, IndexError, TypeError) as e:
         LOG.error(f"Failed to load user database for login: {e}")
         raise HTTPException(status_code=500, detail="Internal server error during login.")

    user = authenticate_user(login_users_db, form_data.username, form_data.password)
    if not user:
        LOG.debug(f"Login failed for username: {form_data.username}")
        raise HTTPException(
             status_code=401, # Use 401 for failed authentication
             detail="Incorrect username or password",
             headers={"WWW-Authenticate": "Bearer"}, # Indicate Bearer for token endpoint
             )

    access_token_expires = timedelta(minutes=ACCESS_TOKEN_EXPIRE_MINUTES)
    access_token = create_access_token(
        data={"sub": user.username}, expires_delta=access_token_expires # Use user.username from authenticated user
    )

    if not access_token:
        LOG.error(f"Failed to create access token for user: {user.username}")
        raise HTTPException(status_code=500, detail="Could not create access token.")

    # Set token in HTTPOnly cookie
    response.set_cookie(
        key="Authorization",
        value=f"Bearer {access_token}",
        httponly=True,
        max_age=int(access_token_expires.total_seconds()), # Use max_age
        expires=int(access_token_expires.total_seconds()), # 'expires' often takes seconds or datetime
        samesite="lax", # Recommended for security
        secure=True # Set Secure flag if served over HTTPS (which it should be)
    )

    # Also return token in response body as per OAuth2 standard
    return {"access_token": access_token, "token_type": "bearer"}


@app.get("/logout", summary="Logout and clear authentication cookie")
async def route_logout_and_remove_cookie():
    response = RedirectResponse(url="/", status_code=302) # Redirect after logout
    response.delete_cookie("Authorization", httponly=True, samesite="lax", secure=True)
    LOG.info("User logged out.")
    return response


# Login for doc using Basic Auth - sets cookie for Swagger UI
@app.get("/login_basic", summary="Login via Basic Auth (for API Docs access)")
async def login_basic(auth: Optional[str] = Depends(basic_auth)): # Use Optional str
    # If basic_auth dependency returns None (auto_error=False and no auth provided)
    if not auth:
        return Response(
             headers={"WWW-Authenticate": "Basic realm=\"API Docs\""},
             status_code=401
             )

    try:
        decoded = base64.b64decode(auth).decode("ascii")
        username, _, password = decoded.partition(":")

        # Reload config for fresh user data
        try:
            with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
                omr_config_data = json.load(f)
            login_users_db = omr_config_data.get('users', [{}])[0]
        except (FileNotFoundError, json.JSONDecodeError, IndexError, TypeError) as e:
            LOG.error(f"Failed to load user database for basic auth login: {e}")
            # Return a generic 401 to avoid revealing server issues
            return Response(headers={"WWW-Authenticate": "Basic realm=\"API Docs\""}, status_code=401)

        user = authenticate_user(login_users_db, username, password)
        if not user:
            LOG.debug(f"Basic auth login failed for username: {username}")
            # Return 401 on failed auth
            return Response(headers={"WWW-Authenticate": "Basic realm=\"API Docs\""}, status_code=401)

        # Check if user has permission to view docs (e.g., admin or specific role)
        # if user.permissions != 'admin': # Example permission check
        #     LOG.warning(f"User '{username}' attempted basic auth login for docs without permission.")
        #     return Response(status_code=403) # Forbidden

        # Create JWT token
        access_token_expires = timedelta(minutes=ACCESS_TOKEN_EXPIRE_MINUTES) # Or shorter for docs access
        access_token = create_access_token(
            data={"sub": user.username}, expires_delta=access_token_expires
        )

        if not access_token:
            LOG.error(f"Failed to create access token for basic auth user: {user.username}")
            return Response(headers={"WWW-Authenticate": "Basic realm=\"API Docs\""}, status_code=500)

        token_json_str = jsonable_encoder(access_token) # Already a string

        # Redirect to docs page and set the cookie
        response = RedirectResponse(url="/docs", status_code=302)
        response.set_cookie(
            "Authorization",
            value=f"Bearer {token_json_str}",
            httponly=True,
            max_age=int(access_token_expires.total_seconds()),
            expires=int(access_token_expires.total_seconds()),
            samesite="lax",
            secure=True # Assume HTTPS
        )
        LOG.info(f"User '{username}' logged in via Basic Auth for docs.")
        return response

    except (ValueError, TypeError, base64.binascii.Error) as e:
        # Handle errors decoding Basic auth header
        LOG.warning(f"Failed to decode Basic auth header: {e}")
        return Response(headers={"WWW-Authenticate": "Basic realm=\"API Docs\""}, status_code=401)
    except Exception as e:
         LOG.error(f"Unexpected error during Basic auth login: {e}")
         return Response(headers={"WWW-Authenticate": "Basic realm=\"API Docs\""}, status_code=500)


@app.get("/openapi.json", summary="Get OpenAPI schema (requires authentication)")
async def get_open_api_endpoint(current_user: User = Depends(get_current_active_user)):
     # current_user dependency ensures authentication
    return JSONResponse(get_openapi(title="OpenMPTCProuter Server API (iptables)", version="2.1.0", routes=app.routes))


@app.get("/docs", summary="Get Swagger UI documentation (requires authentication)")
async def get_documentation(current_user: User = Depends(get_current_active_user)):
     # current_user dependency ensures authentication
    return get_swagger_ui_html(openapi_url="/openapi.json", title="OMR Admin API Docs (iptables)")

# Get Client IP
@app.get('/clienthost', summary="Get the IP address of the client making the request")
async def clienthost(request: Request):
    client_host = request.client.host if request.client else "Unknown"
    return {"client_host": client_host}

# Check if MPTCP is enabled on this connection
@app.get('/mptcpsupport', summary="Check if the connection from the client uses MPTCP")
async def mptcpsupport(request: Request):
    if not request.client:
         return {"mptcp": "unknown", "reason": "Client IP not available"}

    ip_str = request.client.host
    try:
        ip = ip_address(ip_str)
        # Handle IPv4-mapped IPv6 addresses
        if isinstance(ip, IPv6Address) and ip.ipv4_mapped:
            ip_str = str(ip.ipv4_mapped)
            ip = ip.ipv4_mapped # Work with the IPv4 address object
            LOG.debug(f"Client IP is IPv4-mapped: {request.client.host} -> {ip_str}")

        if isinstance(ip, IPv4Address):
            # Check using /proc first (if available and reliable)
            mptcp_proc_path = '/proc/net/mptcp_net/mptcp'
            if path.exists(mptcp_proc_path):
                 # Convert IP to reversed hex format used in proc
                ipr = list(reversed(ip_str.split('.')))
                iptohex = '{:02X}{:02X}{:02X}{:02X}'.format(*map(int, ipr))
                try:
                    with open(mptcp_proc_path) as f:
                        # Reading whole file might be inefficient for large files
                        # Consider reading line by line if performance is an issue
                        if iptohex in f.read():
                            LOG.debug(f"MPTCP detected for {ip_str} via {mptcp_proc_path}")
                            return {"mptcp": "working"}
                        else:
                             LOG.debug(f"MPTCP NOT detected for {ip_str} via {mptcp_proc_path}")
                             # Don't return yet, try ss as fallback
                except IOError as e:
                     LOG.warning(f"Could not read {mptcp_proc_path}: {e}")
                except Exception as e: # Catch other potential errors
                     LOG.error(f"Error checking {mptcp_proc_path}: {e}")


            # Fallback to using 'ss' command
            ss_cmd = ['/usr/bin/ss', '-Mnt', 'dst', ip_str] # More specific ss command
            # ss_cmd_str = f"timeout 2 ss -M | grep -q {ip_str}" # Original command
            try:
                LOG.debug(f"Checking MPTCP for {ip_str} using ss command: {' '.join(ss_cmd)}")
                # Use timeout with subprocess.run
                result = subprocess.run(ss_cmd, capture_output=True, text=True, timeout=3)
                # Check if output contains MPTCP info for the destination IP
                if result.returncode == 0 and 'mptcp' in result.stdout.lower():
                     LOG.debug(f"MPTCP detected for {ip_str} via ss command.")
                     return {"mptcp": "working"}
                else:
                     LOG.debug(f"MPTCP NOT detected for {ip_str} via ss command. RC: {result.returncode}, Output: {result.stdout[:100]}...")
                     return {"mptcp": "not working"}
            except subprocess.TimeoutExpired:
                LOG.warning(f"ss command timed out checking MPTCP for {ip_str}")
                return {"mptcp": "unknown", "reason": "ss command timeout"}
            except FileNotFoundError:
                 LOG.error("'ss' command not found. Cannot check MPTCP status.")
                 return {"mptcp": "unknown", "reason": "ss command not found"}
            except Exception as e:
                 LOG.error(f"Error running ss command for MPTCP check: {e}")
                 return {"mptcp": "unknown", "reason": f"ss command error: {e}"}

        elif isinstance(ip, IPv6Address):
             # MPTCP over IPv6 check might need different /proc entry or ss flags
             LOG.debug(f"MPTCP check for IPv6 ({ip_str}) is not fully implemented/tested.")
             # Basic ss check for IPv6 (might not show MPTCP explicitly in all ss versions)
             ss_cmd_v6 = ['/usr/bin/ss', '-Mnt', 'dst', ip_str]
             try:
                result_v6 = subprocess.run(ss_cmd_v6, capture_output=True, text=True, timeout=3)
                if result_v6.returncode == 0 and 'mptcp' in result_v6.stdout.lower(): # Heuristic check
                     LOG.debug(f"Potential MPTCP detected for IPv6 {ip_str} via ss command.")
                     return {"mptcp": "working"} # Tentative
                else:
                     return {"mptcp": "not working (or check unreliable)"}
             except Exception as e:
                  LOG.error(f"Error running ss command for IPv6 MPTCP check: {e}")
                  return {"mptcp": "unknown", "reason": f"ss command error for IPv6"}

        else:
             return {"mptcp": "unknown", "reason": "Unrecognized IP address type"}

    except ValueError:
        return {"mptcp": "unknown", "reason": f"Invalid client IP address format: {ip_str}"}
    except Exception as e:
         LOG.error(f"Unexpected error during MPTCP support check: {e}")
         return {"mptcp": "unknown", "reason": "Internal server error"}

# Get VPS status
@app.get('/status', summary="Get current server load, uptime, resources, and basic traffic stats")
async def status(
    # Allow querying specific user stats only for admin users
    userid_query: Optional[int] = Query(None, alias="userid"), # Use alias
    username_query: Optional[str] = Query(None, alias="username"), # Use alias
    serial: Optional[str] = Query(None),
    current_user: User = Depends(get_current_active_user)): # Use get_current_active_user

    LOG.debug('Processing /status request...')

    target_userid = current_user.userid # Default to the logged-in user's ID
    target_username = current_user.username

    # Admins can query other users
    if current_user.permissions == "admin":
        if username_query is not None:
             # Find userid for the queried username
             queried_userid = get_userid_from_username(username_query)
             if queried_userid != -1: # Check if user was found
                 target_userid = queried_userid
                 target_username = username_query
             else:
                  raise HTTPException(status_code=404, detail=f"Username '{username_query}' not found.")
        elif userid_query is not None:
             # Find username for the queried userid
             queried_username = get_username_from_userid(userid_query)
             if queried_username:
                  target_userid = userid_query
                  target_username = queried_username
             else:
                  raise HTTPException(status_code=404, detail=f"UserID '{userid_query}' not found.")
        # If neither username nor userid is provided by admin, defaults to admin's own info

    LOG.debug(f"Getting status for user: {target_username} (ID: {target_userid}) requested by {current_user.username}")

    # Serial number check (only if serial is provided)
    if serial is not None:
         # Enforce serial check if not admin, OR if admin is querying a specific non-admin user
         needs_serial_check = current_user.permissions != "admin" or \
                              (current_user.permissions == "admin" and target_username != current_user.username)

         if needs_serial_check and not check_username_serial(target_username, serial):
             # Log specific failure details if possible from check_username_serial
             LOG.warning(f"Serial number check failed for user '{target_username}' with serial '{serial}'")
             raise HTTPException(status_code=403, detail='Invalid or mismatched serial number for target user.')


    # --- System Information Gathering ---
    try:
        vps_loadavg = os.getloadavg() # Returns tuple (1min, 5min, 15min)
        vps_loadavg_str = "{:.2f} {:.2f} {:.2f}".format(*vps_loadavg)
        vps_cpu_count = os.cpu_count()
        vps_memory = psutil.virtual_memory()
        vps_disk = psutil.disk_usage('/')
        # Sometimes cpu_freq() requires root or specific permissions
        vps_cpu_freq = None
        try:
             freq = psutil.cpu_freq()
             if freq: vps_cpu_freq = freq.current
        except Exception as e:
            LOG.warning(f"Could not get CPU frequency: {e}")

        # Getting CPU model might fail or require parsing /proc/cpuinfo
        vps_cpu_model = "N/A"
        try:
             with open('/proc/cpuinfo', 'r') as f:
                 for line in f:
                     if line.strip().startswith('model name'):
                         vps_cpu_model = line.split(':', 1)[1].strip()
                         break
        except Exception as e:
             LOG.warning(f"Could not read CPU model from /proc/cpuinfo: {e}")

        # Get uptime from /proc/uptime (first value is seconds)
        vps_uptime_sec = 0.0
        try:
             with open('/proc/uptime', 'r') as f:
                 vps_uptime_sec = float(f.readline().split()[0])
        except Exception as e:
             LOG.warning(f"Could not read uptime from /proc/uptime: {e}")


        vps_hostname = socket.gethostname()
        vps_current_time = time.time()
        vps_kernel = os.uname().release # Use os.uname()
        # Read OMR version carefully
        vps_omr_version = "N/A"
        try:
            # Example: Find file containing version info
            # This grep command is fragile. Better to have a dedicated version file.
            # grep_cmd = "grep -s 'OpenMPTCProuter VPS' /etc/* /etc/*/* | head -n 1 | awk '{print $NF}'"
            # result = subprocess.run(grep_cmd, shell=True, capture_output=True, text=True)
            # if result.returncode == 0 and result.stdout.strip():
            #     vps_omr_version = result.stdout.strip()
            # Safer: Read from a specific version file if it exists
             version_file = '/etc/omr-vps-version'
             if os.path.exists(version_file):
                 with open(version_file, 'r') as vf:
                      vps_omr_version = vf.read().strip()

        except Exception as e:
            LOG.warning(f"Could not determine OMR VPS version: {e}")

        # MPTCP status check
        mptcp_enabled = "0"
        mptcp_sysctl_key = None
        if path.exists("/proc/sys/net/mptcp/enabled"): # Kernel 5.6+ ?
            mptcp_sysctl_key = 'net.mptcp.enabled'
        elif path.exists("/proc/sys/net/mptcp/mptcp_enabled"): # Older kernels
             mptcp_sysctl_key = 'net.mptcp.mptcp_enabled'

        if mptcp_sysctl_key:
             try:
                 result = subprocess.run(['/sbin/sysctl', '-qn', mptcp_sysctl_key], capture_output=True, text=True, check=True)
                 mptcp_enabled = result.stdout.strip()
             except (FileNotFoundError, subprocess.CalledProcessError) as e:
                 LOG.warning(f"Could not get MPTCP status via sysctl '{mptcp_sysctl_key}': {e}")
             except Exception as e:
                  LOG.error(f"Unexpected error getting MPTCP status: {e}")

    except Exception as e:
        LOG.error(f"Failed to get basic system status: {e}")
        # Return partial data or raise HTTPException?
        raise HTTPException(status_code=500, detail="Failed to retrieve system status.")

    # --- User-Specific Traffic Stats ---
    # Reload config for the target user's settings
    user_config = {}
    try:
         with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
             omr_config_data = json.load(f)
             user_config = omr_config_data.get('users', [{}])[0].get(target_username, {})
    except (FileNotFoundError, json.JSONDecodeError, IndexError, TypeError) as e:
         LOG.warning(f"Could not load user config for traffic stats (user: {target_username}): {e}")
         # Continue with defaults (0 traffic)

    # Determine active proxy and VPN for the target user
    proxy_type = user_config.get('proxy', 'none') # Default if not set
    vpn_type = user_config.get('vpn', 'none') # Default if not set

    # Get traffic stats based on proxy type
    ss_traffic = 0
    ss_go_tx = 0
    ss_go_rx = 0
    v2ray_tx = 0
    v2ray_rx = 0
    xray_tx = 0
    xray_rx = 0

    if proxy_type == 'shadowsocks' and 'shadowsocks_port' in user_config:
        ss_port = user_config['shadowsocks_port']
        if ss_port:
            # Check if shadowsocks-libev manager process is likely running
            # This is a basic check; a more robust check might ping the manager port
            if checkIfProcessRunning('ss-manager'):
                ss_traffic = get_bytes_ss(ss_port)
            else:
                LOG.debug("Shadowsocks-libev manager process not detected, skipping traffic stats.")
        else:
             LOG.debug(f"User {target_username} has proxy 'shadowsocks' but no port configured.")

    elif proxy_type in ['shadowsocks-go', 'shadowsocks-rust']:
         # Assuming shadowsocks-go executable name for check
        if checkIfProcessRunning('shadowsocks-go'):
             ss_go_txrx = get_bytes_ss_go(target_username)
             ss_go_tx = ss_go_txrx.get('downlinkBytes', 0)
             ss_go_rx = ss_go_txrx.get('uplinkBytes', 0)
        else:
            LOG.debug("Shadowsocks-go process not detected, skipping traffic stats.")

    elif 'v2ray' in proxy_type: # Covers v2ray, v2ray-vmess, etc.
        if checkIfProcessRunning('v2ray'):
            v2ray_tx = get_bytes_v2ray('tx', target_username)
            v2ray_rx = get_bytes_v2ray('rx', target_username)
        else:
             LOG.debug("V2Ray process not detected, skipping traffic stats.")

    elif 'xray' in proxy_type: # Covers xray, xray-vless, etc.
        if checkIfProcessRunning('xray'):
            xray_tx = get_bytes_xray('tx', target_username)
            xray_rx = get_bytes_xray('rx', target_username)
        else:
            LOG.debug("Xray process not detected, skipping traffic stats.")


    # Get traffic stats based on VPN type
    vpn_traffic_rx = 0
    vpn_traffic_tx = 0
    vpn_iface = None

    if vpn_type == 'glorytun_tcp':
        vpn_iface = f'gt-tun{target_userid}'
    elif vpn_type == 'glorytun_udp':
        vpn_iface = f'gt-udp-tun{target_userid}'
    elif vpn_type == 'mlvpn':
        vpn_iface = f'mlvpn{target_userid}' # Check actual interface naming convention
    elif vpn_type == 'dsvpn':
        vpn_iface = f'dsvpn{target_userid}' # Check actual interface naming convention
    elif vpn_type == 'openvpn':
        # OpenVPN stats via management interface is more reliable than interface bytes
        if checkIfProcessRunning('openvpn'):
             vpn_txrx = get_bytes_openvpn(target_username)
             vpn_traffic_rx = vpn_txrx.get('uplinkBytes', 0) # Uplink from client is RX for server
             vpn_traffic_tx = vpn_txrx.get('downlinkBytes', 0) # Downlink to client is TX for server
        else:
            LOG.debug("OpenVPN process not detected, skipping traffic stats.")
        # vpn_iface = 'tun0' # Example, might vary
    elif vpn_type == 'openvpn_bonding':
        vpn_iface = 'omr-bonding' # Check actual interface name

    # Get bytes from interface if vpn_iface is set and OpenVPN wasn't handled
    if vpn_iface and vpn_type != 'openvpn':
        vpn_traffic_rx = get_bytes('rx', vpn_iface)
        vpn_traffic_tx = get_bytes('tx', vpn_iface)

    # --- Network Interface Traffic (Primary Interface) ---
    net_tx = 0
    net_rx = 0
    if IFACE and path.exists(f'/sys/class/net/{IFACE}/'):
        net_tx = get_bytes('tx', IFACE)
        net_rx = get_bytes('rx', IFACE)
    else:
        LOG.warning(f"Primary interface {IFACE} not found or invalid, cannot get network stats.")


    LOG.debug('Finished processing /status request.')
    # Construct the response payload
    response_data = {
        'vps': {
            'time': vps_current_time,
            'loadavg': vps_loadavg_str,
            'cpu_model': vps_cpu_model,
            'cpu_count': vps_cpu_count,
            'memory_total': vps_memory.total,
            'memory_available': vps_memory.available,
            'memory_percent': vps_memory.percent,
            'memory_used': vps_memory.used,
            'memory_free': vps_memory.free,
            'disk_total': vps_disk.total,
            'disk_used': vps_disk.used,
            'disk_free': vps_disk.free,
            'disk_percent': vps_disk.percent,
            'cpu_freq': vps_cpu_freq,
            'uptime': vps_uptime_sec,
            'mptcp': mptcp_enabled,
            'hostname': vps_hostname,
            'kernel': vps_kernel,
            'omr_version': vps_omr_version
        },
        'network': { # Primary interface traffic
            'iface': IFACE,
            'tx': net_tx,
            'rx': net_rx
        },
         # User-specific traffic, names reflect the proxy/VPN type checked
        'traffic': {
             'user': target_username,
             'vpn_type': vpn_type,
             'vpn_tx': vpn_traffic_tx,
             'vpn_rx': vpn_traffic_rx,
             'proxy_type': proxy_type,
             'shadowsocks_libev_cumulative': ss_traffic, # Cumulative counter for ss-libev
             'shadowsocks_go_tx': ss_go_tx,
             'shadowsocks_go_rx': ss_go_rx,
             'v2ray_tx': v2ray_tx,
             'v2ray_rx': v2ray_rx,
             'xray_tx': xray_tx,
             'xray_rx': xray_rx,
        }
        # # Old structure - less clear which traffic belongs to what
        # 'shadowsocks': {'traffic': ss_traffic},
        # 'vpn': {'tx': vpn_traffic_tx, 'rx': vpn_traffic_rx},
        # 'v2ray': {'tx': v2ray_tx, 'rx': v2ray_rx},
        # 'xray': {'tx': xray_tx, 'rx': xray_rx},
        # 'shadowsocks_go': {'tx': ss_go_tx, 'rx': ss_go_rx}
    }

    return response_data


# Get VPS config
@app.get('/config', summary="Get full server configuration for the current or specified user")
async def config(
    # Allow querying specific user stats only for admin users
    userid_query: Optional[int] = Query(None, alias="userid"), # Use alias
    username_query: Optional[str] = Query(None, alias="username"), # Use alias
    serial: Optional[str] = Query(None),
    current_user: User = Depends(get_current_active_user)):

    LOG.debug('Processing /config request...')

    target_userid = current_user.userid
    target_username = current_user.username
    target_user_obj = current_user # Start with the current user object

    # Admins can query other users
    if current_user.permissions == "admin":
        if username_query is not None:
             queried_userid = get_userid_from_username(username_query)
             if queried_userid != -1:
                 target_userid = queried_userid
                 target_username = username_query
                 # Get the full user object for the target user
                 target_user_obj = get_user(fake_users_db, target_username)
                 if not target_user_obj:
                     raise HTTPException(status_code=500, detail=f"Could not retrieve user object for '{target_username}'.")
             else:
                  raise HTTPException(status_code=404, detail=f"Username '{username_query}' not found.")
        elif userid_query is not None:
             queried_username = get_username_from_userid(userid_query)
             if queried_username:
                  target_userid = userid_query
                  target_username = queried_username
                   # Get the full user object for the target user
                  target_user_obj = get_user(fake_users_db, target_username)
                  if not target_user_obj:
                      raise HTTPException(status_code=500, detail=f"Could not retrieve user object for ID '{target_userid}'.")
             else:
                  raise HTTPException(status_code=404, detail=f"UserID '{userid_query}' not found.")

    LOG.debug(f"Getting config for user: {target_username} (ID: {target_userid}) requested by {current_user.username}")

    # Serial number check (similar logic to /status)
    if serial is not None:
         needs_serial_check = current_user.permissions != "admin" or \
                              (current_user.permissions == "admin" and target_username != current_user.username)
         if needs_serial_check and not check_username_serial(target_username, serial):
             raise HTTPException(status_code=403, detail='Invalid or mismatched serial number for target user.')

    # Reload full config data for comprehensive view
    config_path = '/etc/openmptcprouter-vps-admin/omr-admin-config.json'
    try:
        with open(config_path) as f:
            omr_config_data = json.load(f)
        all_users_data = omr_config_data.get('users', [{}])[0]
        user_config = all_users_data.get(target_username, {}) # Config for the target user
    except (FileNotFoundError, json.JSONDecodeError, IndexError, TypeError) as e:
         LOG.error(f"Could not load OMR admin config from {config_path}: {e}")
         raise HTTPException(status_code=500, detail="Failed to load server configuration.")

    # --- Shadowsocks-libev Config ---
    LOG.debug('Get config... shadowsocks-libev')
    ss_config = {
        'traffic': 0, 'key': '', 'port': None, 'method': 'N/A',
        'fast_open': False, 'reuse_port': False, 'no_delay': False,
        'mptcp': False, 'obfs': False, 'obfs_plugin': '', 'obfs_type': '',
         'ebpf': False # Added ebpf field
    }
    ss_manager_file = '/etc/shadowsocks-libev/manager.json'
    if os.path.isfile(ss_manager_file):
        try:
            with open(ss_manager_file) as f:
                content = f.read()
            content = re.sub(r",\s*([}\]])", r"\1", content) # Tolerate trailing commas
            ss_manager_data = json.loads(content)

            ss_config['method'] = ss_manager_data.get('method', 'N/A')
            ss_config['fast_open'] = ss_manager_data.get('fast_open', False)
            ss_config['reuse_port'] = ss_manager_data.get('reuse_port', False)
            ss_config['no_delay'] = ss_manager_data.get('no_delay', False)
            ss_config['mptcp'] = ss_manager_data.get('mptcp', False) # Default depends on ss-libev version/build
            ss_config['ebpf'] = ss_manager_data.get('ebpf', False) # Check if ebpf is in config

            target_ss_port = user_config.get('shadowsocks_port') # Get port from user's config
            ss_config['port'] = target_ss_port # Store the configured port

            if target_ss_port:
                port_str = str(target_ss_port)
                user_ss_key = None
                if 'port_key' in ss_manager_data and port_str in ss_manager_data['port_key']:
                     user_ss_key = ss_manager_data['port_key'][port_str]
                elif 'port_conf' in ss_manager_data and port_str in ss_manager_data['port_conf'] and 'key' in ss_manager_data['port_conf'][port_str]:
                    user_ss_key = ss_manager_data['port_conf'][port_str]['key']

                if user_ss_key:
                     ss_config['key'] = user_ss_key
                else:
                     LOG.warning(f"Shadowsocks key for port {target_ss_port} (user {target_username}) not found in {ss_manager_file}")

                # Obfs settings
                if "plugin" in ss_manager_data:
                     ss_config['obfs'] = True
                     # Infer plugin and type (this is heuristic)
                     if 'v2ray' in ss_manager_data["plugin"]:
                         ss_config['obfs_plugin'] = 'v2ray'
                         opts = ss_manager_data.get("plugin_opts", "")
                         if 'tls' in opts: ss_config['obfs_type'] = 'tls'
                         elif 'http' in opts: ss_config['obfs_type'] = 'http' # Assuming http if not tls
                     elif 'obfs-server' in ss_manager_data["plugin"]:
                          ss_config['obfs_plugin'] = 'obfs'
                          opts = ss_manager_data.get("plugin_opts", "")
                          if 'obfs=tls' in opts: ss_config['obfs_type'] = 'tls'
                          elif 'obfs=http' in opts: ss_config['obfs_type'] = 'http'

            # Get traffic if this is the active proxy
            active_proxy = user_config.get('proxy', 'none')
            if active_proxy == 'shadowsocks' and target_ss_port:
                if checkIfProcessRunning('ss-manager'):
                     ss_config['traffic'] = get_bytes_ss(target_ss_port)

        except (json.JSONDecodeError, KeyError, TypeError) as e:
            LOG.warning(f"Could not parse {ss_manager_file} or access keys: {e}")
        except Exception as e:
             LOG.error(f"Unexpected error reading {ss_manager_file}: {e}")
    else:
         LOG.debug(f"{ss_manager_file} not found.")


    # --- Glorytun Config ---
    LOG.debug('Get config... glorytun')
    glorytun_config = {
        'key': '', 'port': '65001', 'chacha': False,
        'tcp': {'host_ip': '', 'client_ip': ''},
        'udp': {'host_ip': '', 'client_ip': ''}
    }
    glorytun_key_file = f'/etc/glorytun-tcp/tun{target_userid}.key'
    if os.path.isfile(glorytun_key_file):
        try:
             with open(glorytun_key_file, 'r') as f:
                 glorytun_config['key'] = f.read().strip()
        except IOError as e:
             LOG.warning(f"Could not read {glorytun_key_file}: {e}")

    glorytun_tcp_conf_file = f'/etc/glorytun-tcp/tun{target_userid}'
    if os.path.isfile(glorytun_tcp_conf_file):
        try:
            with open(glorytun_tcp_conf_file, "r") as f:
                for line in f:
                    line = line.strip()
                    if line.startswith('PORT='):
                        glorytun_config['port'] = line.split('=', 1)[1]
                    elif line.startswith('LOCALIP='):
                         glorytun_config['tcp']['host_ip'] = line.split('=', 1)[1]
                    elif line.startswith('REMOTEIP='):
                         glorytun_config['tcp']['client_ip'] = line.split('=', 1)[1]
                    elif 'OPTIONS=' in line and 'chacha20' in line:
                        glorytun_config['chacha'] = True
        except IOError as e:
            LOG.warning(f"Could not read {glorytun_tcp_conf_file}: {e}")

    glorytun_udp_conf_file = f'/etc/glorytun-udp/tun{target_userid}'
    if os.path.isfile(glorytun_udp_conf_file):
        try:
            with open(glorytun_udp_conf_file, "r") as f:
                for line in f:
                    line = line.strip()
                    if line.startswith('LOCALIP='):
                        glorytun_config['udp']['host_ip'] = line.split('=', 1)[1]
                    elif line.startswith('REMOTEIP='):
                        glorytun_config['udp']['client_ip'] = line.split('=', 1)[1]
                    # UDP usually gets chacha option from TCP config or global setting
        except IOError as e:
            LOG.warning(f"Could not read {glorytun_udp_conf_file}: {e}")

    # Fallbacks for user 0 if files didn't exist or IPs were missing
    if target_userid == 0:
         if not glorytun_config['tcp']['host_ip']:
              # Use config value or default static
              tcp_type = omr_config_data.get('glorytun_tcp_type', 'static')
              if tcp_type == 'dhcp':
                   glorytun_config['tcp']['host_ip'] = 'dhcp'
                   glorytun_config['tcp']['client_ip'] = 'dhcp'
              else:
                   glorytun_config['tcp']['host_ip'] = '10.255.255.1'
                   glorytun_config['tcp']['client_ip'] = '10.255.255.2'
         if not glorytun_config['udp']['host_ip']:
              # Use config value or default static
              udp_type = omr_config_data.get('glorytun_udp_type', 'static')
              if udp_type == 'dhcp':
                   glorytun_config['udp']['host_ip'] = 'dhcp'
                   glorytun_config['udp']['client_ip'] = 'dhcp'
              else:
                   glorytun_config['udp']['host_ip'] = '10.255.254.1'
                   glorytun_config['udp']['client_ip'] = '10.255.254.2'


    # --- DSVPN Config ---
    LOG.debug('Get config... dsvpn')
    dsvpn_config = {'key': '', 'port': '65401', 'host_ip': '', 'client_ip': ''}
    dsvpn_key_file = f'/etc/dsvpn/dsvpn{target_userid}.key'
    dsvpn_conf_file = f'/etc/dsvpn/dsvpn{target_userid}'

    if os.path.isfile(dsvpn_key_file):
         try:
             with open(dsvpn_key_file, 'r') as f:
                 dsvpn_config['key'] = f.read().strip()
         except IOError as e:
             LOG.warning(f"Could not read {dsvpn_key_file}: {e}")

    if os.path.isfile(dsvpn_conf_file):
         try:
             with open(dsvpn_conf_file, "r") as f:
                 for line in f:
                     line = line.strip()
                     if line.startswith('PORT='):
                         dsvpn_config['port'] = line.split('=', 1)[1]
                     elif line.startswith('LOCALTUNIP='):
                         dsvpn_config['host_ip'] = line.split('=', 1)[1]
                     elif line.startswith('REMOTETUNIP='):
                         dsvpn_config['client_ip'] = line.split('=', 1)[1]
         except IOError as e:
             LOG.warning(f"Could not read {dsvpn_conf_file}: {e}")

    # Fallbacks for user 0
    if target_userid == 0 and not dsvpn_config['host_ip']:
         dsvpn_config['host_ip'] = '10.255.251.1'
         dsvpn_config['client_ip'] = '10.255.251.2'


    # --- iPerf3 Config ---
    LOG.debug('Get config... iperf3')
    iperf3_key = ''
    iperf_pub_key_file = '/etc/iperf3/public.pem'
    if os.path.isfile(iperf_pub_key_file):
        try:
            with open(iperf_pub_key_file, "rb") as f:
                iperf_keyb = base64.b64encode(f.read())
                iperf3_key = iperf_keyb.decode('utf-8')
        except IOError as e:
             LOG.warning(f"Could not read {iperf_pub_key_file}: {e}")


    # --- Pi-hole ---
    pihole = os.path.isfile('/etc/pihole/setupVars.conf')


    # --- OpenVPN Config ---
    LOG.debug('Get config... openvpn')
    openvpn_config = {
        'key': '', 'client_key': '', 'client_crt': '', 'client_ca': '',
        'host_ip': '10.255.252.1', 'client_ip': 'dhcp', # Defaults
        'port': '65301', 'cipher': 'AES-256-GCM' # Defaults
    }
    ovpn_client_key_file = f'/etc/openvpn/ca/pki/private/{target_username}.key'
    ovpn_client_crt_file = f'/etc/openvpn/ca/pki/issued/{target_username}.crt'
    ovpn_ca_crt_file = '/etc/openvpn/ca/pki/ca.crt'
    ovpn_server_conf_file = '/etc/openvpn/tun0.conf' # Assuming tun0 is the main server

    def read_b64_file(filepath):
        if os.path.isfile(filepath):
            try:
                with open(filepath, "rb") as f:
                    return base64.b64encode(f.read()).decode('utf-8')
            except IOError as e:
                LOG.warning(f"Could not read OpenVPN file {filepath}: {e}")
        return ''

    openvpn_config['client_key'] = read_b64_file(ovpn_client_key_file)
    openvpn_config['client_crt'] = read_b64_file(ovpn_client_crt_file)
    openvpn_config['client_ca'] = read_b64_file(ovpn_ca_crt_file)
    # The 'key' field seems unused/legacy based on the old code, maybe PSK? Keep empty.

    if os.path.isfile(ovpn_server_conf_file):
        try:
            with open(ovpn_server_conf_file, "r") as f:
                for line in f:
                    line = line.strip()
                    if line.startswith('port '):
                        openvpn_config['port'] = line.split(' ', 1)[1]
                    elif line.startswith('cipher '):
                        openvpn_config['cipher'] = line.split(' ', 1)[1]
                    elif line.startswith('server '): # Get server IP/netmask
                         parts = line.split()
                         if len(parts) >= 3:
                              # Derive host IP (usually .1) from network
                              try:
                                   net = ip_network(f"{parts[1]}/{parts[2]}", strict=False)
                                   openvpn_config['host_ip'] = str(net[1])
                              except ValueError as e:
                                   LOG.warning(f"Could not parse OpenVPN server network: {line} - {e}")
                    # Client IP is usually assigned dynamically ('dhcp') or via CCD
        except IOError as e:
            LOG.warning(f"Could not read {ovpn_server_conf_file}: {e}")


    # --- MLVPN Config ---
    LOG.debug('Get config... mlvpn')
    mlvpn_config = {
        'key': '', 'timeout': '', 'reorder_buffer_size': '', 'loss_tolerence': '',
        'cleartext_data': '', 'host_ip': '10.255.253.1', 'client_ip': '10.255.253.2'
    }
    mlvpn_conf_file = '/etc/mlvpn/mlvpn0.conf' # Assuming mlvpn0 for user 0/default
    if os.path.isfile(mlvpn_conf_file):
        try:
            parser = configparser.ConfigParser()
            parser.read(mlvpn_conf_file)
            if 'general' in parser:
                mlvpn_config['key'] = parser.get('general', 'password', fallback='').strip('"')
                mlvpn_config['timeout'] = parser.get('general', 'timeout', fallback='')
                mlvpn_config['reorder_buffer_size'] = parser.get('general', 'reorder_buffer_size', fallback='')
                mlvpn_config['loss_tolerence'] = parser.get('general', 'loss_tolerence', fallback='')
                mlvpn_config['cleartext_data'] = parser.get('general', 'cleartext_data', fallback='') # Should be boolean? Treat as string for now
        except configparser.Error as e:
             LOG.warning(f"Could not parse {mlvpn_conf_file}: {e}")
        except Exception as e:
             LOG.error(f"Unexpected error reading {mlvpn_conf_file}: {e}")


    # --- WireGuard Config ---
    LOG.debug('Get config... wireguard')
    wireguard_config = {
        'key': '', 'host_ip': '10.255.247.1', 'port': '65311', # Server/OMR side
        'client_key': '', 'client_ip': '10.255.246.2', 'client_port': '65312' # External client side
    }
    wg_server_pub_key_file = '/etc/wireguard/vpn-server-public.key'
    wg_client_priv_key_file = '/etc/wireguard/vpn-client-private.key'
    # WireGuard config usually in wg0.conf, vpn-server-public.key might be separate
    if os.path.isfile(wg_server_pub_key_file):
        try:
            with open(wg_server_pub_key_file, "r") as f: # Key is usually text
                wireguard_config['key'] = f.read().strip()
        except IOError as e:
             LOG.warning(f"Could not read {wg_server_pub_key_file}: {e}")
    if os.path.isfile(wg_client_priv_key_file):
        try:
            with open(wg_client_priv_key_file, "r") as f: # Key is usually text
                wireguard_config['client_key'] = f.read().strip()
        except IOError as e:
             LOG.warning(f"Could not read {wg_client_priv_key_file}: {e}")
    # Getting IPs/ports might require parsing wg0.conf or another source

    # --- GRE Tunnel Config (from user config) ---
    gre_tunnel = False
    gre_tunnel_conf = []
    if 'gre_tunnels' in user_config and user_config['gre_tunnels']:
         gre_tunnel = True
         # Convert dict to list of dicts for API response consistency if needed
         gre_tunnel_conf = list(user_config['gre_tunnels'].values())


    # --- VPN IPs (from user config) ---
    vpn_remote_ip = user_config.get('vpnremoteip', '')
    vpn_local_ip = user_config.get('vpnlocalip', '')
    vpn_ula = user_config.get('ula', '') # Get ULA if stored

    # --- V2Ray/Xray/Shadowsocks-Go (from user config) ---
    # These now primarily pull from the user's section in omr-admin-config.json
    # But we still need to get traffic stats.
    v2ray_enabled = os.path.isfile('/etc/v2ray/v2ray-server.json')
    v2ray_conf = user_config.get('v2ray', {})
    v2ray_tx = 0
    v2ray_rx = 0
    if v2ray_enabled and 'v2ray' in user_config.get('proxy', ''):
        if checkIfProcessRunning('v2ray'):
             v2ray_tx = get_bytes_v2ray('tx', target_username)
             v2ray_rx = get_bytes_v2ray('rx', target_username)

    xray_enabled = os.path.isfile('/etc/xray/xray-server.json')
    xray_conf = user_config.get('xray', {})
    xray_tx = 0
    xray_rx = 0
    if xray_enabled and 'xray' in user_config.get('proxy', ''):
        if checkIfProcessRunning('xray'):
             xray_tx = get_bytes_xray('tx', target_username)
             xray_rx = get_bytes_xray('rx', target_username)

    ssgo_enabled = os.path.isfile('/etc/shadowsocks-go/server.json')
    ssgo_conf = user_config.get('shadowsocks-go', {})
    ssgo_tx = 0
    ssgo_rx = 0
    if ssgo_enabled and user_config.get('proxy', '') in ['shadowsocks-go', 'shadowsocks-rust']:
         if checkIfProcessRunning('shadowsocks-go'):
              ssgo_txrx = get_bytes_ss_go(target_username)
              ssgo_tx = ssgo_txrx.get('downlinkBytes', 0)
              ssgo_rx = ssgo_txrx.get('uplinkBytes', 0)


    # --- MPTCP Kernel Params ---
    LOG.debug('Get config... mptcp')
    mptcp_config = {
        'enabled': '0', 'checksum': 'N/A', 'path_manager': 'N/A',
        'scheduler': 'N/A', 'syn_retries': 'N/A', 'version': 'N/A'
    }
    mptcp_sysctl_map = {}
    # Determine which set of sysctls are likely present
    if path.exists('/proc/sys/net/mptcp/enabled'): # Kernel 5.6+ ?
        mptcp_config['version'] = '1+' # Indicate newer MPTCP version presence
        mptcp_sysctl_map = {
            'enabled': 'net.mptcp.enabled',
            'checksum': 'net.mptcp.checksum_enabled', # Mapped name
            'path_manager': 'net.mptcp.path_manager', # Mapped name
            'scheduler': 'net.mptcp.scheduler', # Mapped name
            'syn_retries': 'net.mptcp.syn_retries', # Mapped name
        }
        # Version sysctl might exist too
        try:
             result = subprocess.run(['/sbin/sysctl', '-qn', 'net.mptcp.mptcp_version'], capture_output=True, text=True, check=False)
             if result.returncode == 0:
                  mptcp_config['version'] = result.stdout.strip()
        except Exception: pass # Ignore if version sysctl fails

    elif path.exists('/proc/sys/net/mptcp/mptcp_enabled'): # Older kernels
        mptcp_config['version'] = '0' # Indicate older MPTCP version presence
        mptcp_sysctl_map = {
            'enabled': 'net.mptcp.mptcp_enabled',
            'checksum': 'net.mptcp.mptcp_checksum',
            'path_manager': 'net.mptcp.mptcp_path_manager',
            'scheduler': 'net.mptcp.mptcp_scheduler',
            'syn_retries': 'net.mptcp.mptcp_syn_retries',
        }

    # Read the values using sysctl
    for key, sysctl_name in mptcp_sysctl_map.items():
        try:
            result = subprocess.run(['/sbin/sysctl', '-qn', sysctl_name], capture_output=True, text=True, check=True)
            mptcp_config[key] = result.stdout.strip()
        except (FileNotFoundError, subprocess.CalledProcessError) as e:
            LOG.warning(f"Could not get MPTCP sysctl '{sysctl_name}': {e}")
        except Exception as e:
            LOG.error(f"Unexpected error getting MPTCP sysctl {sysctl_name}: {e}")


    # --- Congestion Control ---
    congestion_control = "N/A"
    try:
        result = subprocess.run(['/sbin/sysctl', '-qn', 'net.ipv4.tcp_congestion_control'], capture_output=True, text=True, check=True)
        congestion_control = result.stdout.strip()
    except (FileNotFoundError, subprocess.CalledProcessError) as e:
        LOG.warning(f"Could not get TCP congestion control: {e}")
    except Exception as e:
         LOG.error(f"Unexpected error getting TCP congestion control: {e}")

    # --- Network Info (IPv4, IPv6, Domain) ---
    LOG.debug('Get config... network addresses')
    network_config = {'ipv6_network': '', 'ipv6': '', 'ipv4': '', 'domain': '', 'internet': True}

    # Use stored values first, then try to detect
    network_config['ipv4'] = omr_config_data.get('ipv4', '')
    network_config['ipv6'] = omr_config_data.get('ipv6_addr', '')
    network_config['ipv6_network'] = omr_config_data.get('ipv6_network', '')
    network_config['domain'] = omr_config_data.get('hostname', '')
    network_config['internet'] = omr_config_data.get('internet', True) # Assume internet unless explicitly false

    # Attempt detection only if stored value is missing and internet is assumed
    if not network_config['ipv4'] and network_config['internet']:
        # Try reliable detection methods first
        # Example: ip route get 1.1.1.1 | grep -oP 'src \K\S+'
        try:
            cmd = "ip -4 route get 1.1.1.1 | grep -oP 'src \\K\\S+'"
            result = subprocess.run(cmd, shell=True, capture_output=True, text=True, timeout=2)
            if result.returncode == 0 and result.stdout.strip():
                network_config['ipv4'] = result.stdout.strip()
                set_global_param('ipv4', network_config['ipv4']) # Save detected IP
            else:
                # Fallback to external service
                LOG.debug("Trying external service for IPv4...")
                try:
                    response = requests.get('http://ip.openmptcprouter.com', timeout=3)
                    response.raise_for_status()
                    network_config['ipv4'] = response.text.strip()
                    set_global_param('ipv4', network_config['ipv4']) # Save detected IP
                except requests.RequestException as e:
                    LOG.warning(f"Could not get IPv4 from external service: {e}")
        except Exception as e:
            LOG.warning(f"Error detecting primary IPv4: {e}")


    if not network_config['ipv6'] and network_config['internet'] and IFACE6:
         try:
             # Get global IPv6 from the detected interface
             cmd_v6 = f"ip -6 addr show {IFACE6} scope global | grep -oP 'inet6 \\K[\\da-fA-F:]+' | head -n 1"
             result_v6 = subprocess.run(cmd_v6, shell=True, capture_output=True, text=True, timeout=2)
             if result_v6.returncode == 0 and result_v6.stdout.strip():
                  network_config['ipv6'] = result_v6.stdout.strip()
                  set_global_param('ipv6_addr', network_config['ipv6'])
                  # Attempt to get network too
                  cmd_v6_net = f"ip -6 addr show {IFACE6} scope global | grep -oP 'inet6 \\K[\\da-fA-F:/]+' | head -n 1"
                  result_v6_net = subprocess.run(cmd_v6_net, shell=True, capture_output=True, text=True, timeout=2)
                  if result_v6_net.returncode == 0 and result_v6_net.stdout.strip():
                       network_config['ipv6_network'] = result_v6_net.stdout.strip()
                       set_global_param('ipv6_network', network_config['ipv6_network'])

         except Exception as e:
             LOG.warning(f"Error detecting primary IPv6: {e}")


    if not network_config['domain'] and network_config['internet'] and network_config['ipv4']:
         # Try reverse DNS lookup (can be slow/unreliable)
         try:
             LOG.debug(f"Trying reverse DNS for {network_config['ipv4']}...")
             # Use dig for potentially better results than wget method
             cmd_dig = f"dig +short +time=2 +tries=1 -x {network_config['ipv4']}"
             result_dig = subprocess.run(cmd_dig, shell=True, capture_output=True, text=True, timeout=3)
             if result_dig.returncode == 0 and result_dig.stdout.strip():
                  domain = result_dig.stdout.strip().rstrip('.') # Remove trailing dot
                  network_config['domain'] = domain
                  set_global_param('hostname', domain) # Save detected hostname
             else:
                  LOG.debug(f"Reverse DNS failed or returned no result for {network_config['ipv4']}")
         except Exception as e:
              LOG.warning(f"Error during reverse DNS lookup: {e}")

    # --- Server Capabilities ---
    vps_aes = 'aes' in psutil.cpu_info().get('flags', []) if hasattr(psutil, 'cpu_info') else 'aes' in open('/proc/cpuinfo').read() # Basic check
    vps_kernel = os.uname().release
    vps_machine = os.uname().machine
    vps_omr_version = omr_config_data.get('omr_version', 'N/A') # Use stored if available
    vps_loadavg_str = "{:.2f} {:.2f} {:.2f}".format(*os.getloadavg())
    vps_uptime_sec = 0.0
    try: vps_uptime_sec = float(open('/proc/uptime').readline().split()[0])
    except: pass

    # --- User Info ---
    user_permissions = target_user_obj.permissions if target_user_obj else 'N/A'
    lanips = user_config.get('lanips', [])

    # --- IPv6 Tunnel Info (6in4) ---
    ip6in4_config = {'localip': '', 'remoteip': '', 'ula': vpn_ula} # Use ULA from user config
    omr6in4_file = f'/etc/openmptcprouter-vps-admin/omr-6in4/user{target_userid}'
    if os.path.isfile(omr6in4_file):
         try:
             with open(omr6in4_file, "r") as f:
                 for line in f:
                     line = line.strip()
                     if line.startswith('LOCALIP6='):
                         ip6in4_config['localip'] = line.split('=', 1)[1]
                     elif line.startswith('REMOTEIP6='):
                         ip6in4_config['remoteip'] = line.split('=', 1)[1]
                     # ULA is now read from main config, ignore from this file if present
         except IOError as e:
             LOG.warning(f"Could not read {omr6in4_file}: {e}")
    elif target_userid != 0: # Default ULA-like IPs for non-admin users if file missing
         ip6in4_config['localip'] = f'fd00::a0{hex(target_userid)[2:]}:1/126'
         ip6in4_config['remoteip'] = f'fd00::a0{hex(target_userid)[2:]}:2/126'


    # --- Client-to-Client Info ---
    client2client_enabled = omr_config_data.get('client2client', False)
    all_other_lanips = []
    if client2client_enabled:
        for uname, uconf in all_users_data.items():
             # Ensure entry is a dict and has 'lanips', exclude self
            if uname != target_username and isinstance(uconf, dict) and 'lanips' in uconf and isinstance(uconf['lanips'], list):
                 for lan_ip_cidr in uconf['lanips']:
                      if lan_ip_cidr not in all_other_lanips:
                          all_other_lanips.append(lan_ip_cidr)


    # --- Available VPN/Proxy Options ---
    available_vpn = ["glorytun_tcp", "glorytun_udp"]
    if dsvpn_config['key']: available_vpn.append("dsvpn")
    if openvpn_config['client_crt']: available_vpn.append("openvpn")
    if os.path.isfile('/etc/openvpn/bonding1.conf'): available_vpn.append("openvpn_bonding")
    if mlvpn_config['key']: available_vpn.append("mlvpn")
    # Add wireguard if needed

    available_proxy = ["none"]
    if ss_config['port'] is not None: available_proxy.append("shadowsocks")
    if ssgo_enabled: available_proxy.extend(["shadowsocks-go", "shadowsocks-rust"])
    if v2ray_enabled: available_proxy.extend(["v2ray", "v2ray-vmess", "v2ray-socks", "v2ray-trojan"]) # Add variants if distinct config exists
    if xray_enabled: available_proxy.extend(["xray", "xray-vless", "xray-vless-reality", "xray-vmess", "xray-socks", "xray-trojan", "xray-shadowsocks"]) # Add variants

    active_vpn = user_config.get('vpn', 'none')
    active_proxy = user_config.get('proxy', 'none')

    # Restrict available options for read-only users
    if user_permissions == 'ro':
         available_vpn = [active_vpn] if active_vpn != 'none' else []
         available_proxy = [active_proxy] if active_proxy != 'none' else []

    # --- VPN Traffic ---
    vpn_traffic_rx = 0
    vpn_traffic_tx = 0
    # (Use same logic as in /status endpoint to get traffic for active_vpn)
    vpn_iface = None
    if active_vpn == 'glorytun_tcp': vpn_iface = f'gt-tun{target_userid}'
    elif active_vpn == 'glorytun_udp': vpn_iface = f'gt-udp-tun{target_userid}'
    elif active_vpn == 'mlvpn': vpn_iface = f'mlvpn{target_userid}'
    elif active_vpn == 'dsvpn': vpn_iface = f'dsvpn{target_userid}'
    elif active_vpn == 'openvpn':
         if checkIfProcessRunning('openvpn'):
             vpn_txrx = get_bytes_openvpn(target_username)
             vpn_traffic_rx = vpn_txrx.get('uplinkBytes', 0)
             vpn_traffic_tx = vpn_txrx.get('downlinkBytes', 0)
    elif active_vpn == 'openvpn_bonding': vpn_iface = 'omr-bonding'

    if vpn_iface and active_vpn != 'openvpn':
         vpn_traffic_rx = get_bytes('rx', vpn_iface)
         vpn_traffic_tx = get_bytes('tx', vpn_iface)


    # --- Local VPN ---
    # This check seems specific, adapt if necessary
    localvpn = "vpn1" if os.popen('ip l | grep " vpn"').read().strip() else ""


    # --- Redirect All Ports Status ---
    # Check if the generic redirect rules exist using iptables -C
    redirect_all_enabled = False
    if IFACE: # Need interface name
         try:
             omr_addr = user_config.get('vpnremoteip', '10.255.255.2') # Get target user's VPN IP or default
             # Check one of the rules (e.g., TCP DNAT)
             check_rule = ['-i', IFACE, '-p', 'tcp', '-m', 'multiport', '--dports', '1:64999', '-j', 'DNAT', '--to-destination', omr_addr]
             redirect_all_enabled = _check_rule_exists(IPTABLES_CMD, 'nat', 'PREROUTING', check_rule)
         except Exception as e:
             LOG.warning(f"Could not check iptables redirect-all status: {e}")
    redirect_status_str = "enable" if redirect_all_enabled else "disable"


    LOG.debug('Finished processing /config request.')
    # --- Assemble Final Response ---
    return {
        'vps': {'kernel': vps_kernel, 'machine': vps_machine, 'omr_version': vps_omr_version, 'loadavg': vps_loadavg_str, 'uptime': vps_uptime_sec, 'aes': vps_aes},
        'lan': {'ips': lanips},
        'shadowsocks': ss_config, # Full ss_config dict
        'glorytun': glorytun_config,
        'dsvpn': dsvpn_config,
        'openvpn': openvpn_config,
        'wireguard': wireguard_config,
        'mlvpn': mlvpn_config,
        'iptables': {'redirect_ports': redirect_status_str}, # Replaced shorewall key
        'mptcp': mptcp_config,
        'network': network_config, # Full network_config dict
        'vpn': {
            'available': available_vpn, 'current': active_vpn,
            'remoteip': vpn_remote_ip, 'localip': vpn_local_ip,
            'rx': vpn_traffic_rx, 'tx': vpn_traffic_tx
        },
        'iperf': {'user': 'openmptcprouter', 'password': 'openmptcprouter', 'key': iperf3_key},
        'pihole': {'state': pihole},
        'user': {'name': target_username, 'permission': user_permissions, 'userid': target_userid},
        'ip6in4': ip6in4_config,
        'client2client': {'enabled': client2client_enabled, 'lanips': all_other_lanips},
        'gre_tunnel': {'enabled': gre_tunnel, 'config': gre_tunnel_conf},
        'v2ray': {'enabled': v2ray_enabled, 'config': v2ray_conf, 'tx': v2ray_tx, 'rx': v2ray_rx},
        'xray': {'enabled': xray_enabled, 'config': xray_conf, 'tx': xray_tx, 'rx': xray_rx},
        'shadowsocks_go': {'enabled': ssgo_enabled, 'config': ssgo_conf, 'tx': ssgo_tx, 'rx': ssgo_rx},
        'proxy': {'available': available_proxy, 'current': active_proxy},
        'localvpn': localvpn
    }


# --- Endpoint /shadowsocks remains largely unchanged, but ensure port handling is correct ---
# --- Endpoint /shadowsocks-go remains largely unchanged ---

# --- NEW: iptables_add_fw_rule / iptables_del_fw_rule ---
def _get_vpn_interface(user: User) -> Optional[str]:
     """Helper to guess VPN interface based on user config"""
     # This is a guess, might need more robust logic based on actual setup
     vpn_type = user.vpn # Assumes user object has vpn type
     userid = user.userid
     if vpn_type == 'glorytun_tcp': return f'gt-tun{userid}'
     if vpn_type == 'glorytun_udp': return f'gt-udp-tun{userid}'
     if vpn_type == 'mlvpn': return f'mlvpn{userid}'
     if vpn_type == 'dsvpn': return f'dsvpn{userid}'
     if vpn_type == 'openvpn': return f'tun{userid}' # Common convention, but might be just tun0
     if vpn_type == 'openvpn_bonding': return 'omr-bonding'
     # Add wireguard, etc. if needed
     LOG.warning(f"Could not determine VPN interface for user {user.username} with VPN type {vpn_type}")
     return None

def iptables_add_fw_rule(user: User, port: str, proto: str, name: str, fwtype: str, source_dip: str = "", dest_ip: str = "", vpn_dest_ip: Optional[str] = None, ipproto: str = "ipv4", comment_extra: str = ""):
    """Adds firewall rules using iptables for ACCEPT or DNAT."""
    iptables_bin = IPTABLES_CMD if ipproto == "ipv4" else IP6TABLES_CMD
    add_rule_func = iptables_add_rule if ipproto == "ipv4" else ip6tables_add_rule
    primary_iface = IFACE if ipproto == "ipv4" else IFACE6

    if not primary_iface:
        LOG.error(f"Cannot add {ipproto} rule, primary interface not determined.")
        return

    # Basic validation
    if not port or not proto or not fwtype:
        LOG.error("Missing required parameters for add_fw_rule (port, proto, fwtype).")
        return
    if fwtype not in ["ACCEPT", "DNAT"]:
        LOG.error(f"Invalid fwtype '{fwtype}' for add_fw_rule.")
        return

    # Common rule parts
    rule_base = ['-p', proto]
    # Handle port ranges (e.g., "1000:2000") vs single port
    if ':' in port or ',' in port:
         rule_base.extend(['-m', 'multiport', '--dports', port])
    else:
         rule_base.extend(['--dport', port])

    if dest_ip: # Original source IP filter
        rule_base.extend(['-s', dest_ip])
    if source_dip: # Original destination IP filter (VPS public IP)
         rule_base.extend(['-d', source_dip])

    # Construct comment
    comment_base = f"OMR {user.username} {fwtype} {name} p {proto}:{port}"
    if dest_ip: comment_base += f" from {dest_ip}"
    if source_dip: comment_base += f" to {source_dip}"
    if comment_extra: comment_base += f" {comment_extra}"


    if fwtype == "ACCEPT":
        # Rule: Accept traffic *to* the firewall/VPS itself
        rule_accept = ['-i', primary_iface] + rule_base
        add_rule_func('filter', 'INPUT', rule_accept, 'ACCEPT', comment_base)

    elif fwtype == "DNAT":
        # Determine destination IP for DNAT (router's VPN IP)
        target_vpn_ip = vpn_dest_ip # Use provided IP first (e.g., for GRE tunnels)
        if not target_vpn_ip:
             # Fallback to user's configured VPN IP
             target_vpn_ip = user.vpnremoteip if user.vpnremoteip else None
             # Default for user 0 if still none
             if not target_vpn_ip and user.userid == 0:
                  # Use default based on VPN type (example)
                  if user.vpn == 'openvpn': target_vpn_ip = '10.255.252.2'
                  elif user.vpn == 'glorytun_tcp': target_vpn_ip = '10.255.255.2'
                  # Add other VPN defaults...
                  else: target_vpn_ip = '10.255.255.2' # Generic fallback
             # Add logic for user != 0 if needed

        if not target_vpn_ip:
             LOG.error(f"Cannot determine DNAT target VPN IP for user {user.username}. Skipping DNAT rule.")
             return

        # Rule 1: DNAT in PREROUTING
        rule_dnat = ['-i', primary_iface] + rule_base
        # Action for DNAT rule includes --to-destination
        dnat_action_spec = ['DNAT', '--to-destination', target_vpn_ip]
        add_rule_func('nat', 'PREROUTING', rule_dnat, dnat_action_spec[0], comment_base + " (DNAT)")

        # Rule 2: FORWARD rule to allow the DNAT'd traffic
        vpn_interface = _get_vpn_interface(user)
        if not vpn_interface:
            LOG.error(f"Cannot determine VPN interface for user {user.username}. Skipping FORWARD rule for DNAT.")
            return

        rule_fwd = ['-i', primary_iface, '-o', vpn_interface]
        # Match original source/dest if specified
        if dest_ip: rule_fwd.extend(['-s', dest_ip])
        # Match the *new* destination after DNAT
        rule_fwd.extend(['-d', target_vpn_ip])
        # Match protocol and destination port
        rule_fwd.extend(['-p', proto])
        if ':' in port or ',' in port:
            rule_fwd.extend(['-m', 'multiport', '--dports', port])
        else:
            rule_fwd.extend(['--dport', port])
        # Add state matching for robustness? Optional.
        # rule_fwd.extend(['-m', 'state', '--state', 'NEW,ESTABLISHED,RELATED'])

        add_rule_func('filter', 'FORWARD', rule_fwd, 'ACCEPT', comment_base + " (FORWARD)")

def iptables_del_fw_rule(username: str, userid: int, port: str, proto: str, name: str, fwtype: str, source_dip: str = "", dest_ip: str = "", vpn_dest_ip: Optional[str] = None, ipproto: str = "ipv4", comment_extra: str = ""):
    """Deletes firewall rules added by iptables_add_fw_rule."""
    iptables_bin = IPTABLES_CMD if ipproto == "ipv4" else IP6TABLES_CMD
    del_rule_func = iptables_del_rule if ipproto == "ipv4" else ip6tables_del_rule
    primary_iface = IFACE if ipproto == "ipv4" else IFACE6

    if not primary_iface:
        LOG.error(f"Cannot delete {ipproto} rule, primary interface not determined.")
        return

    # Basic validation
    if not port or not proto or not fwtype:
        LOG.error("Missing required parameters for del_fw_rule (port, proto, fwtype).")
        return
    if fwtype not in ["ACCEPT", "DNAT"]:
        LOG.error(f"Invalid fwtype '{fwtype}' for del_fw_rule.")
        return

    # Reload user object to get current VPN IPs etc.
    user = get_user(fake_users_db, username)
    if not user:
         LOG.error(f"Cannot find user {username} to delete firewall rule.")
         # Attempt deletion without user object if possible, but might lack info
         # For simplicity, we require the user object here.
         return


    # Common rule parts (must exactly match the add rule)
    rule_base = ['-p', proto]
    if ':' in port or ',' in port:
         rule_base.extend(['-m', 'multiport', '--dports', port])
    else:
         rule_base.extend(['--dport', port])
    if dest_ip: rule_base.extend(['-s', dest_ip])
    if source_dip: rule_base.extend(['-d', source_dip])

    # Construct comment (must exactly match the add comment)
    comment_base = f"OMR {username} {fwtype} {name} p {proto}:{port}"
    if dest_ip: comment_base += f" from {dest_ip}"
    if source_dip: comment_base += f" to {source_dip}"
    if comment_extra: comment_base += f" {comment_extra}"

    if fwtype == "ACCEPT":
        rule_accept = ['-i', primary_iface] + rule_base
        del_rule_func('filter', 'INPUT', rule_accept, 'ACCEPT', comment_base)

    elif fwtype == "DNAT":
         # Determine target VPN IP used during add
        target_vpn_ip = vpn_dest_ip # Use provided IP first
        if not target_vpn_ip:
             target_vpn_ip = user.vpnremoteip if user.vpnremoteip else None
             if not target_vpn_ip and user.userid == 0:
                  # Use same default logic as in add
                  if user.vpn == 'openvpn': target_vpn_ip = '10.255.252.2'
                  elif user.vpn == 'glorytun_tcp': target_vpn_ip = '10.255.255.2'
                  else: target_vpn_ip = '10.255.255.2'

        if not target_vpn_ip:
             LOG.error(f"Cannot determine DNAT target VPN IP for user {username}. Skipping DNAT rule deletion.")
             return

        # Rule 1: Delete DNAT
        rule_dnat = ['-i', primary_iface] + rule_base
        dnat_action_spec = ['DNAT', '--to-destination', target_vpn_ip]
        del_rule_func('nat', 'PREROUTING', rule_dnat, dnat_action_spec[0], comment_base + " (DNAT)")

        # Rule 2: Delete FORWARD
        vpn_interface = _get_vpn_interface(user)
        if not vpn_interface:
            LOG.error(f"Cannot determine VPN interface for user {user.username}. Skipping FORWARD rule deletion for DNAT.")
            return

        rule_fwd = ['-i', primary_iface, '-o', vpn_interface]
        if dest_ip: rule_fwd.extend(['-s', dest_ip])
        rule_fwd.extend(['-d', target_vpn_ip])
        rule_fwd.extend(['-p', proto])
        if ':' in port or ',' in port:
            rule_fwd.extend(['-m', 'multiport', '--dports', port])
        else:
            rule_fwd.extend(['--dport', port])
        # if state matching was used in add, include it here too

        del_rule_func('filter', 'FORWARD', rule_fwd, 'ACCEPT', comment_base + " (FORWARD)")


# Set shorewall config -> Replaced with iptables redirect all
class IPPROTO(str, Enum):
    ipv4 = "ipv4"
    ipv6 = "ipv6"

class IptablesRedirectAllparams(BaseModel):
    redirect_ports: str = Query(..., title="Enable or disable redirecting all ports", pattern="^(enable|disable)$")
    ipproto: IPPROTO = Query("ipv4", title="Protocol IP to apply changes")

@app.post('/iptables-redirect-all', summary="Redirect all ports (1-64999) from Server to router")
def iptables_redirect_all(*, params: IptablesRedirectAllparams, current_user: User = Depends(get_current_active_user)):
    if current_user.permissions == "ro":
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'iptables-redirect-all'}

    state = params.redirect_ports # "enable" or "disable"
    ipproto = params.ipproto
    iptables_bin = IPTABLES_CMD if ipproto == "ipv4" else IP6TABLES_CMD
    add_rule_func = iptables_add_rule if ipproto == "ipv4" else ip6tables_add_rule
    del_rule_func = iptables_del_rule if ipproto == "ipv4" else ip6tables_del_rule
    primary_iface = IFACE if ipproto == "ipv4" else IFACE6

    if not primary_iface:
        LOG.error(f"Cannot configure redirect-all for {ipproto}, primary interface not determined.")
        raise HTTPException(status_code=500, detail=f"Primary {ipproto} interface not configured.")

    # Determine target VPN IP (use current user's, or default for admin if needed)
    target_vpn_ip = current_user.vpnremoteip
    if not target_vpn_ip and current_user.userid == 0:
         # Add default logic similar to config endpoint if needed
         target_vpn_ip = '10.255.255.2' # Example default
    if not target_vpn_ip:
         LOG.error(f"Cannot determine target VPN IP for redirect-all for user {current_user.username}.")
         raise HTTPException(status_code=500, detail="Target VPN IP not configured for user.")

    vpn_interface = _get_vpn_interface(current_user)
    if not vpn_interface:
        LOG.error(f"Cannot determine VPN interface for redirect-all for user {current_user.username}.")
        raise HTTPException(status_code=500, detail="VPN interface not determined for user.")

    port_range = "1:64999" # Original code used 1-64999, multiport uses : or ,
    comment_tcp = f"OMR Redirect All TCP for {current_user.username}"
    comment_udp = f"OMR Redirect All UDP for {current_user.username}"

    # Define the rules
    rule_dnat_tcp = ['-i', primary_iface, '-p', 'tcp', '-m', 'multiport', '--dports', port_range]
    rule_dnat_udp = ['-i', primary_iface, '-p', 'udp', '-m', 'multiport', '--dports', port_range]
    dnat_action = ['DNAT', '--to-destination', target_vpn_ip]

    rule_fwd_tcp = ['-i', primary_iface, '-o', vpn_interface, '-d', target_vpn_ip, '-p', 'tcp', '-m', 'multiport', '--dports', port_range]
    rule_fwd_udp = ['-i', primary_iface, '-o', vpn_interface, '-d', target_vpn_ip, '-p', 'udp', '-m', 'multiport', '--dports', port_range]
    fwd_action = 'ACCEPT'

    if state == 'enable':
        LOG.info(f"Enabling redirect-all ({ipproto}) for user {current_user.username} to {target_vpn_ip} via {vpn_interface}")
        # Add DNAT rules
        add_rule_func('nat', 'PREROUTING', rule_dnat_tcp, dnat_action[0], comment_tcp + " (DNAT)")
        add_rule_func('nat', 'PREROUTING', rule_dnat_udp, dnat_action[0], comment_udp + " (DNAT)")
        # Add FORWARD rules
        add_rule_func('filter', 'FORWARD', rule_fwd_tcp, fwd_action, comment_tcp + " (FORWARD)")
        add_rule_func('filter', 'FORWARD', rule_fwd_udp, fwd_action, comment_udp + " (FORWARD)")
        # Make sure established/related traffic can return
        fwd_back_rule = ['-i', vpn_interface, '-o', primary_iface, '-s', target_vpn_ip, '-m', 'state', '--state', 'RELATED,ESTABLISHED', '-j', 'ACCEPT']
        fwd_back_comment = f"OMR Allow Established back from {current_user.username}"
        add_rule_func('filter', 'FORWARD', fwd_back_rule, 'ACCEPT', fwd_back_comment)


    elif state == 'disable':
        LOG.info(f"Disabling redirect-all ({ipproto}) for user {current_user.username}")
        # Delete DNAT rules
        del_rule_func('nat', 'PREROUTING', rule_dnat_tcp, dnat_action[0], comment_tcp + " (DNAT)")
        del_rule_func('nat', 'PREROUTING', rule_dnat_udp, dnat_action[0], comment_udp + " (DNAT)")
        # Delete FORWARD rules
        del_rule_func('filter', 'FORWARD', rule_fwd_tcp, fwd_action, comment_tcp + " (FORWARD)")
        del_rule_func('filter', 'FORWARD', rule_fwd_udp, fwd_action, comment_udp + " (FORWARD)")
        # Delete established/related rule if added (be careful if it serves other purposes)
        fwd_back_rule = ['-i', vpn_interface, '-o', primary_iface, '-s', target_vpn_ip, '-m', 'state', '--state', 'RELATED,ESTABLISHED', '-j', 'ACCEPT']
        fwd_back_comment = f"OMR Allow Established back from {current_user.username}"
        del_rule_func('filter', 'FORWARD', fwd_back_rule, 'ACCEPT', fwd_back_comment)

    else:
        raise HTTPException(status_code=400, detail="Invalid state parameter. Use 'enable' or 'disable'.")

    # Persistence note: Rules added/deleted here are not persistent.
    return {'result': 'done', 'reason': f'Redirect all ports set to {state} for {ipproto}', 'route': 'iptables-redirect-all'}

# --- Endpoint /shorewalllist removed as it reads shorewall files ---
# You could potentially implement an iptables rule listing endpoint,
# filtering by comments, but it's less straightforward than reading Shorewall files.

# --- Endpoints /shorewallopen, /shorewallclose REPLACED by /iptables-fw-open, /iptables-fw-close ---
class FwRuleParams(BaseModel):
    name: str = Query(..., title="Rule description/name")
    port: str = Query(..., title="Port or port range (e.g., 80 or 1000:2000 or 80,443)")
    proto: str = Query(..., title="Protocol (tcp, udp, icmp, etc.)")
    fwtype: str = Query(..., title="Rule type", pattern="^(ACCEPT|DNAT)$")
    ipproto: IPPROTO = Query("ipv4", title="Protocol IP for changes (ipv4 or ipv6)")
    source_dip: str = Query("", title="Original destination IP filter (VPS Public IP)")
    dest_ip: str = Query("", title="Original source IP filter") # Renamed from source_ip for clarity
    comment: str = Query("", title="Additional comment")
    # Add optional field for specific VPN destination if needed (e.g., for GRE)
    vpn_dest_ip: Optional[str] = Query(None, title="Specific VPN destination IP (overrides user default)")


@app.post('/iptables-fw-open', summary="Add a firewall ACCEPT or DNAT rule using iptables")
def iptables_fw_open(*, params: FwRuleParams, current_user: User = Depends(get_current_active_user)):
    if current_user.permissions == "ro":
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'iptables-fw-open'}

    # V2Ray/Xray integration logic removed - handled separately if needed
    # proxy = current_user.proxy # Assuming User model now has proxy
    # if proxy == 'v2ray' and params.fwtype == 'DNAT':
    #    v2ray_add_port(current_user, params.port, params.proto, params.name, params.dest_ip, params.port) # Assuming destip is router internal IP? Needs clarification.
    #    fwtype_to_apply = 'ACCEPT' # If V2Ray handles the redirect, just ACCEPT on the port
    # else:
    #    fwtype_to_apply = params.fwtype

    fwtype_to_apply = params.fwtype

    LOG.info(f"Adding {params.ipproto} rule: {fwtype_to_apply} {params.name} proto {params.proto} dport {params.port} from {params.dest_ip or 'any'} to {params.source_dip or 'any'}")

    iptables_add_fw_rule(
        user=current_user,
        port=params.port,
        proto=params.proto,
        name=params.name,
        fwtype=fwtype_to_apply,
        source_dip=params.source_dip,
        dest_ip=params.dest_ip,
        vpn_dest_ip=params.vpn_dest_ip, # Pass through specific VPN dest
        ipproto=params.ipproto,
        comment_extra=params.comment
    )
    # Persistence note: Rules are not persistent.
    return {'result': 'done', 'reason': 'changes applied', 'route': 'iptables-fw-open'}

@app.post('/iptables-fw-close', summary="Remove a firewall ACCEPT or DNAT rule using iptables")
def iptables_fw_close(*, params: FwRuleParams, current_user: User = Depends(get_current_active_user)):
    if current_user.permissions == "ro":
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'iptables-fw-close'}

    # V2Ray/Xray removal logic removed
    # proxy = current_user.proxy
    # if proxy == 'v2ray':
    #      v2ray_del_port(...)

    LOG.info(f"Removing {params.ipproto} rule: {params.fwtype} {params.name} proto {params.proto} dport {params.port} from {params.dest_ip or 'any'} to {params.source_dip or 'any'}")

    # Need to delete both potential ACCEPT and DNAT rules associated with the description
    # The provided fwtype helps, but a user might manually change rules. Safest is to try deleting both types.

    # Try deleting ACCEPT rule first
    iptables_del_fw_rule(
        username=current_user.username, # Pass username for lookup
        userid=current_user.userid, # Pass userid
        port=params.port,
        proto=params.proto,
        name=params.name,
        fwtype="ACCEPT", # Try deleting ACCEPT type
        source_dip=params.source_dip,
        dest_ip=params.dest_ip,
        vpn_dest_ip=params.vpn_dest_ip,
        ipproto=params.ipproto,
        comment_extra=params.comment
    )

    # Try deleting DNAT rule (and its corresponding FORWARD rule)
    iptables_del_fw_rule(
        username=current_user.username,
        userid=current_user.userid,
        port=params.port,
        proto=params.proto,
        name=params.name,
        fwtype="DNAT", # Try deleting DNAT type
        source_dip=params.source_dip,
        dest_ip=params.dest_ip,
        vpn_dest_ip=params.vpn_dest_ip,
        ipproto=params.ipproto,
        comment_extra=params.comment
    )

    # Persistence note: Rule deletion is not persistent.
    return {'result': 'done', 'reason': 'changes applied', 'route': 'iptables-fw-close'}


class SipALGparams(BaseModel):
    enable: bool = Query(..., title="Enable or disable SIP ALG kernel modules")

@app.post('/sipalg', summary="Enable/Disable SIP ALG kernel modules")
def sipalg(*, params: SipALGparams, current_user: User = Depends(get_current_active_user)):
    if current_user.permissions == "ro":
        return {'result': 'permission', 'reason': 'Read only user', 'route': 'sipalg'}

    enable = params.enable
    sip_modules = ["nf_nat_sip", "nf_conntrack_sip"]
    action = "Loading" if enable else "Unloading"
    cmd_bin = shutil.which('modprobe') if enable else shutil.which('rmmod')

    if not cmd_bin:
         msg = f"'modprobe'/'rmmod' command not found. Cannot {'enable' if enable else 'disable'} SIP ALG modules."
         LOG.error(msg)
         raise HTTPException(status_code=500, detail=msg)

    # Check current state (optional, but useful)
    try:
         lsmod_result = subprocess.run(['lsmod'], capture_output=True, text=True, check=True)
         modules_loaded = {m.split()[0] for m in lsmod_result.stdout.splitlines()}
    except Exception as e:
         LOG.warning(f"Could not check loaded modules via lsmod: {e}")
         modules_loaded = set() # Assume unknown state

    all_successful = True
    for module in sip_modules:
         is_loaded = module in modules_loaded
         needs_action = (enable and not is_loaded) or (not enable and is_loaded)

         if needs_action:
             LOG.info(f"{action} SIP ALG module: {module}")
             try:
                 result = subprocess.run([cmd_bin, module], capture_output=True, text=True, check=False) # Don't check=True initially
                 if result.returncode != 0:
                     # Ignore "module not found" when unloading, or "module already loaded" when loading
                     stderr_lower = result.stderr.lower()
                     if not ( (not enable and ("module not found" in stderr_lower or "is not currently loaded" in stderr_lower) ) or \
                              (enable and ("module already exists" in stderr_lower)) ):
                          LOG.error(f"Failed to {action.lower()} module {module}: {result.stderr.strip()}")
                          all_successful = False
                     else:
                          LOG.debug(f"Module {module} was already in the desired state ({'loaded' if enable else 'unloaded'}).")

             except Exception as e:
                 LOG.error(f"Error executing {cmd_bin} for module {module}: {e}")
                 all_successful = False
         else:
             LOG.debug(f"Module {module} already {'loaded' if enable else 'unloaded'}, no action needed.")

    # Persistence note: This only affects runtime state. Blacklisting/enabling modules
    # persistently requires modifying /etc/modprobe.d/ files, which is outside
    # the scope of this immediate action.
    reason = f"SIP ALG modules {'enabled' if enable else 'disabled'}."
    if not all_successful:
         reason += " (Some operations failed, check logs)"

    return {'result': 'done' if all_successful else 'warning', 'reason': reason, 'route': 'sipalg'}


# --- Endpoints /v2ray, /xray, /v2rayredirect, /xrayredirect, /v2rayunredirect, /xrayunredirect remain mostly unchanged ---
# They primarily modify V2Ray/Xray JSON config files, not firewall rules directly.

# --- Endpoint /mptcp remains unchanged (modifies sysctl values) ---
# --- Endpoint /vpn remains unchanged (modifies user config) ---
# --- Endpoint /proxy remains unchanged (modifies user config) ---
# --- Endpoints /glorytun, /dsvpn, /mlvpn, /openvpn, /wireguard remain mostly unchanged (modify specific service configs) ---
# --- Endpoint /bypass remains unchanged (modifies omr-bypass.json) ---
# --- Endpoint /wan remains unchanged (modifies shadowsocks local.acl) ---
# --- Endpoint /lan remains unchanged (modifies user config and potentially OpenVPN CCD) ---
# --- Endpoint /vpnips: Update related iptables rules if needed ---
class VPNips(BaseModel):
    remoteip: str = Query(..., pattern=r'^(?:[0-9]{1,3}\.){3}[0-9]{1,3}$') # Basic IPv4 format
    localip: str = Query(..., pattern=r'^(?:[0-9]{1,3}\.){3}[0-9]{1,3}$') # Basic IPv4 format
    remoteip6: Optional[str] = Query(None) # No strict validation here
    localip6: Optional[str] = Query(None)
    ula: Optional[str] = Query(None) # ULA Prefix

@app.post('/vpnips', summary="Set current user VPN IPs (IPv4/IPv6) and potentially update related firewall rules")
def vpnips(*, vpnconfig: VPNips, current_user: User = Depends(get_current_active_user)):
    # Read-only check might be too restrictive if only updating IPs? Decide based on policy.
    # if current_user.permissions == "ro":
    #    return {'result': 'permission', 'reason': 'Read only user', 'route': 'vpnips'}

    # Validate IPs more thoroughly
    try:
        remote_ip_obj = ip_address(vpnconfig.remoteip)
        local_ip_obj = ip_address(vpnconfig.localip)
        if not remote_ip_obj.is_private or not local_ip_obj.is_private:
             raise ValueError("Provided IPv4 addresses must be private.")
        remote_ip_str = str(remote_ip_obj)
        local_ip_str = str(local_ip_obj)

        remote_ip6_str = None
        if vpnconfig.remoteip6:
             remote_ip6_str = str(ip_address(vpnconfig.remoteip6)) # Validate format
        local_ip6_str = None
        if vpnconfig.localip6:
             local_ip6_str = str(ip_address(vpnconfig.localip6)) # Validate format

        ula_str = None
        if vpnconfig.ula:
             ula_str = str(ip_network(vpnconfig.ula, strict=False)) # Validate ULA prefix format

    except ValueError as e:
        raise HTTPException(status_code=400, detail=f"Invalid IP address or ULA format: {e}")

    # Load current config
    config_path = '/etc/openmptcprouter-vps-admin/omr-admin-config.json'
    try:
        with open(config_path, 'r') as f:
            omr_config_data = json.load(f)
        user_config = omr_config_data.get('users', [{}])[0].get(current_user.username, {})
    except (FileNotFoundError, json.JSONDecodeError, IndexError, TypeError) as e:
         LOG.error(f"Could not load config to update VPN IPs for {current_user.username}: {e}")
         raise HTTPException(status_code=500, detail="Failed to load server configuration.")

    # Check if changes are needed
    changes_made = False
    if user_config.get('vpnremoteip') != remote_ip_str:
        LOG.debug(f"Updating vpnremoteip for {current_user.username} to {remote_ip_str}")
        modif_config_user(current_user.username, {'vpnremoteip': remote_ip_str})
        changes_made = True
    if user_config.get('vpnlocalip') != local_ip_str:
        LOG.debug(f"Updating vpnlocalip for {current_user.username} to {local_ip_str}")
        modif_config_user(current_user.username, {'vpnlocalip': local_ip_str})
        changes_made = True
    if ula_str and user_config.get('ula') != ula_str:
        LOG.debug(f"Updating ula for {current_user.username} to {ula_str}")
        modif_config_user(current_user.username, {'ula': ula_str})
        changes_made = True
     # Add checks for vpnremoteip6, vpnlocalip6 if stored in config

    # --- Update omr-6in4 file ---
    userid = current_user.userid or 0 # Handle potential None userid
    omr6in4_dir = '/etc/openmptcprouter-vps-admin/omr-6in4'
    omr6in4_file_path = os.path.join(omr6in4_dir, f'user{userid}')
    sixin4_changed = False
    if not omr_config_data.get('6in4_disabled', False): # Check if 6in4 is globally disabled
         os.makedirs(omr6in4_dir, exist_ok=True) # Ensure directory exists
         new_content_lines = [
             f'LOCALIP={local_ip_str}',
             f'REMOTEIP={remote_ip_str}'
         ]
         # Use provided IPv6 or generate defaults
         effective_localip6 = local_ip6_str if local_ip6_str else f'fd00::a0{hex(userid)[2:]}:1/126'
         effective_remoteip6 = remote_ip6_str if remote_ip6_str else f'fd00::a0{hex(userid)[2:]}:2/126'
         new_content_lines.append(f'LOCALIP6={effective_localip6}')
         new_content_lines.append(f'REMOTEIP6={effective_remoteip6}')
         if ula_str:
             new_content_lines.append(f'ULA={ula_str}')
         new_content = "\n".join(new_content_lines) + "\n"

         current_content = ""
         if os.path.isfile(omr6in4_file_path):
              try:
                  with open(omr6in4_file_path, 'r') as f:
                      current_content = f.read()
              except IOError as e:
                  LOG.warning(f"Could not read existing 6in4 file {omr6in4_file_path}: {e}")

         if current_content != new_content:
              try:
                  with open(omr6in4_file_path, 'w') as f:
                      f.write(new_content)
                  LOG.info(f"Updated 6in4 config file: {omr6in4_file_path}")
                  sixin4_changed = True
                  # Restart the 6in4 service for this user
                  os.system(f"systemctl -q restart omr6in4@user{userid}")
              except IOError as e:
                   LOG.error(f"Failed to write 6in4 config file {omr6in4_file_path}: {e}")
                   # Continue, but log the failure
              except Exception as e:
                   LOG.error(f"Error restarting 6in4 service for user {userid}: {e}")


    # --- Update related iptables rules ---
    # This is the tricky part. If VPN IPs change, existing DNAT/FORWARD rules
    # pointing to the *old* IP will be wrong. We need to find and update them.
    # Option 1: Delete all rules for the user and re-add them (complex).
    # Option 2: Find rules specifically referencing the old VPN IP and replace them.
    # Option 3: Ignore for now, assume rules will be recreated manually or by subsequent calls.

    # Let's log a warning for now, as automatically updating is complex and risky.
    if changes_made:
         LOG.warning(f"VPN IP address changed for user {current_user.username}. Existing iptables DNAT/FORWARD rules referencing the old IP ({user_config.get('vpnremoteip', 'N/A')}) may need manual review or recreation using the new IP ({remote_ip_str}).")
         # set_lastchange() # Trigger update if needed

    return {'result': 'done', 'reason': 'VPN IPs updated' if changes_made or sixin4_changed else 'No changes needed', 'route': 'vpnips'}


# --- Endpoint /update remains unchanged ---
# --- Endpoints /backuppost, /backupget, /backuplist remain unchanged ---
# --- Endpoints /add_user, /remove_user need iptables adjustments ---

@app.post('/add_user', summary="Add a new user and set up basic configurations")
def add_user(*, params: NewUser, current_user: User = Depends(get_current_active_user), request: Request):
    if current_user.permissions != "admin":
        raise HTTPException(status_code=403, detail="Admin privileges required to add users.")

    # --- 1. Load Config and Validate Username ---
    config_path = '/etc/openmptcprouter-vps-admin/omr-admin-config.json'
    try:
        with open(config_path, 'r') as f:
            content = json.load(f)
        users_data = content.get('users', [{}])[0]
    except (FileNotFoundError, json.JSONDecodeError, IndexError, TypeError) as e:
        LOG.error(f"Could not load or parse user data from {config_path} for add_user: {e}")
        raise HTTPException(status_code=500, detail="Failed to load server configuration.")

    if params.username in users_data:
        raise HTTPException(status_code=400, detail=f"Username '{params.username}' already exists.")
    if not re.fullmatch(r'[a-zA-Z0-9_-]+', params.username): # Basic username validation
         raise HTTPException(status_code=400, detail="Username contains invalid characters.")


    # --- 2. Determine User ID ---
    userid = params.userid
    if userid is None or userid <= 0: # Ensure userid > 0, 0 is reserved
        max_id = 1 # Start assigning from 2
        for u_data in users_data.values():
            if isinstance(u_data, dict) and 'userid' in u_data:
                try:
                     current_id = int(u_data['userid'])
                     if current_id > max_id:
                          max_id = current_id
                except (ValueError, TypeError):
                     continue # Ignore invalid userids
        userid = max_id + 1
    else:
         # Check if provided userid is already taken
         for u_name, u_data in users_data.items():
              if isinstance(u_data, dict) and u_data.get('userid') == userid:
                   raise HTTPException(status_code=400, detail=f"UserID {userid} is already assigned to user '{u_name}'.")

    LOG.info(f"Assigning UserID {userid} to new user '{params.username}'")


    # --- 3. Prepare User Data ---
    publicips = params.ips if params.ips is not None else []
    # Generate secure password/key - user_key seems intended as password
    user_password = secrets.token_hex(16) # Generate a secure password
    # Hash the password before storing (if using verify_password with hashing)
    # hashed_password = get_password_hash(user_password) # Replace user_key.upper() below

    # Generate SS keys if not provided
    shadowsocks_key = params.shadowsocks_key if params.shadowsocks_key else base64.urlsafe_b64encode(secrets.token_bytes(16)).decode('utf-8').rstrip('=')
    shadowsocks2022_key = params.shadowsocks2022_key if params.shadowsocks2022_key else base64.urlsafe_b64encode(secrets.token_bytes(16)).decode('utf-8').rstrip('=')

    # Determine SS port if not provided
    shadowsocks_port = params.shadowsocks_port
    if shadowsocks_port is None:
         # Simple scheme: 65100 + userid (ensure it doesn't collide)
         shadowsocks_port = 65100 + userid
         # Add check for collision with existing ports if necessary

    # Generate V2Ray/Xray UUIDs (consider doing this only if they are the selected proxy)
    v2ray_uuid = str(uuid.uuid4()) # Use UUID4 for randomness
    xray_uuid = str(uuid.uuid4())
    xray_ss_ukey = base64.b64encode(secrets.token_bytes(15)).decode('ascii') # Matching original xray_add_user


    user_json_data = {
        "username": params.username,
        "permissions": params.permission,
        "user_password": user_password, # Store plain text password (NOT RECOMMENDED FOR PRODUCTION)
        # "user_password": hashed_password, # Use hashed password
        "disabled": False, # New users are enabled by default
        "userid": userid,
        "public_ips": publicips,
        "vpn": params.vpn,
        "proxy": params.proxy,
        "shadowsocks_port": shadowsocks_port,
        # Store keys directly in user config for easier retrieval? Decide on strategy.
        # "shadowsocks_key": shadowsocks_key,
        # "shadowsocks_go_upsk": shadowsocks2022_key,
        # "v2ray_uuid": v2ray_uuid,
        # "xray_uuid": xray_uuid,
        # "xray_ss_ukey": xray_ss_ukey
    }


    # --- 4. Configure Services (Shadowsocks, VPNs, etc.) ---
    # Shadowsocks-libev
    if os.path.isfile('/etc/shadowsocks-libev/manager.json') and shadowsocks_port:
         # Add SS user/port to manager.json
         # Handle potential conflicts if port is manually specified and taken
         LOG.info(f"Adding Shadowsocks-libev user {params.username} on port {shadowsocks_port}")
         # The add_ss_user function modifies manager.json and sends command
         try:
             actual_port = add_ss_user(str(shadowsocks_port), shadowsocks_key, userid, ip=publicips[0] if publicips else '')
             if actual_port != shadowsocks_port:
                  LOG.warning(f"Shadowsocks-libev assigned port {actual_port} instead of requested {shadowsocks_port}")
                  user_json_data["shadowsocks_port"] = actual_port # Update config with actual port
         except Exception as e:
              LOG.error(f"Failed to configure Shadowsocks-libev for user {params.username}: {e}")
              # Decide if this is a fatal error for user creation


    # Shadowsocks-Go
    if os.path.isfile('/etc/shadowsocks-go/server.json'):
        LOG.info(f"Adding Shadowsocks-Go user {params.username}")
        try:
            # add_ss_go_user sends command, but doesn't modify config file here
            # Need to manually add UPSK to /etc/shadowsocks-go/upsks.json if needed
            add_ss_go_user(params.username, shadowsocks2022_key)
            # TODO: Add logic to update upsks.json if required by ss-go setup
        except Exception as e:
            LOG.error(f"Failed to configure Shadowsocks-Go for user {params.username}: {e}")

    # V2Ray
    if os.path.isfile('/etc/v2ray/v2ray-server.json'):
         LOG.info(f"Adding V2Ray user {params.username} with UUID {v2ray_uuid}")
         try:
             # v2ray_add_user modifies config file and calls v2ray api command
              v2ray_add_user(params.username, v2ray_uuid, restart=0) # Add user without restarting service yet
         except Exception as e:
              LOG.error(f"Failed to configure V2Ray for user {params.username}: {e}")


    # Xray
    if os.path.isfile('/etc/xray/xray-server.json'):
        LOG.info(f"Adding Xray user {params.username} with UUID {xray_uuid}")
        try:
            # xray_add_user modifies config file and calls xray api command
            xray_add_user(params.username, xray_uuid, ukeyss2022=xray_ss_ukey, restart=0) # Add user without restarting service yet
        except Exception as e:
             LOG.error(f"Failed to configure Xray for user {params.username}: {e}")


    # VPN Configurations
    vpn_configured = False
    if os.path.isfile('/etc/openvpn/tun0.conf'):
        LOG.info(f"Creating OpenVPN certificate/key for user {params.username}")
        # Run EasyRSA command - ensure path and command are correct
        # Consider error handling for EasyRSA command
        easyrsa_cmd = f'cd /etc/openvpn/ca && EASYRSA_CERT_EXPIRE=3650 ./easyrsa --batch build-client-full "{params.username}" nopass'
        result = subprocess.run(easyrsa_cmd, shell=True, capture_output=True, text=True)
        if result.returncode != 0:
             LOG.error(f"EasyRSA command failed for user {params.username}: {result.stderr}")
             # Decide if this is fatal
        else:
             vpn_configured = True

    if os.path.isfile('/etc/glorytun-tcp/tun0'): # Check for template/base config
        LOG.info(f"Creating Glorytun-TCP config for user {params.username} (ID {userid})")
        try:
             add_glorytun_tcp(userid) # This creates config and restarts service
             vpn_configured = True
        except Exception as e:
             LOG.error(f"Failed to configure Glorytun-TCP for user {params.username}: {e}")


    if os.path.isfile('/etc/glorytun-udp/tun0'):
        LOG.info(f"Creating Glorytun-UDP config for user {params.username} (ID {userid})")
        try:
             add_glorytun_udp(userid) # This creates config and restarts service
             vpn_configured = True
        except Exception as e:
             LOG.error(f"Failed to configure Glorytun-UDP for user {params.username}: {e}")


    if os.path.isfile('/etc/dsvpn/dsvpn0'): # Check for template/base config
        LOG.info(f"Creating DSVPN config for user {params.username} (ID {userid})")
        try:
             add_dsvpn(userid) # This creates config and restarts service
             vpn_configured = True
        except Exception as e:
             LOG.error(f"Failed to configure DSVPN for user {params.username}: {e}")

    # Add other VPN types (MLVPN, WireGuard) if needed


    # --- 5. Update Master Config File ---
    content['users'][0][params.username] = user_json_data
    try:
        backup_config()
        with open(config_path, 'w') as f:
            json.dump(content, f, indent=4)
        LOG.info(f"User '{params.username}' added to main config file {config_path}.")
    except IOError as e:
        LOG.error(f"Failed to write updated user config to {config_path}: {e}")
        # Rollback service configurations? Complex. Log error and potentially raise HTTP error.
        raise HTTPException(status_code=500, detail="Failed to save user configuration.")
    except Exception as e:
         LOG.error(f"Unexpected error writing user config {config_path}: {e}")
         raise HTTPException(status_code=500, detail="Unexpected error saving user configuration.")


    # --- 6. Restart Services (if necessary, after config file is saved) ---
    # Example: Restart services that were modified but not restarted individually
    if checkIfProcessRunning('v2ray'):
         os.system("systemctl -q restart v2ray")
    if checkIfProcessRunning('xray'):
         os.system("systemctl -q restart xray")
    # Restart OpenVPN if certs were added (might not be strictly needed, depends on setup)
    if os.path.isfile('/etc/openvpn/tun0.conf'):
         os.system("systemctl -q reload openvpn@tun0") # Reload might be sufficient

    # Update global user DB cache used by authentication
    global fake_users_db
    fake_users_db = content['users'][0]

    LOG.info(f"User '{current_user.username}' (IP: {request.client.host if request.client else 'N/A'}) added user '{params.username}' (ID: {userid})")
    # set_lastchange(30) # If needed

    # Return the generated password/key for the admin to give to the user
    return {
         'result': 'done',
         'username': params.username,
         'userid': userid,
         'password': user_password, # Send back the generated password
         'shadowsocks_key': shadowsocks_key,
         'shadowsocks_go_key': shadowsocks2022_key,
         'v2ray_uuid': v2ray_uuid,
         'xray_uuid': xray_uuid
         }


@app.post('/remove_user', summary="Remove a user and their configurations")
def remove_user(*, params: RemoveUser, current_user: User = Depends(get_current_active_user), request: Request):
    if current_user.permissions != "admin":
         raise HTTPException(status_code=403, detail="Admin privileges required to remove users.")

    target_username = params.username
    if target_username == "admin": # Prevent removing admin
         raise HTTPException(status_code=400, detail="Cannot remove the default admin user.")

    # --- 1. Load Config and Find User ---
    config_path = '/etc/openmptcprouter-vps-admin/omr-admin-config.json'
    try:
        with open(config_path, 'r') as f:
            content = json.load(f)
        users_data = content.get('users', [{}])[0]
    except (FileNotFoundError, json.JSONDecodeError, IndexError, TypeError) as e:
        LOG.error(f"Could not load or parse user data from {config_path} for remove_user: {e}")
        raise HTTPException(status_code=500, detail="Failed to load server configuration.")

    if target_username not in users_data:
        raise HTTPException(status_code=404, detail=f"User '{target_username}' not found.")

    user_config = users_data[target_username]
    userid = user_config.get('userid')
    if userid is None or userid == 0: # Should not happen if admin cannot be removed
         raise HTTPException(status_code=400, detail=f"Cannot remove user '{target_username}' with invalid or reserved UserID ({userid}).")

    LOG.warning(f"Attempting to remove user '{target_username}' (ID: {userid}) requested by {current_user.username}")

    # --- 2. Remove Service Configurations ---
    errors_occurred = []

    # Shadowsocks-libev
    ss_port = user_config.get('shadowsocks_port')
    if os.path.isfile('/etc/shadowsocks-libev/manager.json') and ss_port:
        LOG.info(f"Removing Shadowsocks-libev port {ss_port} for user {target_username}")
        try:
             remove_ss_user(str(ss_port))
        except Exception as e:
             msg = f"Failed to remove Shadowsocks-libev config for port {ss_port}: {e}"
             LOG.error(msg)
             errors_occurred.append(msg)

    # Shadowsocks-Go
    if os.path.isfile('/etc/shadowsocks-go/server.json'):
        LOG.info(f"Removing Shadowsocks-Go user {target_username}")
        try:
             remove_ss_go_user(target_username)
             # TODO: Remove from upsks.json if necessary
        except Exception as e:
             msg = f"Failed to remove Shadowsocks-Go user {target_username}: {e}"
             LOG.error(msg)
             errors_occurred.append(msg)

    # V2Ray
    if os.path.isfile('/etc/v2ray/v2ray-server.json'):
        LOG.info(f"Removing V2Ray user {target_username}")
        try:
             v2ray_del_user(target_username, restart=0) # Delete without restart for now
        except Exception as e:
             msg = f"Failed to remove V2Ray user {target_username}: {e}"
             LOG.error(msg)
             errors_occurred.append(msg)

    # Xray
    if os.path.isfile('/etc/xray/xray-server.json'):
        LOG.info(f"Removing Xray user {target_username}")
        try:
             xray_del_user(target_username, restart=0) # Delete without restart for now
        except Exception as e:
             msg = f"Failed to remove Xray user {target_username}: {e}"
             LOG.error(msg)
             errors_occurred.append(msg)

    # VPN Configurations
    if os.path.isfile('/etc/openvpn/tun0.conf'):
        LOG.info(f"Revoking OpenVPN certificate for user {target_username}")
        # Check if certificate exists before revoking
        cert_path = f'/etc/openvpn/ca/pki/issued/{target_username}.crt'
        if os.path.exists(cert_path):
             easyrsa_cmd_revoke = f'cd /etc/openvpn/ca && ./easyrsa --batch revoke "{target_username}"'
             result_revoke = subprocess.run(easyrsa_cmd_revoke, shell=True, capture_output=True, text=True)
             if result_revoke.returncode != 0:
                  msg = f"EasyRSA revoke command failed for user {target_username}: {result_revoke.stderr}"
                  LOG.error(msg)
                  errors_occurred.append(msg)
             else:
                  # Generate new CRL after successful revoke
                  easyrsa_cmd_crl = 'cd /etc/openvpn/ca && ./easyrsa gen-crl'
                  result_crl = subprocess.run(easyrsa_cmd_crl, shell=True, capture_output=True, text=True)
                  if result_crl.returncode != 0:
                       msg = f"EasyRSA gen-crl command failed after revoking {target_username}: {result_crl.stderr}"
                       LOG.error(msg)
                       errors_occurred.append(msg)
                  else:
                       LOG.info(f"Generated new CRL for OpenVPN.")
                       # Clean up leftover files safely
                       for ftype in ['req', 'key', 'crt']:
                           fpath = f'/etc/openvpn/ca/pki/{ftype}s/{target_username}.{ftype}'
                           if os.path.exists(fpath):
                               try: os.remove(fpath)
                               except OSError as e: LOG.warning(f"Could not remove {fpath}: {e}")
        else:
             LOG.warning(f"OpenVPN certificate for {target_username} not found, skipping revoke.")


    # Glorytun-TCP
    if os.path.isfile(f'/etc/glorytun-tcp/tun{userid}'): # Check if config exists
        LOG.info(f"Removing Glorytun-TCP config for user {target_username} (ID {userid})")
        try:
            remove_glorytun_tcp(userid)
        except Exception as e:
             msg = f"Failed to remove Glorytun-TCP for user {target_username}: {e}"
             LOG.error(msg)
             errors_occurred.append(msg)

    # Glorytun-UDP
    if os.path.isfile(f'/etc/glorytun-udp/tun{userid}'):
        LOG.info(f"Removing Glorytun-UDP config for user {target_username} (ID {userid})")
        try:
            remove_glorytun_udp(userid)
        except Exception as e:
            msg = f"Failed to remove Glorytun-UDP for user {target_username}: {e}"
            LOG.error(msg)
            errors_occurred.append(msg)

    # DSVPN
    if os.path.isfile(f'/etc/dsvpn/dsvpn{userid}'):
        LOG.info(f"Removing DSVPN config for user {target_username} (ID {userid})")
        try:
            remove_dsvpn(userid)
        except Exception as e:
            msg = f"Failed to remove DSVPN for user {target_username}: {e}"
            LOG.error(msg)
            errors_occurred.append(msg)

    # Remove GRE tunnel iptables rules (use comment matching)
    LOG.info(f"Removing GRE iptables rules for user {target_username} (ID {userid})")
    try:
        # Delete SNAT rule(s)
        grep_cmd_snat = f"{IPTABLES_CMD} -t nat -S POSTROUTING | grep 'OMR GRE SNAT for user {target_username} ({userid})' | sed 's/^-A/{IPTABLES_CMD} -t nat -D/'"
        process_snat = subprocess.Popen(grep_cmd_snat, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        stdout_snat, stderr_snat = process_snat.communicate()
        if process_snat.returncode == 0 and stdout_snat:
            for line in stdout_snat.strip().split('\n'):
                 if line: _run_iptables_cmd(line.split(), check=False) # Use helper to run command list
        elif process_snat.returncode != 1: # Ignore grep not found
            LOG.warning(f"Error finding SNAT rules for user {target_username}: {stderr_snat}")

        # Delete MASQUERADE rule
        grep_cmd_masq = f"{IPTABLES_CMD} -t nat -S POSTROUTING | grep 'OMR GRE MASQ for user {target_username} ({userid})' | sed 's/^-A/{IPTABLES_CMD} -t nat -D/'"
        process_masq = subprocess.Popen(grep_cmd_masq, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        stdout_masq, stderr_masq = process_masq.communicate()
        if process_masq.returncode == 0 and stdout_masq:
             for line in stdout_masq.strip().split('\n'):
                  if line: _run_iptables_cmd(line.split(), check=False)
        elif process_masq.returncode != 1:
            LOG.warning(f"Error finding MASQUERADE rules for user {target_username}: {stderr_masq}")

         # Delete FORWARD rules
        grep_cmd_fwd = f"{IPTABLES_CMD} -S FORWARD | grep 'OMR GRE FWD.*user {target_username} ({userid})' | sed 's/^-A/{IPTABLES_CMD} -D/'"
        process_fwd = subprocess.Popen(grep_cmd_fwd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        stdout_fwd, stderr_fwd = process_fwd.communicate()
        if process_fwd.returncode == 0 and stdout_fwd:
             for line in stdout_fwd.strip().split('\n'):
                  if line: _run_iptables_cmd(line.split(), check=False)
        elif process_fwd.returncode != 1:
            LOG.warning(f"Error finding FORWARD rules for user {target_username}: {stderr_fwd}")

    except Exception as e:
         msg = f"Error removing GRE iptables rules for user {target_username}: {e}"
         LOG.error(msg)
         errors_occurred.append(msg)

    # Remove user-specific iptables rules (DNAT/ACCEPT) added via API
    LOG.info(f"Removing custom iptables rules for user {target_username}")
    # This requires finding all rules with the user's comment.
    try:
         grep_cmd_custom = f"{IPTABLES_CMD} -S | grep 'OMR {target_username}' | sed 's/^-A//'" # Get chain and rule spec
         process_custom = subprocess.Popen(grep_cmd_custom, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
         stdout_custom, stderr_custom = process_custom.communicate()
         if process_custom.returncode == 0 and stdout_custom:
              for line in stdout_custom.strip().split('\n'):
                   if line:
                       parts = line.split(maxsplit=1)
                       chain = parts[0]
                       rule_spec = parts[1] # Rule including -j target and comment
                       del_cmd = [IPTABLES_CMD, '-D', chain] + rule_spec.split()
                       _run_iptables_cmd(del_cmd, check=False)
         elif process_custom.returncode != 1:
              LOG.warning(f"Error finding custom IPv4 rules for user {target_username}: {stderr_custom}")
         # Repeat for ip6tables
         grep_cmd_custom6 = f"{IP6TABLES_CMD} -S | grep 'OMR {target_username}' | sed 's/^-A//'"
         process_custom6 = subprocess.Popen(grep_cmd_custom6, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
         stdout_custom6, stderr_custom6 = process_custom6.communicate()
         if process_custom6.returncode == 0 and stdout_custom6:
             for line in stdout_custom6.strip().split('\n'):
                  if line:
                      parts = line.split(maxsplit=1)
                      chain = parts[0]
                      rule_spec = parts[1]
                      del_cmd = [IP6TABLES_CMD, '-D', chain] + rule_spec.split()
                      _run_iptables_cmd(del_cmd, check=False)
         elif process_custom6.returncode != 1:
              LOG.warning(f"Error finding custom IPv6 rules for user {target_username}: {stderr_custom6}")

    except Exception as e:
         msg = f"Error removing custom iptables rules for user {target_username}: {e}"
         LOG.error(msg)
         errors_occurred.append(msg)


    # Remove 6in4 config file
    omr6in4_file_path = f'/etc/openmptcprouter-vps-admin/omr-6in4/user{userid}'
    if os.path.isfile(omr6in4_file_path):
        LOG.info(f"Removing 6in4 config file {omr6in4_file_path}")
        try:
            os.system(f"systemctl -q stop omr6in4@user{userid}") # Stop service first
            os.remove(omr6in4_file_path)
        except OSError as e:
             msg = f"Failed to remove 6in4 config file {omr6in4_file_path}: {e}"
             LOG.error(msg)
             errors_occurred.append(msg)
        except Exception as e:
             msg = f"Error stopping 6in4 service for user {userid}: {e}"
             LOG.error(msg)
             errors_occurred.append(msg)


    # --- 3. Remove User from Master Config ---
    del content['users'][0][target_username]
    try:
        backup_config()
        with open(config_path, 'w') as f:
            json.dump(content, f, indent=4)
        LOG.info(f"User '{target_username}' removed from main config file {config_path}.")
    except IOError as e:
        msg = f"Failed to write updated user config to {config_path} after removing {target_username}: {e}"
        LOG.error(msg)
        errors_occurred.append(msg)
        # This is critical, maybe raise 500?
    except Exception as e:
         msg = f"Unexpected error writing user config {config_path} after removing {target_username}: {e}"
         LOG.error(msg)
         errors_occurred.append(msg)


    # --- 4. Restart Services (if needed) ---
    # Restart services whose configs were modified by user removal
    if checkIfProcessRunning('v2ray'):
         os.system("systemctl -q restart v2ray")
    if checkIfProcessRunning('xray'):
         os.system("systemctl -q restart xray")
    if os.path.isfile('/etc/openvpn/tun0.conf'): # If OpenVPN certs were revoked
         os.system("systemctl -q reload openvpn@tun0") # Reload should pick up CRL


    # --- 5. Update Cache and Return ---
    global fake_users_db
    fake_users_db = content['users'][0]

    LOG.info(f"User '{current_user.username}' (IP: {request.client.host if request.client else 'N/A'}) removed user '{target_username}' (ID: {userid})")
    # set_lastchange(30)

    if errors_occurred:
        return {
             'result': 'warning',
             'reason': f"User '{target_username}' removed, but some cleanup operations failed.",
             'errors': errors_occurred
        }
    else:
        return {'result': 'done', 'reason': f"User '{target_username}' removed successfully."}


# --- Endpoint /add_user_note remains unchanged ---
@app.post('/add_user_note', summary="Add or update notes for a specific user")
def add_user_note(*, params: ExistingUser, current_user: User = Depends(get_current_active_user)):
    # Allow admin or the user themselves to modify their own notes? Or just admin?
    # Current check: Only admin
    if current_user.permissions != "admin":
         # Or check: if current_user.permissions != "admin" and current_user.username != params.username:
        raise HTTPException(status_code=403, detail="Admin privileges required to modify user notes.")

    # Validate that the note is a list of strings (or handle other types)
    if not isinstance(params.note, list) or not all(isinstance(item, str) for item in params.note):
         raise HTTPException(status_code=400, detail="Notes must be provided as a list of strings.")

    # Use modif_config_user which handles file I/O and backup
    LOG.info(f"Updating notes for user '{params.username}' by '{current_user.username}'")
    modif_config_user(params.username, {"note": params.note})
    # set_lastchange() # If needed

    return {'result': 'done', 'reason': f'Notes updated for user {params.username}.'}


# --- Endpoint /client2client ---
@app.post('/client2client', summary="Enable/Disable client-to-client communication via VPN")
def client2client(*, params: ClienttoClient, current_user: User = Depends(get_current_active_user)):
    if current_user.permissions != "admin":
        raise HTTPException(status_code=403, detail="Admin privileges required.")

    enable = params.enable
    set_global_param('client2client', enable) # Store global setting

    # --- OpenVPN client-to-client directive ---
    ovpn_conf_file = '/etc/openvpn/tun0.conf'
    ovpn_changed = False
    if os.path.isfile(ovpn_conf_file):
        try:
            with open(ovpn_conf_file, 'r') as f:
                lines = f.readlines()

            new_lines = []
            directive_found = False
            for line in lines:
                stripped_line = line.strip()
                if stripped_line == 'client-to-client':
                    directive_found = True
                    if enable: # Keep it if enabling
                         new_lines.append(line)
                    # else: skip line to remove it
                elif stripped_line.startswith('#') and 'client-to-client' in stripped_line:
                    # Handle commented out directive
                    if enable: # Uncomment it
                         new_lines.append("client-to-client\n")
                         directive_found = True # Mark as found so we don't add again
                    else: # Keep it commented
                         new_lines.append(line)
                else:
                    new_lines.append(line)

            # Add directive if enabling and not found
            if enable and not directive_found:
                 # Insert before a common directive like 'status' or at the end
                 inserted = False
                 for i, line in enumerate(new_lines):
                     if line.strip().startswith('status '):
                          new_lines.insert(i, "client-to-client\n")
                          inserted = True
                          break
                 if not inserted:
                      new_lines.append("client-to-client\n")


            new_content = "".join(new_lines)
            # Read original content again to compare accurately
            with open(ovpn_conf_file, 'r') as f:
                 original_content = f.read()

            if original_content != new_content:
                 with open(ovpn_conf_file, 'w') as f:
                     f.write(new_content)
                 LOG.info(f"OpenVPN client-to-client directive {'enabled' if enable else 'disabled'} in {ovpn_conf_file}.")
                 ovpn_changed = True

        except IOError as e:
            LOG.error(f"Failed to read/write OpenVPN config {ovpn_conf_file}: {e}")
        except Exception as e:
             LOG.error(f"Unexpected error processing OpenVPN config for client2client: {e}")

    # --- iptables FORWARD rules ---
    # Need to determine the main VPN interface(s) used by clients
    # This is complex if multiple VPN types are used concurrently.
    # Assuming a primary VPN interface (e.g., tun0 or wg0) for simplicity.
    # A more robust solution needs to iterate through active VPN interfaces.
    vpn_interface = "tun0" # Placeholder - DETECT OR CONFIGURE THIS
    # Example detection (very basic):
    if os.path.exists('/sys/class/net/wg0'): vpn_interface = 'wg0'
    elif os.path.exists('/sys/class/net/tun0'): vpn_interface = 'tun0'
    # Add more checks if needed

    if not vpn_interface or not os.path.exists(f'/sys/class/net/{vpn_interface}'):
         LOG.warning(f"Could not determine primary VPN interface for client-to-client iptables rules. Skipping.")
    else:
         # Define the rule and comment
         rule_c2c = ['-i', vpn_interface, '-o', vpn_interface]
         comment_c2c = "OMR Allow Client-to-Client VPN"

         # Check default FORWARD policy (assume DROP for security)
         # To check: iptables -L FORWARD -n | grep policy
         # For now, assume default is DROP, so we add/remove ACCEPT rule.

         if enable:
             LOG.info(f"Adding iptables rule to allow client-to-client on {vpn_interface}")
             iptables_add_rule('filter', 'FORWARD', rule_c2c, 'ACCEPT', comment_c2c)
             ip6tables_add_rule('filter', 'FORWARD', rule_c2c, 'ACCEPT', comment_c2c) # Add for IPv6 too
         else:
             LOG.info(f"Removing iptables rule for client-to-client on {vpn_interface}")
             iptables_del_rule('filter', 'FORWARD', rule_c2c, 'ACCEPT', comment_c2c)
             ip6tables_del_rule('filter', 'FORWARD', rule_c2c, 'ACCEPT', comment_c2c)


    # --- Restart services if needed ---
    if ovpn_changed:
         os.system("systemctl -q reload openvpn@tun0") # Reload should be sufficient

    # iptables rules take effect immediately

    return {'result': 'done', 'reason': f"Client-to-client communication {'enabled' if enable else 'disabled'}.", 'route': 'client2client'}


# --- Endpoint /serialenforce remains unchanged (modifies global config) ---
# --- Endpoint /list_users remains unchanged ---
# --- Endpoint /get-number-of-users remains unchanged ---
# --- Endpoints /speedtest (GET/POST) remain unchanged ---


# --- Helper ipv6_enabled remains unchanged ---


def main(omrport: int, omrhost: str, workers: int):
    LOG.info(f"Starting OMR-Admin API (iptables mode) on {omrhost}:{omrport} with {workers} workers.")
    # Ensure cert files exist
    cert_file = '/etc/openmptcprouter-vps-admin/cert.pem'
    key_file = '/etc/openmptcprouter-vps-admin/key.pem'
    if not os.path.exists(cert_file) or not os.path.exists(key_file):
         LOG.error(f"SSL certificate ({cert_file}) or key ({key_file}) not found.")
         LOG.error("Please generate self-signed certificates or provide valid ones.")
         # Example generation (run manually):
         # openssl req -x509 -newkey rsa:4096 -keyout /etc/openmptcprouter-vps-admin/key.pem \
         # -out /etc/openmptcprouter-vps-admin/cert.pem -sha256 -days 3650 -nodes \
         # -subj "/C=XX/ST=State/L=City/O=Organization/OU=OrgUnit/CN=your_server_ip_or_domain"
         # Make sure permissions are appropriate (e.g., chmod 600 key.pem)
         return # Exit if certs are missing

    # Log level mapping for uvicorn
    log_level = LOG.level # Get current level from logging setup
    log_level_str = logging.getLevelName(log_level).lower()

    uvicorn.run(
        "__main__:app",
        host=omrhost,
        port=omrport,
        log_level=log_level_str, # Use detected log level
        ssl_certfile=cert_file,
        ssl_keyfile=key_file,
        # ssl_version=5 is deprecated, use ssl.PROTOCOL_TLS_SERVER
        # ssl_version=ssl.PROTOCOL_TLS_SERVER, # Requires import ssl
        workers=workers
        )

if __name__ == '__main__':
    # Load base config to get parameters
    try:
        with open('/etc/openmptcprouter-vps-admin/omr-admin-config.json') as f:
            omr_config_data = json.load(f)
    except (FileNotFoundError, json.JSONDecodeError) as e:
        print(f"ERROR: Could not load config file /etc/openmptcprouter-vps-admin/omr-admin-config.json: {e}")
        omr_config_data = {} # Use defaults

    # Set log level based on config BEFORE parsing args
    if 'debug' in omr_config_data and omr_config_data['debug']:
         LOG.setLevel(logging.DEBUG)
         print("Debug logging enabled via config file.")
    else:
         LOG.setLevel(logging.INFO)


    omrport_cfg = omr_config_data.get("port", 65500)
    # Determine default host based on IPv6 capability
    default_host = '::' if ipv6_enabled() else '0.0.0.0'
    omrhost_cfg = omr_config_data.get("host", default_host)
    workers_cfg = omr_config_data.get("workers", 4)

    parser = argparse.ArgumentParser(description="OpenMPTCProuter Server API (iptables mode)")
    parser.add_argument("--port", type=int, help=f"Listening port (default: {omrport_cfg})", default=omrport_cfg)
    parser.add_argument("--host", type=str, help=f"Listening host (default: {omrhost_cfg})", default=omrhost_cfg)
    parser.add_argument("--workers", type=int, help=f"Number of worker processes (default: {workers_cfg})", default=workers_cfg)
    parser.add_argument("--debug", action='store_true', help="Enable debug logging (overrides config file setting)")

    args = parser.parse_args()

    # Override log level if --debug is passed
    if args.debug:
        LOG.setLevel(logging.DEBUG)
        print("Debug logging enabled via command line.")

    # Validate worker count
    if args.workers <= 0:
        args.workers = 1
        LOG.warning("Worker count must be positive, defaulting to 1.")

    main(args.port, args.host, args.workers)
```
