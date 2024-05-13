#!/usr/bin/python
# Copyright (c) 2009-2015, Dwight Hubbard
# Copyrights licensed under the New BSD License
# # See the accompanying LICENSE.txt file for terms.
# """
# Digital Loggers Web Power Switch Management
#
# The module provides a python class named
# powerswitch that allows managing the web power
# switch from python programs.
#
# When run as a script this acts as a command line utility to
# manage the DLI Power switch.
#
# Notes
# -----
# This module has been tested against the following
# Digital Loggers Power network power switches:
#   WebPowerSwitch II
#   WebPowerSwitch III
#   WebPowerSwitch IV
#   WebPowerSwitch V
#   Ethernet Power Controller III
#
# Examples
# --------
#
# *Connecting to a Digital Loggers Power switch*
#
# >>> from dlipower import PowerSwitch
# >>> switch = PowerSwitch(hostname='lpc.digital-loggers.com', userid='admin', password='4321')
#
# *Getting the power state (status) from the switch*
# Printing the switch object will print a table with the
# Outlet Number, Name and Power State
#
# >>> switch
# DLIPowerSwitch at lpc.digital-loggers.com
# Outlet	Name           	State
# 1	Battery Charger	     OFF
# 2	K3 Power ON    	     ON
# 3	Cisco Router   	     OFF
# 4	WISP access poi	     ON
# 5	Shack Computer 	     OFF
# 6	Router         	     OFF
# 7	2TB Drive      	     ON
# 8	Cable Modem1   	     ON
#
# *Getting the name and powerswitch of the first outlet*
# The PowerSwitch has a series of Outlet objects, they
# will display their name and state if printed.
#
# >>> switch[0]
# <dlipower_outlet 'Traffic light:OFF'>
#
# *Renaming the first outlet*
# Changing the "name" attribute of an outlet will
# rename the outlet on the powerswitch.
#
# >>> switch[0].name = 'Battery Charger'
# >>> switch[0]
# <dlipower_outlet 'Battery Charger:OFF'>
#
# *Turning the first outlet on*
# Individual outlets can be accessed uses normal
# list slicing operators.
#
# >>> switch[0].on()
# False
# >>> switch[0]
# <dlipower_outlet 'Battery Charger:ON'>
#
# *Turning all outlets off*
# The PowerSwitch() object supports iterating over
# the available outlets.
#
# >>> for outlet in switch:
# ...     outlet.off()
# ...
# False
# False
# False
# False
# False
# False
# False
# False
# >>> switch
# DLIPowerSwitch at lpc.digital-loggers.com
# Outlet	Name           	State
# 1	Battery Charger	OFF
# 2	K3 Power ON    	OFF
# 3	Cisco Router   	OFF
# 4	WISP access poi	OFF
# 5	Shack Computer 	OFF
# 6	Router         	OFF
# 7	2TB Drive      	OFF
# 8	Cable Modem1   	OFF
# """

import hashlib
import logging
import multiprocessing
import json
from typing import List

import requests
import requests.exceptions
import time
import urllib3
from urllib.parse import quote
from common.utils import init_log, Component

from bs4 import BeautifulSoup

import sys
import os
sys.path.append(os.path.dirname(os.path.dirname(os.path.dirname(__file__))))
from common.config import Config
from common.networking import NetworkedDevice


urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)


# Global settings
TIMEOUT = 2
RETRIES = 3
CYCLE_TIME = 3
CONFIG_DEFAULTS = {
    'timeout': TIMEOUT,
    'cycle_time': CYCLE_TIME,
    'userid': 'admin',
    'password': '4321',
    'hostname': '192.168.0.100'
}
CONFIG_FILE = os.path.expanduser('~/.dlipower.conf')


def _call_it(params):   # pragma: no cover
    """indirect caller for instance methods and multiprocessing"""
    instance, name, args = params
    kwargs = {}
    return getattr(instance, name)(*args, **kwargs)


class DLIPowerException(Exception):
    """
    An error occurred talking the DLI Power switch
    """
    pass


class Outlet(object):
    """
    A power outlet class
    """
    use_description = True

    def __init__(self, switch, outlet_number, description=None, state=None):
        self.switch = switch
        self.outlet_number = outlet_number
        self.description = description
        if not description:
            self.description = str(outlet_number)
        self._state = state

    def __unicode__(self):
        name = None
        if self.use_description and self.description:  # pragma: no cover
            name = '%s' % self.description
        if not name:
            name = '%d' % self.outlet_number
        return '%s:%s' % (name, self._state)

    def __str__(self):
        return self.__unicode__()

    def __repr__(self):
        return "<dlipower_outlet '%s'>" % self.__unicode__()

    def _repr_html_(self):  # pragma: no cover
        """ Display representation as an html table when running in ipython """
        return u"""<table>
    <tr><th>Description</th><th>Outlet Number</th><th>State</th></tr>
    <tr><td>{0:s}</td><td>{1:s}</td><td>{2:s}</td></tr>
</table>""".format(self.description, self.outlet_number, self.state)

    @property
    def state(self):
        """ Return the outlet state """
        return self._state

    @state.setter
    def state(self, value):
        """ Set the outlet state """
        self._state = value
        if value in ['off', 'OFF', '0']:
            self.off()
        if value in ['on', 'ON', '1']:
            self.on()

    def off(self):
        """ Turn the outlet off """
        return self.switch.off(self.outlet_number)

    def on(self):
        """ Turn the outlet on """
        return self.switch.on(self.outlet_number)

    def rename(self, new_name):
        """
        Rename the outlet
        :param new_name: New name for the outlet
        :return:
        """
        return self.switch.set_outlet_name(self.outlet_number, new_name)

    @property
    def name(self):
        """ Return the name or description of the outlet """
        return self.switch.get_outlet_name(self.outlet_number)

    @name.setter
    def name(self, new_name):
        """ Set the name of the outlet """
        self.rename(new_name)


class PowerSwitch(Component, NetworkedDevice):
    """ PowerSwitch class to manage the Digital Loggers Web power switch """

    @property
    def was_shut_down(self) -> bool:
        return False

    __len = 0
    login_timeout = 2.0
    secure_login = False
    outlet_names: dict

    def __init__(self, name=None, use_https=False):
        """
        Class initialization
        """
        self._name = name
        self.power_logger = logging.getLogger(f"power-switch-{name}")
        init_log(self.power_logger)
        self.power_logger.setLevel(logging.INFO)

        self.conf = Config().toml['power-switch'][name]
        NetworkedDevice.__init__(self, self.conf)

        self.retries = self.conf['retries'] if 'retries' in self.conf else RETRIES
        self.hostname = self.destination.address
        self.userid = self.conf['username'] if 'username' in self.conf else 'admin'
        self.password = self.conf['password'] if 'password' in self.conf else '1234'
        self.timeout = self.conf['timeout'] if 'timeout' in self.conf else TIMEOUT
        self.cycle_time = self.conf['cycle_time'] if 'cycle_time' in self.conf else CYCLE_TIME
        self.num_outlets = 8
        self.outlet_names = {}
        for i in range(1, self.num_outlets+1):
            if 'outlets' in self.conf:
                self.outlet_names[str(i)] = self.conf['outlets'][str(i)] \
                    if str(i) in self.conf['outlets'] else 'Unknown'
            else:
                self.outlet_names[str(i)] = 'Unknown'

        self.scheme = 'http'
        if use_https:
            self.scheme = 'https'
        self.base_url = '%s://%s' % (self.scheme, self.hostname)
        self._is_admin = True
        self.session = requests.Session()
        self._detected = False
        try:
            self.login()
        except:
            pass

        if self.detected:
            if self.outlet_names:
                for o, name in self.outlet_names.items():
                    if self.get_outlet_name(o) != name:
                        self.set_outlet_name(o, name)

    def __len__(self):
        """
        :return: Number of outlets on the switch
        """
        if not self.detected:
            return 0

        if self.__len == 0:
            self.__len = len(self.status_list())
        return self.__len

    def __repr__(self):
        """
        display the representation
        """
        if not self.status_list():
            return "Digital Loggers Web Powerswitch " \
                   "%s (UNCONNECTED)" % self.hostname
        output = 'DLIPowerSwitch at %s\n' \
                 'Outlet\t%-15.15s\tState\n' % (self.hostname, 'Name')
        for item in self.status_list():
            output += '%d\t%-15.15s\t%s\n' % (item[0], item[1], item[2])
        return output

    def _repr_html_(self):
        """
        __repr__ in an html table format
        """
        if not self.status_list():
            return "Digital Loggers Web Powerswitch " \
                   "%s (UNCONNECTED)" % self.hostname
        output = '<table>' \
                 '<tr><th colspan="3">DLI Web Powerswitch at %s</th></tr>' \
                 '<tr>' \
                 '<th>Outlet Number</th>' \
                 '<th>Outlet Name</th>' \
                 '<th>Outlet State</th></tr>\n' % self.hostname
        for item in self.status_list():
            output += '<tr><td>%d</td><td>%s</td><td>%s</td></tr>\n' % (
                item[0], item[1], item[2])
        output += '</table>\n'
        return output

    def __getitem__(self, index):
        outlets = []
        if isinstance(index, slice):
            status = self.status_list()[index.start:index.stop]
        else:
            status = [self.status_list()[index]]
        for outlet_status in status:
            power_outlet = Outlet(
                switch=self,
                outlet_number=outlet_status[0],
                description=outlet_status[1],
                state=outlet_status[2]
            )
            outlets.append(power_outlet)
        if len(outlets) == 1:
            return outlets[0]
        return outlets

    def login(self):
        self.secure_login = False
        self.session = requests.Session()
        try:
            response = self.session.get(self.base_url, verify=False, timeout=self.login_timeout, allow_redirects=False)
            if response.is_redirect:
                self.base_url = response.headers['Location'].rstrip('/')
                self.power_logger.debug(f'Redirecting to: {self.base_url}')
                response = self.session.get(self.base_url, verify=False, timeout=self.login_timeout)
        except (requests.exceptions.ConnectTimeout, requests.exceptions.ConnectionError):
            self.session = None
            return
        soup = BeautifulSoup(response.text, 'html.parser')
        fields = {}
        for field in soup.find_all('input'):
            name = field.get('name', None)
            value = field.get('value', '')
            if name:
                fields[name] = value

        fields['Username'] = self.userid
        fields['Password'] = self.password

        form_response = fields['Challenge'] + fields['Username'] + fields['Password'] + fields['Challenge']

        m = hashlib.md5()  # nosec - The switch we are talking to uses md5 hashes
        m.update(form_response.encode())
        data = {'Username': 'admin', 'Password': m.hexdigest()}
        headers = {'Content-Type': 'application/x-www-form-urlencoded'}

        try:
            response = self.session.post('%s/login.tgi' % self.base_url, headers=headers, data=data,
                                         timeout=self.timeout, verify=False)
        except requests.exceptions.ConnectTimeout:
            self.secure_login = False
            self.session = None
            return

        if response.status_code == 200:
            if 'Set-Cookie' in response.headers:
                self.secure_login = True
            self._detected = True

    def load_configuration(self):
        """ Return a configuration dictionary """
        if os.path.isfile(CONFIG_FILE):
            file_h = open(CONFIG_FILE, 'r')
            try:
                config = json.load(file_h)
            except ValueError:
                # Failed
                return CONFIG_DEFAULTS
            file_h.close()
            return config
        return CONFIG_DEFAULTS

    def save_configuration(self):
        """ Update the configuration file with the object's settings """
        # Get the configuration from the config file or set to the defaults
        config = self.load_configuration()

        # Overwrite the objects configuration over the existing config values
        config['userid'] = self.userid
        config['password'] = self.password
        config['hostname'] = self.hostname
        config['timeout'] = self.timeout

        # Write it to disk
        file_h = open(CONFIG_FILE, 'w')
        # Make sure the file perms are correct before we write data
        # that can include the password into it.
        if hasattr(os, 'fchmod'):
            os.fchmod(file_h.fileno(), 0o0600)
        if file_h:
            json.dump(config, file_h, sort_keys=True, indent=4)
            file_h.close()
        else:
            raise DLIPowerException('Unable to open configuration file for write')

    def verify(self):
        """ Verify we can reach the switch, returns true if ok """
        if self.geturl():
            return True
        return False

    def geturl(self, url='index.htm'):
        """
        Get a URL from the userid/password protected powerswitch page Return None on failure
        """
        full_url = "%s/%s" % (self.base_url, url)
        result = None
        request = None
        self.power_logger.debug(f'Requesting url: {full_url}')
        for i in range(0, self.retries):
            try:
                if self.secure_login and self.session:
                    request = self.session.get(full_url, timeout=self.timeout, verify=False, allow_redirects=True)
                else:
                    request = requests.get(full_url, auth=(self.userid, self.password,),
                                           timeout=self.timeout, verify=False, allow_redirects=True)
            except requests.exceptions.RequestException as e:
                self.power_logger.warning("Request timed out - %d retries left.", self.retries - i - 1)
                self.power_logger.exception("Caught exception %s", str(e))
                continue
            if request.status_code == 200:
                result = request.content
                break
        self.power_logger.debug('Response code: %s', request.status_code)
        self.power_logger.debug(f'Response content: {result}')
        return result

    def determine_outlet(self, outlet=None):
        """ Get the correct outlet number from the outlet passed in, this
            allows specifying the outlet by the name and making sure the
            returned outlet is an int
        """
        outlets = self.status_list()
        if outlet and outlets and isinstance(outlet, str):
            for plug in outlets:
                plug_name = plug[1]
                if plug_name and plug_name.strip() == outlet.strip():
                    return int(plug[0])
        try:
            outlet_int = int(outlet)
            if outlet_int <= 0 or outlet_int > self.__len__():
                raise DLIPowerException('Outlet number %d out of range' % outlet_int)
            return outlet_int
        except ValueError:
            raise DLIPowerException('Outlet name \'%s\' unknown' % outlet)

    def get_outlet_name(self, outlet=0):
        """ Return the name of the outlet """
        outlet = self.determine_outlet(outlet)
        outlets = self.status_list()
        if outlets and outlet:
            for plug in outlets:
                if int(plug[0]) == outlet:
                    return plug[1]
        return 'Unknown'

    def set_outlet_name(self, outlet=0, name="Unknown"):
        """ Set the name of an outlet """
        self.determine_outlet(outlet)
        self.geturl(
            url='unitnames.cgi?outname%s=%s' % (outlet, quote(name))
        )
        return self.get_outlet_name(outlet) == name

    def off(self, outlet=0):
        """ Turn off a power to an outlet
            False = Success
            True = Fail
        """
        if self.outlet_status(outlet) == 'OFF':
            self.power_logger.info(f"Outlet '{outlet}' ({self.get_outlet_name(outlet)}) already OFF")
            return True

        self.geturl(url='outlet?%d=OFF' % self.determine_outlet(outlet))
        self.power_logger.info(f"Turned outlet '{outlet}' OFF ({self.get_outlet_name(outlet)})")
        return self.outlet_status(outlet) != 'OFF'

    def on(self, outlet=0):
        """ Turn on power to an outlet
            False = Success
            True = Fail
        """
        if self.outlet_status(outlet) == 'ON':
            self.power_logger.info(f"Outlet '{outlet}' ({self.get_outlet_name(outlet)}) already ON")
            return True

        self.geturl(url='outlet?%d=ON' % self.determine_outlet(outlet))
        self.power_logger.info(f"Turned outlet '{outlet}' ON ({self.get_outlet_name(outlet)})")
        return self.outlet_status(outlet) != 'ON'

    def is_on(self, outlet=0):
        return self.outlet_status(outlet) == 'ON'

    def is_off(self, outlet=0):
        return self.outlet_status(outlet) == 'OFF'

    def cycle(self, outlet=0):
        """ Cycle power to an outlet
            False = Power off Success
            True = Power off Fail
            Note, does not return any status info about the power on part of
            the operation by design
        """
        if self.is_off(outlet):
            self.on(outlet)
        else:
            self.off(outlet)
            time.sleep(self.cycle_time)
            self.on(outlet)
        return False

    def status_list(self):
        if not self.detected:
            return None

        """ Return the status of all outlets in a list,
        each item will contain 3 items plugnumber, hostname and state  """
        outlets = []
        try:
            url = self.geturl('index.htm')
        except TimeoutError:
            return None

        if not url:
            return None
        soup = BeautifulSoup(url, "html.parser")
        # Get the root of the table containing the port status info
        try:
            root = soup.findAll('td', string='1')[0].parent.parent.parent
        except IndexError:
            # Finding the root of the table with the outlet info failed
            # try again assuming we're seeing the table for a user
            # account instead of the admin account (tables are different)
            try:
                self._is_admin = False
                root = soup.findAll('th', text='#')[0].parent.parent.parent
            except IndexError:
                return None
        for temp in root.findAll('tr'):
            columns = temp.findAll('td')
            if len(columns) == 5:
                plugnumber = columns[0].string
                hostname = columns[1].string
                state = columns[2].find('font').string.upper()
                outlets.append([int(plugnumber), hostname, state])
        if self.__len == 0:
            self.__len = len(outlets)
        return outlets

    def printstatus(self):
        """ Print the status off all the outlets as a table to stdout """
        if not self.status_list():
            print("Unable to communicate to the Web power switch at %s" % self.hostname)
            return None
        print('Outlet\t%-15.15s\tState' % 'Name')
        for item in self.status_list():
            print('%d\t%-15.15s\t%s' % (item[0], item[1], item[2]))
        return

    def outlet_status(self, outlet=1):
        if self.detected:
            outlet_states = self.status_list()
            if outlet_states is None:
                return 'Unknown'
            st = outlet_states[outlet-1]
            return st[2]
        else:
            return 'Unknown'

    def status(self):
        """
        Return the status of the PowerSwitch
        """
        ret = {
            'ipaddr': self.ipaddress,
            'detected': self.detected,
            'operational': self.operational,
            'why_not_operational': self.why_not_operational,
            'outlets': {str(i + 1): {'name': self.outlet_names[str(i + 1)], 'state': 'Unknown'}
                        for i in range(0, len(self.outlet_names))}
        }
        if self.detected:
            outlet_states = self.status_list()
            if outlet_states is not None and len(outlet_states) != 0:
                ret['outlets'] = {str(i+1): {'name': outlet_states[i][1], 'state': outlet_states[i][2]}
                                  for i in range(0, len(outlet_states))}
        return ret

    @property
    def connected(self) -> bool:
        return self.detected

    def command_on_outlets(self, command, outlets):
        """
        If a single outlet is passed, handle it as a single outlet and
        pass back the return code.  Otherwise run the operation on multiple
        outlets in parallel the return code will be failure if any operation
        fails.  Operations that return a string will return a list of strings.
        """
        if not self.detected:
            return

        if len(outlets) == 1:
            result = getattr(self, command)(outlets[0])
            if isinstance(result, bool):
                return result
            else:
                return [result]
        pool = multiprocessing.Pool(processes=len(outlets))
        result = [
            value for value in pool.imap(
                _call_it,
                [(self, command, (outlet, )) for outlet in outlets],
                chunksize=1
            )
        ]
        pool.close()
        pool.join()
        if isinstance(result[0], bool):
            for value in result:
                if value:
                    return True
            return result[0]
        return result

    @property
    def operational(self) -> bool:
        return self.detected

    @property
    def why_not_operational(self) -> List[str]:
        ret = []
        label = f"power-switch '{self.name}'"
        if not self.detected:
            ret.append(f"{label} not detected")
        return ret

    @property
    def name(self) -> str:
        return self._name

    def abort(self):
        pass

    def startup(self):
        pass

    def shutdown(self):
        pass

    @property
    def detected(self) -> bool:
        return self._detected


class PowerSwitchFactory:
    _instances = {}

    @classmethod
    def get_instance(cls, name: str) -> PowerSwitch:
        if name not in cls._instances:
            cls._instances[name] = PowerSwitch(name=name)

        return cls._instances[name]

    def __init__(self):
        pass


class SwitchedPowerDevice:

    def __init__(self, conf: dict):
        """
        We expect a 'power' entry in the configuration dictionary
            power = {switch=<switch-name>, outlet=<outlet-number>}
        """
        if 'power' not in conf:
            raise Exception(f"Missing 'power' entry in '{conf}'")

        power_conf = conf['power']
        if 'switch' not in power_conf or 'outlet' not in power_conf:
            raise Exception(f"Either 'switch' or 'outlet' (or both) missing from configuration '{power_conf}'")

        if not isinstance(power_conf['switch'], str):
            power_conf['switch'] = str(power_conf['switch'])

        if not isinstance(power_conf['outlet'], int):
            power_conf['outlet'] = int(power_conf['outlet'])

        self.switch: PowerSwitch | None = None
        try:
            self.switch = PowerSwitchFactory.get_instance(power_conf['switch'])
        except Exception as e:
            pass
        self.outlet = power_conf['outlet']
        self.delay_after_on = power_conf['delay-after-on'] if 'delay-after-on' in power_conf else 0
        if self.switch:
            self.switch_logger = self.switch.power_logger
            self.switch_logger.setLevel(logging.INFO)

    def power_on(self):
        if self.switch and not self.switch.is_on(self.outlet):
            self.switch.on(self.outlet)
            if self.delay_after_on:
                outlet_name = self.switch.get_outlet_name(self.outlet)
                self.switch_logger.info(f"delaying {self.delay_after_on} sec. after powering ON ({outlet_name})")
                time.sleep(self.delay_after_on)

    def power_off(self):
        if self.switch and not self.switch.is_off(self.outlet):
            self.switch.off(self.outlet)

    def cycle(self):
        if self.is_on():
            self.power_off()
            time.sleep(3)
            self.power_on()
        else:
            self.power_on()

    def is_on(self) -> bool:
        if not self.switch:
            return False
        return self.switch.outlet_status(outlet=self.outlet) == 'ON'

    def is_off(self) -> bool:
        return self.switch.outlet_status(outlet=self.outlet) == 'OFF'

    def power_status(self):
        return {
            'powered': self.is_on(),
        }


if __name__ == "__main__":  # pragma: no cover
    sp = SwitchedPowerDevice({'power': {'switch': 1, 'outlet': 8}})

    if sp.is_off():
        sp.power_on()
    time.sleep(2)
    if sp.is_on():
        sp.power_off()
