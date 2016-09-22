# -*- coding: utf-8 -*-
# (c) Copyright 2016 Hewlett Packard Enterprise Development LP
#
# GNU Zebra is free software; you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by the
# Free Software Foundation; either version 2, or (at your option) any
# later version.
#
# GNU Zebra is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with GNU Zebra; see the file COPYING.  If not, write to the Free
# Software Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
# 02111-1307, USA.


from time import sleep


TOPOLOGY = """
# +-------+
# |  sw1  |
# +-------+

# Nodes
[type=openswitch name="Switch 1"] sw1

# Ports
[up=True] sw1:4
[up=True] sw1:5
"""


def portd(sw1, step):
    # test cases for sub interface ...
    step("Teestcases for subinterface")
    # creating a Parent interface
    sw1("interface 4")
    sw1("ip address 192.168.1.5/24")
    sw1("no shutdown")
    sw1("exit")
    sw1("interface 4.2")
    sw1("no shutdown")
    sw1("ip address 192.158.1.5/24")
    sw1("encapsulation dot1Q 100")
    sw1("exit")
    sleep(6)
    step("Verify the interface is created with same name for L3 port")
    # assert "4.2" in output
    # configuerd the ip
    sleep(2)
    sw1("ip netns exec swns ifconfig 4.2", shell='bash')
    # assert "inet addr:192.158.1.5" in output
    # verifying ping
    # sw1.libs.ping.ping(5, "192.158.1.5")
    # FIXME: Ping for switch should has a function
    sw1("ping -c 5 192.158.1.5", shell='bash')
    sleep(2)
    # assert output["transmitted"] is output["received"] is 5
    # sw1("exit")
    # No Dot1Q encapsulation
    sw1("interface 4.2")
    sw1("no encapsulation dot1Q 100")
    sw1("exit")
    sw1("ip netns exec swns ifconfig 4.2", shell='bash')
    # assert "inet addr:192.158.1.5" not in output
    # deconfiguring the i/p
    sw1("interface 4.7")
    sw1("no shutdown")
    sw1("ip address 192.158.1.3/24")
    sw1("no ip address 192.158.1.3/24")
    sw1("exit")
    sw1("ip netns exec swns ifconfig 4.7", shell='bash')
    # assert "inet addr:192.158.1.3" not in output
    # verifying ping
    sw1("ping -c 5 192.158.1.5", shell='bash')
    sleep(2)
    # assert output["transmitted"] is 5 and output["received"] is 0
    # parent interface moves to L3 from L2 and vise versa - subinterfaces state
    sw1("interface 4")
    sw1("no routing")
    sw1("exit")
    sw1("ip netns exec swns ifconfig 4.7", shell='bash')
    # assert "ifconfig: error: interface `4.7' does not exist" in output
    # subinterface will down when parent will down
    sw1("interface 7")
    sw1("no shutdown")
    sw1("ip address 152.20.1.4/24")
    sw1("exit")
    sw1("interface 7.2")
    sw1("no shutdown")
    sw1("ip address 172.168.1.4/24")
    sw1("encapsulation dot1Q 10")
    sw1("exit")
    result = "ip netns exec swns ifconfig 7.2"
    sw1(result, shell='bash')
    # assert "UP" in output
    sw1("interface 7.2")
    sw1("shutdown")
    sw1("exit")
    sw1(result, shell='bash')
    # assert "UP" not in output
    # Deleting sub interface
    sw1("no interface 4.2")
    sw1("ip netns exec swns ifconfig 4.2", shell='bash')
    # assert "ifconfig: error: interface `4.2' does not exist" in output
    # Re-start ability of portd and intfd  either together or one at a time
    # test case-1
    sw1("interface 5")
    sw1("no shutdown")
    sw1("exit")
    sw1("interface 5.6")
    sw1("no shutdown")
    sw1("exit")
    sw1("systemctl stop ops-portd", shell='bash')
    ifcon = "ip netns exec swns ifconfig 5.6"
    sw1(ifcon, shell='bash')
    # assert "5.6" in output
    sw1("no int 5.6")
    sw1(ifcon, shell='bash')
    # assert "5.6" in output
    sw1("systemctl start ops-portd", shell='bash')
    sw1(ifcon, shell='bash')
    # assert "ifconfig: error: interface `5.6' does not exist" in output
    # test cases for loop back
    step("*** Test cases for loopback interface ***")
    # enabling the loopback interface
    sw1("interface loopback 1")
    sw1("exit")
    cmnd = "ip netns exec swns ifconfig loopback1"
    #out = sw1(cmnd, shell='bash')
    #assert "loopback1" in out
    # configuring the ip address and verifying
    sw1("interface loopback 1")
    sw1("ip address 192.168.1.5/24")
    sw1("exit")
    # portd needs time to react and create the interface in the kernel
    sleep(5)
    out = sw1(cmnd, shell='bash')
    assert "inet addr:192.168.1.5" in out
    # verifying "kernel_interface_ready" == "true"
    out = sw1("get port loopback1 kernel_interface_ready", shell="vsctl")
    assert "true" in out
    # verifying ping from host
    sw1("ping -c 5 192.168.1.5", shell='bash')
    sleep(2)
    # assert output["transmitted"] is output["received"] is 5
    # deconfiguring the ip addressand verifying
    sw1("interface loopback 1")
    sw1("no ip address 192.168.1.5/24")
    sw1("exit")
    sw1(cmnd, shell='bash')
    # assert "inet addr:192.168.1.5" not in output
    # verifying ping
    sw1("ping -c 5 192.168.1.5", shell='bash')
    sleep(2)
    # assert output["transmitted"] is 5 and output["received"] is 0
    # deleting the loopback interface and verifying
    sw1("no interface loopback 1")
    sw1(cmnd, shell='bash')
    # assert "inet addr:192.168.1.5" not in output


def test_portd_ct_lpbk_subinf_test_cases(topology, step):
    step("**configuring**")
    sw1 = topology.get("sw1")
    # assert sw1 is not None
    sw1("configure terminal")
    portd(sw1, step)
