/*
 * Copyright (C) 2015-2016 Hewlett-Packard Development Company, L.P.
 * All Rights Reserved.
 *
 *   Licensed under the Apache License, Version 2.0 (the "License"); you may
 *   not use this file except in compliance with the License. You may obtain
 *   a copy of the License at
 *
 *        http://www.apache.org/licenses/LICENSE-2.0
 *
 *   Unless required by applicable law or agreed to in writing, software
 *   distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 *   WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 *   License for the specific language governing permissions and limitations
 *   under the License.
 *
 * File: portd.c
 *
 */

/* This daemon handles the following functionality:
 * - Allocating internal VLAN for L3 interface.
 * - Configuring IP address for L3 interface.
 * - Enable/disable IP routing
 * - Add/delete intervlan interfaces
 */

#define _GNU_SOURCE
#include <err.h>
#include <errno.h>
#include <getopt.h>
#include <limits.h>
#include <net/if.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <fcntl.h>
#include <sched.h>
#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>
#include <dynamic-string.h>

/* OVSDB Includes */
#include "config.h"
#include "command-line.h"
#include "coverage.h"
#include "daemon.h"
#include "dirs.h"
#include "fatal-signal.h"
#include "hash.h"
#include "openvswitch/vconn.h"
#include "openvswitch/vlog.h"
#include "openswitch-dflt.h"
#include "poll-loop.h"
#include "stream.h"
#include "unixctl.h"
#include "vlan-bitmap.h"
#include "eventlog.h"
#include  <diag_dump.h>

#include "portd.h"
#include "linux_bond.h"

#include "eventlog.h"

VLOG_DEFINE_THIS_MODULE(ops_portd);

COVERAGE_DEFINE(portd_reconfigure);

#define LAG_NAME_SUFFIX_LENGTH    3
#define LAG_NAME_SUFFIX           "lag"
#define BUF_LEN 16000
#define MAX_ERR_STR_LEN 500
#define IPV4_ADDR_STR_MAXLEN  16
#define MAX_LOOPBACK_CMD_LENGTH 128
int nl_sock = -1; /* Netlink socket */
int init_sock = -1; /* This sock will only be used during init */

/* IDL variables */
unsigned int idl_seqno;
struct ovsdb_idl *idl;
struct ovsdb_idl_txn *txn;

bool commit_txn = false;

static unixctl_cb_func portd_unixctl_dump;
static unixctl_cb_func portd_unixctl_getbondingconfiguration;
static int system_configured = false;

/* This static boolean is used to configure VLANs
 * and sync IP addresses on initialization
 * and to handle restarts. */
static bool portd_config_on_init = true;

/* All vrfs, indexed by name. */
struct hmap all_vrfs = HMAP_INITIALIZER(&all_vrfs);

/**
 * A hash map of daemon's internal data for all the interfaces maintained by
 * portd.
 */
static struct shash all_interfaces = SHASH_INITIALIZER(&all_interfaces);

/**
 * A hash map of daemon's internal data for all the ports maintained by portd.
 */
static struct shash all_ports = SHASH_INITIALIZER(&all_ports);

/* Portd's internal data structure to store per lag data. */
struct port_lag_data {
    char                      *name;
    struct shash              eligible_member_ifs;
    struct shash              bonding_ifs;
    const struct ovsrec_port  *cfg;
};

/* Portd's internal data structure to store per interface data. */
struct iface_data {
    char                            *name;
    struct port_lag_data            *port_datap;
    const struct ovsrec_interface   *cfg;
};

/* Utility functions */
static struct vrf* portd_vrf_lookup(const char *name);
static struct port* portd_port_lookup(const struct vrf *vrf,
                                      const char *name);
static bool portd_check_interface_type_vlan(struct rtattr *link_info,
                                            int len);
static inline void portd_chk_for_system_configured(void);

/* Netlink related functions */
static void portd_vlan_intf_config_on_init(int intf_index,
                                           struct rtattr *link_info);
static void portd_update_kernel_intf_up_down (char *intf_name);
static void parse_nl_new_link_msg(struct nlmsghdr *h, struct shash *kernel_port_list);
static void portd_netlink_socket_open(char* vrf_ns_name, int *sock, bool is_init_sock);

static void portd_init(const char *remote);
static void portd_exit(void);
static void portd_set_status_error(const struct ovsrec_port *port_row,
                                   char *error);
static void portd_set_hw_cfg(struct port *port,
                             const struct ovsrec_port *port_row);
static void portd_interface_up_down(const char *interface_name,
                                    const char *status);
static void portd_set_interface_mtu(const char *interface_name,
                                    unsigned int mtu);
static struct ovsrec_interface* portd_get_matching_interface_row(
        const struct ovsrec_port *portrow);
static struct ovsrec_port* portd_get_port_row(
        const struct ovsrec_interface *intf_row);
static void portd_port_admin_state_reconfigure(
        struct port *port, const struct ovsrec_port *port_row);
static void portd_handle_interface_config_mods(void);

/* Internal VLAN related functions */
static void portd_bridge_del_vlan(struct ovsrec_bridge *br,
                                  struct ovsrec_vlan *vlan);
static void portd_del_internal_vlan(int internal_vid);
static int portd_alloc_internal_vlan(void);
static void portd_bridge_insert_vlan(struct ovsrec_bridge *br,
                                     struct ovsrec_vlan *vlan);
static void portd_create_vlan_row(int vid, struct ovsrec_port *port_row);
static void portd_add_internal_vlan(struct port *port,
                                    struct ovsrec_port *port_row);

/* Port related functions */
static void portd_port_create(struct vrf *vrf,
                              struct ovsrec_port *port_row);
static void portd_reconfig_ports(struct vrf *vrf,
                                 const struct shash *wanted_ports);
static void portd_collect_wanted_ports(struct vrf *vrf,
                                       struct shash *wanted_ports);
static void portd_port_destroy(struct port *port);
static void portd_del_ports(struct vrf *vrf,
                            const struct shash *wanted_ports);
static void portd_add_del_ports(void);

/* Init functions */
static void portd_intf_config_on_init (struct shash *kernel_port_list);
static void portd_vlan_config_on_init(void);
static int portd_kernel_if_sync_check_on_init (void);
extern struct kernel_port* find_or_create_kernel_port(
        struct shash *kernel_port_list, const char *ifname);

/* VRF related functions */
static void portd_vrf_del(struct vrf *vrf);
static void portd_vrf_add(const struct ovsrec_vrf *vrf_row);
static void
portd_vrf_netlink_socket_open(struct vrf *vrf_in);
static void portd_add_del_vrf(void);

static void portd_reconfigure(void);
static void portd_service_netlink_messages(void);
static void portd_run(void);
static void portd_netlink_recv_wait__(void);
static void portd_wait(void);
static void portd_unixctl_dump(struct unixctl_conn *conn,
                               int argc OVS_UNUSED,
                               const char *argv[] OVS_UNUSED,
                               void *aux OVS_UNUSED);
static char * parse_options(int argc, char *argv[], char **unixctl_pathp);
static void ops_portd_exit(struct unixctl_conn *conn, int argc OVS_UNUSED,
        const char *argv[] OVS_UNUSED, void *exiting_);
extern int
portd_get_prefix(int family, char *ip_address, void *prefix,
                 unsigned char *prefixlen);
void
portd_del_interface_netlink(const char *sub_interface_name, struct vrf *vrf);

/* Lag bonding related functions */
static void portd_del_old_interface(struct shash_node *sh_node);
static void portd_add_new_interface(const struct ovsrec_interface *ifrow);
static void update_interface_cache(void);
static void portd_del_old_port(struct shash_node *sh_node);
static void portd_add_new_port(const struct ovsrec_port *port_row);
static void portd_update_bond_slaves(struct port_lag_data *portp);
static void portd_handle_port_config(const struct ovsrec_port *row,
                                     struct port_lag_data *portp);
static void portd_update_interface_lag_eligibility(struct iface_data *idp);

bool
portd_reconfig_ns_loopback(struct port *port,
                           struct ovsrec_port *port_row, bool create_flag);

void
portd_reconfig_loopback_ipaddr(struct ovsrec_port *port_row);
void
portd_register_event_log(struct ovsrec_port *port_row,
                                     struct port *port);
static void portd_dump(char* buf, int buflen, const char* feature);
static void portd_diag_dump_basic_subif_lpbk(const char *feature , char **buf);
static bool portd_check_vlan_interface(char *port_name);

int subintf_count;
int lpbk_count;
/*
 * Lookup port entry from DB
 */
struct ovsrec_port*
portd_port_db_lookup(const char *name)
{
    const struct ovsrec_port *port_row;

    OVSREC_PORT_FOR_EACH(port_row, idl) {
        if (!strcmp(port_row->name, name)) {
            struct ovsrec_port *temp_port_row =
                    CONST_CAST(struct ovsrec_port *, port_row);
            return temp_port_row;
        }
    }
    return NULL;
}

/**
 * Function: portd_interface_type_internal_check
 * Param:
 *      port: port record whose interfaces are examined for "internal" type.
 *      interface_name: Name of interface to check "internal" type.
 * Return:
 *      true  : Provided interface exists and is of type "internal"
 *      false : Provide interface either doesn't exist or not "internal" type.
 */
bool
portd_interface_type_internal_check(const struct ovsrec_port *port,
                                    const char *interface_name)
{
    struct ovsrec_interface *intf;
    size_t i = 0;

    for (i = 0; i < port->n_interfaces; ++i) {
        intf = port->interfaces[i];
        if (strcmp(port->name, intf->name) == 0 &&
            strcmp(intf->type, OVSREC_INTERFACE_TYPE_INTERNAL) == 0) {

            VLOG_DBG("[%s:%d]: Interface %s is of type \"internal\" found. ",
                        __FUNCTION__, __LINE__, interface_name);
            return true;
        }
    }

    VLOG_DBG("[%s:%d]: Interface %s is NOT of type \"internal\". ",
                __FUNCTION__, __LINE__, interface_name);
    return false;
}

/**
 * Function: portd_interface_type_loopback_check
 * Param:
 *      port: port record whose interfaces are examined for "loopback" type.
 *      interface_name: Name of interface to check "loopback" type.
 * Return:
 *      true  : Provided interface exists and is of type "loopback"
 *      false : Provide interface either doesn't exist or not "loopback" type.
 */
bool
portd_interface_type_loopback_check(const struct ovsrec_port *port,
        const char *interface_name)
{
    struct ovsrec_interface *intf;
    size_t i=0;

    for (i=0; i<port->n_interfaces; ++i) {
        intf = port->interfaces[i];
        if (strcmp(port->name, intf->name)==0 &&
                strcmp(intf->type, OVSREC_INTERFACE_TYPE_LOOPBACK)==0) {

            VLOG_DBG("[%s:%d]: Interface %s is of type \"loopback\" found. ",
                    __FUNCTION__, __LINE__, interface_name);
            return true;
        }
    }

    VLOG_DBG("[%s:%d]: Interface %s is NOT of type \"loopback\". ",
            __FUNCTION__, __LINE__, interface_name);
    return false;
}


/**
 * Function: portd_interface_type_subinterface_check
 * Param:
 *      port: port record whose interfaces are examined for "subinterface" type
 *      interface_name: Name of interface to check "subinterface" type
 * Return:
 *      true  : Provided interface exists and is of type "subinterface"
 *      false : Provide interface either doesn't exist or not "subinterface".
 */
bool
portd_interface_type_subinterface_check(const struct ovsrec_port *port,
        const char *interface_name)
{
    struct ovsrec_interface *intf;
    size_t i=0;

    for (i=0; i<port->n_interfaces; ++i) {
        intf = port->interfaces[i];
        if (strcmp(port->name, intf->name)==0 &&
                strcmp(intf->type, OVSREC_INTERFACE_TYPE_VLANSUBINT)==0) {

            VLOG_DBG("[%s:%d]: Interface %s is of type \"vlansubintf\" found.",
                    __FUNCTION__, __LINE__, interface_name);
            return true;
        }
    }

    VLOG_DBG("[%s:%d]: Interface %s is NOT of type \"vlansubintf\". ",
            __FUNCTION__, __LINE__, interface_name);
    return false;
}




/**
 * Function: portd_port_in_bridge_check
 * Param:
 *      port_name: Name of port that is examined in bridge normal record.
 *      bridge_name: Name of bridge to be examined. If NULL/Empty, check all
 *                   bridge records.
 * Return:
 *      true  : Provided port is present in "bridge_normal"
 *      false : Provide port is not in "bridge_normal"
 */
bool
portd_port_in_bridge_check(const char *port_name, const char *bridge_name)
{
    const struct ovsrec_bridge *row, *next;
    struct ovsrec_port  *port;
    size_t i;

    OVSREC_BRIDGE_FOR_EACH_SAFE (row, next, idl) {
        if (bridge_name &&
            (strcmp(bridge_name, PORTD_EMPTY_STRING) != 0) &&
            (strcmp(row->name, bridge_name) != 0)) {
            continue;
        }

        for (i = 0; i < row->n_ports; i++) {
            port = row->ports[i];
            /* input port is part of one of bridge */
            if (strcmp(port->name, port_name) == 0) {
                VLOG_DBG("[%s:%d]: Port %s is part of bridge %s", __FUNCTION__,
                                __LINE__, port_name, bridge_name);
                return true;
            }
        }
    }

    VLOG_DBG("[%s:%d]: Port %s is NOT found in bridge %s", __FUNCTION__,
            __LINE__, port_name, bridge_name);

    return false;
}

/**
 * Function: portd_port_in_vrf_check
 * Param:
 *      port_name: Name of port that is examined in default VRF record.
 *      vrf_name: Name of VRF to be examined. NULL/empty string means, search
 *                ALL VRF records.
 * Return:
 *      true  : Provided port is present in default VRF
 *      false : Provide port is not in default VRF
 */
bool
portd_port_in_vrf_check(const char *port_name, const char *vrf_name)
{
    const struct ovsrec_vrf *row, *next;
    struct ovsrec_port  *port;
    size_t  i;

    OVSREC_VRF_FOR_EACH_SAFE (row, next, idl) {
        if (vrf_name &&
            (strcmp(vrf_name, PORTD_EMPTY_STRING) != 0) &&
            (strcmp(row->name, vrf_name) != 0)) {
            continue;
        }

        for (i = 0; i < row->n_ports; i++) {
            port = row->ports[i];
            /* input port is part of one of bridge */
            if (strcmp(port->name, port_name) == 0) {
                VLOG_DBG("[%s:%d]: Port %s is part of VRF %s", __FUNCTION__,
                                __LINE__, port_name, vrf_name);
                return true;
            }
        }
    }

    VLOG_DBG("[%s:%d]: Port %s is NOT found in VRF %s", __FUNCTION__,
            __LINE__, port_name, vrf_name);

    return false;
}

/*
 * This function is used to parse the dump command response.
 * It handles multi part message and calls the parse_nl_msg
 * function to act on Netlink messages.
 * The on_init flag is used to ensure that the recvmsg
 * blocks when init socket is reading the dump responses.
 */
void
nl_msg_process(void *user_data, int sock, bool on_init)
{
    bool multipart_msg_end = false;

    while (!multipart_msg_end) {
        struct sockaddr_nl nladdr;
        struct msghdr msg;
        struct iovec iov;
        struct nlmsghdr *nlh;
        char buffer[RECV_BUFFER_SIZE];
        int ret;

        iov.iov_base = (void *)buffer;
        iov.iov_len = sizeof(buffer);
        msg.msg_name = (void *)&(nladdr);
        msg.msg_namelen = sizeof(nladdr);
        msg.msg_iov = &iov;
        msg.msg_iovlen = 1;

        /* In order not to block on the recvmsg, MSG_DONTWAIT
         * is passed as a flag. the return value is EAGAIN if
         * no data is available
         * MSG_DONTWAIT is used during normal flow.
         * On init, we will block till we get updates from
         * the kernel and perform reconfiguration of
         * IP addresses and interfaces
         */
        ret = recvmsg(sock, &msg, on_init ? 0 : MSG_DONTWAIT);

        if (ret < 0) {
            return;
        }

        nlh = (struct nlmsghdr*) buffer;

        for (nlh = (struct nlmsghdr *) buffer;
             NLMSG_OK(nlh, ret);
             nlh = NLMSG_NEXT(nlh, ret)) {
            switch(nlh->nlmsg_type) {

            case RTM_NEWADDR:
                /*
                 * The network address dump request is only made
                 * during init. The assumption is that all the
                 * address messages from the kernel comes back
                 * immediately. So, check on the portd_config_on_init
                 * flag before we process address messages from kernel
                 */
                if (portd_config_on_init) {
                    parse_nl_ip_address_msg_on_init(nlh, ret, user_data);
                }
                break;
            case RTM_NEWLINK:
                parse_nl_new_link_msg(nlh, user_data);
                break;

            case NLMSG_DONE:
                VLOG_DBG("End of multi part message");
                multipart_msg_end = true;
                break;

            default:
                break;
            } /* end of switch */

            if (!(nlh->nlmsg_flags & NLM_F_MULTI)) {
                VLOG_DBG("End of message. Not a multipart message");
                goto end;
            }
        }
    }
end:
    return;
}

/**
 * Identify which 'vrf' a 'port' belongs to and return
 * the corresponding vrf or NULL if not found
 */
static struct vrf*
portd_vrf_lookup(const char *name)
{
    struct vrf *vrf;

    HMAP_FOR_EACH_WITH_HASH (vrf, node, hash_string(name, 0), &all_vrfs) {
        if ( vrf && !strcmp(vrf->name, name)) {
            return vrf;
        }
    }
    return NULL;
}

/**
 * This function returns the 'port' structure corresponding to a
 * port 'name' in a given 'vrf'. If the port does not not exist
 * within the 'vrf', then this function will return 'NULL'.
 */
static struct port*
portd_port_lookup(const struct vrf *vrf, const char *name)
{
    struct port *port;

    if (!vrf || !name) {
        VLOG_DBG("vrf is %s and port name is %s\n",
                 vrf ? vrf->name:"NULL",
                 name ? name:"NULL");
        return NULL;
    }

    HMAP_FOR_EACH_WITH_HASH (port, port_node, hash_string(name, 0),
                             &vrf->ports) {
        if (port && !strcmp(port->name, name)) {
            return port;
        }
    }
    return NULL;
}

/*
 * Parse the nested rtattr in IFLA_LINKFO and check if the interface
 * is of type 'vlan'
 */
static bool
portd_check_interface_type_vlan(struct rtattr *link_info, int len)
{
    while ((RTA_OK(link_info, len)) &&
           (link_info->rta_type <= IFLA_INFO_MAX)) {
            /* Check for Interface type 'vlan' */
            if ((link_info->rta_type == IFLA_INFO_KIND) &&
                (strcmp(RTA_DATA(link_info), INTERFACE_TYPE_VLAN) == 0)) {
            return true;
        }
        link_info = RTA_NEXT(link_info, len);
    }
    return false;
}

static inline void
portd_chk_for_system_configured(void)
{
    const struct ovsrec_system *ovs_vsw = NULL;

    if (system_configured) {
        /* Nothing to do if we're already configured. */
        return;
    }

    ovs_vsw = ovsrec_system_first(idl);

    if (ovs_vsw && (ovs_vsw->cur_cfg > (int64_t) 0)) {
        system_configured = true;
        VLOG_DBG("System is now configured (cur_cfg=%d).",
                (int)ovs_vsw->cur_cfg);
    }

}

/*
 * Fetch the OVSDB port row for VLAN
 * and delete from kernel if not present in DB
 */
static void
portd_vlan_intf_config_on_init(int intf_index, struct rtattr *link_info)
{
    struct ovsrec_port *port_row;
    char ifname[IF_NAMESIZE];

    if (!portd_check_interface_type_vlan(RTA_DATA(link_info),
                                         RTA_PAYLOAD(link_info))) {
        /* Interface is not of type 'vlan' */
        return;
    }

    memset(ifname, 0, sizeof(ifname));
    if_indextoname(intf_index, ifname);

    port_row = portd_port_db_lookup(ifname);
    /*
     * Check if vlan interface entry was present in DB.
     * If not, remove the vlan interface from the kernel.
     */
    if (!port_row ||
        !(portd_interface_type_internal_check(port_row, port_row->name) &&
          portd_port_in_bridge_check(port_row->name, DEFAULT_BRIDGE_NAME) &&
          portd_port_in_vrf_check(port_row->name, DEFAULT_VRF_NAME))) {
        VLOG_DBG("Deleting VLAN Interface %s", ifname);
        portd_del_vlan_interface(ifname);
    }
}

/*
 * Fetch the OVSDB interface row and update the kernel with
 * admin up/down messages
 */
static void
portd_update_kernel_intf_up_down(char *intf_name)
{
    const struct ovsrec_interface *interface_row = NULL;
    struct smap user_config;
    const char *admin_status;

    OVSREC_INTERFACE_FOR_EACH (interface_row, idl) {
        if (!strcmp(intf_name, interface_row->name)) {
            smap_clone(&user_config, &interface_row->user_config);
            admin_status = smap_get(&user_config,
                                    INTERFACE_USER_CONFIG_MAP_ADMIN);

            if (admin_status != NULL &&
                !strcmp(admin_status,
                        OVSREC_INTERFACE_USER_CONFIG_ADMIN_UP)) {
                portd_interface_up_down(interface_row->name,
                                        OVSREC_INTERFACE_USER_CONFIG_ADMIN_UP);
            } else {
                portd_interface_up_down(interface_row->name,
                                        OVSREC_INTERFACE_USER_CONFIG_ADMIN_DOWN);
            }
            smap_destroy(&user_config);
        }
    }
}

/*
 * Parse the netlink message to read all the attributes of a
 * new link message. On reading IFLA_IFNAME, verify the interface
 * state from the DB and update the kernel accordingly.
 */
static void
parse_nl_new_link_msg(struct nlmsghdr *h, struct shash *kernel_port_list)
{
    struct ifinfomsg *iface;
    struct rtattr *attribute;
    int len;

    iface = NLMSG_DATA(h);
    len = h->nlmsg_len - NLMSG_LENGTH(sizeof(*iface));

    for (attribute = IFLA_RTA(iface); RTA_OK(attribute, len);
         attribute = RTA_NEXT(attribute, len)) {
        switch(attribute->rta_type) {
        case IFLA_IFNAME:
            VLOG_DBG("New interface %d : %s\n",
                     iface->ifi_index, (char *) RTA_DATA(attribute));

            if (portd_config_on_init && kernel_port_list) {
                struct kernel_port *port;

                port = find_or_create_kernel_port (kernel_port_list, (char *)RTA_DATA(attribute));
                shash_add_once(kernel_port_list, (char *)RTA_DATA(attribute), port);
            }

            portd_update_kernel_intf_up_down((char *)RTA_DATA(attribute));
            break;
        case IFLA_LINKINFO:
            /*
             * This case is especially used for processing
             * intervlan interfaces. They are processed only during init.
             */
            if (portd_config_on_init) {
                portd_vlan_intf_config_on_init(iface->ifi_index, attribute);
            }
            break;
        default:
            break;
        }
    }
}

/*
 * Creates a netlink socket. We currently use two sockets:
 * 1. nl_sock   : To listen for udpates from the kernel
 * 2. init_sock : To send IP address & interface dump requests
 *                and perform reconfiguration on init.
 */
static void
portd_netlink_socket_open(char *vrf_ns_name, int *sock, bool is_init_sock)
{
    struct sockaddr_nl s_addr;
    struct vrf_sock_params vrf_params;

    if (*sock > 0)
        return;

    vrf_params.nl_params.family = AF_NETLINK;
    vrf_params.nl_params.type = SOCK_RAW;
    vrf_params.nl_params.protocol = NETLINK_ROUTE;

    *sock = vrf_create_socket(vrf_ns_name, &vrf_params);

    if (*sock < 0) {
        VLOG_ERR("Netlink socket creation failed (%s) for ns (%s)",
                     strerror(errno), vrf_ns_name);
        log_event("PORT_SOCKET_CREATION_FAIL",
            EV_KV("error", "%s", strerror(errno)));
        goto label;
    }

    memset((void *) &s_addr, 0, sizeof(s_addr));
    s_addr.nl_family = AF_NETLINK;
    if (!is_init_sock) {
        s_addr.nl_pid = getpid();
        s_addr.nl_groups = RTMGRP_IPV4_IFADDR | RTMGRP_IPV6_IFADDR | RTMGRP_LINK;
    }
    if (bind(*sock, (struct sockaddr *) &s_addr, sizeof(s_addr)) < 0) {
       if (errno != EADDRINUSE) {
           VLOG_ERR("Netlink socket bind failed (%s) for ns (%s)",
                    strerror(errno), vrf_ns_name);
            log_event("PORT_SOCKET_BIND_FAIL",
                          EV_KV("error", "%s", strerror(errno)));
           goto label;
           return;
       }
    }
    VLOG_DBG("Netlink socket created. fd = %d for ns (%s)", *sock, vrf_ns_name);

label:
    return;
}

/* Register for port table notifications so that:
 * When port is marked L3 (by attaching to VRF), create an internal VLAN for it.
 * When port is not L3, delete the internal VLAN associated with it.
 * When IP address (primary, secondary) are configured on the port,
 *      configure the IP in Linux kernel interfaces using netlink sockets.
 * When IP addresses are removed/modified, reflect the same in Linux.
 * When VRF is added/deleted, enable/disable Linux forwarding (routing).
 * When Interface transitions its admin state.
 */
static void
portd_init(const char *remote)
{
    int retval;

    idl = ovsdb_idl_create(remote, &ovsrec_idl_class, false, true);
    idl_seqno = ovsdb_idl_get_seqno(idl);
    ovsdb_idl_set_lock(idl, "ops_portd");
    ovsdb_idl_verify_write_only(idl);

    ovsdb_idl_add_table(idl, &ovsrec_table_subsystem);
    ovsdb_idl_add_column(idl, &ovsrec_subsystem_col_other_info);

    ovsdb_idl_add_table(idl, &ovsrec_table_system);
    ovsdb_idl_add_column(idl, &ovsrec_system_col_cur_cfg);
    ovsdb_idl_add_column(idl, &ovsrec_system_col_other_config);

    ovsdb_idl_add_table(idl, &ovsrec_table_vrf);
    ovsdb_idl_add_column(idl, &ovsrec_vrf_col_name);
    ovsdb_idl_add_column(idl, &ovsrec_vrf_col_ports);
    ovsdb_idl_add_column(idl, &ovsrec_vrf_col_status);
    ovsdb_idl_add_column(idl, &ovsrec_vrf_col_table_id);

    ovsdb_idl_add_table(idl, &ovsrec_table_bridge);
    ovsdb_idl_add_column(idl, &ovsrec_bridge_col_name);
    ovsdb_idl_add_column(idl, &ovsrec_bridge_col_vlans);
    ovsdb_idl_omit_alert(idl, &ovsrec_bridge_col_vlans);
    ovsdb_idl_add_column(idl, &ovsrec_bridge_col_ports);

    ovsdb_idl_add_table(idl, &ovsrec_table_port);
    ovsdb_idl_add_column(idl, &ovsrec_port_col_name);
    ovsdb_idl_add_column(idl, &ovsrec_port_col_hw_config);
    ovsdb_idl_omit_alert(idl, &ovsrec_port_col_hw_config);
    ovsdb_idl_add_column(idl, &ovsrec_port_col_ip4_address);
    ovsdb_idl_add_column(idl, &ovsrec_port_col_ip4_address_secondary);
    ovsdb_idl_add_column(idl, &ovsrec_port_col_ip6_address);
    ovsdb_idl_add_column(idl, &ovsrec_port_col_ip6_address_secondary);
    ovsdb_idl_add_column(idl, &ovsrec_port_col_interfaces);
    ovsdb_idl_add_column(idl, &ovsrec_port_col_vlan_tag);
    ovsdb_idl_add_column(idl, &ovsrec_port_col_admin);
    ovsdb_idl_add_column(idl, &ovsrec_port_col_status);
    ovsdb_idl_omit_alert(idl, &ovsrec_port_col_status);
    ovsdb_idl_add_column(idl, &ovsrec_port_col_other_config);
    ovsdb_idl_add_column(idl, &ovsrec_port_col_forwarding_state);
    ovsdb_idl_omit_alert(idl, &ovsrec_port_col_forwarding_state);
    ovsdb_idl_add_column(idl, &ovsrec_port_col_kernel_interface_ready);
    ovsdb_idl_omit_alert(idl, &ovsrec_port_col_kernel_interface_ready);

    /*
     * Adding the interface table so that we can listen to interface
     * "up"/"down" notifications. We need to add two columns to the
     * interface table:-
     * 1. Interface name for finding which port corresponding to the
     *    interface went "up"/"down".
     * 2. Interface admin state.
     * 3. Interface type. If it's "internal", then create a VLAN interface in
     *    kernel.
     */
    ovsdb_idl_add_table(idl, &ovsrec_table_interface);
    ovsdb_idl_add_column(idl, &ovsrec_interface_col_name);
    ovsdb_idl_add_column(idl, &ovsrec_interface_col_admin_state);
    ovsdb_idl_add_column(idl, &ovsrec_interface_col_user_config);
    ovsdb_idl_add_column(idl, &ovsrec_interface_col_hw_intf_config);
    ovsdb_idl_add_column(idl, &ovsrec_interface_col_type);
    ovsdb_idl_add_column(idl, &ovsrec_interface_col_subintf_parent);
    ovsdb_idl_add_column(idl, &ovsrec_interface_col_hw_bond_config);
    ovsdb_idl_add_column(idl, &ovsrec_interface_col_forwarding_state);

    ovsdb_idl_add_table(idl, &ovsrec_table_vlan);
    ovsdb_idl_add_column(idl, &ovsrec_vlan_col_name);
    ovsdb_idl_omit_alert(idl, &ovsrec_vlan_col_name);
    ovsdb_idl_add_column(idl, &ovsrec_vlan_col_id);
    ovsdb_idl_omit_alert(idl, &ovsrec_vlan_col_id);
    ovsdb_idl_add_column(idl, &ovsrec_vlan_col_admin);
    ovsdb_idl_omit_alert(idl, &ovsrec_vlan_col_admin);
    ovsdb_idl_add_column(idl, &ovsrec_vlan_col_oper_state);
    ovsdb_idl_omit_alert(idl, &ovsrec_vlan_col_oper_state);
    ovsdb_idl_add_column(idl, &ovsrec_vlan_col_oper_state_reason);
    ovsdb_idl_omit_alert(idl, &ovsrec_vlan_col_oper_state_reason);
    ovsdb_idl_add_column(idl, &ovsrec_vlan_col_internal_usage);
    ovsdb_idl_omit_alert(idl, &ovsrec_vlan_col_internal_usage);

    INIT_DIAG_DUMP_BASIC(portd_diag_dump_basic_subif_lpbk);
    unixctl_command_register("portd/dump", "", 0, 0,
                             portd_unixctl_dump, NULL);
    unixctl_command_register("portd/getbondingconfiguration", "", 0, 1,
                             portd_unixctl_getbondingconfiguration, NULL);
    /*
     * Open a netlink socket for communication with the kernel
     */
    portd_netlink_socket_open(DEFAULT_VRF_NAME, &nl_sock, false);

    /* By default, we disable routing at the start.
     * Enabling will be done as part of reconfigure. */
    portd_config_iprouting(DEFAULT_VRF_NAME, PORTD_DISABLE_ROUTING);

    retval = event_log_init("PORT");
    if(retval < 0) {
        VLOG_ERR("Event log initialization failed for PORT");
    }

    portd_arbiter_init();

}

static void
portd_exit(void)
{
    close(nl_sock);
    nl_sock = -1;
    ovsdb_idl_destroy(idl);
}

/* Functin to add status to port table ie up or no_internal_vlan */
static void
portd_set_status_error(const struct ovsrec_port *port_row, char *error)
{
    struct smap set_status_smap;
    if(!port_row){
        VLOG_ERR("Invalid call with port entry null");
        return;
    }
    smap_init(&set_status_smap);
    smap_clone(&set_status_smap, &port_row->status);
    smap_replace(&set_status_smap, PORT_STATUS_MAP_ERROR, error);
    ovsrec_port_set_status(port_row, &set_status_smap);
    smap_destroy(&set_status_smap);
    commit_txn = true;
}

/* Function to set hw_cfg in port row */
static void
portd_set_hw_cfg(struct port *port, const struct ovsrec_port *port_row)
{
    char vlan_id[PORTD_VLAN_ID_STRING_MAX_LEN];
    struct smap hw_cfg_smap;

    if(!port || !port_row) {
        VLOG_ERR("Invalid call with port entry null");
        return;
    }

    VLOG_DBG("Port %s  hw_config:intenal_vlan_id = %d, "
             "hw_config:enable = %d", port->name,
             port->internal_vid, port->hw_cfg_enable);

    smap_init(&hw_cfg_smap);
    smap_clone(&hw_cfg_smap, &port_row->hw_config);

    if (port->internal_vid > 0) {
        /* update port table "hw_config" with the generated vlan id */
        snprintf(vlan_id, PORTD_VLAN_ID_STRING_MAX_LEN,
                 "%d", port->internal_vid);
        smap_replace(&hw_cfg_smap, PORT_HW_CONFIG_MAP_INTERNAL_VLAN_ID,
                     vlan_id);
    } else {
        /*
         * Uninitialized VLAN ID, so we will clear this attribute
         * Internal vlan id are not generated only for L3 interfaces
         * For other ports such as Vlan interfaces we dont need this.
         */
        smap_remove(&hw_cfg_smap, PORT_HW_CONFIG_MAP_INTERNAL_VLAN_ID);
    }

    /* update enable/disable in hw_cfg */
    smap_replace(&hw_cfg_smap, PORT_HW_CONFIG_MAP_ENABLE,
                 port->hw_cfg_enable ?"true":"false");

    ovsrec_port_set_hw_config(port_row, &hw_cfg_smap);

    smap_destroy(&hw_cfg_smap);
    commit_txn = true;
}

unsigned int portd_if_nametoindex(struct vrf *vrf, const char *name)
{
    int status;
    unsigned int ifindex = 0;
    int pipe_fd[2];

    pipe(pipe_fd);
    int pid = fork();

    if (pid) { /*Parent Process waits child to exit*/
           close(pipe_fd[1]); /*read only. close write*/
           wait(&status);
           read(pipe_fd[0], &ifindex, sizeof(ifindex));
           VLOG_DBG("ifindex is :%d line number-%d ", ifindex, __LINE__);
           close(pipe_fd[0]);
           return ifindex;
    } else {
           int fd_to_ns = -1;
           char set_ns[MAX_BUFFER_LENGTH] = {0};
            close(pipe_fd[0]); /*write only. close read*/

           if (vrf && strcmp(vrf->name, DEFAULT_VRF_NAME) != 0)
           {
                    char buff[UUID_LEN+1] = {0};
                   /* non default vrf. We need to open socket by entering corresponding
                      namespace Open FD to set the thread to a namespace */
                   strcat(set_ns, "/var/run/netns/");
                   get_vrf_ns_from_table_id(idl, vrf->table_id, buff);
                   strncat(set_ns, buff, strlen(buff));
                   fd_to_ns = open(set_ns, O_RDONLY);
                   if (fd_to_ns == -1) {
                           VLOG_ERR("Unable to open fd for namepsace %s line %d ",
                                   vrf->name, __LINE__);
                            _exit(EXIT_SUCCESS);
                           return 0;
                   }
                   if (setns(fd_to_ns, 0) == -1) {
                           VLOG_ERR("Unable to set %s namespace to the thread %d %s",
                                    vrf->name, __LINE__, strerror(errno));
                           close(fd_to_ns);
                            _exit(EXIT_SUCCESS);
                           return 0;
                   }
           }
           ifindex = if_nametoindex(name);
           write(pipe_fd[1], &ifindex, sizeof(ifindex));
           if (fd_to_ns != -1)
               close(fd_to_ns);
           close(pipe_fd[1]);
           _exit(EXIT_SUCCESS);
    }
    return EXIT_SUCCESS;
}

/*
 * Function: portd_set_interface_mtu
 * Param:
 *      interface_name: Name of the interface.
 *      mtu : MTU configured for the interface.
 * Return:
 * Desc:
 *      Set MTU value for the interface specified.
 */
static void
portd_set_interface_mtu(const char *interface_name, unsigned int mtu)
{
    struct rtattr *rta;
    struct rtareq req;
    struct vrf *vrf = get_vrf_for_port(interface_name);

    if (interface_name == NULL ||
            strcmp(interface_name, PORTD_EMPTY_STRING) == 0) {
        VLOG_ERR("Invalid interface-name as argument");
        return;
    }
    memset(&req, 0, sizeof(req));

    req.n.nlmsg_len     = NLMSG_SPACE(sizeof(struct ifinfomsg));
    req.n.nlmsg_pid     = getpid();
    req.n.nlmsg_type    = RTM_NEWLINK;
    req.n.nlmsg_flags   = NLM_F_REQUEST;

    req.i.ifi_family    = AF_UNSPEC;
    req.i.ifi_index     = portd_if_nametoindex(vrf, interface_name);
    if (req.i.ifi_index == 0) {
        VLOG_ERR("Unable to get ifindex for interface: %s/%d", interface_name, __LINE__);
        return;
    }

    req.i.ifi_change = 0xffffffff;
    rta = (struct rtattr *)(((char *) &req) + NLMSG_ALIGN(req.n.nlmsg_len));
    rta->rta_type = IFLA_MTU;
    rta->rta_len = RTA_LENGTH(sizeof(unsigned int));
    req.n.nlmsg_len = NLMSG_ALIGN(req.n.nlmsg_len) + RTA_LENGTH(sizeof(mtu));
    memcpy(RTA_DATA(rta), &mtu, sizeof(mtu));

    if (send(NL_SOCK(vrf), &req, req.n.nlmsg_len, 0) == -1) {
        VLOG_ERR("Netlink failed to set mtu %d for interface %s", mtu,
                 interface_name);
        log_event("PORT_MTU_FAIL", EV_KV("mtu", "%d", mtu),
            EV_KV("interface", "%s", interface_name));
        return;
    }
}

/**
 * Function: portd_interface_up_down
 * Param:
 *      vlan_interface_name: Name of the interface to be set to "up" or "down".
 *      status: "up" or "down".
 * Return:
 * Desc:
 *      Set an interface state to "up" or "down".
 * FIXME:
 *      Plugin to "shutdown"/"no shutdown" commands under an interface.
 */
static void
portd_interface_up_down(const char *interface_name, const char *status)
{
    struct rtareq req;
    struct vrf *vrf = get_vrf_for_port(interface_name);

    if (status == NULL || strcmp(status, PORTD_EMPTY_STRING) == 0) {
        VLOG_ERR("Invalid status argument");
        return;
    }

    if (interface_name == NULL ||
            strcmp(interface_name, PORTD_EMPTY_STRING) == 0) {
        VLOG_ERR("Invalid interface-name as argument");
        return;
    }

    memset(&req, 0, sizeof(req));

    req.n.nlmsg_len = NLMSG_SPACE(sizeof(struct ifinfomsg));
    req.n.nlmsg_pid     = getpid();
    req.n.nlmsg_type    = RTM_NEWLINK;
    req.n.nlmsg_flags   = NLM_F_REQUEST;

    req.i.ifi_family    = AF_UNSPEC;
    req.i.ifi_index     = portd_if_nametoindex(vrf, interface_name);

    if (req.i.ifi_index == 0) {
        VLOG_ERR("Unable to get ifindex for interface: %s ns (%s)",
                 interface_name, vrf == NULL ? "" : vrf->name);
        return;
    }

    /* FIXME: _May_ have to convert this to "no shutdown"/"shutdown" */
    if (strcmp(status, "up") == 0) {
        req.i.ifi_change |= IFF_UP;
        req.i.ifi_flags  |= IFF_UP;
    } else if (strcmp(status, "down") == 0) {
        req.i.ifi_change |= IFF_UP;
        req.i.ifi_flags  &= ~IFF_UP;
    }

    if (send(NL_SOCK(vrf), &req, req.n.nlmsg_len, 0) == -1) {
        VLOG_ERR("Netlink failed to bring %s the interface %s", status,
                 interface_name);
        log_event("PORT_INTERFACE_FAIL", EV_KV("status", "%s", status),
            EV_KV("interface", "%s", interface_name));
        return;
    }
}

static int
add_link_attr(struct nlmsghdr *n, int nlmsg_maxlen,
        int attr_type, const void *payload, int payload_len)
{
    int len = RTA_LENGTH(payload_len);
    struct rtattr *rta;

    if (NLMSG_ALIGN(n->nlmsg_len) + RTA_ALIGN(len) > nlmsg_maxlen) {
        VLOG_ERR("message exceeded bound of %d. Failed to add attribute: %d",
                nlmsg_maxlen, attr_type);
        return -1;
    }

    rta = NLMSG_TAIL(n);
    rta->rta_type = attr_type;
    rta->rta_len = len;
    if(payload_len)
         memcpy(RTA_DATA(rta), payload, payload_len);
    n->nlmsg_len = NLMSG_ALIGN(n->nlmsg_len) + RTA_ALIGN(len);
    return 0;
}


bool
portd_reconfigure_subinterface(const struct ovsrec_port *port_row)
{
    int ifindex;

    struct {
        struct nlmsghdr  n;
        struct ifinfomsg i;
        char             buf[128];  /* must fit interface name length (IFNAMSIZ)
                                       and attribute hdrs. */
    } req;
    unsigned short vlan_tag = 0;
    const struct ovsrec_interface *intf_row = NULL,  *parent_intf_row = NULL;
    memset(&req, 0, sizeof(req));
    struct vrf *vrf = get_vrf_for_port(port_row->name);

    intf_row = portd_get_matching_interface_row(port_row);
    if (NULL == intf_row) {
        VLOG_ERR("Failed to get interface row %s", port_row->name );
        return false;
    }

    bool intf_status = false;
    if(intf_row->n_subintf_parent)
    {   static int old_tag = 0;
        parent_intf_row = intf_row->value_subintf_parent[0];
        vlan_tag = (unsigned short)intf_row->key_subintf_parent[0];
        if ((OVSREC_IDL_IS_ROW_MODIFIED(intf_row, idl_seqno)) &&
           (OVSREC_IDL_IS_COLUMN_MODIFIED(ovsrec_interface_col_subintf_parent,
                                          idl_seqno))) {
            if (old_tag != vlan_tag){
               log_event("SUBINTERFACE_ENC_UPDATE", EV_KV("interface",
                      "%s", port_row->name),
                      EV_KV("value", "%d", vlan_tag));
               old_tag = vlan_tag;
           }
       }
    }

    if (parent_intf_row && (strcmp(parent_intf_row->admin_state,
            OVSREC_INTERFACE_USER_CONFIG_ADMIN_UP) == 0))
    {
        intf_status = true;
    }else {
      return false;
    }
    const char *cur_state =NULL;
    cur_state = smap_get(&intf_row->user_config,
                INTERFACE_USER_CONFIG_MAP_ADMIN);
    if ((NULL != cur_state)
                && (strcmp(cur_state,
                        OVSREC_INTERFACE_USER_CONFIG_ADMIN_UP) == 0))
    {
        if(intf_status)
        {
            VLOG_ERR("Parent interface is down for subinterface %s",
                    port_row->name);
        }
        intf_status = false;
    }

    if(0 == vlan_tag) intf_status = false;
        portd_del_interface_netlink(port_row->name, vrf);
    if (0 != vlan_tag) {
        VLOG_INFO("Creating subinterface %s", port_row->name);

        req.n.nlmsg_len = NLMSG_SPACE(sizeof(struct ifinfomsg));
        req.n.nlmsg_pid     = getpid();
        req.n.nlmsg_type    = RTM_NEWLINK;
        req.n.nlmsg_flags   = NLM_F_REQUEST | NLM_F_CREATE | NLM_F_EXCL;

        req.i.ifi_family    = AF_UNSPEC;
        ifindex             = portd_if_nametoindex(vrf, parent_intf_row->name);

        if (ifindex == 0) {
            VLOG_ERR("Unable to get ifindex for interface: %s line number %d",
                   parent_intf_row->name,__LINE__);
            return false;
        }

        struct rtattr *linkinfo = NLMSG_TAIL(&req.n);
        add_link_attr(&req.n, sizeof(req), IFLA_LINKINFO, NULL, 0);
        add_link_attr(&req.n, sizeof(req), IFLA_INFO_KIND,
                                         INTERFACE_TYPE_VLAN, 4);

        struct rtattr * data = NLMSG_TAIL(&req.n);
        add_link_attr(&req.n, sizeof(req), IFLA_INFO_DATA, NULL, 0);
        add_link_attr(&req.n, sizeof(req), IFLA_VLAN_ID, &vlan_tag, 2);

        /* Adjust rta_len for attributes */
        data->rta_len = (void *)NLMSG_TAIL(&req.n) - (void *)data;
        linkinfo->rta_len = (void *)NLMSG_TAIL(&req.n) - (void *)linkinfo;

        add_link_attr(&req.n, sizeof(req), IFLA_LINK, &ifindex, 4);
        add_link_attr(&req.n, sizeof(req), IFLA_IFNAME, port_row->name,
                strlen(port_row->name)+1);

        if (send(NL_SOCK(vrf), &req, req.n.nlmsg_len, 0) == -1) {
            VLOG_ERR("Netlink failed to create sub interface: %s (%s)",
                    port_row->name, strerror(errno));
            return false;
        }
    }
    portd_interface_up_down(port_row->name, intf_status ? "up" : "down");

    return true;
}

/* Maskbit. */
static const u_char maskbit[] = {0x00, 0x80, 0xc0, 0xe0, 0xf0,
                                 0xf8, 0xfc, 0xfe, 0xff};

/* Number of bits in prefix type. */
#ifndef PNBBY
#define PNBBY 8
#endif /* PNBBY */

#define MASKBIT(offset)  ((0xff << (PNBBY - (offset))) & 0xff)

void
masklen2ip (int masklen,char* netmask)
{
    u_int i=0,j=0,subnet_bits = 0;
    u_char address[7];
    char *data;

    while(i < masklen)
        subnet_bits |= (1 << i++);

    data = (char *)&subnet_bits;
    j=4; i=0;
    while (j--)
      address[i++] = *data++;

    snprintf(netmask,IPV4_ADDR_STR_MAXLEN ,"%d.%d.%d.%d",
            address[0],address[1],address[2],address[3]);
}


#define ifreq_offsetof(x)  offsetof(struct ifreq, x)

void
portd_del_interface_netlink(const char *interface_name, struct vrf *vrf)
{
    struct {
        struct nlmsghdr  n;
        struct ifinfomsg i;
        char             buf[128];
    } req;

    memset(&req, 0, sizeof(req));

    req.n.nlmsg_len = NLMSG_SPACE(sizeof(struct ifinfomsg));
    req.n.nlmsg_pid     = getpid();
    req.n.nlmsg_type    = RTM_DELLINK;
    req.n.nlmsg_flags   = NLM_F_REQUEST;

    req.i.ifi_family    = AF_UNSPEC;
    req.i.ifi_index     = portd_if_nametoindex(vrf, interface_name);

    if (req.i.ifi_index == 0) {
        VLOG_ERR("Unable to get ifindex for interface: %s/%d",
                 interface_name, __LINE__);
        return;
    }

    if (send(NL_SOCK(vrf), &req, req.n.nlmsg_len, 0) == -1) {
        VLOG_ERR("Netlink failed to delete interface: %s (%s)",
                interface_name, strerror(errno));
        return;
    }

    VLOG_INFO("Deleted interface %s", interface_name);
    return;
}


/* Function : fffffffet_matching_interface_row()
 * Desc     : search the ovsdb and get the matching
 *            interface row based on the port row name.
 * Param    : seach based on row name
 * Return   : returns the matching row or NULL incase
 *            no row is found.
 */
static struct ovsrec_interface *
portd_get_matching_interface_row(const struct ovsrec_port *port_row)
{
    const struct ovsrec_interface *int_row = NULL;
    int i;

    for (i = 0; i < port_row->n_interfaces; i++) {
        int_row = port_row->interfaces[i];
        if (!strcmp(int_row->name, port_row->name)) {
            return (struct ovsrec_interface *)int_row;
        }
    }
    return NULL;
}

/* Function : portd_get_port_row()
 * Desc     : search the ovsdb and get the port
 *           row for the interface.
 * Param    : interface row
 * Return   : returns the port row or NULL in case
 *            no row is found.
 */
static struct ovsrec_port *
portd_get_port_row(const struct ovsrec_interface *intf_row)
{
    const struct ovsrec_port *port_row = NULL;
    int i;

    /* find out which port has this interface associated with it */
    OVSREC_PORT_FOR_EACH(port_row, idl) {
        if (port_row->n_interfaces) {
            for (i = 0; i < port_row->n_interfaces; i++) {
                if (port_row->interfaces[i] == intf_row) {
                    return (struct ovsrec_port *)port_row;
                }
            }
        }
    }

    return NULL;
}

/* Function : portd_port_admin_state_reconfigure()
 * Desc     : Updates the hw_config key "enable" based on the user
 *            configuration to set the port admin state to up or down.
 * Param    : None
 * Return   : None
 */
static void
portd_port_admin_state_reconfigure(struct port *port,
                                   const struct ovsrec_port *port_row)
{
    const struct ovsrec_interface *intf_row = NULL;
    char *cur_state = NULL;
    /* default states of interface and port admin */
    bool intf_admin = false;
    bool port_admin = true;

    /*
     * Check if the admin state column changed.
     */
    if ((OVSREC_IDL_IS_COLUMN_MODIFIED(
                ovsrec_port_col_admin, idl_seqno)) ||
        (OVSREC_IDL_IS_COLUMN_MODIFIED(
                ovsrec_port_col_interfaces, idl_seqno))) {

        VLOG_DBG("port column modified\n");

            /* If the port row is modified then
             * update the hw_config for that row */
            if (OVSREC_IDL_IS_ROW_MODIFIED(port_row, idl_seqno)) {
                /* Check for port admin changes based on interface
                   row user_config chnages */
                if ((intf_row = portd_get_matching_interface_row(port_row))
                        != NULL) {
                    /* Its a VLAN or L3 interface */
                    VLOG_DBG("set up state for L3 and vlan interface\n");
                    /* Get interface state */
                    cur_state = (char *)smap_get(&intf_row->user_config,
                                                 INTERFACE_USER_CONFIG_MAP_ADMIN);
                    if (cur_state &&
                        (VTYSH_STR_EQ(cur_state,
                                      OVSREC_INTERFACE_USER_CONFIG_ADMIN_UP))) {
                        intf_admin = true;
                    }
                    /* Get port state */
                    if (port_row->admin &&
                        (VTYSH_STR_EQ(port_row->admin,
                                      PORT_CONFIG_ADMIN_DOWN))) {
                        port_admin = false;
                    }
                    /* The final state is the 'and operation' between
                       the port admin and the interface admin */
                    port->hw_cfg_enable = (intf_admin && port_admin);
                } else {
                    /* its a LAG */
                    /* set hw_config same as port admin_status */
                    VLOG_DBG("set up in LAG interface\n");
                    if ((port_row->admin == NULL) ||
                        (strcmp(port_row->admin, "up") == 0)) {
                        port->hw_cfg_enable = true;
                    } else {
                        port->hw_cfg_enable = false;
                    }
                }
                portd_set_hw_cfg(port, port_row);
            }
    }
}

/**
 * Deletes an old interface from the daemon's internal data structures
 */
static void
portd_del_old_interface(struct shash_node *sh_node)
{
    if (sh_node) {
        struct iface_data *idp = sh_node->data;
        SAFE_FREE(idp->name);
        SAFE_FREE(idp);
        shash_delete(&all_interfaces, sh_node);
    }
} /* portd_del_old_interface */

/**
 * Adds a new interface to daemon's internal data structures.
 *
 * Allocates a new iface_data entry. Parses the ifrow and
 * copies data into new iface_data entry.
 * Adds the new iface_data entry into all_interfaces shash map.
 * @param ifrow pointer to interface configuration row in IDL cache.
 */
static void
portd_add_new_interface(const struct ovsrec_interface *ifrow)
{
    struct iface_data *idp = NULL;

    VLOG_DBG("Interface %s being added!", ifrow->name);

    /* Allocate structure to save state information for this interface. */
    idp = xzalloc(sizeof *idp);

    if (!shash_add_once(&all_interfaces, ifrow->name, idp)) {
        VLOG_WARN("Interface %s specified twice", ifrow->name);
        SAFE_FREE(idp);
    } else {
       /* Save the interface name. */
       idp->name = xstrdup(ifrow->name);

       /* Save the reference to IDL row. */
       idp->cfg = ifrow;

       VLOG_DBG("Created local data for interface %s", ifrow->name);
    }
} /* portd_add_new_interface */

/**
 * Update daemon's internal interface data structures based on the latest
 * data from OVSDB.
 */
static void
update_interface_cache(void)
{
    struct shash sh_idl_interfaces;
    const struct ovsrec_interface *ifrow;
    struct shash_node *sh_node, *sh_next;

    /* Collect all the interfaces in the DB. */
    shash_init(&sh_idl_interfaces);
    OVSREC_INTERFACE_FOR_EACH(ifrow, idl) {
        if (!shash_add_once(&sh_idl_interfaces, ifrow->name, ifrow)) {
            VLOG_WARN("interface %s specified twice", ifrow->name);
        }
    }

    /* Delete old interfaces. */
    SHASH_FOR_EACH_SAFE(sh_node, sh_next, &all_interfaces) {
        struct iface_data *idp =
            shash_find_data(&sh_idl_interfaces, sh_node->name);
        if (!idp) {
            portd_del_old_interface(sh_node);
        }
    }

    /* Add new interfaces. */
    SHASH_FOR_EACH(sh_node, &sh_idl_interfaces) {
        struct iface_data *idp =
            shash_find_data(&all_interfaces, sh_node->name);
        if (!idp) {
            portd_add_new_interface(sh_node->data);
        }
    }

    /* Check for changes in the interface row entries. */
    SHASH_FOR_EACH(sh_node, &all_interfaces) {
        struct iface_data *idp = sh_node->data;
        const struct ovsrec_interface *ifrow =
            shash_find_data(&sh_idl_interfaces, sh_node->name);

        /* Check for changes to row. */
        if (OVSREC_IDL_IS_ROW_INSERTED(ifrow, idl_seqno) ||
            OVSREC_IDL_IS_ROW_MODIFIED(ifrow, idl_seqno)) {

            /* Update eligibility in interfaces that are already in a LAG */
            if(idp->port_datap && !strncmp(idp->port_datap->name,
                                           LAG_NAME_SUFFIX,
                                           LAG_NAME_SUFFIX_LENGTH)) {
                portd_update_interface_lag_eligibility(idp);
                portd_update_bond_slaves(idp->port_datap);
            }
        }
    }
    /* Destroy the shash of the IDL interfaces. */
    shash_destroy(&sh_idl_interfaces);
}
/**
 * This function processes the interface "up"/"down" notifications
 * & MTU notifications that are received from OVSDB.
 * In response to a change in interface
 * admin state, this function does the following:
 * 1. Based on interface user_config:admin, bring up/down the kernel
 *    interface
 * 2. The functions finds the port structure corresponding to the
 *    interface name whose state has changed. For this we need to
 *    iterate over all the vrfs in our cache and find the port
 *    structure corresponding to the interface name.
 * 3. In event, we find a port structure corresponding to the
 *    interface name and the interface administration state went to
 *    "up", we go ahead and reprogram the IPv6 addresses on that
 *    port.
 * 4. If port found, updates the hw_config key "enable" based on the user
 *            configuration to set the port admin state to up or down.
 * In response to change in MTU value in hw_config_info,
 * 1. Finds the port structure corresponding to the interface name and
 *    updates the MTU value for that kernel interface.
 */
static void
portd_handle_interface_config_mods(void)
{
    const struct ovsrec_port *port_row = NULL;
    const struct ovsrec_interface *intf_row = NULL;
    char *cur_state = NULL;
    char *hw_intf_config_mtu = NULL;

    /* default states of interface and port admin */
    bool intf_admin = false;
    bool port_admin = true;
    struct port *port = NULL;
    struct vrf *vrf;

    VLOG_DBG("portd_intf_admin_state_up_down_events\n");

    OVSREC_INTERFACE_FOR_EACH (intf_row, idl) {
        port = NULL;
        port_row = NULL;

        /* If the interface row is modified then update the hw_intf_config
               for the corresponding port row */
        if (OVSREC_IDL_IS_ROW_MODIFIED(intf_row, idl_seqno)) {

            /* get the port row for an interface */
            if ((port_row = portd_get_port_row(intf_row)) != NULL) {
                VLOG_DBG("Port found for interface %s", intf_row->name);

                /* For each vrf in all_vrfs, update the port list */
                HMAP_FOR_EACH (vrf, node, &all_vrfs) {
                    VLOG_DBG("vrf %s to search port %s\n", vrf->name,
                             port_row->name);
                    port = portd_port_lookup(vrf, port_row->name);
                    if (port) {
                        break;
                    }
                }

                if(!port) {
                    /* No port for this interface */
                    VLOG_DBG("No port found for interface %s", intf_row->name);
                }
            } else {
                VLOG_DBG("No port row for interface %s in ovsdb",
                         intf_row->name);
            }

            /*
             * Check if the user_config column changed.
             */
            if (OVSREC_IDL_IS_COLUMN_MODIFIED(ovsrec_interface_col_user_config,
                                              idl_seqno)) {
                /* Bring up kernel interface */
                cur_state = (char *)smap_get(&intf_row->user_config,
                                             INTERFACE_USER_CONFIG_MAP_ADMIN);
                if (cur_state != NULL &&
                    !strcmp(cur_state, OVSREC_INTERFACE_USER_CONFIG_ADMIN_UP)) {
                    portd_interface_up_down(intf_row->name,
                                            OVSREC_INTERFACE_USER_CONFIG_ADMIN_UP);
                } else {
                    portd_interface_up_down(intf_row->name,
                                            OVSREC_INTERFACE_USER_CONFIG_ADMIN_DOWN);
                }

                if(port) {
                    /* Set port hw_config:enable based on interface state */
                    /* Get interface state */
                    if (cur_state &&
                        (VTYSH_STR_EQ(cur_state,
                                      OVSREC_INTERFACE_USER_CONFIG_ADMIN_UP))) {
                        intf_admin = true;
                    }
                    /* Get port state */
                    if (port_row->admin &&
                        (VTYSH_STR_EQ(port_row->admin,
                                      PORT_CONFIG_ADMIN_DOWN))) {
                        port_admin = false;
                    }
                    /* The final state is the 'and operation' between
                     * the port admin and the interface admin */
                    port->hw_cfg_enable = (intf_admin && port_admin);
                    portd_set_hw_cfg(port, port_row);
                }
            }

            /*
             * Check if the hw_intf_config column changed.
             */
            if (OVSREC_IDL_IS_COLUMN_MODIFIED(ovsrec_interface_col_hw_intf_config,
                                              idl_seqno))
            {
                hw_intf_config_mtu = (char *)smap_get(&intf_row->hw_intf_config,
                                             INTERFACE_HW_INTF_CONFIG_MAP_MTU);

                if (hw_intf_config_mtu != NULL) {
                    portd_set_interface_mtu(intf_row->name,
                                            atoi(hw_intf_config_mtu));
                }
            }

            /*
             * Check if the admin_state column changed.
             * FIXME We should really be looking for kernel interface
             *       state using netlink instead of admin_state which
             *       is actually the physical hardware interface state
             */
            if (port && OVSREC_IDL_IS_COLUMN_MODIFIED(
                    ovsrec_interface_col_admin_state, idl_seqno)) {

                if ((intf_row->admin_state != NULL) &&
                    (strcmp(intf_row->admin_state,
                        PORT_INTERFACE_ADMIN_UP) == 0)) {

                    struct net_address *addr, *next_addr;
                    /*
                     * If the interface event is administratively forced to,
                     * 'OVSREC_INTERFACE_USER_CONFIG_ADMIN_UP' reprogram the
                     * primary port address and all the secondary port addresses
                     * on the port. This needs to be done for IPv6 since
                     * the IPv6 addresses get deleted from the kernel when
                     * the kernel interface is administratively forced
                     * 'OVSREC_INTERFACE_USER_CONFIG_ADMIN_UP'.
                     */
                    VLOG_DBG("Reprogramming the IPv6 address again since "
                            "the interface is forced up again");

                    if (port->ip6_address) {
                        nl_add_ip_address(RTM_NEWADDR, port->name,
                                          port->ip6_address, AF_INET6, false);
                    }

                    HMAP_FOR_EACH_SAFE (addr, next_addr, addr_node,
                                        &port->secondary_ip6addr) {
                        nl_add_ip_address(RTM_NEWADDR, port->name,
                                          addr->address, AF_INET6, true);
                    }
                }
            }
        }
    }
}

/* delete vlan from VLAN table in DB */
static void
portd_bridge_del_vlan(struct ovsrec_bridge *br, struct ovsrec_vlan *vlan)
{
    struct ovsrec_vlan **vlans;
    size_t i, n;

    VLOG_DBG("Deleting VLAN %d", (int)vlan->id);
    vlans = xmalloc(sizeof *br->vlans * br->n_vlans);
    for (i = n = 0; i < br->n_vlans; i++) {
        if (br->vlans[i] != vlan) {
            vlans[n++] = br->vlans[i];
        }
    }
    ovsrec_bridge_set_vlans(br, vlans, n);
    commit_txn = true;
    SAFE_FREE(vlans);
}

/**
 * Function: portd_del_internal_vlan
 * Param:
 *      interface_vid: ID of the internal VLAN that must be removed from default
 *      bridge row.
 * Description: Delete a VLAN from bridge table. Specifically, delete internal
 *              VLAN from default-bridge row.
 */
static void
portd_del_internal_vlan(int internal_vid)
{
    int i;
    struct ovsrec_vlan *vlan = NULL;
    const struct ovsrec_bridge *br_row = NULL;
    if (internal_vid == -1) {
        return;
    }

    OVSREC_BRIDGE_FOR_EACH (br_row, idl) {
        if (!strcmp(br_row->name, DEFAULT_BRIDGE_NAME)) {
            for (i = 0; i < br_row->n_vlans; i++) {
                if (internal_vid == br_row->vlans[i]->id) {
                    vlan = br_row->vlans[i];
                    portd_bridge_del_vlan((struct ovsrec_bridge *)br_row, vlan);
                }
            }
        }
    }
}

static bool
portd_check_vlan_interface(char *port_name)
{
    const struct ovsrec_port *port_row;
    bool interface_vlan_found;

    /*
     * Check if vlan is configured as by interface VLAN.
     */

    interface_vlan_found = false;
    OVSREC_PORT_FOR_EACH (port_row, idl) {
        if (!strncmp(port_row->name, port_name, strlen(port_name))) {
            interface_vlan_found = true;
        }
    }
    return interface_vlan_found;
}

/* FIXME - update port table status column with error if no VLAN allocated. */
static int
portd_alloc_internal_vlan(void)
{
    int i, j;
    const struct ovsrec_bridge *br_row = NULL;
    const struct ovsrec_system *sys = NULL;
    unsigned long *vlans_bmp;
    bool ascending;
    int vlan_allocated = -1;

    int min_internal_vlan, max_internal_vlan;
    const char *internal_vlan_policy;

    sys = ovsrec_system_first(idl);

    if (sys) {
        min_internal_vlan =
                smap_get_int(&sys->other_config,
                             SYSTEM_OTHER_CONFIG_MAP_MIN_INTERNAL_VLAN,
                             DFLT_SYSTEM_OTHER_CONFIG_MAP_MIN_INTERNAL_VLAN_ID);
        max_internal_vlan =
                smap_get_int(&sys->other_config,
                             SYSTEM_OTHER_CONFIG_MAP_MAX_INTERNAL_VLAN,
                             DFLT_SYSTEM_OTHER_CONFIG_MAP_MAX_INTERNAL_VLAN_ID);
        internal_vlan_policy =
                smap_get(&sys->other_config,
                         SYSTEM_OTHER_CONFIG_MAP_INTERNAL_VLAN_POLICY);
        if (!internal_vlan_policy) {
            internal_vlan_policy =
                SYSTEM_OTHER_CONFIG_MAP_INTERNAL_VLAN_POLICY_ASCENDING_DEFAULT;
        }
        VLOG_DBG("min_internal : %d, %d, %s",
                  min_internal_vlan, max_internal_vlan,
                  internal_vlan_policy);

        /* Check if internal VLAN policy is valid */
        if ((strcmp(
                internal_vlan_policy,
                SYSTEM_OTHER_CONFIG_MAP_INTERNAL_VLAN_POLICY_ASCENDING_DEFAULT) != 0) &&
            (strcmp(
                internal_vlan_policy,
                SYSTEM_OTHER_CONFIG_MAP_INTERNAL_VLAN_POLICY_DESCENDING) != 0)) {
            VLOG_ERR("Unknown internal vlan policy '%s'",
                      internal_vlan_policy);
            log_event("PORT_UNKNOWN_VLAN_POLICY",
                EV_KV("policy", "%s", internal_vlan_policy));
            return -1;
        }
    } else {
        VLOG_ERR("Unable to access system table in db.");
        return -1;
    }

    ascending = (strcmp(
                    internal_vlan_policy,
                    SYSTEM_OTHER_CONFIG_MAP_INTERNAL_VLAN_POLICY_ASCENDING_DEFAULT) == 0);

    OVSREC_BRIDGE_FOR_EACH (br_row, idl) {
        if (!strcmp(br_row->name, DEFAULT_BRIDGE_NAME)) {
            /* Set bitmap to identify available VLANs */
            vlans_bmp = bitmap_allocate(VLAN_BITMAP_SIZE);
            for (i = 0; i < br_row->n_vlans; i++) {
                struct ovsrec_vlan *vlan_row = br_row->vlans[i];
                bitmap_set1(vlans_bmp, vlan_row->id);
            }
            /* Loop through vlan bitmap and identify an available VLAN */
            for (j = ascending ? min_internal_vlan : max_internal_vlan;
                 ascending ? j <= max_internal_vlan : j >= min_internal_vlan;
                 ascending ? j++ : j--) {

                char port_name[8] = {0};
                char vlan_id[8] = {0};

                strncat(port_name, INTERFACE_TYPE_VLAN, strlen(INTERFACE_TYPE_VLAN));
                snprintf(vlan_id,5, "%d", j);
                strncat(port_name, vlan_id, strlen(vlan_id));
                if (portd_check_vlan_interface(port_name)) {
                    continue;
                }
                if (!bitmap_is_set(vlans_bmp,j)) {
                    VLOG_DBG("Allocated internal vlan (%d)", j);
                    vlan_allocated = j;
                    break;
                }
            }
            SAFE_FREE(vlans_bmp);
        }
    }
    return vlan_allocated;
}

/* add new vlan row into db */
static void
portd_bridge_insert_vlan(struct ovsrec_bridge *br, struct ovsrec_vlan *vlan)
{
    struct ovsrec_vlan **vlans;
    size_t i;

    vlans = xmalloc(sizeof *br->vlans * (br->n_vlans + 1));
    for (i = 0; i < br->n_vlans; i++) {
        vlans[i] = br->vlans[i];
    }
    vlans[br->n_vlans] = vlan;
    ovsrec_bridge_set_vlans(br, vlans, br->n_vlans + 1);
    commit_txn = true;
    SAFE_FREE(vlans);
}

/* create a new internal vlan row to be inserted into db */
static void
portd_create_vlan_row(int vid, struct ovsrec_port *port_row)
{
    char vlan_name[16];
    struct smap vlan_internal_smap;
    const struct ovsrec_bridge *br_row = NULL;
    struct ovsrec_vlan *vlan = NULL;

    vlan = ovsrec_vlan_insert(txn);
    snprintf(vlan_name, 16, "VLAN%d", vid);
    ovsrec_vlan_set_name(vlan, vlan_name);
    ovsrec_vlan_set_id(vlan, vid);
    ovsrec_vlan_set_admin(vlan, OVSREC_VLAN_ADMIN_UP);
    ovsrec_vlan_set_oper_state(vlan, OVSREC_VLAN_OPER_STATE_UP);
    ovsrec_vlan_set_oper_state_reason(vlan, OVSREC_VLAN_OPER_STATE_REASON_OK);

    /* update VLAN table "internal_usage" with the L3 port name */
    smap_init(&vlan_internal_smap);
    smap_add(&vlan_internal_smap, VLAN_INTERNAL_USAGE_L3PORT, port_row->name);
    ovsrec_vlan_set_internal_usage(vlan, &vlan_internal_smap);
    commit_txn = true;
    smap_destroy(&vlan_internal_smap);

    OVSREC_BRIDGE_FOR_EACH (br_row, idl) {
        if (!strcmp(br_row->name, DEFAULT_BRIDGE_NAME)) {
            VLOG_DBG("Creating VLAN row '%s'", vlan_name);
            portd_bridge_insert_vlan((struct ovsrec_bridge *)br_row, vlan);
        }
    }
}

/* FIXME - move internal_vlan functions to a separate file */
static void
portd_add_internal_vlan(struct port *port, struct ovsrec_port *port_row)
{
    int vid;
    int require_vlan;
    const struct ovsrec_subsystem *ovs_subsys;

    /* FIXME: handle multiple subsystems. */
    ovs_subsys = ovsrec_subsystem_first(idl);

    if (ovs_subsys) {
        require_vlan = smap_get_int(&ovs_subsys->other_info,
                                    "l3_port_requires_internal_vlan",
                                    0);
        VLOG_DBG("l3_port requires vlan : %d", require_vlan);
        if (require_vlan == 0) {
            return;
        }
    } else {
        VLOG_ERR("Unable to acces subsystem table in db.");
        return;
    }

    vid = portd_alloc_internal_vlan();
    if (vid == -1) {
        VLOG_ERR("Error allocating internal vlan for port '%s'", port_row->name);
        log_event("PORT_VLAN_ALLOCATION_ERROR",
            EV_KV("vlan", "%s", port_row->name));
        portd_set_status_error(port_row, PORT_STATUS_MAP_ERROR_NO_INTERNAL_VLAN);
        log_event("INTERNAL_VLAN_ALLOCATION_ERR",
                  EV_KV("port", "%s", port_row->name));
        return;
    }
    log_event("INTERNAL_VLAN_ALLOCATION", EV_KV("vid", "%d", vid),
              EV_KV("port", "%s", port_row->name));

    portd_create_vlan_row(vid, port_row);
    port->internal_vid = vid;

    portd_set_hw_cfg(port, port_row);

    return;
}

/* create port in cache */
static void
portd_port_create(struct vrf *vrf, struct ovsrec_port *port_row)
{
    struct port *port;

    port = xzalloc(sizeof *port);
    port->vrf = vrf;
    port->name = xstrdup(port_row->name);
    port->type = NULL; /* regular (non-intervlan) interface */
    port->cfg = port_row;
    port->internal_vid = -1;
    port->hw_cfg_enable = false;
    hmap_init(&port->secondary_ip4addr);
    hmap_init(&port->secondary_ip6addr);
    hmap_insert(&vrf->ports, &port->port_node, hash_string(port->name, 0));

    VLOG_DBG("port '%s' created", port->name);
    return;
}

/**
 * Add a new port to local cache or reconfigure existing port
 * if anything changed
 */
static void
portd_reconfig_ports(struct vrf *vrf, const struct shash *wanted_ports)
{
    struct shash_node *port_node;
    int vlan_id;
    bool port_admin = true;
    bool intf_admin = false;
    struct smap hw_cfg_smap;
    char *cur_state = NULL;
    char *proxy_arp_state = NULL;
    char *local_proxy_arp_state = NULL;

    SHASH_FOR_EACH (port_node, wanted_ports) {
        struct ovsrec_port *port_row = port_node->data;
        struct ovsrec_interface *intf_row = NULL;
        struct port *port = portd_port_lookup(vrf, port_row->name);
        if (!port) {
            VLOG_DBG("Creating new port %s vrf %s\n",port_row->name, vrf->name);
            portd_port_create(vrf, port_row);
            port = portd_port_lookup(vrf, port_row->name);

            if (vrf->cfg && strcmp(vrf->name, DEFAULT_VRF_NAME) &&
                            vrf_is_ready(idl, vrf->name)) {
                struct setns_info setns_local_info;
                memcpy(&setns_local_info.from_ns[0], SWITCH_NAMESPACE,  strlen(SWITCH_NAMESPACE) + 1);
                get_vrf_ns_from_table_id(idl, vrf->table_id, &setns_local_info.to_ns[0]);
                memcpy(&setns_local_info.intf_name[0], port_row->name, strlen(port_row->name) + 1);
                if (!nl_move_intf_to_vrf(&setns_local_info)) {
                    VLOG_ERR("Failed to move interface from %s to %s",
                              SWITCH_NAMESPACE, vrf->name);
                }
            }
            portd_config_src_routing(vrf, port_row->name, true);
            if (portd_interface_type_internal_check(port_row, port_row->name) &&
                portd_port_in_bridge_check(port_row->name, DEFAULT_BRIDGE_NAME) &&
                portd_port_in_vrf_check(port_row->name, DEFAULT_VRF_NAME)) {

                portd_add_vlan_interface(DEFAULT_BRIDGE_NAME, port_row->name,
                                         ops_port_get_tag(port->cfg));
                portd_interface_up_down(port_row->name,
                                        port_row->admin ? port_row->admin: "down");

                port->type = xstrdup(OVSREC_INTERFACE_TYPE_INTERNAL);
            } else if (portd_interface_type_subinterface_check(port_row,
                    port_row->name)) {
                portd_reconfigure_subinterface(port_row);
                port->type = xstrdup(OVSREC_INTERFACE_TYPE_VLANSUBINT);
                subintf_count++;
                log_event("SUBINTERFACE_CREATE", EV_KV("interface", "%s", port_row->name));
            } else if (portd_interface_type_loopback_check(port_row,
                       port_row->name)) {
                portd_reconfig_ns_loopback(port, port_row,
                                           (!strncmp(vrf->name, DEFAULT_VRF_NAME,
                                           strlen(DEFAULT_VRF_NAME))));
                port->type = xstrdup(OVSREC_INTERFACE_TYPE_LOOPBACK);
                lpbk_count++;
                log_event("LOOPBACK_CREATE", EV_KV("interface", "%s", port_row->name));
            } else {
                /* Only assign internal VLAN if not already present. */
                smap_clone(&hw_cfg_smap, &port_row->hw_config);
                vlan_id = smap_get_int(&hw_cfg_smap,
                                       PORT_HW_CONFIG_MAP_INTERNAL_VLAN_ID, 0);
                if(vlan_id == 0) {
                    portd_add_internal_vlan(port, port_row);
                } else {
                    port->internal_vid = vlan_id;
                }
                smap_destroy(&hw_cfg_smap);
                if ((intf_row = portd_get_matching_interface_row(port_row)) != NULL) {
                    /* Its a VLAN or L3 interface */
                    VLOG_DBG("set up state for L3 and vlan interface\n");
                    /* Get interface state */
                    cur_state = (char *)smap_get(&intf_row->user_config,
                                                 INTERFACE_USER_CONFIG_MAP_ADMIN);
                    if (cur_state &&
                        (VTYSH_STR_EQ(cur_state,
                                      OVSREC_INTERFACE_USER_CONFIG_ADMIN_UP)))
                    {
                         intf_admin = true;
                    }
                    port->hw_cfg_enable = (intf_admin && port_admin);
                } else {
                    /* its a LAG */
                    /* set hw_config same as port admin_status */
                    VLOG_DBG("set up in LAG interface\n");
                    if ((port_row->admin == NULL) ||
                        (strcmp(port_row->admin, "up") == 0)) {
                        port->hw_cfg_enable = true;
                    } else {
                        port->hw_cfg_enable = false;
                    }
                }
                portd_set_hw_cfg(port, port_row);
            }

            portd_reconfig_ipaddr(port, port_row);
            VLOG_DBG("Port has IP: %s vrf %s\n", port_row->ip4_address,
                      vrf->name);

        } else if (port) {
            if (OVSREC_IDL_IS_ROW_MODIFIED(port_row, idl_seqno)) {
                if ((NULL != port->type) &&
                    (strcmp(port->type,
                     OVSREC_INTERFACE_TYPE_LOOPBACK) == 0)) {
                    portd_reconfig_ns_loopback(port, port_row, false);
                    portd_register_event_log(port_row, port);
                    continue;
                }
                portd_reconfig_ipaddr(port, port_row);
                portd_register_event_log(port_row, port);
                portd_port_admin_state_reconfigure(port, port_row);
                portd_update_kernel_intf_up_down(port_row->name);
                /* Port table row modified */
                VLOG_DBG("Port modified IP: %s vrf %s\n", port_row->ip4_address,
                        vrf->name);

                if (OVSREC_IDL_IS_COLUMN_MODIFIED(ovsrec_port_col_other_config,
                                                  idl_seqno)) {
                    /* Check if proxy arp state has changed */
                    proxy_arp_state = (char *)smap_get(
                                      &port_row->other_config,
                                      PORT_OTHER_CONFIG_MAP_PROXY_ARP_ENABLED);

                    if (proxy_arp_state && (VTYSH_STR_EQ(proxy_arp_state,
                        PORT_OTHER_CONFIG_MAP_PROXY_ARP_ENABLED_TRUE))) {
                        if (!port->proxy_arp_enabled) {
                            portd_config_proxy_arp(port, port_row->name,
                                                   PORTD_ENABLE_PROXY_ARP);
                        }
                    } else {
                        if (port->proxy_arp_enabled) {
                            portd_config_proxy_arp(port, port_row->name,
                                                   PORTD_DISABLE_PROXY_ARP);
                        }
                    }
                    /* Check if  local proxy arp state has changed */
                    local_proxy_arp_state = (char *)smap_get(
                                      &port_row->other_config,
                                      PORT_OTHER_CONFIG_MAP_LOCAL_PROXY_ARP_ENABLED);

                    if (local_proxy_arp_state && (VTYSH_STR_EQ(local_proxy_arp_state,
                        PORT_OTHER_CONFIG_MAP_LOCAL_PROXY_ARP_ENABLED_TRUE))) {
                        if (!port->local_proxy_arp_enabled) {
                            portd_config_local_proxy_arp(port, port_row->name,
                                                   PORTD_ENABLE_LOCAL_PROXY_ARP);
                        }
                    } else {
                        if (port->local_proxy_arp_enabled) {
                            portd_config_local_proxy_arp(port, port_row->name,
                                                   PORTD_DISABLE_LOCAL_PROXY_ARP);
                        }
                    }
                }
            }
        } else {
            VLOG_DBG("[%s:%d]: port %s exists, but no change in seqno",
                       __FUNCTION__, __LINE__, port_row->name);
        }
    }

    SHASH_FOR_EACH (port_node, wanted_ports) {
        struct ovsrec_port *port_row = port_node->data;
        struct port *port = portd_port_lookup(vrf, port_row->name);
        struct ovsrec_interface *intf_row = NULL;
        intf_row = portd_get_matching_interface_row(port_row);

        if ((port) &&
            (intf_row) &&
            ((OVSREC_IDL_IS_ROW_MODIFIED(port_row, idl_seqno)) ||
            (OVSREC_IDL_IS_ROW_MODIFIED(intf_row, idl_seqno))))
        {
            if((NULL != port->type) &&
                    (strcmp(port->type,
                            OVSREC_INTERFACE_TYPE_VLANSUBINT) == 0)) {
                char str[512] = {0};
                portd_reconfigure_subinterface(port_row);

                if (portd_if_nametoindex(vrf, port_row->name))
                {
                   if (port_row->ip4_address != NULL)
                   {
                       nl_add_ip_address(RTM_NEWADDR, port_row->name,
                                 port_row->ip4_address, AF_INET, false);
                        log_event("SUBINTERFACE_IP_UPDATE", EV_KV("interface",
                                  "%s", port_row->name),
                                  EV_KV("value", "%s", port_row->ip4_address));
                   }
                   if (port_row->ip6_address != NULL)
                   {
                        snprintf(str, 512, "/sbin/ip netns exec swns "
                               "/sbin/ip -6 address add %s dev %s",
                               port_row->ip6_address, port_row->name);
                        if (system(str) != 0)
                        {
                            VLOG_ERR("Failed to add subinterface. cmd=%s, rc=%s",
                                        str, strerror(errno));
                        }
                   }
                }
            }
        }
    }

    return;
}

/* collect the ports from the current config in db */
static void
portd_collect_wanted_ports(struct vrf *vrf,
                             struct shash *wanted_ports)
{
    size_t i;

    shash_init(wanted_ports);

    for (i = 0; i < vrf->cfg->n_ports; i++) {
        const char *name = vrf->cfg->ports[i]->name;
        shash_add_once(wanted_ports, name, vrf->cfg->ports[i]);
    }
}

/* delete internal port cache */
static void
portd_port_destroy(struct port *port)
{
    if (port) {
        struct vrf *vrf = port->vrf;
        struct net_address *addr, *next_addr;

        VLOG_DBG("port '%s' destroy", port->name);
        if (port->ip4_address) {
            SAFE_FREE(port->ip4_address);
        }
        if (port->ip6_address) {
            SAFE_FREE(port->ip6_address);
        }

        HMAP_FOR_EACH_SAFE (addr, next_addr, addr_node,
                            &port->secondary_ip4addr) {
            SAFE_FREE(addr->address);
            SAFE_FREE(addr);
        }
        hmap_destroy(&port->secondary_ip4addr);

        HMAP_FOR_EACH_SAFE (addr, next_addr, addr_node,
                            &port->secondary_ip6addr) {
            SAFE_FREE(addr->address);
            SAFE_FREE(addr);
        }
        hmap_destroy(&port->secondary_ip6addr);
        hmap_remove(&vrf->ports, &port->port_node);
        SAFE_FREE(port->name);
        SAFE_FREE(port);
    }
}

/* remove the ports that are in local cache and not in db */
static void
portd_del_ports(struct vrf *vrf, const struct shash *wanted_ports)
{
    struct port *port, *next;

    HMAP_FOR_EACH_SAFE (port, next, port_node, &vrf->ports) {
        port->cfg = shash_find_data(wanted_ports, port->name);
        const struct ovsrec_port *row = shash_find_data(&all_ports,
                                                        port->name);

        if (!port->cfg) {

            VLOG_DBG("Processing port delete port: %s type: %s",
                     port->name, port->type ? "inter-vlan" : "L3");
            if (vrf->cfg && strcmp(vrf->name, DEFAULT_VRF_NAME)) {
                portd_config_src_routing(vrf, port->name, false);
                struct setns_info setns_local_info;
                get_vrf_ns_from_table_id(idl, vrf->table_id, &setns_local_info.from_ns[0]);
                memcpy(&setns_local_info.to_ns[0], SWITCH_NAMESPACE,  strlen(SWITCH_NAMESPACE)+1);
                memcpy(&setns_local_info.intf_name[0], port->name,  strlen(port->name) + 1);
                if (!nl_move_intf_to_vrf(&setns_local_info)) {
                    VLOG_ERR("Failed to move interface from %s to %s",
                               vrf->name, SWITCH_NAMESPACE);
                }
            }
            /* Send delete interface to kernel */
            if (port->type &&
                (strcmp(port->type, OVSREC_INTERFACE_TYPE_INTERNAL) == 0)) {
                portd_del_vlan_interface(port->name);
            }
            else if(port->type &&
                    (strcmp(port->type, OVSREC_INTERFACE_TYPE_VLANSUBINT) == 0)) {
                /* The port here is moved to default VRF if it was part of non-default VRF
                 * but the port structure is not updated yet. Hence passing the default VRF
                 * structure always from here */
                portd_del_interface_netlink(port->name, portd_vrf_lookup(DEFAULT_VRF_NAME));
                subintf_count--;
                log_event("SUBINTERFACE_DELETE", EV_KV("interface",
                          "%s", port->name));
            }
            else if(port->type &&
                    (strcmp(port->type, OVSREC_INTERFACE_TYPE_LOOPBACK) == 0)) {
                if (!row)
                {
                    /* The port here is moved to default VRF if it was part of non-default VRF
                     * but the port structure is not updated yet. Hence passing the default VRF
                     * structure always from here */
                    portd_del_interface_netlink(port->name, portd_vrf_lookup(DEFAULT_VRF_NAME));
                    lpbk_count--;
                    log_event("LOOPBACK_DELETE", EV_KV("interface",
                              "%s", port->name));
                }
            }

            if (port->proxy_arp_enabled) {
                portd_config_proxy_arp(port, port->name,
                                       PORTD_DISABLE_PROXY_ARP);
            }

            if (port->local_proxy_arp_enabled) {
                portd_config_local_proxy_arp(port, port->name,
                                       PORTD_DISABLE_LOCAL_PROXY_ARP);
            }

            /* Port not present in the wanted_ports list. Destroy */
            portd_del_internal_vlan(port->internal_vid);
            portd_del_ipaddr(port);
            portd_port_destroy(port);
        }
    }
}

/* Delete an old port found in the internal port cache */
static void
portd_del_old_port(struct shash_node *sh_node)
{
    if (sh_node) {
        struct port_lag_data *portp = sh_node->data;
        struct shash_node *node, *next;
        if (!portp)
        {
            VLOG_ERR ("No port data found for %s",sh_node->name);
            return;
        }
        SHASH_FOR_EACH_SAFE(node, next, &portp->eligible_member_ifs) {
            /* Since we have got the shash_node. Why do we do find again
               node->data won't have same idp? */
            struct iface_data *idp =
                shash_find_data(&all_interfaces, node->name);
            if (idp) {
                VLOG_DBG("Removing interface %s from port %s hash map",
                         idp->name, portp->name);

                shash_delete(&portp->eligible_member_ifs, node);
                idp->port_datap = NULL;
            }
        }
        /* When the eligible_member_ifs is NULL, say for parent interface,
           there will be case where the idp->port_datap pointing to a location
           which is freed and the location may not necessarily be empty.
           So we need to NULLify the idp->port_datap for all those interface
           data which had the deleted port */
        SHASH_FOR_EACH_SAFE(node, next, &all_interfaces)
        {
            struct iface_data *idp = node->data;
            if (idp && idp->port_datap &&
               (idp->port_datap == portp))
            {
                VLOG_INFO ("IDP PORT DATA NULLIFIED FOR : %s",idp->name);
                idp->port_datap = NULL;
            }
        }
        SAFE_FREE(portp->name);
        SAFE_FREE(portp);
        shash_delete(&all_ports, sh_node);
    }
} /* portd_del_old_port */

/* Add a new port found in the internal port cache */
static void
portd_add_new_port(const struct ovsrec_port *port_row)
{
    struct port_lag_data *portp = NULL;
    size_t i;
    struct ovsrec_interface *intf;
    struct iface_data *idp;

    VLOG_DBG("Port %s being added!", port_row->name);

    /* Allocate structure to save state information for this interface. */
    portp = xzalloc(sizeof *portp);

    if (!shash_add_once(&all_ports, port_row->name, portp)) {
        VLOG_WARN("Port %s specified twice", port_row->name);
        SAFE_FREE(portp);
    } else {
        portp->cfg = port_row;
        portp->name = xstrdup(port_row->name);
        shash_init(&portp->eligible_member_ifs);
        shash_init(&portp->bonding_ifs);

        for (i = 0; i < port_row->n_interfaces; i++) {
            intf = port_row->interfaces[i];
            idp = shash_find_data(&all_interfaces, intf->name);
            if (!idp) {
                VLOG_ERR("Error adding interface to new port %s. "
                         "Interface %s not found.", portp->name, intf->name);
            }
            else {
                VLOG_DBG("Storing interface %s in port %s hash map",
                           intf->name, portp->name);
                shash_add(&portp->eligible_member_ifs, intf->name, (void *)idp);
                idp->port_datap = portp;
            }
        }
        VLOG_DBG("Created local data for Port %s", port_row->name);
    }
} /* portd_add_new_port */

/**
 * Handles Port related configuration changes for a given port table entry.
 *
 * @param row pointer to port row in IDL.
 * @param portp pointer to daemon's internal port data struct.
 *
 * @return
 */

static void portd_update_bond_slaves(struct port_lag_data *portp)
{
    struct shash_node *node;
    struct iface_data *idp = NULL;
    const struct ovsrec_interface *ifrow = NULL;
    struct shash_node *next;
    bool set_interface_up;
    const char *state_value;

    /* Find a deleted interface first */
    SHASH_FOR_EACH_SAFE(node, next, &portp->bonding_ifs) {
        VLOG_DBG("bond: interface %s to be deleted", node->name);
        if(!shash_find(&(portp->eligible_member_ifs), node->name)) {
            if(remove_slave_from_bond(portp->name, node->name)) {
                VLOG_DBG("bond: Interface %s removed from bond", node->name);
            }
            shash_delete(&portp->bonding_ifs, node);
        }else{

           VLOG_DBG("bond: interface %s in not in eligibles", node->name);
        }
    }

    /* Find added interfaces */
    SHASH_FOR_EACH(node, &portp->eligible_member_ifs) {
        VLOG_DBG("bond: interface %s to be added", node->name);
        if(!shash_find(&(portp-> bonding_ifs), node->name)) {
            set_interface_up = false;
            idp = shash_find_data(&all_interfaces, node->name);
            ifrow = idp->cfg;

            state_value = smap_get(&ifrow->user_config,
                                   INTERFACE_USER_CONFIG_MAP_ADMIN);

            if(state_value != NULL && !strcmp(state_value,
                                              PORT_INTERFACE_ADMIN_UP)) {
                portd_interface_up_down(node->name,
                                        PORT_INTERFACE_ADMIN_DOWN);
                set_interface_up = true;
            }

            shash_add(&portp->bonding_ifs, node->name, (void *)idp);
            if(add_slave_to_bond(portp->name, node->name)) {
                VLOG_DBG("Interface %s added to bond", node->name);
            }

            if(set_interface_up) {
                portd_interface_up_down(node->name, PORT_INTERFACE_ADMIN_UP);
            }

            VLOG_DBG("bond: interface %s added", node->name);
        }
        else{
           VLOG_DBG("bond: interface %s is in bondings_ifs", node->name);
        }
    }
} /* portd_update_bond_slaves */

/**
 * Check if an interfaces is eligible by checking the map hw_bond_config and
 * the key rx_enable and tx_enable.
 *
 * @param idp pointer to interface data being select for eligibility.
 *
 * @return
 */

static void
portd_update_interface_lag_eligibility(struct iface_data *idp)
{

    if (smap_get_bool(&idp->cfg->hw_bond_config,
                      INTERFACE_HW_BOND_CONFIG_MAP_RX_ENABLED, false) &&
        smap_get_bool(&idp->cfg->hw_bond_config,
                      INTERFACE_HW_BOND_CONFIG_MAP_TX_ENABLED, false)) {
       VLOG_DBG("bond: interface %s is eligible", idp->name);

        shash_add_once(&idp->port_datap->eligible_member_ifs, idp->name,
                       (void *)idp);

    } else {
       VLOG_DBG("bond: interface %s is not eligible", idp->name);
        shash_find_and_delete(&idp->port_datap->eligible_member_ifs,
                              idp->name);
    }
} /* portd_update_interface_lag_eligibility */

/**
 * Updates internal caches with new interfaces or delete old interfaces
 * also, updates bond slaves in order to keep them sycronized with LAG
 * interfaces.
 *
 * @param row pointer to port row in IDL
 * @param portp pointer to daemon's internal port lag data
 *
 * @return
 */
static void
portd_handle_port_config(const struct ovsrec_port *row,
                         struct port_lag_data *portp)
{
    struct ovsrec_interface *intf;
    struct shash sh_idl_port_intfs;
    struct shash_node *node, *next;
    size_t i;

    VLOG_DBG("%s: port %s, n_interfaces=%d",
             __FUNCTION__, row->name, (int)row->n_interfaces);

    /* Build a new map for this port's interfaces in idl. */
    shash_init(&sh_idl_port_intfs);
    for (i = 0; i < row->n_interfaces; i++) {
        intf = row->interfaces[i];
        if (!shash_add_once(&sh_idl_port_intfs, intf->name, intf)) {
            VLOG_WARN("interface %s specified twice", intf->name);
        }
    }

    /* Process deleted interfaces first. */
    SHASH_FOR_EACH_SAFE(node, next, &portp->eligible_member_ifs) {
        struct ovsrec_interface *ifrow =
            shash_find_data(&sh_idl_port_intfs, node->name);
        if (!ifrow) {
            struct iface_data *idp =
                shash_find_data(&all_interfaces, node->name);
            if (idp) {
                VLOG_DBG("bond: Found a deleted interface %s", node->name);
                shash_delete(&portp->eligible_member_ifs, node);
                idp->port_datap = NULL;
            }
        }
    }

    /* Look for newly added interfaces. */
    SHASH_FOR_EACH(node, &sh_idl_port_intfs) {
        struct ovsrec_interface *ifrow =
            shash_find_data(&portp->eligible_member_ifs, node->name);
        if (!ifrow) {
            VLOG_DBG("bond: Found an added interface %s in port %s", node->name,
                     portp->name);
            struct iface_data *idp =
                shash_find_data(&all_interfaces, node->name);
            if (idp) {
                shash_add(&portp->eligible_member_ifs, node->name, (void *)idp);
                idp->port_datap = portp;
            }
            else {
                VLOG_ERR("bond: Error adding interface to port %s. "
                         "Interface %s not found.",
                         portp->name, node->name);
            }
        }
    }

    /* Update LAG member eligibility for configured member interfaces. */
    SHASH_FOR_EACH_SAFE(node, next, &portp->eligible_member_ifs) {
        struct iface_data *idp = shash_find_data(&all_interfaces, node->name);
        if (idp) {
            portd_update_interface_lag_eligibility(idp);
        }
    }

    if(!strncmp(portp->name, LAG_NAME_SUFFIX, LAG_NAME_SUFFIX_LENGTH)) {
        portd_update_bond_slaves(portp);
    }

    /* Destroy the shash of the IDL interfaces. */
    shash_destroy(&sh_idl_port_intfs);
} /* portd_handle_port_config */

/**
 * Handles database reconfigurations in ports
 *
 */

static void
portd_add_del_ports(void)
{
    struct vrf *vrf;
    struct shash sh_idl_ports;
    const struct ovsrec_port *row;
    struct shash_node *sh_node, *sh_next;

    /* Collect all the ports in the DB. */
    shash_init(&sh_idl_ports);
    OVSREC_PORT_FOR_EACH(row, idl) {
       if (!shash_add_once(&sh_idl_ports, row->name, row)) {
           VLOG_WARN("port %s specified twice", row->name);
       }
    }

    /* Delete old ports. */
    SHASH_FOR_EACH_SAFE(sh_node, sh_next, &all_ports) {
        /* Even though it will not effect anything but the below find
           will return ovsrec_port row not port_lag_data */
        struct port_lag_data *portp = shash_find_data(&sh_idl_ports, sh_node->name);
        if (!portp) {
            VLOG_DBG("bond:Found a deleted port %s", sh_node->name);

            /* Check if port's name begins with "lag" to delete Linux bond */
            if(!strncmp(sh_node->name, LAG_NAME_SUFFIX,
                        LAG_NAME_SUFFIX_LENGTH)) {
                if(delete_linux_bond(sh_node->name)) {
                    VLOG_DBG("bond:Deleted bond %s, ", sh_node->name);
                }
            }
            portd_del_old_port(sh_node);
        }
    }

    /* Add new ports. */
    SHASH_FOR_EACH(sh_node, &sh_idl_ports) {
        struct port_lag_data *portp = shash_find_data(&all_ports,
                                                      sh_node->name);
        if (!portp) {
            VLOG_DBG("bond:Found an added port %s", sh_node->name);

            /* Check if port's name begins with "lag" to create Linux bond */
            if(!strncmp(sh_node->name, LAG_NAME_SUFFIX,
                        LAG_NAME_SUFFIX_LENGTH)) {
                if(create_linux_bond(sh_node->name)) {
                    portd_interface_up_down(sh_node->name, "up");
                }
            }
            portd_add_new_port(sh_node->data);
        }
    }

    /* Check for changes in the port row entries. */
    SHASH_FOR_EACH(sh_node, &all_ports) {
        const struct ovsrec_port *row = shash_find_data(&sh_idl_ports,
                                                       sh_node->name);
        /* Check for changes to row. */
        if (OVSREC_IDL_IS_ROW_INSERTED(row, idl_seqno) ||
            OVSREC_IDL_IS_ROW_MODIFIED(row, idl_seqno)) {
            struct port_lag_data *portp = sh_node->data;
            /* Handle Port config update. */
            portd_handle_port_config(row, portp);
        }
    }

    /* Destroy the shash of the IDL ports. */
    shash_destroy(&sh_idl_ports);

    /* For each vrf in all_vrfs, update the port list */
    HMAP_FOR_EACH (vrf, node, &all_vrfs) {
        VLOG_DBG("in vrf %s to delete ports\n",vrf->name);
        portd_collect_wanted_ports(vrf, &vrf->wanted_ports);
        portd_del_ports(vrf, &vrf->wanted_ports);
    }
    /* For each vrfs' port list, configure them */
    HMAP_FOR_EACH (vrf, node, &all_vrfs) {
        VLOG_DBG("in vrf %s to reconfigure ports\n",vrf->name);
        portd_reconfig_ports(vrf, &vrf->wanted_ports);
        shash_destroy(&vrf->wanted_ports);
    }
}

/**
 * One time request to get a dump of all the interfaces from the kernel
 * This is done during init, or daemon restart to keep the interface
 * state in sync with the OVSDB
 */
static void
portd_intf_config_on_init (struct shash *kernel_port_list)
{
    struct rtattr *rta;
    struct {
        struct nlmsghdr hdr;
        struct rtgenmsg gen;
    } req;

    memset (&req, 0, sizeof(req));

    req.hdr.nlmsg_len = NLMSG_LENGTH(sizeof(struct rtgenmsg));
    req.hdr.nlmsg_flags = NLM_F_REQUEST | NLM_F_DUMP;
    req.hdr.nlmsg_type = RTM_GETLINK;

    req.gen.rtgen_family = AF_PACKET;

    rta = (struct rtattr *)(((char *)&req) + NLMSG_ALIGN(req.hdr.nlmsg_len));
    rta->rta_len = RTA_LENGTH(4);

    if (send(init_sock, &req, req.hdr.nlmsg_len, 0) == -1) {
        VLOG_ERR("Netlink failed to send message for link dump");
        return;
    }
    /* Process the response from kernel */
    VLOG_DBG("Interfaces dump request sent on init");

    nl_msg_process(kernel_port_list, init_sock, true);
}

/* This function checks if the kernel has all the interfaces already
 * created in sync with the db.
 * This is function is created on init.
 * return : number of interfaces yet to be created in the kernel
 */
static int
portd_kernel_if_sync_check_on_init (void)
{
    struct shash kernel_port_list;
    const struct ovsrec_interface *intf_row;
    struct kernel_port *kernel_port;
    struct shash_node *node, *next;
    unsigned int wait_for_kernel_if_sync;

    shash_init (&kernel_port_list);

    portd_intf_config_on_init (&kernel_port_list);

    wait_for_kernel_if_sync = 0;

    OVSREC_INTERFACE_FOR_EACH (intf_row, idl) {
        if (!(strncmp(intf_row->type, OVSREC_INTERFACE_TYPE_SYSTEM,
                     strlen(OVSREC_INTERFACE_TYPE_SYSTEM))) &&
            !shash_find_data(&kernel_port_list, intf_row->name)) {
            wait_for_kernel_if_sync++;
        }
    }

    SHASH_FOR_EACH_SAFE (node, next, &kernel_port_list) {
        kernel_port = node->data;
        hmap_destroy(&kernel_port->ip4addr);
        hmap_destroy(&kernel_port->ip6addr);
        SAFE_FREE(kernel_port->name);
        SAFE_FREE(kernel_port);
    }
    shash_destroy(&kernel_port_list);

    VLOG_DBG ("%u interfaces are yet be created in the kernel", wait_for_kernel_if_sync);
    return wait_for_kernel_if_sync;
}

/**
 * This function will delete VLANs which no longer point to L3 ports.
 * There are two cases:
 * 1. The daemon crashed and an L3 interface became L2. The internal VLAN which
 *    was previously pointing to the L3 interface needs to be deleted.
 * 2. The daemon crashed and an interface went from L3 to L2 and back to L3.
 *    A new internal VLAN would be assigned as it is considered
 *    a new L3 interface. The previous internal VLAN needs to be removed.
 */
static void
portd_vlan_config_on_init(void)
{
    const struct ovsrec_vlan *int_vlan_row;
    struct smap vlan_internal_smap, hw_cfg_smap;
    struct ovsrec_port *port_row;
    int vlan_id;

    OVSREC_VLAN_FOR_EACH(int_vlan_row, idl) {
        smap_clone(&vlan_internal_smap, &int_vlan_row->internal_usage);
        /* Check to see if VLAN is of type 'internal' */
        if (!smap_is_empty(&vlan_internal_smap)) {
            const char *port_name = smap_get(&vlan_internal_smap,
                    VLAN_INTERNAL_USAGE_L3PORT);
            port_row = portd_port_db_lookup(port_name);
            smap_clone(&hw_cfg_smap, &port_row->hw_config);
            vlan_id = smap_get_int(&hw_cfg_smap,
                    PORT_HW_CONFIG_MAP_INTERNAL_VLAN_ID, 0);
            /* Checks for the following cases:
             * 1. Port has no internal VLAN id
             * 2. Port has a VLAN id which is different */
            if (vlan_id == 0 || int_vlan_row->id != vlan_id) {
                VLOG_DBG("Deleting the internal VLAN : %"PRId64, int_vlan_row->id);
                portd_del_internal_vlan(int_vlan_row->id);
            }
            smap_destroy(&hw_cfg_smap);
        }
        smap_destroy(&vlan_internal_smap);
    }
}

/* delete vrf from cache */
static void
portd_vrf_del(struct vrf *vrf)
{
    if (vrf) {
        /* Delete all the associated ports before destroying vrf */
        struct port *port, *next_port;

        VLOG_DBG("Deleting vrf '%s'",vrf->name);

        HMAP_FOR_EACH_SAFE (port, next_port, port_node, &vrf->ports) {
            portd_del_internal_vlan(port->internal_vid);
            portd_del_ipaddr(port);
            portd_port_destroy(port);
        }
        hmap_remove(&all_vrfs, &vrf->node);
        hmap_destroy(&vrf->ports);
        close(vrf->nl_sock);
        SAFE_FREE(vrf->name);
        SAFE_FREE(vrf);
    }
}
static void
portd_vrf_netlink_socket_open(struct vrf *vrf_in)
{
     char buff[UUID_LEN+1] = {0};

     if (vrf_in->nl_sock > 0)
     {
        return;
     }
     get_vrf_ns_from_table_id(idl, vrf_in->table_id, buff);
     portd_netlink_socket_open(buff, &vrf_in->nl_sock, false);

     return;
}
/* add vrf into cache */
static void
portd_vrf_add(const struct ovsrec_vrf *vrf_row)
{
    struct vrf *vrf;

    ovs_assert(!portd_vrf_lookup(vrf_row->name));
    vrf = xzalloc(sizeof *vrf);

    vrf->name = xstrdup(vrf_row->name);
    vrf->cfg = vrf_row;
    vrf->table_id = *vrf_row->table_id;

    if (strcmp(vrf->name, DEFAULT_VRF_NAME) == 0) {
        vrf->nl_sock = nl_sock;
    }
    else {
        /* in portd restart case the vrf would be ready to open socket */
         portd_vrf_netlink_socket_open(vrf);
    }

    portd_config_iprouting(vrf->name, PORTD_ENABLE_ROUTING);
    hmap_init(&vrf->ports);
    hmap_insert(&all_vrfs, &vrf->node, hash_string(vrf->name, 0));

    VLOG_DBG("Added vrf '%s'",vrf_row->name);
}

static void
portd_add_del_vrf(void)
{
    struct vrf *vrf, *next;
    struct shash new_vrfs;
    const struct ovsrec_vrf *vrf_row = NULL;

    /* Collect new vrfs' names and types. */
    shash_init(&new_vrfs);
    OVSREC_VRF_FOR_EACH (vrf_row, idl) {
        shash_add_once(&new_vrfs, vrf_row->name, vrf_row);
    }

    /* Delete the vrfs' that are deleted from the db */
    HMAP_FOR_EACH_SAFE (vrf, next, node, &all_vrfs) {
        vrf->cfg = shash_find_data(&new_vrfs, vrf->name);
        if (!vrf->cfg) {
            portd_vrf_del(vrf);
        }
    }

    /* Add new vrfs. */
    OVSREC_VRF_FOR_EACH (vrf_row, idl) {
        struct vrf *vrf = portd_vrf_lookup(vrf_row->name);
        if (!vrf) {
            if (vrf_is_ready(idl, vrf_row->name)) {
                portd_vrf_add(vrf_row);
            }
        }
    }

    shash_destroy(&new_vrfs);
}

/* Checks to see if:
 * vrf has been added/deleted.
 * port has been added/deleted from a vrf.
 * port has been modified (IP address(es)).
 * interface has been created in the kernel.
 */
static void
portd_reconfigure(void)
{
    unsigned int new_idl_seqno = ovsdb_idl_get_seqno(idl);

    VLOG_DBG("Received a OVSDB change notification "
             "with current idl as %u and new idl as %u\n",
             idl_seqno, new_idl_seqno);

    if (new_idl_seqno == idl_seqno){
        return;
    }

    portd_add_del_vrf();

    /* In case the daemon restarts, ensure:
     * 1. Unused internal VLANs are deleted.
     * 2. IP addresses between DB and kernel are in sync.
     * 3. Interfaces link state (up/down) are in sync with DB.
     * 4. Intervlan interfaces on the kernel are in sync with DB.
     */
    if (portd_config_on_init) {
        /* Open an init sock to process reconfiguration */
        portd_netlink_socket_open(DEFAULT_VRF_NAME, &init_sock, true);
        if (portd_kernel_if_sync_check_on_init()) {
            VLOG_DBG ("kernel if NOT in sync - returning!!");
            sleep (1);
            return;
        }
        portd_vlan_config_on_init();
        portd_intf_config_on_init(NULL);
        portd_ipaddr_config_on_init();
    }

    update_interface_cache();

    portd_add_del_ports();

    /* IP addresses on kernel and DB are already in sync on init.
       Skipping this function on init */
    if (!portd_config_on_init) {
        /*
         * Read any OVSDB interface changes and
         * apply configurations
         */
        portd_handle_interface_config_mods();
    }

    if (portd_config_on_init) {
        portd_config_on_init = false;
        VLOG_DBG ("restting portd_config_on_init to 0");
        /* Close the init socket as it is not needed anymore */
        close(init_sock);
        init_sock = -1;
    }

    /* Determine the new 'forwarding state' for each port */
    portd_arbiter_run();

    /* After all changes are done, update the seqno. */
    idl_seqno = new_idl_seqno;
    return;
}

static void
portd_service_netlink_messages (void)
{
    struct vrf *vrf;
    if (!portd_config_on_init) {
        /*
         * Get kernel notifications about interface creations
         * and update the kernel interface with IFF_UP/~IFF_UP
         * as per DB configurations
         */
        /* For each vrfs netlink socket, process them */
        HMAP_FOR_EACH (vrf, node, &all_vrfs) {
            if (vrf->nl_sock > 0) {
                nl_msg_process(NULL, vrf->nl_sock, false);
            }
        }
    }
}

static void
portd_run(void)
{
    ovsdb_idl_run(idl);

    if (ovsdb_idl_is_lock_contended(idl)) {
        static struct vlog_rate_limit rl = VLOG_RATE_LIMIT_INIT(1, 1);

        VLOG_ERR_RL(&rl, "another ops-portd process is running, "
                    "disabling this process until it goes away");
        return;
    } else if (!ovsdb_idl_has_lock(idl)) {
        return;
    }

    portd_chk_for_system_configured();
    if (!system_configured) {
        return;
    }

    commit_txn = false; /* if db was modified, this flag gets set */
    txn = ovsdb_idl_txn_create(idl);
    portd_reconfigure();
    portd_service_netlink_messages();
    if (commit_txn) {
        ovsdb_idl_txn_commit_block(txn);
    }
    ovsdb_idl_txn_destroy(txn);
    VLOG_INFO_ONCE("%s (ops-portd) %s", program_name, VERSION);

    /* FIXME - verify db write was successful, else retry. */
    /* FIXME - cur_cfg delete once after system init */
}

static void
portd_netlink_recv_wait__ (void)
{
    struct vrf *vrf;
    if (system_configured) {
        /* For each vrfs' port list, wait on them */
        HMAP_FOR_EACH (vrf, node, &all_vrfs) {
            if (vrf->nl_sock > 0) {
                poll_fd_wait(vrf->nl_sock, POLLIN);
            }
        }
    }
}

static void
portd_wait(void)
{
    ovsdb_idl_wait(idl);
    portd_netlink_recv_wait__();
    poll_timer_wait(PORTD_POLL_INTERVAL * 1000);
}


/**
 * @details
 * Dumps the Linux bonding driver configuration for all the LAGs in the system
 * or for a specified LAG.
 */
void portd_bonding_configuration_dump(struct ds *ds, int argc, const char *argv[])
{
    struct shash_node *sh_node;
    struct port_lag_data *portp = NULL;

    if (argc > 1) { /* a lag is specified in argv */
        portp = shash_find_data(&all_ports, argv[1]);
        if (portp){
            if (!strncmp(portp->name, LAG_NAME_SUFFIX, LAG_NAME_SUFFIX_LENGTH)) {
                portd_bonding_configuration_file_dump(ds, portp->name);
            }
        }
    } else { /* dump all lags */
        SHASH_FOR_EACH(sh_node, &all_ports) {
            portp = sh_node->data;
            if (portp) {
                if (!strncmp(portp->name, LAG_NAME_SUFFIX, LAG_NAME_SUFFIX_LENGTH)) {
                    portd_bonding_configuration_file_dump(ds, portp->name);
                }
            }
        }
    }
}

/**
 * ovs-appctl interface callback function to dump Linux bonding driver
 * configuration file.
 *
 * @param conn connection to ovs-appctl interface.
 * @param argc number of arguments.
 * @param argv array of arguments.
 * @param OVS_UNUSED aux argument not used.
 */
static void
portd_unixctl_getbondingconfiguration(struct unixctl_conn *conn, int argc,
                   const char *argv[], void *aux OVS_UNUSED)
{
    struct ds ds = DS_EMPTY_INITIALIZER;
    portd_bonding_configuration_dump(&ds, argc, argv);
    unixctl_command_reply(conn, ds_cstr(&ds));
    ds_destroy(&ds);
}

static void
portd_unixctl_dump(struct unixctl_conn *conn, int argc OVS_UNUSED,
                   const char *argv[] OVS_UNUSED, void *aux OVS_UNUSED)
{
       char err_str[MAX_ERR_STR_LEN];
       char *buf = xcalloc(1, BUF_LEN);
       if (buf){
               portd_dump(buf, BUF_LEN, "sub-interface");
               unixctl_command_reply(conn, buf);
               portd_dump(buf, BUF_LEN, "loopback");
               unixctl_command_reply(conn, buf);
               SAFE_FREE(buf);
       } else {
               snprintf(err_str,sizeof(err_str),
                               "portd daemon failed to allocate %d bytes", BUF_LEN );
               unixctl_command_reply(conn, err_str );
       }
       return;
}

static void
portd_dump(char* buf, int buflen, const char* feature)
{
    if (strcmp(feature, "subinterface") == 0)
       snprintf(buf, buflen, "Number of Configured sub-interfaces are : %d.", subintf_count);
    else if (strcmp(feature, "loopback") == 0)
       snprintf(buf, buflen, "Number of Configured loopback interfaces are : %d.", lpbk_count);
    /* Dump Linux bonding configuration for lacp feature. */
    else if (strcmp(feature, "lacp") == 0) {
        struct ds ds = DS_EMPTY_INITIALIZER;
        portd_bonding_configuration_dump(&ds, 0, NULL);
        snprintf(buf, buflen, "%s", ds_cstr(&ds));
    }
}

static void
portd_diag_dump_basic_subif_lpbk(const char *feature , char **buf)
{
     if (!buf)
             return;
     *buf =  xcalloc(1,BUF_LEN);
     if (*buf) {
         portd_dump(*buf, BUF_LEN, feature);
         /* populate basic diagnostic data to buffer  */
         VLOG_DBG("basic diag-dump data populated for feature %s",
                  feature);
     }else{
         VLOG_ERR("Memory allocation failed for feature %s , %d bytes",
                  feature , BUF_LEN);
     }
     return ;
}

static void
usage(void)
{
    printf("%s: OPS portd daemon\n"
            "usage: %s [OPTIONS] [DATABASE]\n"
            "where DATABASE is a socket on which ovsdb-server is listening\n"
            "      (default: \"unix:%s/db.sock\").\n",
            program_name, program_name, ovs_rundir());
    stream_usage("DATABASE", true, false, true);
    daemon_usage();
    vlog_usage();
    printf("\nOther options:\n"
            "  --unixctl=SOCKET        override default control socket name\n"
            "  -h, --help              display this help message\n"
            "  -V, --version           display version information\n");
    exit(EXIT_SUCCESS);
}

static char *
parse_options(int argc, char *argv[], char **unixctl_pathp)
{
    enum {
        OPT_UNIXCTL = UCHAR_MAX + 1,
        VLOG_OPTION_ENUMS,
        DAEMON_OPTION_ENUMS,
    };

    static const struct option long_options[] = {
            {"help",        no_argument, NULL, 'h'},
            {"version",     no_argument, NULL, 'V'},
            {"unixctl",     required_argument, NULL, OPT_UNIXCTL},
            DAEMON_LONG_OPTIONS,
            VLOG_LONG_OPTIONS,
            {NULL, 0, NULL, 0},
    };

    char *short_options = long_options_to_short_options(long_options);

    for (;;) {
        int c;

        c = getopt_long(argc, argv, short_options, long_options, NULL);

        if (c == -1) {
            break;
        }

        switch (c) {
        case 'h':
            usage();

        case 'V':
            ovs_print_version(OFP10_VERSION, OFP10_VERSION);
            exit(EXIT_SUCCESS);

        case OPT_UNIXCTL:
            *unixctl_pathp = optarg;
            break;

            VLOG_OPTION_HANDLERS
            DAEMON_OPTION_HANDLERS

        case '?':
            exit(EXIT_FAILURE);

        default:
            abort();
        }
    }
    free(short_options);

    argc -= optind;
    argv += optind;

    switch (argc) {
    case 0:
        return xasprintf("unix:%s/db.sock", ovs_rundir());

    case 1:
        return xstrdup(argv[0]);

    default:
        VLOG_FATAL("at most one non-option argument accepted; "
                "use --help for usage");
    }
}

static void
ops_portd_exit(struct unixctl_conn *conn, int argc OVS_UNUSED,
               const char *argv[] OVS_UNUSED, void *exiting_)
{
    bool *exiting = exiting_;
    *exiting = true;
    shash_destroy_free_data(&all_ports);
    shash_destroy_free_data(&all_interfaces);
    unixctl_command_reply(conn, NULL);
}

bool portd_add_interface_netlink(struct ovsrec_port *port_row,
                                 char* intf_type, int ifi_index)
{
    struct {
        struct nlmsghdr  n;
        struct ifinfomsg i;
        char             buf[128];  /* must fit interface name length (IFNAMSIZ)
                                       and attribute hdrs. */
    } req;

    VLOG_INFO("Creating %s interface for interface %s", intf_type, port_row->name);
    req.n.nlmsg_len = NLMSG_SPACE(sizeof(struct ifinfomsg));
    req.n.nlmsg_pid     = getpid();
    req.n.nlmsg_type    = RTM_NEWLINK;
    req.n.nlmsg_flags   = NLM_F_REQUEST | NLM_F_CREATE | NLM_F_EXCL;
    req.i.ifi_family    = AF_UNSPEC;
    req.i.ifi_index     = ifi_index;

    struct rtattr *linkinfo = NLMSG_TAIL(&req.n);
    add_link_attr(&req.n, sizeof(req), IFLA_LINKINFO, NULL, 0);
    add_link_attr(&req.n, sizeof(req), IFLA_INFO_KIND,
                  intf_type, strlen(intf_type));

    struct rtattr * data = NLMSG_TAIL(&req.n);
    add_link_attr(&req.n, sizeof(req), IFLA_INFO_DATA, NULL, 0);

    /* Adjust rta_len for attributes */
    data->rta_len = (void *)NLMSG_TAIL(&req.n) - (void *)data;
    linkinfo->rta_len = (void *)NLMSG_TAIL(&req.n) - (void *)linkinfo;

    add_link_attr(&req.n, sizeof(req), IFLA_IFNAME, port_row->name,
                  strlen(port_row->name)+1);

    if (send(nl_sock, &req, req.n.nlmsg_len, 0) == -1) {
        VLOG_ERR("Netlink failed to create netlink for interface: %s (%s)",
                 port_row->name, strerror(errno));
        return false;
    }

    return true;
}

bool
portd_reconfig_ns_loopback(struct port *port,
                           struct ovsrec_port *port_row, bool create_flag)
{
    struct vrf *vrf = get_vrf_for_port(port_row->name);

    if (create_flag)
    {
        bool kernel_interface_ready = true;

        if (!portd_add_interface_netlink(port_row, "dummy", 0))
        {
            VLOG_ERR("Netlink failed to create dummy interface: %s (%s)",
	             port_row->name, strerror(errno));
            return false;
        }
        /* kernel interface is created */
        ovsrec_port_set_kernel_interface_ready(port_row, &kernel_interface_ready, 1);
        commit_txn = true;
    }

    if (vrf->cfg && strcmp(vrf->name, DEFAULT_VRF_NAME) &&
                    vrf_is_ready(idl, vrf->name))
    {
        struct setns_info setns_local_info;
        memcpy(&setns_local_info.from_ns[0], SWITCH_NAMESPACE,  strlen(SWITCH_NAMESPACE) + 1);
        get_vrf_ns_from_table_id(idl, vrf->table_id, &setns_local_info.to_ns[0]);
        memcpy(&setns_local_info.intf_name[0], port_row->name, strlen(port_row->name) + 1);
        if (!nl_move_intf_to_vrf(&setns_local_info))
        {
            VLOG_ERR("Failed to move interface from %s to %s",
                      SWITCH_NAMESPACE, vrf->name);
        }
    }

    if (portd_if_nametoindex(vrf, port_row->name))
    {
        portd_reconfig_ipaddr(port, port_row);
    }

    return true;
}

void
portd_register_event_log(struct ovsrec_port *port_row,
                                     struct port *port) {
    bool admin_modified = false;
    bool ipv6_add = false;
    bool ipv6_delete = false;
    bool ipv4_add = false;
    bool ipv4_delete = false;

    if (OVSREC_IDL_IS_COLUMN_MODIFIED(
             ovsrec_port_col_ip4_address, idl_seqno)) {
       if (port->ip4_address) {
          if (port_row->ip4_address) {
             ipv4_add = true;
          }else {
             ipv4_delete = true;
       }
     }else {
        ipv4_delete = true;
       }
    }
    else if (OVSREC_IDL_IS_COLUMN_MODIFIED(
             ovsrec_port_col_ip6_address, idl_seqno)) {
       if (port->ip6_address) {
          if (port_row->ip6_address) {
             ipv6_add = true;
          }else {
             ipv6_delete = true;
         }
      } else {
           ipv6_delete = true;
      }
    }
    else if (OVSREC_IDL_IS_COLUMN_MODIFIED(
             ovsrec_port_col_admin, idl_seqno)) {
       admin_modified = true;
    }

   if (NULL != port->type){
      if (strcmp(port->type,
          OVSREC_INTERFACE_TYPE_LOOPBACK) == 0) {
          if (ipv6_add == true){
               log_event("LOOPBACK_IP_UPDATE", EV_KV("interface",
                         "%s", port_row->name),
                         EV_KV("value", "%s",
                         port_row->ip6_address));
          }else if (ipv6_delete == true){
               log_event("LOOPBACK_IPV6_DELETE", EV_KV("interface",
                          "%s", port_row->name));
          }

          if (ipv4_add == true){
               log_event("LOOPBACK_IP_UPDATE", EV_KV("interface",
                         "%s", port_row->name),
                         EV_KV("value", "%s",
                         port_row->ip4_address));
          }else if (ipv4_delete == true){
               log_event("LOOPBACK_IPV4_DELETE", EV_KV("interface",
                          "%s", port_row->name));
          }
     }else if (strcmp(port->type,
         OVSREC_INTERFACE_TYPE_VLANSUBINT) == 0) {
         if (ipv6_add == true){
              log_event("SUBINTERFACE_IPV6_UPDATE", EV_KV("interface",
                        "%s", port_row->name),
                        EV_KV("value", "%s",
                        port_row->ip6_address));
         }else if (ipv6_delete == true){
              log_event("SUBINTERFACE_IPV6_DELETE", EV_KV("interface",
                         "%s", port_row->name));
         }

         if (ipv4_add == true){
              log_event("SUBINTERFACE_IP_UPDATE", EV_KV("interface",
                        "%s", port_row->name),
                        EV_KV("value", "%s",
                        port_row->ip4_address));
         }else if (ipv4_delete == true){
              log_event("SUBINTERFACE_IPV4_DELETE", EV_KV("interface",
                         "%s", port_row->name));
         }
         if (admin_modified == true){
            log_event("SUBINTERFACE_ADMIN_STATE", EV_KV("interface",
                   "%s", port_row->name),
                   EV_KV("state", "%s", port_row->admin));
        }
     }
   }
}

void
portd_arbiter_run(void)
{
    const struct ovsrec_port *port = NULL;
    struct smap forwarding_state;

    /* Walk through all the interfaces and update the forwarding states
     * for each layer and the final forwarding state. */
    OVSREC_PORT_FOR_EACH(port, idl) {
        smap_clone(&forwarding_state, &port->forwarding_state);
        /* Run the arbiter for the port */
        portd_arbiter_port_run(port, &forwarding_state);
        /* Check if the OVSDB column needs an update */
        if (!smap_equal(&forwarding_state, &port->forwarding_state)) {
            ovsrec_port_set_forwarding_state(port, &forwarding_state);
            commit_txn = true;
        }
        smap_destroy(&forwarding_state);
    }

    return;
}

int
main(int argc, char *argv[])
{
    char *unixctl_path = NULL;
    struct unixctl_server *unixctl;
    char *remote;
    bool exiting;
    int retval;

    set_program_name(argv[0]);
    proctitle_init(argc, argv);
    remote = parse_options(argc, argv, &unixctl_path);
    fatal_ignore_sigpipe();

    ovsrec_init();

    daemonize_start();

    retval = unixctl_server_create(unixctl_path, &unixctl);
    if (retval) {
        exit(EXIT_FAILURE);
    }
    unixctl_command_register("exit", "", 0, 0, ops_portd_exit, &exiting);

    portd_init(remote);
    free(remote);
    daemonize_complete();
    vlog_enable_async();
    retval = event_log_init("SUBINTERFACE");
    if(retval < 0) {
         VLOG_ERR("Event log initialization failed for subinterface");
    }
    retval = event_log_init("LOOPBACK");
    if(retval < 0) {
         VLOG_ERR("Event log initialization failed for loopback");
    }
    sleep(2);
    retval = event_log_init("VLAN");
    if(retval < 0) {
         VLOG_ERR("Event log initialization failed for vlan");
    }

    exiting = false;
    while (!exiting) {
        portd_run();
        unixctl_server_run(unixctl);

        portd_wait();
        unixctl_server_wait(unixctl);
        if (exiting) {
            poll_immediate_wake();
        }
        poll_block();
    }
    portd_exit();
    unixctl_server_destroy(unixctl);

    return 0;
}
