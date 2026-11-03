(** * LinuxProcessSem.Ns.Net — network namespaces, NETLINK_ROUTE sockets and SIOCGIFINDEX

    A network namespace as [Tables.NetNs] holds it, and the five calls a
    process uses to configure the loopback device of its namespace and read
    the configuration back: [socket] (198) for a NETLINK_ROUTE socket or an
    AF_UNIX datagram socket, [bind] (200) of the netlink socket, [sendto]
    (206) of one rtnetlink request to the kernel, [recvfrom] (207) of the
    datagrams the kernel queued for the socket, and [ioctl] (29)
    SIOCGIFINDEX.  [net_arms] lists the five arms by call number.

    Linux 6.18.44 sources:
    - a new namespace: [copy_net_ns] (net/core/net_namespace.c) runs the
      pernet initialisers in order: [loopback_net_init] and
      [gen_lo_setup] (drivers/net/loopback.c) register [lo] with ifindex
      [LOOPBACK_IFINDEX] (1), flags IFF_LOOPBACK and no address, down; the
      fallback devices of the tunnel drivers the host has loaded follow, each
      down, with the indexes [dev_index_reserve] (net/core/dev.c) hands out
      from 2 ([new_netns]);
    - the flags a reader sees: [netif_get_flags] (net/core/dev.c), with
      [netif_oper_up] and [netif_carrier_ok] (include/linux/netdevice.h);
    - a flag change: [rtnl_dev_combine_flags], [rtnl_dev_get_flags]
      (net/core/rtnetlink.c), [netif_change_flags], [__dev_change_flags],
      [__dev_open], [__dev_close], [__dev_set_promiscuity],
      [netif_set_allmulti] (net/core/dev.c); bringing a loopback device up
      runs [inetdev_event]'s NETDEV_UP arm (net/ipv4/devinet.c), which adds
      127.0.0.1/8 through [inet_insert_ifa]: a refused duplicate when that
      address is already there, and no address when [inet_alloc_ifa]
      fails ([lo_up_noaddr]);
    - an IPv4 address: [inet_rtm_newaddr], [inet_validate_rtm],
      [inet_rtm_to_ifa], [find_matching_ifa], [__inet_insert_ifa],
      [set_ifa_lifetime], [inet_fill_ifaddr], [inet_dump_addr],
      [in_dev_dump_ifaddr] (net/ipv4/devinet.c);
    - a link: [rtnl_newlink], [__rtnl_newlink], [rtnl_changelink],
      [do_setlink], [rtnl_dump_ifinfo], [rtnl_valid_dump_ifinfo_req],
      [rtnl_fill_ifinfo], [rtnetlink_rcv_msg], [rtnetlink_dump_start],
      [rtnl_dumpit] (net/core/rtnetlink.c);
    - the netlink socket: [netlink_create], [__netlink_create],
      [netlink_bind], [netlink_insert], [netlink_autobind],
      [netlink_sendmsg], [netlink_unicast], [netlink_unicast_kernel],
      [netlink_rcv_skb], [netlink_ack], [__netlink_dump_start],
      [netlink_dump], [netlink_dump_done], [netlink_recvmsg],
      [netlink_attachskb], [netlink_ns_capable], [netlink_allowed],
      [netlink_ioctl] (net/netlink/af_netlink.c);
    - the AF_UNIX socket: [unix_create], [unix_ioctl] (net/unix/af_unix.c);
    - the system calls: [__sys_socket], [__sys_socket_create],
      [__sock_create], [sock_map_fd], [__sys_bind], [move_addr_to_kernel],
      [move_addr_to_user], [__sys_sendto], [__sys_recvfrom], [sock_ioctl],
      [sock_do_ioctl], [get_user_ifreq], [put_user_ifreq] (net/socket.c);
      [import_ubuf] (lib/iov_iter.c); [dev_ioctl], [dev_ifsioc_locked],
      [dev_load] (net/core/dev_ioctl.c).

    WHAT THE NAMESPACE RECORD MEANS HERE.  [if_flags] is the device's
    [dev->flags]; its IFF_PROMISC and IFF_ALLMULTI bits stand for
    [dev->gflags] too, which they equal while no other source (a packet
    socket, a multicast join) moves the device's counters, and no arm of
    this model does.  [if_addrs] lists the device's IPv4 addresses in the
    order of [in_dev->ifa_list], each as (address, prefix length) with the
    address as a number in host order; every address the model holds was
    added with IFA_LOCAL = IFA_ADDRESS, no label, broadcast, protocol or
    priority attribute, an infinite lifetime and the scope [addr_scope]
    gives (host for 127.0.0.0/8, universe otherwise): the shape the
    loopback device's own address has, and the only shape [sendto] adds.
    A namespace that is not [netns_sealed] is the host's: its devices and
    addresses were not made by this model, so a request that would read or
    change them past the permission check declines.

    DATAGRAMS AND THE QUEUE.  [NfNetlink n port q] is a socket of
    namespace [n] with port id [port] (0 while unbound; a port is held as
    its u32 value) and [q] the datagrams queued for it, oldest first.  A
    request to the kernel is handled while [sendto] runs
    ([netlink_unicast_kernel]), so its acknowledgement is queued before
    [sendto] returns.  A dump queues its first datagram then and each
    later one while [recvfrom] consumes the one before; [q] holds them all
    from the request on, which is the same sequence as long as nothing
    else is queued to the socket and nothing changes the namespace before
    the last datagram is read.  So a request that would queue an answer
    while [q] is not empty declines (the kernel compares the queue's memory
    with the receive buffer, a host setting, in [netlink_attachskb]), and
    a request that would change a namespace in which some socket's dump is
    still running declines ([dump_running]).

    KINDS.  [socket_arm] exact; [bind_arm] exact in a sealed namespace and
    over in another (a port may be held by a socket the model does not
    see); [sendto_arm] exact on the namespace's new state and on every
    acknowledgement, over on dump replies (the attributes after IFLA_IFNAME
    of a link message, the [ifi_type] of a device other than a loopback
    device, the two timestamps of IFA_CACHEINFO and how the kernel batches
    messages into datagrams are the environment's, chosen by [NlEnv]);
    [recvfrom_arm] exact; [ioctl_arm] exact.  Each header lists what it
    declines.

    INJECTED FAILURES.  The environment's refusals the arms offer beside
    their answer are listed in [net_injected], with the kernel functions
    that return them; no security module but the capability one runs
    (SCOPE.md).  A netlink socket's pending error is not modelled, so an
    allocation failure reported asynchronously, by an acknowledgement or a
    dump that could not be queued, is admitted as [recvfrom]'s refusal
    rather than a stored [sk_err]; a handler's own allocation failure is
    the error of the acknowledgement [sendto] queues, and a dump that fails
    so keeps running, its datagrams behind that acknowledgement
    ([nl_handler_errnos]); a loopback device brought up while its address
    cannot be allocated is up with no address ([lo_up_noaddr]).

    THE DESCRIPTOR TABLE.  [ns_fd_entry] and [Arm.ns_file_of] are the only
    places that name the descriptor kind of an open file of the namespace
    model. *)

From Stdlib Require Import ZArith List Bool NArith PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Userns Ext Arm.
Import ListNotations.
Local Open Scope Z_scope.

(* =========================================================================
   Constants (include/uapi/linux/{netlink,rtnetlink,if,if_addr,if_arp,
   sockios}.h, include/linux/socket.h, include/uapi/asm-generic/errno.h)
   ========================================================================= *)

Definition AF_UNIX : Z := 1.
Definition AF_NETLINK : Z := 16.
Definition NETLINK_ROUTE : Z := 0.

Definition CAP_NET_ADMIN : Z := 12.
Definition CAP_SYS_MODULE : Z := 16.

Definition MSG_OOB : Z := 1.
Definition MSG_PEEK : Z := 2.
Definition MSG_TRUNC : Z := 32.
Definition MSG_DONTWAIT : Z := 64.

Definition SIOCGIFINDEX : Z := 35123.        (* 0x8933 *)
Definition IFREQ_SIZE : Z := 40.             (* sizeof(struct ifreq), LP64 *)
Definition SOCKADDR_NL_SIZE : Z := 12.       (* sizeof(struct sockaddr_nl) *)

Definition IFF_UP : Z := 1.
Definition IFF_BROADCAST : Z := 2.
Definition IFF_DEBUG : Z := 4.
Definition IFF_LOOPBACK : Z := 8.
Definition IFF_POINTOPOINT : Z := 16.
Definition IFF_NOTRAILERS : Z := 32.
Definition IFF_RUNNING : Z := 64.
Definition IFF_NOARP : Z := 128.
Definition IFF_PROMISC : Z := 256.
Definition IFF_ALLMULTI : Z := 512.
Definition IFF_MASTER : Z := 1024.
Definition IFF_SLAVE : Z := 2048.
Definition IFF_MULTICAST : Z := 4096.
Definition IFF_PORTSEL : Z := 8192.
Definition IFF_AUTOMEDIA : Z := 16384.
Definition IFF_DYNAMIC : Z := 32768.
Definition IFF_LOWER_UP : Z := 65536.
Definition IFF_DORMANT : Z := 131072.
Definition IFF_ECHO : Z := 262144.

(** [IFF_VOLATILE] (include/uapi/linux/if.h), and the bits
    [__dev_change_flags] copies from the request. *)
Definition IFF_VOLATILE : Z :=
  IFF_LOOPBACK + IFF_POINTOPOINT + IFF_BROADCAST + IFF_ECHO + IFF_MASTER + IFF_SLAVE
  + IFF_RUNNING + IFF_LOWER_UP + IFF_DORMANT.
Definition IFF_USER_SET : Z :=
  IFF_DEBUG + IFF_NOTRAILERS + IFF_NOARP + IFF_DYNAMIC + IFF_MULTICAST + IFF_PORTSEL
  + IFF_AUTOMEDIA.

Definition NLM_F_REQUEST : Z := 1.
Definition NLM_F_MULTI : Z := 2.
Definition NLM_F_ACK : Z := 4.
Definition NLM_F_ECHO : Z := 8.
Definition NLM_F_DUMP : Z := 768.            (* NLM_F_ROOT | NLM_F_MATCH *)
Definition NLM_F_REPLACE : Z := 256.
Definition NLM_F_EXCL : Z := 512.
Definition NLM_F_CREATE : Z := 1024.
Definition NLM_F_CAPPED : Z := 256.

Definition NLMSG_ERROR : Z := 2.
Definition NLMSG_DONE : Z := 3.
Definition NLMSG_MIN_TYPE : Z := 16.

Definition RTM_NEWLINK : Z := 16.
Definition RTM_GETLINK : Z := 18.
Definition RTM_NEWADDR : Z := 20.
Definition RTM_GETADDR : Z := 22.
Definition RTM_MAX : Z := 123.

Definition IFLA_IFNAME : Z := 3.
Definition IFA_ADDRESS : Z := 1.
Definition IFA_LOCAL : Z := 2.
Definition IFA_LABEL : Z := 3.
Definition IFA_CACHEINFO : Z := 6.
Definition IFA_FLAGS : Z := 8.
Definition IFA_F_SECONDARY : Z := 1.
Definition IFA_F_PERMANENT : Z := 128.
Definition INFINITY_LIFE_TIME : Z := 4294967295.

Definition RT_SCOPE_UNIVERSE : Z := 0.
Definition RT_SCOPE_HOST : Z := 254.
Definition ARPHRD_LOOPBACK : Z := 772.

(** The longest request [sendto] judges.  Above it, [netlink_sendmsg]'s
    [len > sk->sk_sndbuf - 32] (-EMSGSIZE) reads net.core.wmem_default, a
    host setting whose floor (SOCK_MIN_SNDBUF, include/net/sock.h) leaves
    more than 4096 + 32 bytes. *)
Definition NL_SEND_MAX : Z := 4096.

(** The negative port ids [netlink_autobind] draws from after a collision,
    [S32_MIN, -4097], as u32 values. *)
Definition ROVER_LO : Z := 2147483648.
Definition ROVER_HI : Z := 4294963199.

(* =========================================================================
   Bytes
   ========================================================================= *)

Definition nl_len (bs : list byte) : Z := Z.of_nat (length bs).
Definition nl_align (n : Z) : Z := (n + 3) / 4 * 4.
Definition nl_zeros (n : Z) : list byte := List.repeat (Z_to_bv 8 0) (Z.to_nat n).
Definition nl_le16 (z : Z) : list byte := Z_to_le_bytes 2 z.
Definition nl_le32 (z : Z) : list byte := Z_to_le_bytes 4 z.
Definition nl_be32 (z : Z) : list byte := rev (Z_to_le_bytes 4 z).

Definition nl_get (bs : list byte) (off n : nat) : Z := bytes_le_to_Z (firstn n (skipn off bs)).
Definition nl_u8 (bs : list byte) (off : nat) : Z := nl_get bs off 1.
Definition nl_u16 (bs : list byte) (off : nat) : Z := nl_get bs off 2.
Definition nl_u32 (bs : list byte) (off : nat) : Z := nl_get bs off 4.
Definition nl_be32_at (bs : list byte) (off : nat) : Z :=
  bytes_le_to_Z (rev (firstn 4 (skipn off bs))).

Fixpoint nl_bytes_eqb (a b : list byte) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (bv_unsigned x =? bv_unsigned y) && nl_bytes_eqb a' b'
  | _, _ => false
  end.

(** The C string at the start of [bs]: the bytes before the first NUL. *)
Fixpoint c_string (bs : list byte) : list byte :=
  match bs with
  | [] => []
  | b :: r => if bv_unsigned b =? 0 then [] else b :: c_string r
  end.

(** The bytes before the first ':' ([dev_ioctl]'s alias cut). *)
Fixpoint upto_colon (bs : list byte) : list byte :=
  match bs with
  | [] => []
  | b :: r => if bv_unsigned b =? 58 then [] else b :: upto_colon r
  end.

(* =========================================================================
   Namespaces and interfaces
   ========================================================================= *)

Definition lo_name : list byte := [Z_to_bv 8 108; Z_to_bv 8 111].

(** [lo] as [loopback_net_init] registers it: ifindex 1, IFF_LOOPBACK
    alone (down), no address. *)
Definition loopback_if : NetIf := mkNetIf 1 lo_name IFF_LOOPBACK [].

(** The host's fallback devices as a new namespace gets them: in the order
    the host registers them, with indexes from 2 on, down, no address. *)
Fixpoint fallback_ifs (k : Z) (fs : list NetIf) : list NetIf :=
  match fs with
  | [] => []
  | d :: r => mkNetIf k (if_name d) (Z.ldiff (if_flags d) IFF_UP) [] :: fallback_ifs (k + 1) r
  end.

(** [copy_net_ns]: a fresh network namespace [id] owned by user namespace
    [owner], whose every socket the model holds. *)
Definition new_netns (id owner : positive) (fallback : list NetIf) : NetNs :=
  mkNetNs id owner (loopback_if :: fallback_ifs 2 fallback) true.

Definition find_netns (st : NsState) (n : positive) : option NetNs :=
  List.find (fun x => Pos.eqb (netns_id x) n) (ns_netns st).

Definition with_netns (st : NsState) (ns : list NetNs) : NsState :=
  mkNsState (ns_mounts st) (ns_userns st) (ns_mntns st) (ns_pidns st) ns (ns_sbs st)
            (ns_dentries st) (ns_inodes st) (ns_files st) (ns_env st).

Definition set_netns_ifs (st : NsState) (n : positive) (ifs : list NetIf) : NsState :=
  with_netns st (map (fun x => if Pos.eqb (netns_id x) n
                               then mkNetNs (netns_id x) (netns_owner x) ifs (netns_sealed x)
                               else x) (ns_netns st)).

Definition if_by_index (ifs : list NetIf) (k : Z) : option NetIf :=
  List.find (fun d => if_index d =? k) ifs.

Definition if_by_name (ifs : list NetIf) (nm : list byte) : option NetIf :=
  List.find (fun d => nl_bytes_eqb (if_name d) nm) ifs.

Definition replace_if (ifs : list NetIf) (d : NetIf) : list NetIf :=
  map (fun x => if if_index x =? if_index d then d else x) ifs.

Definition is_up (d : NetIf) : bool := Z.testbit (if_flags d) 0.
Definition is_loopback (d : NetIf) : bool := Z.testbit (if_flags d) 3.

(** [netif_get_flags]: [dev->flags] without the bits the state decides,
    then IFF_RUNNING and IFF_LOWER_UP for a running loopback device, whose
    operational state stays IF_OPER_UNKNOWN ([netif_oper_up] counts it as
    up) and whose carrier is never turned off.  A device of another kind
    that is up has its driver's state; no reply of this model shows one
    ([rt_handle] declines there). *)
Definition netif_get_flags (d : NetIf) : Z :=
  Z.lor (Z.ldiff (if_flags d) (IFF_RUNNING + IFF_LOWER_UP + IFF_DORMANT))
        (if is_up d && is_loopback d then IFF_RUNNING + IFF_LOWER_UP else 0).

(* =========================================================================
   IPv4 addresses
   ========================================================================= *)

(** [inet_make_mask]. *)
Definition inet_mask (p : Z) : Z :=
  if p =? 0 then 0 else Z.land (Z.shiftl 4294967295 (32 - p)) 4294967295.

(** The scope every address the model holds has: host for 127.0.0.0/8,
    universe otherwise. *)
Definition addr_scope (a : Z) : Z :=
  if Z.shiftr a 24 =? 127 then RT_SCOPE_HOST else RT_SCOPE_UNIVERSE.

(** The test [__inet_insert_ifa] and [find_matching_ifa] make: the same
    mask, and [inet_ifa_match] of the one address in the other's subnet. *)
Definition same_subnet (x y : Z * Z) : bool :=
  (snd x =? snd y) && (Z.land (Z.lxor (fst x) (fst y)) (inet_mask (snd y)) =? 0).

(** IFA_F_SECONDARY of each address of a list in [ifa_list] order: an
    address is secondary exactly when an earlier one shares its subnet. *)
Fixpoint secondaries (prev l : list (Z * Z)) : list bool :=
  match l with
  | [] => []
  | e :: r => existsb (fun x => same_subnet x e) prev :: secondaries (prev ++ [e]) r
  end.

(** [__inet_insert_ifa]'s loop over the existing addresses: the first
    address of the new one's subnet with the same local address is
    -EEXIST, one with another scope -EINVAL. *)
Fixpoint ifa_conflict (l : list (Z * Z)) (n : Z * Z) : option Z :=
  match l with
  | [] => None
  | e :: r =>
      if same_subnet e n then
        if fst e =? fst n then Some EEXIST
        else if negb (addr_scope (fst e) =? addr_scope (fst n)) then Some EINVAL
        else ifa_conflict r n
      else ifa_conflict r n
  end.

(** Where a new primary address goes: after the last primary address whose
    scope is at least its own, else first. *)
Fixpoint primary_pos (sc : Z) (prev l : list (Z * Z)) (i best : nat) : nat :=
  match l with
  | [] => best
  | e :: r =>
      let prim := negb (existsb (fun x => same_subnet x e) prev) in
      primary_pos sc (prev ++ [e]) r (Datatypes.S i)
                  (if prim && (sc <=? addr_scope (fst e)) then Datatypes.S i else best)
  end.

Definition nl_insert_at {A} (k : nat) (x : A) (l : list A) : list A :=
  firstn k l ++ x :: skipn k l.

Inductive InsResult :=
  | InsOk (l : list (Z * Z))
  | InsErr (e : Z).

(** [__inet_insert_ifa]: the errno, or the list with the address in place
    (a secondary at the end). *)
Definition inet_insert (l : list (Z * Z)) (n : Z * Z) : InsResult :=
  match ifa_conflict l n with
  | Some e => InsErr e
  | None =>
      if existsb (fun e => same_subnet e n) l then InsOk (l ++ [n])
      else InsOk (nl_insert_at (primary_pos (addr_scope (fst n)) [] l 0 0) n l)
  end.

(** 127.0.0.1/8, which [inetdev_event] adds when a loopback device comes up. *)
Definition loopback_addr : Z * Z := (2130706433, 8).

Definition lo_up_addrs (l : list (Z * Z)) : list (Z * Z) :=
  match inet_insert l loopback_addr with
  | InsOk l' => l'
  | InsErr _ => l
  end.

(* =========================================================================
   Flags
   ========================================================================= *)

(** [rtnl_dev_combine_flags]: an [ifi_change] of 0 means every bit.
    [rtnl_dev_get_flags] is [if_flags] here (see the header). *)
Definition combine_flags (f ifl ich : Z) : Z :=
  if ich =? 0 then ifl else Z.lor (Z.land ifl ich) (Z.ldiff f ich).

(** [__dev_change_flags] with [__dev_open]/[__dev_close] (which a
    loopback device never refuses: it has no [ndo_open] and no
    [ndo_validate_addr]), the gflags toggles and their counters. *)
Definition changed_flags (f c : Z) : Z :=
  Z.lor (Z.land c IFF_USER_SET)
        (Z.lor (Z.land f IFF_VOLATILE) (Z.land c (IFF_UP + IFF_PROMISC + IFF_ALLMULTI))).

(** [netif_change_flags] on a loopback device, with NETDEV_UP's address. *)
Definition set_link_flags (d : NetIf) (ifl ich : Z) : NetIf :=
  let f := if_flags d in
  let f' := changed_flags f (combine_flags f ifl ich) in
  let addrs := if negb (Z.testbit f 0) && Z.testbit f' 0 && is_loopback d
               then lo_up_addrs (if_addrs d) else if_addrs d in
  mkNetIf (if_index d) (if_name d) f' addrs.

(** The interfaces a request leaves when, as a loopback device comes up,
    [inetdev_event]'s [inet_alloc_ifa] fails (net/ipv4/devinet.c:1613-1629):
    the device is up, and 127.0.0.1/8 is not added; the request is still
    acknowledged with 0, as [inetdev_event] returns NOTIFY_DONE whatever
    happened (devinet.c:1668).  [ifs] are the interfaces before the
    request, [ifs'] the ones [rt_handle] gives. *)
Definition lo_up_noaddr (ifs ifs' : list NetIf) : list NetIf :=
  map (fun d' => match if_by_index ifs (if_index d') with
                 | Some d => if negb (is_up d) && is_up d' && is_loopback d'
                             then mkNetIf (if_index d') (if_name d') (if_flags d') (if_addrs d)
                             else d'
                 | None => d'
                 end) ifs'.

(** The request brings a loopback device of [ifs] up. *)
Definition lo_comes_up (ifs ifs' : list NetIf) : bool :=
  existsb (fun d' => match if_by_index ifs (if_index d') with
                     | Some d => negb (is_up d) && is_up d' && is_loopback d'
                     | None => false
                     end) ifs'.

(** A loopback device of [ifs] that is up in [ifs'], down in [ifs], with as
    many addresses as it had, where [lo_up_addrs] would have added
    127.0.0.1/8: the device came up without its address ([lo_up_noaddr]).
    A request that brings a loopback device up with no allocation failing
    never leaves that, as [set_link_flags] adds the address. *)
Definition lo_up_without_addr (ifs ifs' : list NetIf) : bool :=
  existsb (fun d' => match if_by_index ifs (if_index d') with
                     | Some d => negb (is_up d) && is_up d' && is_loopback d'
                                 && Nat.eqb (length (if_addrs d')) (length (if_addrs d))
                                 && negb (Nat.eqb (length (lo_up_addrs (if_addrs d)))
                                                  (length (if_addrs d)))
                     | None => false
                     end) ifs'.

(* =========================================================================
   Messages
   ========================================================================= *)

Definition nlmsg_hdr (len ty fl seq port : Z) : list byte :=
  nl_le32 len ++ nl_le16 ty ++ nl_le16 fl ++ nl_le32 seq ++ nl_le32 port.

(** An attribute, padded to four bytes ([nla_put]). *)
Definition nla (ty : Z) (payload : list byte) : list byte :=
  let n := 4 + nl_len payload in
  nl_le16 n ++ nl_le16 ty ++ payload ++ nl_zeros (nl_align n - n).

(** [nla_put_string]: the string and its NUL. *)
Definition nla_string (ty : Z) (s : list byte) : list byte := nla ty (s ++ [Z_to_bv 8 0]).

Definition req_seq (req : list byte) : Z := nl_u32 req 8.

(** [netlink_ack] for request [req] from port [port], errno [e] (0 for
    success): NLMSG_ERROR with the request's sequence number, the error,
    and the request's header; on an error the request's payload follows,
    padded, since the socket has no NETLINK_CAP_ACK; on success the reply
    is capped (NLM_F_CAPPED).  No NETLINK_EXT_ACK, so no attribute. *)
Definition nl_ack (port : Z) (req : list byte) (e : Z) : list byte :=
  let hdr := firstn 16 req in
  if e =? 0 then nlmsg_hdr 36 NLMSG_ERROR NLM_F_CAPPED (req_seq req) port ++ nl_le32 0 ++ hdr
  else
    let pl := nl_u32 req 0 - 16 in
    nlmsg_hdr (36 + nl_align pl) NLMSG_ERROR 0 (req_seq req) port ++ nl_le32 (- e) ++ hdr
      ++ firstn (Z.to_nat pl) (skipn 16 req) ++ nl_zeros (nl_align pl - pl).

(** [rtnl_fill_ifinfo] for a dump: the header, [struct ifinfomsg] (family
    AF_UNSPEC, type [ty], index, [netif_get_flags], change 0), IFLA_IFNAME,
    then the attributes the model does not hold, [rest]. *)
Definition link_msg (seq port ty : Z) (d : NetIf) (rest : list byte) : list byte :=
  let body := [Z_to_bv 8 0; Z_to_bv 8 0] ++ nl_le16 ty ++ nl_le32 (if_index d)
              ++ nl_le32 (netif_get_flags d) ++ nl_le32 0
              ++ nla_string IFLA_IFNAME (if_name d) ++ rest in
  nlmsg_hdr (16 + nl_len body) RTM_NEWLINK NLM_F_MULTI seq port ++ body.

(** [inet_fill_ifaddr] for an address the model holds: [struct ifaddrmsg],
    IFA_ADDRESS, IFA_LOCAL, IFA_LABEL (the device's name), IFA_FLAGS
    (IFA_F_PERMANENT, and IFA_F_SECONDARY when it is), IFA_CACHEINFO
    (infinite lifetimes; the creation and update timestamps [stamp]). *)
Definition addr_msg (seq port : Z) (d : NetIf) (a : Z * Z) (sec : bool) (stamp : Z * Z)
    : list byte :=
  let fl := IFA_F_PERMANENT + (if sec then IFA_F_SECONDARY else 0) in
  let body := [Z_to_bv 8 AF_INET; Z_to_bv 8 (snd a); Z_to_bv 8 fl; Z_to_bv 8 (addr_scope (fst a))]
              ++ nl_le32 (if_index d)
              ++ nla IFA_ADDRESS (nl_be32 (fst a)) ++ nla IFA_LOCAL (nl_be32 (fst a))
              ++ nla_string IFA_LABEL (if_name d) ++ nla IFA_FLAGS (nl_le32 fl)
              ++ nla IFA_CACHEINFO (nl_le32 INFINITY_LIFE_TIME ++ nl_le32 INFINITY_LIFE_TIME
                                    ++ nl_le32 (fst stamp) ++ nl_le32 (snd stamp)) in
  nlmsg_hdr (16 + nl_len body) RTM_NEWADDR NLM_F_MULTI seq port ++ body.

(** [netlink_dump_done]: NLMSG_DONE with error 0. *)
Definition done_msg (seq port : Z) : list byte :=
  nlmsg_hdr 20 NLMSG_DONE NLM_F_MULTI seq port ++ nl_le32 0.

(** What the environment chooses in a dump: per interface (in order) the
    [ifi_type] of a device that is not a loopback device and the attributes
    after IFLA_IFNAME; per address message (in order) its two timestamps;
    and how many messages each datagram carries.  [nl_env_ok] below says
    which choices Linux can make. *)
Record NlEnv := mkNlEnv {
  ne_types  : list Z;
  ne_rests  : list (list byte);
  ne_stamps : list (Z * Z);
  ne_split  : list nat
}.

(** A run of attributes as [nla_put] (include/net/netlink.h) writes them:
    each starts with its [nla_len], at least the 4-byte header and within
    the run, and the next starts [NLA_ALIGN(nla_len)] after it; the run
    ends exactly at the end of the last one's padding.  So its length is a
    multiple of 4, and a reader's [nla_ok]/[nla_next] walks it to the end.
    Each step consumes at least 4 bytes, so [length bs + 1] steps
    suffice. *)
Fixpoint nla_run_ok (fuel : nat) (bs : list byte) : bool :=
  match fuel with
  | O => false
  | Datatypes.S f =>
      match bs with
      | [] => true
      | _ :: _ =>
          let n := nl_u16 bs 0 in
          (4 <=? n) && (nl_align n <=? nl_len bs)
          && nla_run_ok f (skipn (Z.to_nat (nl_align n)) bs)
      end
  end.

Definition nla_list_ok (bs : list byte) : bool := nla_run_ok (Datatypes.S (length bs)) bs.

(** The most a dump datagram can hold besides [rtnl_calcit]'s
    [min_dump_alloc]: [netlink_dump] (net/netlink/af_netlink.c) allocates
    [max(min_dump_alloc, NLMSG_GOODSIZE)], or [nlk->max_recvmsg_len] when
    that is larger, and trims the skb to exactly that ([skb_reserve]);
    [netlink_recvmsg] caps [max_recvmsg_len] at [SKB_WITH_OVERHEAD(32768)],
    and [NLMSG_GOODSIZE] is below 8192.  So every dump datagram is at most
    [max(min_dump_alloc, 32768)].  The model does not follow
    [max_recvmsg_len], so it admits up to 32768 bytes even before a large
    receive: an over-approximation, never a refusal of a Linux datagram. *)
Definition NL_DUMP_SKB_MAX : Z := 32768.

Definition dgrams_fit (cap : Z) (dgs : list (list byte)) : bool :=
  forallb (fun dg => nl_len dg <=? cap) dgs.

Fixpoint link_msgs (env : NlEnv) (seq port : Z) (k : nat) (ifs : list NetIf) : list (list byte) :=
  match ifs with
  | [] => []
  | d :: r =>
      link_msg seq port (if is_loopback d then ARPHRD_LOOPBACK else nth k (ne_types env) 0) d
               (nth k (ne_rests env) [])
        :: link_msgs env seq port (Datatypes.S k) r
  end.

Definition addr_items (ifs : list NetIf) : list (NetIf * (Z * Z) * bool) :=
  flat_map (fun d => combine (map (fun a => (d, a)) (if_addrs d)) (secondaries [] (if_addrs d))) ifs.

Fixpoint addr_msgs (env : NlEnv) (seq port : Z) (k : nat) (items : list (NetIf * (Z * Z) * bool))
    : list (list byte) :=
  match items with
  | [] => []
  | (d, a, sec) :: r =>
      addr_msg seq port d a sec (nth k (ne_stamps env) (0, 0))
        :: addr_msgs env seq port (Datatypes.S k) r
  end.

(** Consecutive messages into datagrams of [ks] messages each; [None] when
    [ks] is not a partition of them into non-empty groups. *)
Fixpoint split_msgs (ks : list nat) (ms : list (list byte)) : option (list (list byte)) :=
  match ks with
  | [] => match ms with [] => Some [] | _ :: _ => None end
  | k :: ks' =>
      if Nat.eqb k 0 || Nat.ltb (length ms) k then None
      else option_map (cons (concat (firstn k ms))) (split_msgs ks' (skipn k ms))
  end.

(** What one request queues. *)
Inductive NlReply :=
  | RNone
  | RAck (dg : list byte)
  | RLinkDump (seq port : Z) (ifs : list NetIf)
  | RAddrDump (seq port : Z) (ifs : list NetIf).

Definition reply_queues (r : NlReply) : bool :=
  match r with RNone => false | _ => true end.

(** The datagrams a reply queues under [env]: a dump's messages in
    datagrams, then NLMSG_DONE in a datagram of its own ([rtnl_dumpit]
    with RTNL_FLAG_DUMP_SPLIT_NLM_DONE, which [rtnl_dump_ifinfo] and
    [inet_dump_ifaddr] are registered with). *)
Definition reply_dgrams (env : NlEnv) (r : NlReply) : option (list (list byte)) :=
  match r with
  | RNone => Some []
  | RAck dg => Some [dg]
  | RLinkDump seq port ifs =>
      option_map (fun g => g ++ [done_msg seq port])
                 (split_msgs (ne_split env) (link_msgs env seq port 0 ifs))
  | RAddrDump seq port ifs =>
      option_map (fun g => g ++ [done_msg seq port])
                 (split_msgs (ne_split env) (addr_msgs env seq port 0 (addr_items ifs)))
  end.

(** The choices Linux can make for a dump, given [lim], the build's
    largest [if_nlmsg_size] ([Tables.env_nl_link_max]):
    - each device's attributes after IFLA_IFNAME are a run [nla_put]
      writes ([nla_list_ok]);
    - each RTM_NEWLINK message is at most [lim]: [rtnl_fill_ifinfo] writes
      at most [if_nlmsg_size] bytes, and [rtnetlink_rcv_msg] sets a link
      dump's [min_dump_alloc] to [rtnl_calcit]'s largest [if_nlmsg_size]
      (net/core/rtnetlink.c), so one message always fits an empty skb;
    - each datagram of a link dump is at most [max(lim, NL_DUMP_SKB_MAX)],
      and of an address dump at most [NL_DUMP_SKB_MAX], since
      [inet_dump_ifaddr]'s [min_dump_alloc] is 0.
    How many messages share a datagram ([ne_split]) stays free: Linux
    packs as many as fit, and the model admits every packing within the
    caps.  Read at v6.18.44; identical at v6.18.46. *)
Definition nl_env_ok (lim : Z) (env : NlEnv) (r : NlReply) : bool :=
  match r with
  | RLinkDump seq port ifs =>
      let ms := link_msgs env seq port 0 ifs in
      forallb nla_list_ok (firstn (length ifs) (ne_rests env))
      && forallb (fun msg => nl_len msg <=? lim) ms
      && match split_msgs (ne_split env) ms with
         | Some g => dgrams_fit (Z.max lim NL_DUMP_SKB_MAX) g
         | None => true
         end
  | RAddrDump seq port ifs =>
      match split_msgs (ne_split env) (addr_msgs env seq port 0 (addr_items ifs)) with
      | Some g => dgrams_fit NL_DUMP_SKB_MAX g
      | None => true
      end
  | RNone | RAck _ => true
  end.

(* =========================================================================
   One rtnetlink request
   ========================================================================= *)

(** [netlink_ns_capable] for CAP_NET_ADMIN over the namespace's owner: the
    opener of the socket ([file_ns_capable]) unless the datagram named a
    destination (NETLINK_SKB_DST), and the caller ([ns_capable]). *)
Definition net_admin (U : list UserNs) (owner : positive) (opener caller : IdCred) (dst : bool)
    : bool :=
  (dst || cap_capable U opener owner CAP_NET_ADMIN) && cap_capable U caller owner CAP_NET_ADMIN.

(** [netlink_rcv_skb]'s acknowledgement: on NLM_F_ACK or an error. *)
Definition ack_if (fl port : Z) (req : list byte) (e : Z) : NlReply :=
  if (Z.land fl NLM_F_ACK =? 0) && (e =? 0) then RNone else RAck (nl_ack port req e).

(** RTM_NEWLINK, family AF_UNSPEC, no attribute ([rtnl_newlink],
    [__rtnl_newlink], [rtnl_changelink], [do_setlink]): the namespace's
    new interfaces when they change, and the handler's errno; [None]
    declines (an attribute, or a flag change on a device that is not a
    loopback device, whose driver opens it). *)
Definition rt_newlink (ifs : list NetIf) (fl : Z) (req : list byte)
    : option (option (list NetIf) * Z) :=
  let p := nl_len req - 16 in
  if p <? 16 then Some (None, EINVAL)
  else if 19 <? p then None
  else
    let idx := s32 (Z_to_bv 64 (nl_u32 req 20)) in
    let ifl := nl_u32 req 24 in
    let ich := nl_u32 req 28 in
    let absent := if Z.land fl NLM_F_CREATE =? 0 then ENODEV else EOPNOTSUPP in
    if 0 <? idx then
      match if_by_index ifs idx with
      | Some d =>
          if negb (Z.land fl NLM_F_EXCL =? 0) then Some (None, EEXIST)
          else if negb (Z.land fl NLM_F_REPLACE =? 0) then Some (None, EOPNOTSUPP)
          else if (ifl =? 0) && (ich =? 0) then Some (None, 0)
          else if negb (is_loopback d) then None
          else Some (Some (replace_if ifs (set_link_flags d ifl ich)), 0)
      | None => Some (None, absent)
      end
    else if idx <? 0 then Some (None, EINVAL)
    else Some (None, absent).

(** The attributes of an RTM_NEWADDR request the arm reads: none; IFA_LOCAL
    with or without IFA_ADDRESS, each of four bytes; IFA_ADDRESS alone;
    anything else. *)
Inductive AddrAttrs :=
  | AANone
  | AALocal (l : Z) (peer : option Z)
  | AAAddressOnly
  | AAOther.

Definition addr_attrs (a : list byte) : AddrAttrs :=
  if Nat.ltb (length a) 4 then AANone
  else if Nat.eqb (length a) 8 then
    if negb (nl_u16 a 0 =? 8) then AAOther
    else if nl_u16 a 2 =? IFA_LOCAL then AALocal (nl_be32_at a 4) None
    else if nl_u16 a 2 =? IFA_ADDRESS then AAAddressOnly
    else AAOther
  else if Nat.eqb (length a) 16 then
    if negb ((nl_u16 a 0 =? 8) && (nl_u16 a 8 =? 8)) then AAOther
    else if (nl_u16 a 2 =? IFA_LOCAL) && (nl_u16 a 10 =? IFA_ADDRESS)
    then AALocal (nl_be32_at a 4) (Some (nl_be32_at a 12))
    else if (nl_u16 a 2 =? IFA_ADDRESS) && (nl_u16 a 10 =? IFA_LOCAL)
    then AALocal (nl_be32_at a 12) (Some (nl_be32_at a 4))
    else AAOther
  else AAOther.

(** RTM_NEWADDR, family AF_INET ([inet_rtm_newaddr]): the new interfaces
    when they change and the errno; [None] declines (another attribute; a
    device that is not a loopback device, whose [in_dev] the device's MTU
    decides; IFA_ADDRESS other than IFA_LOCAL; a scope other than
    [addr_scope]).  The request's [ifa_flags] do not matter:
    [set_ifa_lifetime] and [__inet_insert_ifa] leave IFA_F_PERMANENT of
    them, and IFA_F_SECONDARY as the list decides. *)
Definition rt_newaddr (ifs : list NetIf) (fl : Z) (req : list byte)
    : option (option (list NetIf) * Z) :=
  let p := nl_len req - 16 in
  if p <? 8 then Some (None, EINVAL)
  else
    let plen := nl_u8 req 17 in
    let scope := nl_u8 req 19 in
    let idx := s32 (Z_to_bv 64 (nl_u32 req 20)) in
    match addr_attrs (skipn 24 req) with
    | AAOther => None
    | AANone | AAAddressOnly => Some (None, EINVAL)
    | AALocal l peer =>
        if 32 <? plen then Some (None, EINVAL)
        else if l =? 0 then Some (None, 0)
        else
          match if_by_index ifs idx with
          | None => Some (None, ENODEV)
          | Some d =>
              if negb (is_loopback d) then None
              else if negb (match peer with Some v => v =? l | None => true end) then None
              else if negb (scope =? addr_scope l) then None
              else if existsb (fun e => same_subnet e (l, plen) && (fst e =? l)) (if_addrs d) then
                if negb (Z.land fl NLM_F_EXCL =? 0) || (Z.land fl NLM_F_REPLACE =? 0)
                then Some (None, EEXIST) else Some (None, 0)
              else
                match inet_insert (if_addrs d) (l, plen) with
                | InsErr e => Some (None, e)
                | InsOk l' =>
                    Some (Some (replace_if ifs (mkNetIf (if_index d) (if_name d) (if_flags d) l')), 0)
                end
          end
    end.

Inductive NlStep :=
  | SDecline
  | SDone (ifs : option (list NetIf)) (r : NlReply).

(** One datagram [dg] from port [port] to the kernel's NETLINK_ROUTE socket
    of namespace [x] ([netlink_rcv_skb] with [rtnetlink_rcv_msg]): the
    namespace's new interfaces when they change and what is queued.
    Shorter than a header, or a header whose length does not fit, is
    dropped unanswered.  A datagram with a second message declines.
    Answered: a control or non-request message (an acknowledgement on
    NLM_F_ACK); a type above RTM_MAX (-EOPNOTSUPP); no payload (success);
    a change request without CAP_NET_ADMIN (-EPERM); and in a sealed
    namespace RTM_GETLINK dumps (family AF_UNSPEC, no attribute) and
    RTM_GETADDR dumps (family AF_INET), RTM_NEWLINK and RTM_NEWADDR as
    [rt_newlink] and [rt_newaddr] say.  Every other request declines, as
    does a change request with NLM_F_ECHO (its notification is unicast to
    the sender), a link dump while a device other than a loopback device is
    up, and an address dump while such a device has an address. *)
Definition rt_handle (x : NetNs) (U : list UserNs) (opener caller : IdCred) (dst : bool)
    (port : Z) (dg : list byte) : NlStep :=
  let ifs := netns_ifs x in
  let len := nl_len dg in
  let nl := nl_u32 dg 0 in
  if len <? 16 then SDone None RNone
  else if (nl <? 16) || (len <? nl) then SDone None RNone
  else if 16 <=? len - Z.min (nl_align nl) len then SDecline
  else
    let req := firstn (Z.to_nat nl) dg in
    let ty := nl_u16 dg 4 in
    let fl := nl_u16 dg 6 in
    if (Z.land fl NLM_F_REQUEST =? 0) || (ty <? NLMSG_MIN_TYPE) then SDone None (ack_if fl port req 0)
    else if RTM_MAX <? ty then SDone None (ack_if fl port req EOPNOTSUPP)
    else if nl - 16 <? 1 then SDone None (ack_if fl port req 0)
    else
      let fam := nl_u8 dg 16 in
      let get := Z.land (ty - 16) 3 =? 2 in
      if negb get && negb (net_admin U (netns_owner x) opener caller dst)
      then SDone None (ack_if fl port req EPERM)
      else if negb (netns_sealed x) then SDecline
      else if get then
        if Z.land fl NLM_F_DUMP =? 0 then SDecline
        else if (ty =? RTM_GETLINK) && (fam =? AF_UNSPEC) then
          let p := nl - 16 in
          if negb ((p <=? 4) || ((16 <=? p) && (p <=? 19))) then SDecline
          else if existsb (fun d => is_up d && negb (is_loopback d)) ifs then SDecline
          else SDone None (RLinkDump (req_seq req) port ifs)
        else if (ty =? RTM_GETADDR) && (fam =? AF_INET) then
          if existsb (fun d => negb (is_loopback d) && negb (Nat.eqb (length (if_addrs d)) 0)) ifs
          then SDecline
          else SDone None (RAddrDump (req_seq req) port ifs)
        else SDecline
      else if negb (Z.land fl NLM_F_ECHO =? 0) then SDecline
      else
        let r := if (ty =? RTM_NEWLINK) && (fam =? AF_UNSPEC) then rt_newlink ifs fl req
                 else if (ty =? RTM_NEWADDR) && (fam =? AF_INET) then rt_newaddr ifs fl req
                 else None in
        match r with
        | None => SDecline
        | Some (ifs', e) => SDone ifs' (ack_if fl port req e)
        end.

(* =========================================================================
   Sockets of the namespace model
   ========================================================================= *)

(** The port ids the NETLINK_ROUTE sockets of namespace [n] hold. *)
Definition netlink_ports (st : NsState) (n : positive) : list Z :=
  flat_map (fun p => match nf_kind (snd p) with
                     | NfNetlink n' port _ => if Pos.eqb n' n && negb (port =? 0) then [port] else []
                     | _ => []
                     end) (ns_files st).

(** [netlink_autobind]: the caller's tgid when no socket of the namespace
    holds it, else one of [ROVER_LO, ROVER_HI] that none holds; in a
    namespace that is not sealed a socket the model does not see may hold
    the tgid, so the second answer is admitted there too. *)
Definition autobind_port (sealed : bool) (held : list Z) (tgid p : Z) : Prop :=
  (existsb (Z.eqb tgid) held = false /\ p = tgid)
  \/ ((sealed = false \/ existsb (Z.eqb tgid) held = true)
      /\ ROVER_LO <= p <= ROVER_HI /\ existsb (Z.eqb p) held = false).

Definition is_done_dgram (dg : list byte) : bool :=
  (16 <=? nl_len dg) && (nl_u16 dg 4 =? NLMSG_DONE).

(** A dump is running on a socket while its queue holds NLMSG_DONE behind
    another datagram: the kernel has not produced that last datagram yet. *)
Definition dump_running (q : list (list byte)) : bool :=
  match q with [] => false | _ :: r => existsb is_done_dgram r end.

Definition netns_dump_running (st : NsState) (n : positive) : bool :=
  existsb (fun p => match nf_kind (snd p) with
                    | NfNetlink n' _ q => Pos.eqb n' n && dump_running q
                    | _ => false
                    end) (ns_files st).

Definition netlink_file (f : NsFile) (n : positive) (port : Z) (q : list (list byte)) : NsFile :=
  mkNsFile (NfNetlink n port q) (nf_flags f) (nf_cred f).

(** The caller's credential: its user namespace, its kernel euid and egid
    (the [Model]'s), its effective set. *)
Definition caller_cred (m : Model) (ctx : NsCtx) : IdCred :=
  mkIdCred (cx_user ctx) (bv_unsigned (cr_euid (m_creds m))) (bv_unsigned (cr_egid (m_creds m)))
           (cap_effective (cx_caps ctx)).

(** An answer with writes and a copy-in ledger. *)
Definition ns_out (r : word) (ws : list (word * list byte)) (reads : list (word * nat))
    (m : Model) (ctx : NsCtx) (st : NsState) : ext_outcome :=
  EOk (mkEffectU r ws [] [] [] reads) m ctx st [].

Definition ns_fail (e : Z) (reads : list (word * nat)) (m : Model) (ctx : NsCtx) (st : NsState)
    : ext_outcome :=
  ns_out (errno_ret e) [] reads m ctx st.

Inductive SockRes :=
  | SkFile (h : N) (f : NsFile)
  | SkErr (e : Z)
  | SkDecline.

(** What [CLASS(fd, f)] and [sock_from_file] make of descriptor [fd]: an
    open file of the namespace model that is a socket; -EBADF for no
    descriptor or an O_PATH file ([fdget] refuses FMODE_PATH); -ENOTSOCK
    for any other file; a descriptor of the released model as
    [Net.Socket.sockfd_lookup_errno] answers it, declining a socket there. *)
Definition sock_of (m : Model) (st : NsState) (fd : word) : SockRes :=
  match ns_file_of m st fd with
  | Some (h, f) =>
      match nf_kind f with
      | NfPath _ => SkErr EBADF
      | NfNetlink _ _ _ | NfUnixDgram _ => SkFile h f
      | NfDir _ _ | NfFile _ _ | NfEventfd | NfSignalfd _ | NfUserNsFile _ _ _ | NfMountinfo _ _ _ _ =>
          SkErr ENOTSOCK
      end
  | None =>
      match sockfd_lookup_errno (m_fds m) fd with
      | Some e => SkErr e
      | None => SkDecline
      end
  end.

(* =========================================================================
   socket (198)
   ========================================================================= *)

(** The failures of a socket's creation beside its answer: [sock_alloc]'s
    -ENFILE when [new_inode_pseudo] cannot allocate the socket's inode
    (net/socket.c:632-639, 1570-1575), [sk_alloc]'s -ENOMEM,
    [unix_create1]'s -ENFILE when the AF_UNIX sockets pass twice the
    system-wide file limit (net/unix/af_unix.c:1101-1105), and
    [sock_map_fd]'s table growth (-ENOMEM) and file allocation
    ([alloc_file_pseudo]: -ENOMEM, and [alloc_empty_file]'s -ENFILE at the
    system-wide file limit, fs/file_table.c:248-255, 278). *)
Definition socket_create_errnos : list Z := [ENOMEM; ENFILE].

Definition new_socket_kind (ctx : NsCtx) (fam base pro : Z) : option NsFileKind :=
  if (fam =? AF_NETLINK) && (base =? SOCK_RAW) && (pro =? NETLINK_ROUTE)
  then Some (NfNetlink (cx_net ctx) 0 [])
  else if (fam =? AF_UNIX) && (base =? SOCK_DGRAM) && ((pro =? 0) || (pro =? AF_UNIX))
  then Some (NfUnixDgram (cx_net ctx))
  else None.

(** [socket] (198): [__sys_socket], [__sys_socket_create], [__sock_create],
    [netlink_create] and [__netlink_create] (net/netlink/af_netlink.c),
    [unix_create] (net/unix/af_unix.c), [sock_map_fd].  A flag other than
    SOCK_CLOEXEC and SOCK_NONBLOCK is -EINVAL before anything.  AF_NETLINK
    with SOCK_RAW and NETLINK_ROUTE (always registered: rtnetlink is built
    in), and AF_UNIX with SOCK_DGRAM and protocol 0 or PF_UNIX (CONFIG_UNIX
    built in), make an open file of the task's network namespace at the
    lowest free descriptor, -EMFILE when that is not below RLIMIT_NOFILE;
    the file's [f_flags] are O_RDWR ([sock_alloc_file]) and its [f_cred]
    the caller's; SOCK_CLOEXEC sets the descriptor's close-on-exec mark and
    its absence clears it ([get_unused_fd_flags]).  Kind: exact, with
    [socket_create_errnos] beside the answer.  Declines SOCK_NONBLOCK (the
    socket's file has no non-blocking mode here) and every other family,
    type and protocol. *)
Definition socket_arm : NsArm := fun i m ctx st o =>
  let fam := sint32 (in_arg i 0) in
  let ty := bv_unsigned (abi_low32 (in_arg i 1)) in
  let pro := sint32 (in_arg i 2) in
  let fl := Z.ldiff ty SOCK_TYPE_MASK in
  let base := Z.land ty SOCK_TYPE_MASK in
  if negb (Z.ldiff fl (Z.lor SOCK_CLOEXEC SOCK_NONBLOCK) =? 0) then o = ns_errno EINVAL m ctx st
  else if negb (Z.land fl SOCK_NONBLOCK =? 0) then o = EUnmodeled
  else
    match new_socket_kind ctx fam base pro with
    | None => o = EUnmodeled
    | Some k =>
        let fd := alloc_fd (m_fds m) in
        let h := fresh_handle st in
        (if bv_unsigned fd <? bv_unsigned (m_nofile m)
         then o = EOk (mkEffect fd [] [])
                      (with_fds (fd_insert (m_fds m) fd (ns_fd_entry h)) m)
                      (set_cloexec ctx (bv_unsigned fd) (negb (Z.land fl SOCK_CLOEXEC =? 0)))
                      (with_files st (ns_files st ++ [(h, mkNsFile k O_RDWR (caller_cred m ctx))]))
                      []
         else o = ns_errno EMFILE m ctx st)
        \/ (exists e, errno_in socket_create_errnos e = true /\ o = ns_errno e m ctx st)
    end.

(* =========================================================================
   bind (200)
   ========================================================================= *)

(** [netlink_insert]'s failures other than a held port: the hash table's
    allocation (-ENOMEM, [bucket_table_alloc] in [rhashtable_insert_rehash],
    lib/rhashtable.c:466-470) and its -EBUSY (:458), which
    [netlink_insert] reports as -EOVERFLOW
    (net/netlink/af_netlink.c:573-574). *)
Definition nl_insert_errnos : list Z := [ENOMEM; EOVERFLOW].

(** The port a socket of namespace [x] has once bound: [port] when it has
    one, else what [netlink_autobind] gives the caller. *)
Definition bound_port (st : NsState) (x : NetNs) (ctx : NsCtx) (port p : Z) : Prop :=
  if port =? 0 then
    match task_pid ctx with
    | Some t => autobind_port (netns_sealed x) (netlink_ports st (netns_id x)) t p
    | None => False
    end
  else p = port.

(** [bind] (200) on the netlink socket: [__sys_bind],
    [move_addr_to_kernel], [netlink_bind], [netlink_insert],
    [netlink_autobind].  In order: an address length below 0 or above 128
    is -EINVAL; a length of 0 copies nothing and [netlink_bind]'s 12-byte
    minimum refuses it (-EINVAL); an unreadable address is -EFAULT; below
    12 bytes, or a family other than AF_NETLINK, -EINVAL.  A bound socket
    answers 0 to its own port id and -EINVAL to another.  An unbound socket
    takes the requested port id (-EADDRINUSE when a socket of the
    namespace holds it; in a namespace that is not sealed also when the
    model sees no holder) or, for 0, the port [netlink_autobind] chooses.
    Kind: exact in a sealed namespace, over in another; [nl_insert_errnos]
    beside the success.  Declines multicast groups (nl_groups other than
    0), the AF_UNIX socket, a socket of a namespace the model does not
    hold, and an autobind for a task with no pid in its namespace. *)
Definition bind_arm : NsArm := fun i m ctx st o =>
  let fd := fd32 (in_arg i 0) in
  let addrp := in_arg i 1 in
  let al := sint32 (in_arg i 2) in
  match sock_of m st fd with
  | SkErr e => o = ns_errno e m ctx st
  | SkDecline => o = EUnmodeled
  | SkFile h f =>
      match nf_kind f with
      | NfNetlink n port q =>
          if (al <? 0) || (SOCKADDR_STORAGE_SIZE <? al) || (al =? 0) then o = ns_errno EINVAL m ctx st
          else
            match copy_bytes_map (in_mem i) addrp al with
            | None => o = ns_errno EFAULT m ctx st
            | Some bs =>
                let rd := [(addrp, Z.to_nat al)] in
                if (al <? SOCKADDR_NL_SIZE) || negb (nl_u16 bs 0 =? AF_NETLINK)
                then o = ns_fail EINVAL rd m ctx st
                else if negb (nl_u32 bs 8 =? 0) then o = EUnmodeled
                else
                  let pid := nl_u32 bs 4 in
                  if negb (port =? 0) then
                    o = (if pid =? port then ns_out (Z_to_bv 64 0) [] rd m ctx st
                         else ns_fail EINVAL rd m ctx st)
                  else
                    match find_netns st n with
                    | None => o = EUnmodeled
                    | Some x =>
                        let bound p := ns_out (Z_to_bv 64 0) [] rd m ctx
                                              (set_file st h (netlink_file f n p q)) in
                        if negb (pid =? 0) then
                          if existsb (Z.eqb pid) (netlink_ports st n)
                          then o = ns_fail EADDRINUSE rd m ctx st
                          else o = bound pid
                               \/ (netns_sealed x = false /\ o = ns_fail EADDRINUSE rd m ctx st)
                               \/ (exists e, errno_in nl_insert_errnos e = true
                                             /\ o = ns_fail e rd m ctx st)
                        else
                          match task_pid ctx with
                          | None => o = EUnmodeled
                          | Some _ =>
                              (exists p, bound_port st x ctx 0 p /\ o = bound p)
                              \/ (exists e, errno_in nl_insert_errnos e = true
                                            /\ o = ns_fail e rd m ctx st)
                          end
                    end
            end
      | _ => o = EUnmodeled
      end
  end.

(* =========================================================================
   sendto (206)
   ========================================================================= *)

(** [netlink_alloc_large_skb]'s failure, -ENOBUFS. *)
Definition nl_alloc_errnos : list Z := [ENOBUFS].

(** The request [dg] reaches an rtnetlink handler: the tests [rt_handle]
    makes before one runs hold, and its type is RTM_NEWLINK, RTM_NEWADDR,
    RTM_GETLINK or RTM_GETADDR.  The tests: a header of at least 16 bytes
    that fits the datagram ([netlink_rcv_skb] drops it otherwise,
    net/netlink/af_netlink.c); NLM_F_REQUEST; a payload of at least one
    byte ([rtnetlink_rcv_msg] answers 0 before any handler otherwise,
    net/core/rtnetlink.c); and for RTM_NEWLINK and RTM_NEWADDR,
    CAP_NET_ADMIN ([rtnetlink_rcv_msg]'s -EPERM otherwise).  [sendto]
    asks it only of a request [rt_handle] answers, which then reaches its
    type's handler or dump. *)
Definition handler_reached (x : NetNs) (U : list UserNs) (opener caller : IdCred) (dst : bool)
    (dg : list byte) : bool :=
  let nl := nl_u32 dg 0 in
  let ty := nl_u16 dg 4 in
  (16 <=? nl) && (nl <=? nl_len dg) && (1 <=? nl - 16)
  && negb (Z.land (nl_u16 dg 6) NLM_F_REQUEST =? 0)
  && ((ty =? RTM_GETLINK) || (ty =? RTM_GETADDR)
      || (((ty =? RTM_NEWLINK) || (ty =? RTM_NEWADDR))
          && net_admin U (netns_owner x) opener caller dst)).

(** The errno a reached handler of request type [ty] returns when an
    allocation fails, Linux 6.18.44:
    - RTM_NEWLINK: ENOMEM, from [rtnl_newlink]'s first step, the
      [kmalloc] of its attribute table (net/core/rtnetlink.c);
    - RTM_NEWADDR: ENOBUFS, which [inet_rtm_to_ifa] sets before its
      [inet_alloc_ifa] (net/ipv4/devinet.c).  Over: a request that
      [inet_validate_rtm] refuses, whose address is 0 or whose device is
      absent does not get there;
    - RTM_GETLINK and RTM_GETADDR dumps: ENOBUFS, the one allocation error
      of [netlink_dump], which [__netlink_dump_start] runs for the dump's
      first part (net/netlink/af_netlink.c).
    [netlink_rcv_skb] acknowledges the request with that error
    ([netlink_ack]) and [sendto] still returns the length.  A change
    leaves the namespace as it was.  A dump keeps running:
    [__netlink_dump_start] set [cb_running] before the failed
    [netlink_dump], and [netlink_recvmsg] runs the dump again from its
    first part once the acknowledgement is read, so its datagrams follow
    the acknowledgement.  The environment's refusal, carried in the
    acknowledgement: the forced-only filter reads it in the state after
    the call ([nl_alloc_after]) and removes it (SCOPE.md). *)
Definition nl_handler_errnos (ty : Z) : list Z :=
  if ty =? RTM_NEWLINK then [ENOMEM]
  else if (ty =? RTM_NEWADDR) || (ty =? RTM_GETLINK) || (ty =? RTM_GETADDR) then [ENOBUFS]
  else [].

(** A reply that is a dump. *)
Definition reply_dumps (r : NlReply) : bool :=
  match r with RLinkDump _ _ _ | RAddrDump _ _ _ => true | RNone | RAck _ => false end.

(** The acknowledgement of request [dg] from port [port] with its handler's
    error [e] ([netlink_ack] of the request's first message). *)
Definition handler_fail_ack (port : Z) (dg : list byte) (e : Z) : list byte :=
  nl_ack port (firstn (Z.to_nat (nl_u32 dg 0)) dg) e.

(** Does the request [rt_handle] judges decline under the queue rules (see
    the header), whatever port answers it? *)
Definition rt_declines (st : NsState) (x : NetNs) (U : list UserNs) (opener caller : IdCred)
    (dst : bool) (q : list (list byte)) (dg : list byte) : bool :=
  match rt_handle x U opener caller dst 0 dg with
  | SDecline => true
  | SDone ifs r =>
      (reply_queues r && negb (Nat.eqb (length q) 0))
      || (match ifs with Some _ => netns_dump_running st (netns_id x) | None => false end)
  end.

(** The netlink part of [sendto], once [import_ubuf] and the descriptor
    have passed: [__sys_sendto]'s address copy ([move_addr_to_kernel]),
    then [netlink_sendmsg]: MSG_OOB is -EOPNOTSUPP, a length of 0
    -ENODATA; an address shorter than [struct sockaddr_nl] or of another
    family -EINVAL; a destination port or group without CAP_NET_ADMIN over
    the namespace's owner -EPERM ([netlink_allowed]); an unbound socket is
    bound ([netlink_autobind], kept whatever follows); the buffer is
    copied (-EFAULT when it cannot be read) and handed to the kernel's
    socket, whose answer [rt_handle] gives; the call returns the length. *)
Definition netlink_sendto (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState) (h : N)
    (f : NsFile) (n : positive) (port : Z) (q : list (list byte)) (buf : word) (len fl : Z)
    (addrp : word) (al : Z) (o : ext_outcome) : Prop :=
  let has_addr := negb (bv_unsigned addrp =? 0) in
  if has_addr && ((al <? 0) || (SOCKADDR_STORAGE_SIZE <? al)) then o = ns_errno EINVAL m ctx st
  else
    let copy := has_addr && (0 <? al) in
    match (if copy then copy_bytes_map (in_mem i) addrp al else Some []) with
    | None => o = ns_errno EFAULT m ctx st
    | Some nm =>
        let rd0 := if copy then [(addrp, Z.to_nat al)] else [] in
        let namelen := if has_addr then al else 0 in
        if negb (Z.land fl MSG_OOB =? 0) then o = ns_fail EOPNOTSUPP rd0 m ctx st
        else if len =? 0 then o = ns_fail ENODATA rd0 m ctx st
        else if negb (namelen =? 0) && ((namelen <? SOCKADDR_NL_SIZE) || negb (nl_u16 nm 0 =? AF_NETLINK))
        then o = ns_fail EINVAL rd0 m ctx st
        else
          let dpid := if namelen =? 0 then 0 else nl_u32 nm 4 in
          let dgrp := if namelen =? 0 then 0 else nl_u32 nm 8 in
          let dst := negb (namelen =? 0) in
          let caller := caller_cred m ctx in
          match find_netns st n with
          | None => o = EUnmodeled
          | Some x =>
              if negb ((dpid =? 0) && (dgrp =? 0))
                 && negb (cap_capable (ns_userns st) caller (netns_owner x) CAP_NET_ADMIN)
              then o = ns_fail EPERM rd0 m ctx st
              else if (NL_SEND_MAX <? len) || negb ((dpid =? 0) && (dgrp =? 0)) then o = EUnmodeled
              else if (port =? 0) && match task_pid ctx with None => true | Some _ => false end
              then o = EUnmodeled
              else
                let dgo := read_bytes_map (in_mem i) buf (Z_to_bv 64 len) in
                if match dgo with
                   | Some dg => rt_declines st x (ns_userns st) (nf_cred f) caller dst q dg
                   | None => false
                   end
                then o = EUnmodeled
                else
                  ((port =? 0) = true
                   /\ exists e, errno_in nl_insert_errnos e = true /\ o = ns_fail e rd0 m ctx st)
                  \/ exists p, bound_port st x ctx port p /\
                     let st1 := set_file st h (netlink_file f n p q) in
                     ((exists e, errno_in nl_alloc_errnos e = true /\ o = ns_fail e rd0 m ctx st1)
                      \/ match dgo with
                         | None => o = ns_fail EFAULT rd0 m ctx st1
                         | Some dg =>
                             let sent st' qs := ns_out (Z_to_bv 64 len) [] (rd0 ++ [(buf, Z.to_nat len)]) m ctx
                                                       (set_file st' h (netlink_file f n p (q ++ qs))) in
                             let fails e := handler_reached x (ns_userns st) (nf_cred f) caller dst dg = true
                                            /\ errno_in (nl_handler_errnos (nl_u16 dg 4)) e = true in
                             match rt_handle x (ns_userns st) (nf_cred f) caller dst p dg with
                             | SDecline => False
                             | SDone ifs r =>
                                 (exists env dgs,
                                   nl_env_ok (env_nl_link_max (ns_env st)) env r = true /\
                                   reply_dgrams env r = Some dgs /\
                                   (o = sent (match ifs with
                                              | Some l => set_netns_ifs st n l
                                              | None => st
                                              end) dgs
                                    \/ (reply_dumps r = true
                                        /\ exists e, fails e /\ o = sent st (handler_fail_ack p dg e :: dgs))
                                    \/ (exists l, ifs = Some l /\ lo_comes_up (netns_ifs x) l = true
                                        /\ o = sent (set_netns_ifs st n (lo_up_noaddr (netns_ifs x) l)) dgs)))
                                 \/ (reply_dumps r = false
                                     /\ exists e, fails e /\ o = sent st [handler_fail_ack p dg e])
                             end
                         end)
          end
    end.

(** [sendto] (206) on the netlink socket: [__sys_sendto] with
    [import_ubuf] (the length capped at MAX_RW_COUNT; -EFAULT for a buffer
    [access_ok] refuses) before the descriptor, then [netlink_sendto].
    Kind: exact on the namespace's new state and on acknowledgements, over
    on dump replies ([NlEnv], within [nl_env_ok]); [nl_insert_errnos] (an
    autobind) and [nl_alloc_errnos] beside the answer; beside a request
    that reaches an rtnetlink handler ([handler_reached]), the
    acknowledgement of its allocation failure ([nl_handler_errnos]) with
    the namespace unchanged and, for a dump, the dump behind it; and beside
    a request that brings a loopback device up, the same answer with the
    device up and no address added, when [inetdev_event]'s
    [inet_alloc_ifa] fails ([lo_up_noaddr]).  Those last two are the
    environment's allocation failures whose effect is the answer's own
    (the length): only the state after the call shows them
    ([nl_alloc_after]), and there the forced-only filter removes them
    (SCOPE.md).
    Declines: the AF_UNIX socket; a
    destination other than the kernel (a port or a group); a request longer
    than [NL_SEND_MAX]; an autobind for a task with no pid in its
    namespace; what [rt_handle] declines; a request that would queue while
    the queue is not empty, or change a namespace in which a dump is
    running. *)
Definition sendto_arm : NsArm := fun i m ctx st o =>
  let fd := fd32 (in_arg i 0) in
  let buf := in_arg i 1 in
  let len := Z.min (bv_unsigned (in_arg i 2)) MAX_RW_COUNT in
  let fl := bv_unsigned (abi_low32 (in_arg i 3)) in
  let addrp := in_arg i 4 in
  let al := sint32 (in_arg i 5) in
  if negb (access_okb buf len) then o = ns_errno EFAULT m ctx st
  else
    match sock_of m st fd with
    | SkErr e => o = ns_errno e m ctx st
    | SkDecline => o = EUnmodeled
    | SkFile h f =>
        match nf_kind f with
        | NfNetlink n port q => netlink_sendto i m ctx st h f n port q buf len fl addrp al o
        | _ => o = EUnmodeled
        end
    end.

(** [a] is the acknowledgement of a handler's allocation failure
    ([handler_fail_ack]): an NLMSG_ERROR message whose error, at byte 16,
    is an errno [nl_handler_errnos] lists for the type of the request.
    [nl_ack] puts the request's header from byte 20: its length at bytes
    20-23, its type at bytes 24-25. *)
Definition nl_fail_ack_alloc (a : list byte) : bool :=
  (36 <=? nl_len a) && (nl_u16 a 4 =? NLMSG_ERROR)
  && errno_in (nl_handler_errnos (nl_u16 a 24)) (4294967296 - nl_u32 a 16).

(** THE ALLOCATION FAILURES [sendto] SHOWS ONLY IN THE STATE AFTER IT.  Two
    answers of [netlink_sendto] are reached only when an allocation of the
    kernel fails, and their effect is the answer's own (the request's
    length).  Linux v6.18.46:
    - a loopback device brought up without 127.0.0.1/8 ([lo_up_noaddr]):
      [inetdev_event]'s NETDEV_UP arm adds the address only when
      [inet_alloc_ifa] returns one (net/ipv4/devinet.c:1613-1629), which it
      does unless its [kzalloc] fails (devinet.c:208-214).  The arm's other
      way to leave the address out, an MTU below 68 (devinet.c:1611-1612),
      never holds of the model's loopback device, whose MTU is
      [gen_lo_setup]'s (drivers/net/loopback.c:168) and which no arm
      changes; and where [inet_insert_ifa] refuses the address
      (devinet.c:515-525) the answer with the address adds nothing either
      ([lo_up_addrs]), so [lo_up_without_addr] does not hold.
    - the acknowledgement of a handler's allocation failure
      ([nl_handler_errnos]): RTM_NEWLINK's -ENOMEM is [rtnl_newlink]'s
      [kmalloc] (net/core/rtnetlink.c:4010-4012); no other step of a
      request the model answers returns it ([rtnetlink_rcv_msg],
      rtnetlink.c:6897-7010; [__rtnl_newlink], [rtnl_changelink] and
      [do_setlink], 3060-3185 and 3738-3997; [__dev_open],
      net/core/dev.c:1660-1709, whose NETDEV_PRE_UP notifiers refuse a
      loopback device nothing).  RTM_NEWADDR's -ENOBUFS is
      [inet_rtm_to_ifa]'s (devinet.c:900-910): a device without an
      [in_dev], which a registered loopback device always has
      (devinet.c:1588-1596: a failed [inetdev_init] fails the
      registration), or [inet_alloc_ifa]'s failed [kzalloc];
      [__inet_insert_ifa] returns -EEXIST, -EINVAL or an ipvlan
      validator's errno (devinet.c:490-569).  A dump's -ENOBUFS is
      [netlink_dump]'s failed [alloc_skb]
      (net/netlink/af_netlink.c:2269, 2288-2300); its two other
      -ENOBUFS are not reached here: the receive-buffer test
      (af_netlink.c:2302-2307) needs a receive queue that is not empty,
      where the model declines the request ([rt_declines]), and
      [netlink_dump_done]'s (af_netlink.c:2239-2242) has the tailroom
      that af_netlink.c:2346-2347 checks.
    [nl_alloc_after i m st st'] says that [st'], a state [sendto] [i]
    leaves from [st], shows one of them: a loopback device of some
    namespace came up without its address ([lo_up_without_addr]), or the
    first datagram the call queued on its socket is such an
    acknowledgement ([nl_fail_ack_alloc]).  No answer reached without an
    allocation failing leaves either: [set_link_flags] adds the address,
    and the acknowledgements [rt_handle] gives carry 0, -EOPNOTSUPP,
    -EPERM, -EINVAL, -EEXIST or -ENODEV. *)
Definition nl_alloc_after (i : SyscallInput) (m : Model) (st st' : NsState) : bool :=
  existsb (fun x' => match find_netns st (netns_id x') with
                     | Some x => lo_up_without_addr (netns_ifs x) (netns_ifs x')
                     | None => false
                     end) (ns_netns st')
  || match sock_of m st (fd32 (in_arg i 0)) with
     | SkFile h f =>
         match nf_kind f, lookup_file (ns_files st') h with
         | NfNetlink _ _ q, Some f' =>
             match nf_kind f' with
             | NfNetlink _ _ q' =>
                 match skipn (length q) q' with
                 | a :: _ => nl_fail_ack_alloc a
                 | [] => false
                 end
             | _ => false
             end
         | _, _ => false
         end
     | _ => false
     end.

(* =========================================================================
   recvfrom (207)
   ========================================================================= *)

Definition RECV_FLAGS_KNOWN : Z := MSG_OOB + MSG_PEEK + MSG_TRUNC + MSG_DONTWAIT.

(** The sender of every datagram the kernel queues ([NETLINK_CB] of a
    kernel-made skb is zero): AF_NETLINK, port 0, no group. *)
Definition kernel_sockaddr : list byte :=
  nl_le16 AF_NETLINK ++ nl_le16 0 ++ nl_le32 0 ++ nl_le32 0.

(** [recvfrom] (207) on the netlink socket: [__sys_recvfrom] with
    [import_ubuf] (capped length; -EFAULT for a refused buffer) before the
    descriptor, [netlink_recvmsg], [move_addr_to_user].  MSG_OOB is
    -EOPNOTSUPP.  The first queued datagram is copied, cut to the buffer,
    and taken off the queue (left there under MSG_PEEK); the call returns
    the bytes copied, or the datagram's length under MSG_TRUNC.  With an
    address, the address length is read (-EFAULT), 12 written back unless
    it is negative (then -EINVAL after the copy), and the first bytes of
    [kernel_sockaddr] copied.  An empty queue is -EAGAIN under MSG_DONTWAIT
    or O_NONBLOCK.  Kind: exact.  Declines: an empty queue for a blocking
    socket ([netlink_recvmsg] waits for a datagram that no task of the
    model will cause); flags other than MSG_OOB, MSG_PEEK, MSG_TRUNC and
    MSG_DONTWAIT; a destination the task cannot write; the AF_UNIX
    socket. *)
Definition recvfrom_arm : NsArm := fun i m ctx st o =>
  let fd := fd32 (in_arg i 0) in
  let ubuf := in_arg i 1 in
  let size := Z.min (bv_unsigned (in_arg i 2)) MAX_RW_COUNT in
  let fl := bv_unsigned (abi_low32 (in_arg i 3)) in
  let addrp := in_arg i 4 in
  let alenp := in_arg i 5 in
  if negb (access_okb ubuf size) then o = ns_errno EFAULT m ctx st
  else
    match sock_of m st fd with
    | SkErr e => o = ns_errno e m ctx st
    | SkDecline => o = EUnmodeled
    | SkFile h f =>
        match nf_kind f with
        | NfNetlink n port q =>
            if negb (Z.ldiff fl RECV_FLAGS_KNOWN =? 0) then o = EUnmodeled
            else if negb (Z.land fl MSG_OOB =? 0) then o = ns_errno EOPNOTSUPP m ctx st
            else
              match q with
              | [] =>
                  if negb (Z.land fl MSG_DONTWAIT =? 0) || negb (Z.land (nf_flags f) O_NONBLOCK =? 0)
                  then o = ns_errno EAGAIN m ctx st
                  else o = EUnmodeled
              | d :: rest =>
                  let copied := Z.min size (nl_len d) in
                  let ret := Z_to_bv 64 (if Z.land fl MSG_TRUNC =? 0 then copied else nl_len d) in
                  let st' := if Z.land fl MSG_PEEK =? 0 then set_file st h (netlink_file f n port rest)
                             else st in
                  let data := (ubuf, firstn (Z.to_nat copied) d) in
                  match read_bytes_map (in_wmem i) ubuf (Z_to_bv 64 copied) with
                  | None => o = EUnmodeled
                  | Some _ =>
                      if bv_unsigned addrp =? 0 then o = ns_out ret [data] [] m ctx st'
                      else
                        match get_u32 i alenp with
                        | GetFault => o = ns_out (errno_ret EFAULT) [data] [] m ctx st'
                        | GetUnmapped => o = EUnmodeled
                        | GetVal v =>
                            let l := Z.min (s32 (Z_to_bv 64 v)) SOCKADDR_NL_SIZE in
                            let rd := [(alenp, 4%nat)] in
                            if l <? 0 then o = ns_out (errno_ret EINVAL) [data] rd m ctx st'
                            else
                              match put_ok i alenp 4 with
                              | PutFault => o = ns_out (errno_ret EFAULT) [data] rd m ctx st'
                              | PutPartial => o = EUnmodeled
                              | PutOk =>
                                  if l =? 0 then
                                    o = ns_out ret [data; (alenp, u32_bytes SOCKADDR_NL_SIZE)] rd m ctx st'
                                  else match put_ok i addrp l with
                                       | PutFault =>
                                           o = ns_out (errno_ret EFAULT)
                                                 [data; (alenp, u32_bytes SOCKADDR_NL_SIZE)] rd m ctx st'
                                       | PutPartial => o = EUnmodeled
                                       | PutOk =>
                                           o = ns_out ret
                                                 ([data; (alenp, u32_bytes SOCKADDR_NL_SIZE);
                                                   (addrp, firstn (Z.to_nat l) kernel_sockaddr)])
                                                 rd m ctx st'
                                       end
                              end
                        end
                  end
              end
        | _ => o = EUnmodeled
        end
    end.

(* =========================================================================
   ioctl (29)
   ========================================================================= *)

(** The initial user namespace: the one with no parent. *)
Definition init_userns (st : NsState) : option positive :=
  option_map uns_id (List.find (fun u => match uns_parent u with None => true | Some _ => false end)
                               (ns_userns st)).

(** [dev_load] may load a module for a name no device has: the caller holds
    CAP_NET_ADMIN or CAP_SYS_MODULE over the initial user namespace
    ([capable]). *)
Definition may_load_module (st : NsState) (m : Model) (ctx : NsCtx) : bool :=
  match init_userns st with
  | Some u => cap_capable (ns_userns st) (caller_cred m ctx) u CAP_NET_ADMIN
              || cap_capable (ns_userns st) (caller_cred m ctx) u CAP_SYS_MODULE
  | None => true
  end.

(** SIOCGIFINDEX on a socket of namespace [n]: [get_user_ifreq] copies the
    40-byte [struct ifreq] (-EFAULT), [dev_ioctl] ends the name at byte 15
    and at a ':', [dev_ifsioc_locked] answers the device's index (-ENODEV
    when no device has the name), and [put_user_ifreq] writes the 40 bytes
    back: the name with byte 15 cleared, [ifr_ifindex] at byte 16, the rest
    as copied.  Declines a name no device has when [dev_load] may load a
    module, which can make one; a namespace the model does not hold; a
    structure the task cannot write. *)
Definition siocgifindex (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState) (n : positive)
    (arg : word) (o : ext_outcome) : Prop :=
  match copy_bytes_map (in_mem i) arg IFREQ_SIZE with
  | None => o = ns_errno EFAULT m ctx st
  | Some ifr =>
      let rd := [(arg, Z.to_nat IFREQ_SIZE)] in
      match find_netns st n with
      | None => o = EUnmodeled
      | Some x =>
          match if_by_name (netns_ifs x) (upto_colon (c_string (firstn 15 ifr))) with
          | Some d =>
              match put_ok i arg IFREQ_SIZE with
              | PutFault => o = ns_fail EFAULT rd m ctx st
              | PutPartial => o = EUnmodeled
              | PutOk =>
                  o = ns_out (Z_to_bv 64 0)
                        [(arg, firstn 15 ifr ++ [Z_to_bv 8 0] ++ u32_bytes (if_index d) ++ skipn 20 ifr)]
                        rd m ctx st
              end
          | None =>
              if may_load_module st m ctx then o = EUnmodeled
              else o = ns_fail ENODEV rd m ctx st
          end
      end
  end.

(** [ioctl] (29) SIOCGIFINDEX: the ioctl entry's [fdget] (-EBADF for no
    descriptor and an O_PATH file), [do_vfs_ioctl] (no generic command
    matches), [vfs_ioctl] to [sock_ioctl], [sock_do_ioctl]: [unix_ioctl]
    and [netlink_ioctl] answer -ENOIOCTLCMD, so the command goes to
    [dev_ioctl] in the socket's network namespace ([siocgifindex]).  Kind:
    exact.  Declines every other command, and every descriptor that is not
    one of the two sockets but for -EBADF. *)
Definition ioctl_arm : NsArm := fun i m ctx st o =>
  let fd := fd32 (in_arg i 0) in
  let cmd := bv_unsigned (cmd32 (in_arg i 1)) in
  let arg := in_arg i 2 in
  match ns_file_of m st fd with
  | Some (_, f) =>
      match nf_kind f with
      | NfPath _ => o = ns_errno EBADF m ctx st
      | NfUnixDgram n | NfNetlink n _ _ =>
          if cmd =? SIOCGIFINDEX then siocgifindex i m ctx st n arg o else o = EUnmodeled
      | NfDir _ _ | NfFile _ _ | NfEventfd | NfSignalfd _ | NfUserNsFile _ _ _ | NfMountinfo _ _ _ _ =>
          o = EUnmodeled
      end
  | None =>
      match fd_lookup (m_fds m) fd with
      | None => o = ns_errno EBADF m ctx st
      | Some _ => o = EUnmodeled
      end
  end.

(** A pending error of the socket that [recvfrom] reports first
    ([__skb_try_recv_datagram]'s [sock_error], net/core/datagram.c):
    ENOBUFS, which [netlink_ack] stores when it cannot allocate the
    acknowledgement, [netlink_overrun] when the kernel's answer does not fit
    the receive buffer, and [netlink_recvmsg] when the next part of a dump
    cannot be allocated or queued ([netlink_dump]) (net/netlink/af_netlink.c). *)
Definition nl_pending_errnos : list Z := [ENOBUFS].

(** The environment's refusals of the net arms, Linux 6.18.44; an arm with
    a row admits the row's errnos after any answer ([Arm.with_injected]),
    and where the kernel's order matters the arm places them itself.
    - [socket]: [socket_create_errnos].  Their ENFILE has two causes, so it
      is in two families ([Arm.NsInjected]): [sock_alloc]'s inode, an
      allocation (FamAlloc), and the file limits of [alloc_empty_file] and
      [unix_create1], counts of the file table (FamFd, as in
      [Files.open_pairs]).  The released [socket] row (AF_INET sockets,
      [Run.injected_table]) gives its ENOMEM, EMFILE and ENFILE the one
      family FamFd: the two worlds agree on ENFILE's FamFd, and that row
      cannot also give [sock_alloc]'s ENFILE and the ENOMEMs FamAlloc while
      it has one family (a released FamAlloc row needs the budget
      dispatcher, [Run.alloc_family_dispatched]).
    - [bind]: [netlink_insert]'s [nl_insert_errnos], by cause
      ([nl_insert_pairs]).  [sendto]: [netlink_autobind]'s
      [nl_insert_errnos], and [netlink_sendmsg]'s [nl_alloc_errnos].
    - [recvfrom]: [nl_pending_errnos].
    - none for [ioctl]: SIOCGIFINDEX allocates nothing ([dev_ioctl],
      net/core/dev_ioctl.c).
    Each row also lists the errnos its arm answers from the tables
    ([Arm.ni_answers]); [sock_of]'s EBADF and ENOTSOCK among them. *)
Definition socket_injected : NsInjected :=
  mkNsInjected 198 [(errno_in socket_create_errnos, FamAlloc); (errno_in [ENFILE], FamFd)]
               [EINVAL; EMFILE] [].

(** [nl_insert_errnos] by kernel cause: the ENOMEM of
    [bucket_table_alloc] is an allocation (FamAlloc); the EOVERFLOW of the
    table's -EBUSY is the table's state (FamNet).  No released row answers
    them: the released model makes no netlink socket, and its [bind] row
    (FamNet) is [inet_csk_get_port]'s EADDRINUSE. *)
Definition nl_insert_pairs : list ((Z -> bool) * SpuriousFamily) :=
  [(errno_in [ENOMEM], FamAlloc); (errno_in [EOVERFLOW], FamNet)].

Definition bind_injected : NsInjected :=
  mkNsInjected 200 nl_insert_pairs [EBADF; ENOTSOCK; EINVAL; EFAULT; EADDRINUSE] [].
Definition sendto_injected : NsInjected :=
  mkNsInjected 206 (nl_insert_pairs ++ [(errno_in nl_alloc_errnos, FamAlloc)])
               [EFAULT; EBADF; ENOTSOCK; EINVAL; EOPNOTSUPP; ENODATA; EPERM] [].
Definition recvfrom_injected : NsInjected :=
  mkNsInjected 207 [(errno_in nl_pending_errnos, FamAlloc)]
               [EFAULT; EBADF; ENOTSOCK; EOPNOTSUPP; EAGAIN; EINVAL] [].

(** The five arms by call number, for [Spec.ns_table], each with its row's
    refusals. *)
Definition net_arms : list (Z * NsArm) :=
  [(29, ioctl_arm); (198, with_injected (ni_errno socket_injected) socket_arm);
   (200, with_injected (ni_errno bind_injected) bind_arm);
   (206, with_injected (ni_errno sendto_injected) sendto_arm);
   (207, with_injected (ni_errno recvfrom_injected) recvfrom_arm)].

Definition net_injected : list NsInjected :=
  [socket_injected; bind_injected; sendto_injected; recvfrom_injected].

(* =========================================================================
   Deterministic functional cores for checks
   ========================================================================= *)

(** The descriptor-independent part of [__sys_socket],
    [__sys_socket_create], [netlink_create] and [unix_create].  The arm
    below adds the lowest free descriptor, f_cred and its state update. *)
Inductive SocketFn :=
  | SfNetlink (cloexec : bool)
  | SfUnixDgram (cloexec : bool)
  | SfErr (e : Z)
  | SfDecline.

Definition socket_fn (fam ty pro : Z) : SocketFn :=
  let fl := Z.ldiff ty SOCK_TYPE_MASK in
  let base := Z.land ty SOCK_TYPE_MASK in
  if negb (Z.ldiff fl (Z.lor SOCK_CLOEXEC SOCK_NONBLOCK) =? 0) then SfErr EINVAL
  else if negb (Z.land fl SOCK_NONBLOCK =? 0) then SfDecline
  else if (fam =? AF_NETLINK) && (base =? SOCK_RAW) && (pro =? NETLINK_ROUTE)
       then SfNetlink (negb (Z.land fl SOCK_CLOEXEC =? 0))
  else if (fam =? AF_UNIX) && (base =? SOCK_DGRAM) && ((pro =? 0) || (pro =? AF_UNIX))
       then SfUnixDgram (negb (Z.land fl SOCK_CLOEXEC =? 0))
  else SfDecline.

(** The address checks of [netlink_bind], after [__sys_bind] resolved a
    NETLINK_ROUTE descriptor and copied [bs].  A group subscription is a
    deliberate decline; [bind_arm] adds existing-port and autobind state. *)
Inductive BindFn :=
  | BfPort (port : Z)
  | BfErr (e : Z)
  | BfDecline.

Definition bind_fn (al : Z) (bs : list byte) : BindFn :=
  if (al <? 0) || (SOCKADDR_STORAGE_SIZE <? al) || (al =? 0) then BfErr EINVAL
  else if (al <? SOCKADDR_NL_SIZE) || negb (nl_u16 bs 0 =? AF_NETLINK) then BfErr EINVAL
  else if negb (nl_u32 bs 8 =? 0) then BfDecline
  else BfPort (nl_u32 bs 4).

(** [rtnetlink_rcv_msg] as a deterministic core once the caller, opener,
    namespace, port and one copied datagram are given.  [sendto_arm] adds
    autobind, the user-copy ledger, injected allocation refusals and queue
    state. *)
Definition sendto_fn := rt_handle.

(** The queue part of [netlink_recvmsg], before its user-memory copies.
    [RfWait] is the blocking empty-queue branch that [recvfrom_arm]
    declines. *)
Inductive RecvFn :=
  | RfData (ret : Z) (copied : list byte) (q : list (list byte))
  | RfErr (e : Z)
  | RfWait
  | RfDecline.

Definition recvfrom_fn (q : list (list byte)) (size fl : Z) : RecvFn :=
  if negb (Z.ldiff fl RECV_FLAGS_KNOWN =? 0) then RfDecline
  else if negb (Z.land fl MSG_OOB =? 0) then RfErr EOPNOTSUPP
  else match q with
       | [] => if negb (Z.land fl MSG_DONTWAIT =? 0) then RfErr EAGAIN else RfWait
       | d :: rest =>
           let n := Z.min size (nl_len d) in
           RfData (if Z.land fl MSG_TRUNC =? 0 then n else nl_len d)
                  (firstn (Z.to_nat n) d)
                  (if Z.land fl MSG_PEEK =? 0 then rest else q)
       end.

(** [dev_ioctl]'s SIOCGIFINDEX lookup after [get_user_ifreq] and its
    name truncations.  The arm applies [dev_load]'s capability-dependent
    unknown-name rule and constructs the ifreq write-back. *)
Definition ifindex_fn (ifs : list NetIf) (ifr : list byte) : option Z :=
  option_map if_index (if_by_name ifs (upto_colon (c_string (firstn 15 ifr)))).

(** [CLASS(fd, f)] followed by [sock_from_file]'s first two outcomes. *)
Definition socket_fd_fn (open is_socket : bool) : option Z :=
  if negb open then Some EBADF else if negb is_socket then Some ENOTSOCK else None.
