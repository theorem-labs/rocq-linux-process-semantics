(** * LinuxProcessSem.Checks.Cases.Ns.NetCases — the observable netlink core

    These cases compute the deterministic cores of the namespace network
    arms.  [socket_fn], [bind_fn], [sendto_fn], [recvfrom_fn], [ifindex_fn]
    and [socket_fd_fn] keep the chosen outcome and its observable state
    separate from the arms' environment refusals and full [Model] updates.
    The arms in [Ns.Net] connect each core to descriptors, user memory and
    the namespace state. *)

From Stdlib Require Import ZArith List Bool NArith PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Userns Ext Arm Net.
Import ListNotations.
Local Open Scope Z_scope.

Definition bs (l : list Z) : list byte := map (Z_to_bv 8) l.

(** A fresh namespace has down loopback at index 1 and renumbers fallback
    devices from index 2 without carrying their addresses. *)
Example new_netns_loopback : new_netns 2 2 [] = mkNetNs 2 2 [loopback_if] true := eq_refl.

Example new_netns_fallback :
  netns_ifs (new_netns 2 2 [mkNetIf 9 (bs [115; 105; 116; 48]) (IFF_UP + IFF_NOARP) [(167772161, 8)]])
  = [loopback_if; mkNetIf 2 (bs [115; 105; 116; 48]) IFF_NOARP []] := eq_refl.

(* =========================================================================
   socket and bind
   ========================================================================= *)

(** socket(AF_NETLINK, SOCK_RAW | SOCK_CLOEXEC, NETLINK_ROUTE) selects the
    route-socket kind and records close-on-exec. *)
Example socket_netlink : socket_fn AF_NETLINK (SOCK_RAW + SOCK_CLOEXEC) NETLINK_ROUTE = SfNetlink true.
Proof. vm_compute. reflexivity. Qed.

(** socket(AF_UNIX, SOCK_DGRAM | SOCK_CLOEXEC, 0) selects an AF_UNIX
    datagram socket. *)
Example socket_unix : socket_fn AF_UNIX (SOCK_DGRAM + SOCK_CLOEXEC) 0 = SfUnixDgram true.
Proof. vm_compute. reflexivity. Qed.

(** A family or type the model does not hold declines. *)
Example socket_refused : socket_fn 10 SOCK_DGRAM 0 = SfDecline.
Proof. vm_compute. reflexivity. Qed.

Definition nl_addr0 : list byte := bs [16; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0].

(** bind of sockaddr_nl { AF_NETLINK, pid 0, groups 0 } asks the arm to
    autobind the socket. *)
Example bind_autobind : bind_fn 12 nl_addr0 = BfPort 0.
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   RTM_NEWADDR and its acknowledgement
   ========================================================================= *)

Definition lo (flags : Z) (addrs : list (Z * Z)) : NetIf := mkNetIf 1 lo_name flags addrs.
Definition lo_addr : Z * Z := (2130706433, 8).

(** RTM_NEWADDR, request|ack|excl|create, sequence 1: IFA_LOCAL and
    IFA_ADDRESS both hold 127.0.0.1/8 on ifindex 1. *)
Definition newaddr_req : list byte :=
  bs [40; 0; 0; 0; 20; 0; 5; 6; 1; 0; 0; 0; 0; 0; 0; 0;
      2; 8; 128; 254; 1; 0; 0; 0;
      8; 0; 2; 0; 127; 0; 0; 1;
      8; 0; 1; 0; 127; 0; 0; 1].

(** The address core adds 127.0.0.1/8 to loopback. *)
Example newaddr_changes_loopback :
  match rt_newaddr [lo IFF_LOOPBACK []] 1541 newaddr_req with
  | Some (Some (d :: []), 0) =>
      match if_addrs d with
      | (a, p) :: [] => (if_index d =? 1) && (a =? 2130706433) && (p =? 8)
      | _ => false
      end
  | _ => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** A successful acknowledgement is NLMSG_ERROR, capped, sequence 1 and
    port 2, with error zero and the request header. *)
Definition newaddr_ack : list byte :=
  bs [36; 0; 0; 0; 2; 0; 0; 1; 1; 0; 0; 0; 2; 0; 0; 0;
      0; 0; 0; 0;
      40; 0; 0; 0; 20; 0; 5; 6; 1; 0; 0; 0; 0; 0; 0; 0].

Example newaddr_ack_bytes :
  let a := nl_ack 2 newaddr_req 0 in
  ((nl_len a =? 36) && (nl_u16 a 4 =? NLMSG_ERROR) && (nl_u16 a 6 =? NLM_F_CAPPED)
   && (nl_u32 a 8 =? 1) && (nl_u32 a 12 =? 2) && (nl_u32 a 16 =? 0)) = true.
Proof. vm_compute. reflexivity. Qed.

(** recvfrom takes the first queued acknowledgement, returns all 36 bytes,
    and leaves an empty queue. *)
Example recvfrom_ack :
  match recvfrom_fn [newaddr_ack] 1024 0 with
  | RfData ret got [] => (ret =? 36) && (nl_len got =? 36) && (nl_u32 got 0 =? 36)
  | _ => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** An empty blocking receive waits, so the full arm declines it. *)
Example recvfrom_empty_waits : recvfrom_fn [] 1024 0 = RfWait.
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   RTM_NEWLINK IFF_UP and link dump
   ========================================================================= *)

(** RTM_NEWLINK, request|ack, sequence 2, sets IFF_UP under an IFF_UP
    change mask on loopback. *)
Definition newlink_req : list byte :=
  bs [32; 0; 0; 0; 16; 0; 5; 0; 2; 0; 0; 0; 0; 0; 0; 0;
      0; 0; 0; 0; 1; 0; 0; 0; 1; 0; 0; 0; 1; 0; 0; 0].

Definition lo_up : NetIf := lo (IFF_UP + IFF_LOOPBACK) [lo_addr].

(** The link core brings loopback up and the NETDEV_UP path adds exactly
    one 127.0.0.1/8 address. *)
Example newlink_brings_lo_up :
  match rt_newlink [lo IFF_LOOPBACK []] 5 newlink_req with
  | Some (Some (d :: []), 0) =>
      (netif_get_flags d =? (IFF_UP + IFF_LOOPBACK + IFF_RUNNING + IFF_LOWER_UP))
      && match if_addrs d with (a, p) :: [] => (a =? 2130706433) && (p =? 8) | _ => false end
  | _ => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** The visible GETLINK flags are IFF_UP, IFF_LOOPBACK, IFF_RUNNING and
    IFF_LOWER_UP. *)
Example getlink_lo_flags : netif_get_flags lo_up = IFF_UP + IFF_LOOPBACK + IFF_RUNNING + IFF_LOWER_UP.
Proof. vm_compute. reflexivity. Qed.

(** RTM_GETLINK with NLM_F_DUMP chooses a link dump for the sealed
    namespace. *)
Definition getlink_req : list byte :=
  bs [17; 0; 0; 0; 18; 0; 1; 3; 3; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0].
Definition users : list UserNs :=
  [mkUserNs 1 None 0 0 (Some [mkExtent 0 0 4294967295]) (Some [mkExtent 0 0 4294967295]) true true 1000000 false;
   mkUserNs 2 (Some 1%positive) 1 1000 (Some [mkExtent 0 1000 1]) (Some [mkExtent 0 1000 1]) false true 1000000 true].
Definition capable : IdCred := mkIdCred 2 65534 65534 CAP_NET_ADMIN.
Definition net2 (ifs : list NetIf) : NetNs := mkNetNs 2 2 ifs true.

Example getlink_selects_dump :
  match sendto_fn (net2 [lo_up]) users capable capable false 2 getlink_req with
  | SDone None (RLinkDump seq port (d :: [])) =>
      (seq =? 3) && (port =? 2)
      && (netif_get_flags d =? (IFF_UP + IFF_LOOPBACK + IFF_RUNNING + IFF_LOWER_UP))
  | _ => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** The dump batches one RTM_NEWLINK message, then a separate NLMSG_DONE. *)
Definition getlink_lo : list byte :=
  bs [40; 0; 0; 0; 16; 0; 2; 0; 3; 0; 0; 0; 2; 0; 0; 0;
      0; 0; 4; 3; 1; 0; 0; 0; 73; 0; 1; 0; 0; 0; 0; 0;
      7; 0; 3; 0; 108; 111; 0; 0].
Definition getlink_done : list byte :=
  bs [20; 0; 0; 0; 3; 0; 2; 0; 3; 0; 0; 0; 2; 0; 0; 0; 0; 0; 0; 0].

Example getlink_dgrams :
  match reply_dgrams (mkNlEnv [] [[]] [] [1%nat]) (RLinkDump 3 2 [lo_up]) with
  | Some (x :: y :: []) =>
      (nl_len x =? 40) && (nl_u16 x 4 =? RTM_NEWLINK) && (nl_u32 x 24 =? 65609)
      && (nl_len y =? 20) && (nl_u16 y 4 =? NLMSG_DONE)
  | _ => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** recvfrom truncation keeps the first ten bytes while MSG_TRUNC returns
    the full datagram length and removes it from the queue. *)
Example recvfrom_truncates :
  match recvfrom_fn [getlink_lo] 10 MSG_TRUNC with
  | RfData ret got [] => (ret =? 40) && (nl_len got =? 10) && (nl_u32 got 0 =? 40)
  | _ => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   RTM_GETADDR, privilege and SIOCGIFINDEX
   ========================================================================= *)

(** RTM_GETADDR with NLM_F_DUMP selects the IPv4 address dump. *)
Definition getaddr_req : list byte :=
  bs [17; 0; 0; 0; 22; 0; 1; 3; 4; 0; 0; 0; 0; 0; 0; 0; 2; 0; 0; 0].

Example getaddr_selects_dump :
  match sendto_fn (net2 [lo_up]) users capable capable false 2 getaddr_req with
  | SDone None (RAddrDump seq port (d :: [])) =>
      (seq =? 4) && (port =? 2) && (if_index d =? 1)
  | _ => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** The address message reader sees 127.0.0.1 and prefix length 8. *)
Example getaddr_message_fields :
  let m := addr_msg 4 2 lo_up lo_addr false (5, 5) in nl_be32_at m 36 = 2130706433 /\ nl_u8 m 17 = 8.
Proof. vm_compute. split; reflexivity. Qed.

(** A caller without CAP_NET_ADMIN receives an EPERM acknowledgement for
    RTM_NEWADDR. *)
Example newaddr_without_cap :
  match sendto_fn (net2 [lo IFF_LOOPBACK []]) users capable (mkIdCred 2 65534 65534 0) false 2 newaddr_req with
  | SDone None (RAck a) => (nl_len a =? 60) && (nl_u32 a 16 =? 4294967295)
  | _ => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

Definition ifr_lo : list byte := bs ([108; 111] ++ List.repeat 0 38).
Definition ifr_none : list byte := bs ([101; 116; 104; 57] ++ List.repeat 0 36).

(** SIOCGIFINDEX finds [lo] and returns index 1. *)
Example siocgifindex_lo : ifindex_fn [lo_up] ifr_lo = Some 1.
Proof. vm_compute. reflexivity. Qed.

(** SIOCGIFINDEX leaves an unknown interface to the arm's ENODEV or module
    loading branch; here the lookup has no result. *)
Example siocgifindex_unknown : ifindex_fn [lo_up] ifr_none = None.
Proof. vm_compute. reflexivity. Qed.

(** recvfrom on a closed descriptor reaches the descriptor gate's EBADF
    before any socket operation. *)
Example recvfrom_closed : socket_fd_fn false false = Some EBADF.
Proof. vm_compute. reflexivity. Qed.

(** The five syscall arms are exported by their Linux RISC-V numbers. *)
Example net_arm_numbers : map fst net_arms = [29; 198; 200; 206; 207] := eq_refl.

(** Net arms publish every allocation and security-hook refusal family. *)
Example net_injected_numbers : map ni_no net_injected = [198; 200; 206; 207].
Proof. vm_compute. reflexivity. Qed.
