(** * LinuxProcessSem.Checks.Cases.Ns.NetCases — the observable netlink core

    These cases compute the deterministic cores of the namespace network
    arms.  [socket_fn], [bind_fn], [sendto_fn], [recvfrom_fn], [ifindex_fn]
    and [socket_fd_fn] keep the chosen outcome and its observable state
    separate from the arms' environment refusals and full [Model] updates.
    The arms in [Ns.Net] connect each core to descriptors, user memory and
    the namespace state. *)

From Stdlib Require Import ZArith List Bool NArith PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Spec Tables Userns Ext Arm Net.
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

(** THE ATTRIBUTES AFTER IFLA_IFNAME are a run [nla_put] writes: an
    attribute of 5 bytes with its 3 padding bytes, then one of 8, is one;
    3 stray bytes, an attribute whose length runs past the end, a length
    below the header, and a run that stops inside the padding are not. *)
Example nla_runs :
  nla_list_ok [] = true
  /\ nla_list_ok (bs [5; 0; 1; 0; 7; 0; 0; 0; 8; 0; 2; 0; 1; 2; 3; 4]) = true
  /\ nla_list_ok (bs [1; 2; 3]) = false
  /\ nla_list_ok (bs [12; 0; 1; 0; 7; 0; 0; 0]) = false
  /\ nla_list_ok (bs [2; 0; 1; 0]) = false
  /\ nla_list_ok (bs [5; 0; 1; 0; 7]) = false.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** A link dump's choices: lo's 40-byte message fits a bound of 40, not
    one of 39; a rest that is not an attribute run is refused whatever the
    bound. *)
Example link_dump_env :
  nl_env_ok 40 (mkNlEnv [] [[]] [] [1%nat]) (RLinkDump 3 2 [lo_up]) = true
  /\ nl_env_ok 39 (mkNlEnv [] [[]] [] [1%nat]) (RLinkDump 3 2 [lo_up]) = false
  /\ nl_env_ok 65536 (mkNlEnv [] [bs [1; 2; 3]] [] [1%nat]) (RLinkDump 3 2 [lo_up]) = false.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** The datagram cap: two 40-byte messages in one datagram fit 80, not 79. *)
Example dgram_cap :
  dgrams_fit 80 [getlink_lo ++ getlink_lo] = true
  /\ dgrams_fit 79 [getlink_lo ++ getlink_lo] = false.
Proof. split; vm_compute; reflexivity. Qed.

(** lo and a fallback device in one datagram, the fallback with an 8-byte
    attribute run: NLMSG_NEXT from the first message (at NLMSG_ALIGN of its
    length) lands on the second, whose own length ends the datagram. *)
Definition sit0 : NetIf := mkNetIf 2 (bs [115; 105; 116; 48]) IFF_NOARP [].
Example two_messages_parse :
  let env := mkNlEnv [0; 776] [[]; bs [8; 0; 4; 0; 0; 5; 0; 0]] [] [2%nat] in
  nl_env_ok 1024 env (RLinkDump 3 2 [lo_up; sit0]) = true
  /\ match reply_dgrams env (RLinkDump 3 2 [lo_up; sit0]) with
     | Some (x :: _ :: []) =>
         let l1 := nl_u32 x 0 in
         let off := Z.to_nat (nl_align l1) in
         (l1 =? 40) && (nl_u16 x (off + 4) =? RTM_NEWLINK) && (nl_u32 x (off + 20) =? 2)
         && (nl_align l1 + nl_u32 x off =? nl_len x)
     | _ => false
     end = true.
Proof. split; vm_compute; reflexivity. Qed.

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

(** Net arms export their environment refusals: socket's allocation
    failures, netlink_insert's (bind, and sendto's autobind), sendto's skb
    allocation, recvfrom's pending ENOBUFS.  recvfrom's EAGAIN on an empty
    queue and bind's EADDRINUSE, the tables' answers, are no refusal. *)
Example net_injected_rows :
  map ni_no net_injected = [198; 200; 206; 207]
  /\ ni_errno socket_injected ENFILE = true /\ ni_errno bind_injected EOVERFLOW = true
  /\ ni_errno sendto_injected ENOBUFS = true /\ ni_errno sendto_injected EOVERFLOW = true
  /\ ni_errno recvfrom_injected ENOBUFS = true /\ ni_errno recvfrom_injected EAGAIN = false
  /\ ni_errno bind_injected EADDRINUSE = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* =========================================================================
   The full recvfrom arm
   ========================================================================= *)

(** Descriptor 3 names open file 7, a NETLINK_ROUTE socket of network
    namespace 2 with port 5 and one queued acknowledgement. *)
Definition rcv_model : Model :=
  let base := init_model [] (Z_to_bv 64 0) (Z_to_bv 64 0) demo_sp demo_limit (demo_input [] IEof) in
  with_fds (fd_insert (m_fds base) (Z_to_bv 64 3) (ns_fd_entry 7)) base.

Definition rcv_state : NsState :=
  with_files empty_nsstate [(7%N, mkNsFile (NfNetlink 2 5 [newaddr_ack]) 2 (mkIdCred 1 0 0 0))].

(** 164 writable bytes at 65536 (the buffer is the first 64); the address
    length 12 at 131072. *)
Definition rcv_mem : word -> option byte :=
  fun a => let v := bv_unsigned a in
           if (65536 <=? v) && (v <? 65700) then Some (Z_to_bv 8 0)
           else if (131072 <=? v) && (v <? 131076) then Some (Z_to_bv 8 (if v =? 131072 then 12 else 0))
           else None.

Definition rcv_call (addr : Z) : SyscallInput :=
  mkInput (Z_to_bv 64 207) (map (Z_to_bv 64) [3; 65536; 64; 0; addr; 131072]) rcv_mem rcv_mem.

Definition out_of (o : ext_outcome) : option (Z * list (Z * list Z)) :=
  match o with
  | EOk eff _ _ _ _ =>
      Some (bv_signed (eff_ret eff),
            map (fun p => (bv_unsigned (fst p), map bv_unsigned (snd p))) (eff_writes eff))
  | EUnmodeled => None
  end.

(** An address the task cannot write (above the user address range): the
    datagram is copied and the address length 12 written back before the
    address copy faults, so the call answers -EFAULT with both writes
    ([__sys_recvfrom], [move_addr_to_user]). *)
Example recvfrom_address_fault : forall o,
  recvfrom_arm (rcv_call (2 ^ 63)) rcv_model init_nsctx rcv_state o ->
  out_of o = Some (-14, [(65536, map bv_unsigned newaddr_ack); (131072, [12; 0; 0; 0])]).
Proof. intros o H. unfold recvfrom_arm in H. vm_compute in H. subst o. vm_compute. reflexivity. Qed.

(** With a writable address the same call returns the 36 bytes and
    writes the kernel's address. *)
Example recvfrom_address_ok : forall o,
  recvfrom_arm (rcv_call 65620) rcv_model init_nsctx rcv_state o ->
  option_map fst (out_of o) = Some 36.
Proof. intros o H. unfold recvfrom_arm in H. vm_compute in H. subst o. vm_compute. reflexivity. Qed.

(* =========================================================================
   An rtnetlink handler's allocation failure
   ========================================================================= *)

(** [handler_reached] makes [rt_handle]'s tests: a change request without
    CAP_NET_ADMIN (-EPERM), a request with no payload (answered 0) and a
    header longer than its datagram (dropped) reach no handler.  The errno
    by type: ENOMEM for RTM_NEWLINK, ENOBUFS for RTM_NEWADDR and the
    dumps, none for another type (17, RTM_DELLINK). *)
Definition getlink_bare : list byte := bs [16; 0; 0; 0; 18; 0; 1; 3; 3; 0; 0; 0; 0; 0; 0; 0].
Definition getlink_long : list byte :=
  bs [40; 0; 0; 0; 18; 0; 1; 3; 3; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0].

Example handler_reached_cases :
  handler_reached (net2 [lo IFF_LOOPBACK []]) users capable (mkIdCred 2 65534 65534 0) false newaddr_req
    = false
  /\ handler_reached (net2 [lo_up]) users capable capable false getlink_bare = false
  /\ handler_reached (net2 [lo_up]) users capable capable false getlink_long = false
  /\ handler_reached (net2 [lo_up]) users capable capable false getlink_req = true
  /\ nl_handler_errnos RTM_NEWLINK = [ENOMEM] /\ nl_handler_errnos RTM_NEWADDR = [ENOBUFS]
  /\ nl_handler_errnos RTM_GETLINK = [ENOBUFS] /\ nl_handler_errnos RTM_GETADDR = [ENOBUFS]
  /\ nl_handler_errnos 17 = [].
Proof. vm_compute. repeat split; reflexivity. Qed.

(** The forced-only filter reads an acknowledgement's errno and the type
    of the request it echoes ([nl_fail_ack_alloc]): it marks only the
    allocation errno of that type ([nl_handler_errnos]): -ENOBUFS for a
    link dump or RTM_NEWADDR, -ENOMEM for RTM_NEWLINK.  Another errno
    (-EPERM, -EEXIST, -ENOBUFS on RTM_NEWLINK) and a success are not
    marked, so they are never removed. *)
Example fail_ack_alloc_by_type :
  nl_fail_ack_alloc (handler_fail_ack 2 getlink_req ENOBUFS) = true
  /\ nl_fail_ack_alloc (nl_ack 2 newlink_req ENOMEM) = true
  /\ nl_fail_ack_alloc (nl_ack 2 newaddr_req ENOBUFS) = true
  /\ nl_fail_ack_alloc (nl_ack 2 newlink_req EPERM) = false
  /\ nl_fail_ack_alloc (nl_ack 2 newlink_req ENOBUFS) = false
  /\ nl_fail_ack_alloc (nl_ack 2 newaddr_req EEXIST) = false
  /\ nl_fail_ack_alloc (nl_ack 2 newlink_req 0) = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** A bound socket (port 2) of the sealed namespace 2 sends the link dump
    request [getlink_req] to the kernel, from a task of that namespace
    ([snd_ctx]).  The dump's first part can fail for lack of memory:
    [sendto] still returns the request's length, the queue holds the
    acknowledgement with -ENOBUFS ([handler_fail_ack]) and behind it the
    dump ([lo_dump]), which keeps running, and the namespace does not
    change.  [ns_spec] admits that answer beside the dump without the
    failure ([dump_out]), with the same effect: a length, which matches no
    pair.  Only the state after the call shows the failure
    ([Net.nl_alloc_after]): under forced-only the filter removes the
    answer with the acknowledgement and keeps the dump
    ([Spec.ns_alloc_refusal]); under may-fail it keeps both (SCOPE.md). *)
Definition snd_len : Z := Z.of_nat (length getlink_req).
Definition snd_file : NsFile := mkNsFile (NfNetlink 2 2 []) 2 capable.
Definition snd_state : NsState :=
  mkNsState [] users [] [] [net2 [lo_up]] [] [] [] [(7%N, snd_file)] (ns_env empty_nsstate).
Definition snd_ctx : NsCtx :=
  mkNsCtx 1 1 1 2 [] (1%positive, 1%positive) (1%positive, 1%positive) 18 (mkCaps 0 0 0 0 0) 0 [].
Definition snd_mem : word -> option byte :=
  fun a => let k := bv_unsigned a - 65536 in
           if (0 <=? k) && (k <? snd_len) then Some (nth (Z.to_nat k) getlink_req (Z_to_bv 8 0))
           else None.
Definition snd_in : SyscallInput :=
  mkInput (Z_to_bv 64 206) (map (Z_to_bv 64) [3; 65536; snd_len; 0; 0; 0]) snd_mem snd_mem.

(** The link dump of [lo_up]: one datagram, then NLMSG_DONE. *)
Definition lo_env : NlEnv := mkNlEnv [] [[]] [] [1%nat].
Definition lo_dump : list (list byte) :=
  match reply_dgrams lo_env (RLinkDump 3 2 [lo_up]) with Some dgs => dgs | None => [] end.

Definition fail_eff : SyscallEffect :=
  mkEffectU (Z_to_bv 64 snd_len) [] [] [] [] [(Z_to_bv 64 65536, Z.to_nat snd_len)].
Definition fail_out : ext_outcome :=
  EOk fail_eff rcv_model snd_ctx
      (set_file snd_state 7 (netlink_file snd_file 2 2 (handler_fail_ack 2 getlink_req ENOBUFS :: lo_dump)))
      [].

Definition dump_out : ext_outcome :=
  EOk fail_eff rcv_model snd_ctx (set_file snd_state 7 (netlink_file snd_file 2 2 lo_dump)) [].

Example getlink_handler_failure_admitted :
  nl_u32 (handler_fail_ack 2 getlink_req ENOBUFS) 16 = 4294967191
  /\ ns_spec snd_in rcv_model snd_ctx snd_state fail_out.
Proof.
  split; [vm_compute; reflexivity|].
  (* Head reductions only: a full normalization of the relation, whose
     dump branch quantifies over the environment's NlEnv, does not fit in
     memory. *)
  hnf. left. hnf. right. exists 2. split; [exact eq_refl|].
  hnf. right. hnf. left. exists lo_env, lo_dump.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  right. left. split; [vm_compute; reflexivity|].
  exists ENOBUFS. split; [split; vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

Example getlink_dump_admitted : ns_spec snd_in rcv_model snd_ctx snd_state dump_out.
Proof.
  (* Head reductions only, as for [getlink_handler_failure_admitted]. *)
  hnf. left. hnf. right. exists 2. split; [exact eq_refl|].
  hnf. right. hnf. left. exists lo_env, lo_dump.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  left. vm_compute. reflexivity.
Qed.

Example getlink_handler_failure_forced_only :
  ns_refusal forced_only_cfg snd_in rcv_model snd_ctx snd_state fail_out
  /\ ~ ns_refusal forced_only_cfg snd_in rcv_model snd_ctx snd_state dump_out.
Proof.
  split.
  - hnf. right. split; [vm_compute; reflexivity|].
    exists rcv_model, snd_ctx, (set_file snd_state 7 (netlink_file snd_file 2 2 lo_dump)), [].
    split; [exact getlink_dump_admitted | vm_compute; reflexivity].
  - intros H. hnf in H. destruct H as [H | [Hb _]].
    + apply (proj1 (ns_refusal_eff_ns forced_only_cfg snd_in rcv_model snd_ctx snd_state fail_eff
                      ltac:(vm_compute; reflexivity))) in H.
      destruct H as [Hoff _]. vm_compute in Hoff. discriminate Hoff.
    + vm_compute in Hb. discriminate Hb.
Qed.

Example getlink_handler_failure_may_fail :
  ~ ns_refusal may_fail_cfg snd_in rcv_model snd_ctx snd_state fail_out
  /\ ~ ns_refusal may_fail_cfg snd_in rcv_model snd_ctx snd_state dump_out.
Proof.
  split; intros H; hnf in H; destruct H as [H | [Hb _]].
  - apply (proj1 (ns_refusal_eff_ns may_fail_cfg snd_in rcv_model snd_ctx snd_state fail_eff
                    ltac:(vm_compute; reflexivity))) in H.
    destruct H as [Hoff _]. vm_compute in Hoff. discriminate Hoff.
  - vm_compute in Hb. discriminate Hb.
  - apply (proj1 (ns_refusal_eff_ns may_fail_cfg snd_in rcv_model snd_ctx snd_state fail_eff
                    ltac:(vm_compute; reflexivity))) in H.
    destruct H as [Hoff _]. vm_compute in Hoff. discriminate Hoff.
  - vm_compute in Hb. discriminate Hb.
Qed.

(* =========================================================================
   The loopback device brought up without its address
   ========================================================================= *)

(** A bound socket (port 2) of the sealed namespace 2, whose [lo] is down,
    sends [newlink_req] (IFF_UP on lo, with NLM_F_ACK), from a task of user
    namespace 2 with CAP_NET_ADMIN ([up_ctx]).  [ns_spec] admits two
    answers: lo up with 127.0.0.1/8, and, when [inetdev_event]'s
    [inet_alloc_ifa] fails, lo up with no address.  Both return the
    request's length with the same effect ([up_eff]) and queue the same
    acknowledgement of 0; only the state after the call tells them apart
    ([Net.nl_alloc_after]).  Under forced-only the filter removes the
    answer without the address and keeps the one with it
    ([Spec.ns_alloc_refusal]); under may-fail it keeps both (SCOPE.md). *)
Definition admin : IdCred := mkIdCred 2 65534 65534 (2 ^ CAP_NET_ADMIN).
Definition up_file : NsFile := mkNsFile (NfNetlink 2 2 []) 2 admin.
Definition up_state : NsState :=
  mkNsState [] users [] [] [net2 [lo IFF_LOOPBACK []]] [] [] [] [(7%N, up_file)] (ns_env empty_nsstate).
Definition up_ctx : NsCtx :=
  mkNsCtx 2 1 1 2 [] (1%positive, 1%positive) (1%positive, 1%positive) 18
          (mkCaps (2 ^ CAP_NET_ADMIN) 0 0 0 0) 0 [].
Definition up_len : Z := Z.of_nat (length newlink_req).
Definition up_mem : word -> option byte :=
  fun a => let k := bv_unsigned a - 65536 in
           if (0 <=? k) && (k <? up_len) then Some (nth (Z.to_nat k) newlink_req (Z_to_bv 8 0))
           else None.
Definition up_in : SyscallInput :=
  mkInput (Z_to_bv 64 206) (map (Z_to_bv 64) [3; 65536; up_len; 0; 0; 0]) up_mem up_mem.

Definition up_eff : SyscallEffect :=
  mkEffectU (Z_to_bv 64 up_len) [] [] [] [] [(Z_to_bv 64 65536, Z.to_nat up_len)].
Definition up_out (ifs : list NetIf) : ext_outcome :=
  EOk up_eff rcv_model up_ctx
      (set_file (set_netns_ifs up_state 2 ifs) 7 (netlink_file up_file 2 2 [nl_ack 2 newlink_req 0]))
      [].

Example lo_up_without_address :
  lo_up_noaddr [lo IFF_LOOPBACK []] [lo_up] = [lo (IFF_UP + IFF_LOOPBACK) []]
  /\ ns_spec up_in rcv_model up_ctx up_state (up_out [lo_up])
  /\ ns_spec up_in rcv_model up_ctx up_state (up_out [lo (IFF_UP + IFF_LOOPBACK) []]).
Proof.
  split; [vm_compute; reflexivity|].
  (* Head reductions only, as for [getlink_handler_failure_admitted]. *)
  split.
  - hnf. left. hnf. right. exists 2. split; [exact eq_refl|].
    hnf. right. hnf. left. exists lo_env, [nl_ack 2 newlink_req 0].
    split; [vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|].
    left. vm_compute. reflexivity.
  - hnf. left. hnf. right. exists 2. split; [exact eq_refl|].
    hnf. right. hnf. left. exists lo_env, [nl_ack 2 newlink_req 0].
    split; [vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|].
    right. right. exists [lo_up].
    split; [vm_compute; reflexivity|].
    split; [vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

Example lo_up_without_address_forced_only :
  ns_refusal forced_only_cfg up_in rcv_model up_ctx up_state (up_out [lo (IFF_UP + IFF_LOOPBACK) []])
  /\ ~ ns_refusal forced_only_cfg up_in rcv_model up_ctx up_state (up_out [lo_up]).
Proof.
  destruct lo_up_without_address as (_ & Hok & _).
  split.
  - hnf. right. split; [vm_compute; reflexivity|].
    exists rcv_model, up_ctx,
      (set_file (set_netns_ifs up_state 2 [lo_up]) 7 (netlink_file up_file 2 2 [nl_ack 2 newlink_req 0])),
      [].
    split; [exact Hok | vm_compute; reflexivity].
  - intros H. hnf in H. destruct H as [H | [Hb _]].
    + apply (proj1 (ns_refusal_eff_ns forced_only_cfg up_in rcv_model up_ctx up_state up_eff
                      ltac:(vm_compute; reflexivity))) in H.
      destruct H as [Hoff _]. vm_compute in Hoff. discriminate Hoff.
    + vm_compute in Hb. discriminate Hb.
Qed.

Example lo_up_both_kept_may_fail :
  ~ ns_refusal may_fail_cfg up_in rcv_model up_ctx up_state (up_out [lo (IFF_UP + IFF_LOOPBACK) []])
  /\ ~ ns_refusal may_fail_cfg up_in rcv_model up_ctx up_state (up_out [lo_up]).
Proof.
  split; intros H; hnf in H; destruct H as [H | [Hb _]].
  - apply (proj1 (ns_refusal_eff_ns may_fail_cfg up_in rcv_model up_ctx up_state up_eff
                    ltac:(vm_compute; reflexivity))) in H.
    destruct H as [Hoff _]. vm_compute in Hoff. discriminate Hoff.
  - vm_compute in Hb. discriminate Hb.
  - apply (proj1 (ns_refusal_eff_ns may_fail_cfg up_in rcv_model up_ctx up_state up_eff
                    ltac:(vm_compute; reflexivity))) in H.
    destruct H as [Hoff _]. vm_compute in Hoff. discriminate Hoff.
  - vm_compute in Hb. discriminate Hb.
Qed.
