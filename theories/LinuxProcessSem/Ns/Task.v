(** * LinuxProcessSem.Ns.Task — arms on a task's own state

    The calls that read or change only what a task holds: its umask, its
    pid, its session, its capability sets, its no_new_privs bit, its parent-death signal
    and its dumpable mode; and the calls on the names of its UTS namespace:
    [uname], [sethostname] and [setdomainname].  Each header names the
    Linux functions it follows (6.18.44; the UTS arms cite v6.18.46) and
    its kind.

    The security modules are the capability module alone, as the released
    model's capability arms assume: [security_capget], [security_capset]
    and [security_task_prctl] are [cap_capget], [cap_capset] and
    [cap_task_prctl].  A read from user memory that [access_ok] admits but
    that finds an unmapped byte declines, as the released capability arms
    do; [sethostname] and [setdomainname] read their name with the
    released model's [copy_from_user] reader ([uts_copy_in]) and answer
    EFAULT there, as the released arms that use it do.  A write to user
    memory that is not wholly writable after [access_ok] declines too (a
    partial copy). *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Arm Userns.
Import ListNotations.
Local Open Scope Z_scope.

(* =========================================================================
   Setters on the task context (the per-field ones are [Ns.Tables]')
   ========================================================================= *)

Definition with_dumpable (ctx : NsCtx) (d : Z) : NsCtx := with_dumpable_opt ctx (Some d).

Definition with_no_new_privs (ctx : NsCtx) : NsCtx := with_nnp_opt ctx (Some true).

(** The task's credential as the capability checks read it: its user
    namespace, euid and egid (the model's kernel ids) and effective set. *)
Definition task_cred (m : Model) (ctx : NsCtx) : IdCred :=
  mkIdCred (cx_user ctx) (bv_unsigned (cr_euid (m_creds m))) (bv_unsigned (cr_egid (m_creds m)))
           (cap_effective (cx_caps ctx)).

(** [ns_capable (current_user_ns (), cap)]. *)
Definition own_capable (m : Model) (ctx : NsCtx) (st : NsState) (cap : Z) : bool :=
  cap_capable (ns_userns st) (task_cred m ctx) (cx_user ctx) cap.

(* =========================================================================
   Arms on the task's own state
   ========================================================================= *)

(** [umask] (166): [SYSCALL_DEFINE1(umask)], kernel/sys.c: the mask's
    permission bits are stored and the old mask returned.  Kind: exact. *)
Definition umask_arm : NsArm := fun i m ctx st o =>
  o = ns_ret (Z_to_bv 64 (cx_umask ctx)) m
             (with_umask ctx (Z.land (bv_unsigned (in_arg i 0)) 511)) st.

(** [getpid] (172) and [gettid] (178): [task_tgid_vnr] and
    [task_pid_vnr] (kernel/sys.c), the pid in the task's active pid
    namespace; one thread per process, so both are the same.  Kind: exact;
    a task with no pid in its own namespace is not one the model holds,
    and declines. *)
Definition getpid_arm : NsArm := fun i m ctx st o =>
  match task_pid ctx with
  | Some p => o = ns_ret (Z_to_bv 64 p) m ctx st
  | None => o = EUnmodeled
  end.

(** The task's active pid namespace is one the tables made: it has a
    parent.  A pid namespace with no parent, or one the tables do not
    hold, is the host's ([Tables.PidNs]). *)
Definition pidns_made (st : NsState) (p : positive) : bool :=
  match find (fun x => Pos.eqb (pidns_id x) p) (ns_pidns st) with
  | Some x => match pidns_parent x with Some _ => true | None => false end
  | None => false
  end.

(** [setsid] (157): [ksys_setsid], kernel/sys.c:1268-1301 (Linux
    v6.18.46), in kernel order:
    - the answer is [pid_vnr(task_pid(group_leader))], the caller's pid in
      its own active pid namespace (:1271-1273), as [getpid_arm] answers;
    - EPERM when the caller already leads a session ([signal->leader],
      :1278-1279).  That bit is [State.m_setsid_succeeded]: only
      [ksys_setsid] sets it and nothing clears it
      ([Kernel.Sys.setsid_spec]'s note);
    - EPERM when a live task's process group is the caller's pid
      ([pid_task(sid, PIDTYPE_PGID)], :1284-1285);
    - else the caller leads a new session and process group
      ([set_special_pids], :1257-1266, 1287-1288) and the answer is its
      pid (:1292).  Nothing before the answer allocates, and the steps
      after the unlock (:1295-1299) cannot change it: no environment
      refusal.

    THE PROCESS-GROUP TEST.  In a pid namespace the tables made
    ([pidns_made]) the caller's pid came from a modelled clone.  A
    process group is that pid only after a [setpgid] that names it
    ([SYSCALL_DEFINE2(setpgid)], kernel/sys.c:1114-1185: the target is
    the caller or its child, and a group other than the target's own pid
    must already exist in the caller's session), or after the caller's
    own [setsid], which sets the leader bit and so answers EPERM at the
    first test.  [setpgid] (154) has no arm, in [Spec.ns_table] or in the
    released table, so no modelled run makes such a group: the test is
    false, and the arm is exact.  If [setpgid] is ever modelled, this
    test must read the multi-process core's group table instead.
    In the host's pid namespace (a task that unshared only its user
    namespace, say) group membership is the environment's, as for the
    released arm: EPERM is admitted beside the success.

    WHAT IS WRITTEN: the leader bit only ([with_setsid_succeeded]).  The
    session and group ids become the caller's pid; no call of the
    namespace model reads them ([getsid] 156 and [getpgid] 155 have no
    arm here).  [m_tid] is not written: it holds the host's numbering,
    and a pid of another namespace must not go there (the multi-process
    core's owner, 2026-11-03).
    Kind: exact in a pid namespace the tables made; over in the host's;
    a task with no pid in its own namespace declines. *)
Definition setsid_arm : NsArm := fun i m ctx st o =>
  if m_setsid_succeeded m then o = ns_errno EPERM m ctx st
  else match task_pid ctx with
       | None => o = EUnmodeled
       | Some p =>
           if pidns_made st (cx_pidns ctx)
           then o = ns_ret (Z_to_bv 64 p) (with_setsid_succeeded m) ctx st
           else o = ns_errno EPERM m ctx st
                \/ o = ns_ret (Z_to_bv 64 p) (with_setsid_succeeded m) ctx st
       end.

(* =========================================================================
   Capabilities
   ========================================================================= *)

Definition CAP_VALID_MASK : Z := 2 ^ 41 - 1.
Definition CAP_SETPCAP : Z := 8.
Definition LINUX_CAPABILITY_VERSION_1 : Z := 429392688.   (* 0x19980330 *)
Definition LINUX_CAPABILITY_VERSION_2 : Z := 537333798.   (* 0x20071026 *)
Definition LINUX_CAPABILITY_VERSION_3 : Z := 537396514.   (* 0x20080522 *)

Definition subset (a b : Z) : bool := Z.eqb (Z.land a (Z.lnot b)) 0.

(** [cap_validate_magic]: the number of 32-bit halves a version copies
    (1 for version 1, 2 for versions 2 and 3); for another version the
    kernel writes version 3 back into the header and answers EINVAL. *)
Inductive Magic := MagicFault | MagicUnmapped | MagicBad | MagicOk (tocopy : Z).

Definition validate_magic (i : SyscallInput) (header : word) : Magic :=
  match get_u32 i header with
  | GetFault => MagicFault
  | GetUnmapped => MagicUnmapped
  | GetVal v =>
      if v =? LINUX_CAPABILITY_VERSION_1 then MagicOk 1
      else if (v =? LINUX_CAPABILITY_VERSION_2) || (v =? LINUX_CAPABILITY_VERSION_3) then MagicOk 2
      else MagicBad
  end.

(** The version written back for [MagicBad]: [put_user], EFAULT when the
    header is not writable. *)
Definition bad_magic (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState) (header : word)
    (final : Z) : ext_outcome :=
  match put_ok i header 4 with
  | PutFault => ns_errno EFAULT m ctx st
  | PutPartial => EUnmodeled
  | PutOk => EOk (with_copyins [(header, 4%nat)]
                 (mkEffect (Z_to_bv 64 final) [(header, u32_bytes LINUX_CAPABILITY_VERSION_3)] []))
               m ctx st []
  end.

(** The six 32-bit words of [__user_cap_data_struct] x 2 (effective,
    permitted, inheritable; low halves then high halves), [tocopy] halves. *)
Definition cap_data (tocopy : Z) (c : CapSets) : list byte :=
  let w (z : Z) := u32_bytes (Z.land z 4294967295) in
  let h (z : Z) := u32_bytes (Z.shiftr z 32) in
  w (cap_effective c) ++ w (cap_permitted c) ++ w (cap_inheritable c)
  ++ (if tocopy =? 2 then h (cap_effective c) ++ h (cap_permitted c) ++ h (cap_inheritable c)
      else []).

(** An errno answer after the user reads [reads]. *)
Definition errno_after (reads : list (word * nat)) (e : Z) (m : Model) (ctx : NsCtx) (st : NsState)
    : ext_outcome :=
  EOk (with_copyins reads (mkEffect (errno_ret e) [] [])) m ctx st [].

(** [capget] (90): [SYSCALL_DEFINE2(capget)], [cap_validate_magic],
    [cap_get_target_pid], [cap_capget] (kernel/capability.c,
    security/commoncap.c).  A NULL data pointer answers 0 for a bad
    version (after the version is written back) and for a good one; a
    negative pid EINVAL; another task's sets decline (the model does not
    hold them).  Kind: exact. *)
Definition capget_fn (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState) : ext_outcome :=
  let header := in_arg i 0 in
  let dataptr := in_arg i 1 in
  let r1 := [(header, 4%nat)] in
  let r2 := [(header, 4%nat); ((header + Z_to_bv 64 4)%bv, 4%nat)] in
  match validate_magic i header with
  | MagicFault => ns_errno EFAULT m ctx st
  | MagicUnmapped => EUnmodeled
  | MagicBad => bad_magic i m ctx st header (if w_is0 dataptr then 0 else - EINVAL)
  | MagicOk tocopy =>
      if w_is0 dataptr then
        EOk (with_copyins r1 (mkEffect (Z_to_bv 64 0) [] [])) m ctx st []
      else match get_u32 i (header + Z_to_bv 64 4)%bv with
           | GetFault => errno_after r1 EFAULT m ctx st
           | GetUnmapped => EUnmodeled
           | GetVal pv =>
               let pid := (if pv <? 2147483648 then pv else pv - 4294967296) in
               if pid <? 0 then errno_after r2 EINVAL m ctx st
               else if negb ((pid =? 0) || (match task_pid ctx with Some p => pid =? p | None => false end))
               then EUnmodeled
               else match put_ok i dataptr (12 * tocopy) with
                    | PutFault => errno_after r2 EFAULT m ctx st
                    | PutPartial => EUnmodeled
                    | PutOk => EOk (with_copyins r2
                                   (mkEffect (Z_to_bv 64 0) [(dataptr, cap_data tocopy (cx_caps ctx))] []))
                                 m ctx st []
                    end
           end
  end.

Definition capget_arm : NsArm := fun i m ctx st o => o = capget_fn i m ctx st.

(** [cap_capset]'s four refusals, in order, and the new sets. *)
Definition cap_capset (own_setpcap : bool) (old : CapSets) (e p ih : Z) : option CapSets :=
  if (negb own_setpcap) && negb (subset ih (Z.lor (cap_inheritable old) (cap_permitted old)))
  then None
  else if negb (subset ih (Z.lor (cap_inheritable old) (cap_bounding old))) then None
  else if negb (subset p (cap_permitted old)) then None
  else if negb (subset e p) then None
  else Some (mkCaps e p ih (cap_bounding old) (Z.land (cap_ambient old) (Z.land p ih))).

(** [capset] (91): [SYSCALL_DEFINE2(capset)], [cap_capset].  The pid must
    be 0 or the caller's (else EPERM); the sets are masked to
    CAP_VALID_MASK; [prepare_creds] may fail (ENOMEM, the environment's:
    [task_injected]); a refused set is EPERM.  The permitted set can only
    shrink, so [commit_creds] resets neither the parent-death signal nor
    the dumpable mode.  Kind: exact, with the environment's ENOMEM.

    [capset_stage] is the call up to [prepare_creds]: an answer, or the
    copy-ins and the three sets read. *)
Definition capset_stage (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState)
    : ext_outcome + (list (word * nat) * Z * Z * Z) :=
  let header := in_arg i 0 in
  let data := in_arg i 1 in
  match validate_magic i header with
  | MagicFault => inl (ns_errno EFAULT m ctx st)
  | MagicUnmapped => inl EUnmodeled
  | MagicBad => inl (bad_magic i m ctx st header (- EINVAL))
  | MagicOk tocopy =>
      match get_u32 i (header + Z_to_bv 64 4)%bv with
      | GetFault => inl (errno_after [(header, 4%nat)] EFAULT m ctx st)
      | GetUnmapped => inl EUnmodeled
      | GetVal pv =>
          let pid := (if pv <? 2147483648 then pv else pv - 4294967296) in
          if negb ((pid =? 0) || (match task_pid ctx with Some p => pid =? p | None => false end))
          then inl (errno_after [(header, 4%nat); ((header + Z_to_bv 64 4)%bv, 4%nat)] EPERM m ctx st)
          else if negb (access_okb data (12 * tocopy))
          then inl (errno_after [(header, 4%nat); ((header + Z_to_bv 64 4)%bv, 4%nat)] EFAULT m ctx st)
          else match read_bytes_map (in_mem i) data (Z_to_bv 64 (12 * tocopy)) with
               | None => inl EUnmodeled
               | Some bs =>
                   let word_at (k : nat) := bytes_le_to_Z (firstn 4 (skipn (4 * k) bs)) in
                   let hi (k : nat) := if tocopy =? 2 then word_at (3 + k)%nat else 0 in
                   let mk (k : nat) := Z.land (Z.lor (word_at k) (Z.shiftl (hi k) 32)) CAP_VALID_MASK in
                   inr ([(header, 4%nat); ((header + Z_to_bv 64 4)%bv, 4%nat);
                         (data, Z.to_nat (12 * tocopy))], mk 0%nat, mk 1%nat, mk 2%nat)
               end
      end
  end.

Definition capset_fn (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState) : ext_outcome :=
  match capset_stage i m ctx st with
  | inl o => o
  | inr (reads, e, p, ih) =>
      match cap_capset (own_capable m ctx st CAP_SETPCAP) (cx_caps ctx) e p ih with
      | None => EOk (with_copyins reads (mkEffect (errno_ret EPERM) [] [])) m ctx st []
      | Some c => EOk (with_copyins reads (mkEffect (Z_to_bv 64 0) [] [])) m (with_caps ctx c) st []
      end
  end.

(** [prepare_creds]'s ENOMEM, where the call gets that far. *)
Definition capset_enomem (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState)
    : option ext_outcome :=
  match capset_stage i m ctx st with
  | inl _ => None
  | inr (reads, _, _, _) => Some (EOk (with_copyins reads (mkEffect (errno_ret ENOMEM) [] [])) m ctx st [])
  end.

Definition capset_arm : NsArm := fun i m ctx st o =>
  o = capset_fn i m ctx st \/ capset_enomem i m ctx st = Some o.

(* =========================================================================
   prctl
   ========================================================================= *)

(** [prctl] (167): [SYSCALL_DEFINE5(prctl)] (kernel/sys.c) after
    [cap_task_prctl] (security/commoncap.c), for the options
    PR_CAPBSET_READ (23), PR_CAPBSET_DROP (24, [cap_prctl_drop]: CAP_SETPCAP
    in the task's namespace, then a valid number), PR_GET_DUMPABLE (3),
    PR_SET_DUMPABLE (4, 0 or 1), PR_SET_NO_NEW_PRIVS (38) and
    PR_GET_NO_NEW_PRIVS (39), each with its argument checks; a GET of a
    value the model does not know declines.  PR_SET_PDEATHSIG (1) and
    PR_GET_PDEATHSIG (2) are the released model's answers: the signal is
    its state ([State.m_pdeath_signal]).  The option is the low 32 bits of
    a0.  Any other option is DECLINED ([EUnmodeled]), never read as one of
    these eight.  Kind: exact, with [prepare_creds]'s ENOMEM for
    PR_CAPBSET_DROP, the environment's. *)
Definition prctl_fn (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState) : ext_outcome :=
  let opt := s32 (in_arg i 0) in
  let a2 := bv_unsigned (in_arg i 1) in
  let z3 := w_is0 (in_arg i 2) && w_is0 (in_arg i 3) && w_is0 (in_arg i 4) in
  if opt =? 23 then
    (if 40 <? a2 then ns_errno EINVAL m ctx st
     else ns_ret (Z_to_bv 64 (if Z.testbit (cap_bounding (cx_caps ctx)) a2 then 1 else 0)) m ctx st)
  else if opt =? 24 then
    (if negb (own_capable m ctx st CAP_SETPCAP) then ns_errno EPERM m ctx st
     else if 40 <? a2 then ns_errno EINVAL m ctx st
     else let c := cx_caps ctx in
          ns_ret (Z_to_bv 64 0) m
            (with_caps ctx (mkCaps (cap_effective c) (cap_permitted c) (cap_inheritable c)
                                   (Z.land (cap_bounding c) (Z.lnot (2 ^ a2))) (cap_ambient c)))
            st)
  else if opt =? 3 then
    (match cx_dumpable ctx with
     | Some d => ns_ret (Z_to_bv 64 d) m ctx st
     | None => EUnmodeled
     end)
  else if opt =? 4 then
    (if 1 <? a2 then ns_errno EINVAL m ctx st else ns_ret (Z_to_bv 64 0) m (with_dumpable ctx a2) st)
  else if opt =? 38 then
    (if negb ((a2 =? 1) && z3) then ns_errno EINVAL m ctx st
     else ns_ret (Z_to_bv 64 0) m (with_no_new_privs ctx) st)
  else if opt =? 39 then
    (if negb ((a2 =? 0) && z3) then ns_errno EINVAL m ctx st
     else match cx_no_new_privs ctx with
          | Some b => ns_ret (Z_to_bv 64 (if b then 1 else 0)) m ctx st
          | None => EUnmodeled
          end)
  else EUnmodeled.

(** [cap_prctl_drop]'s [prepare_creds] ENOMEM, after its two checks. *)
Definition prctl_enomem (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState)
    : option ext_outcome :=
  if (s32 (in_arg i 0) =? 24) && own_capable m ctx st CAP_SETPCAP
     && (bv_unsigned (in_arg i 1) <=? 40)
  then Some (ns_errno ENOMEM m ctx st) else None.

Definition prctl_arm : NsArm := fun i m ctx st o =>
  let opt := s32 (in_arg i 0) in
  if (opt =? 1) || (opt =? 2) then released i m ctx st o
  else o = prctl_fn i m ctx st \/ prctl_enomem i m ctx st = Some o.

(* =========================================================================
   The UTS namespace: uname, sethostname, setdomainname
   ========================================================================= *)

(** The two members of [struct new_utsname] a call can write, and where
    each starts in the 390 bytes [uname] copies out: [nodename] at 65,
    [domainname] at 325 (include/uapi/linux/utsname.h:25-32, Linux
    v6.18.46). *)
Inductive UtsField := UtsNodename | UtsDomainname.

Definition uts_offset (k : UtsField) : nat :=
  match k with UtsNodename => 65%nat | UtsDomainname => 325%nat end.

Definition uts_put (k : UtsField) (u : UtsNs) (v : list byte) : UtsNs :=
  match k with
  | UtsNodename => with_nodename u (Some v)
  | UtsDomainname => with_domainname u (Some v)
  end.

(** [ns_capable(current->nsproxy->uts_ns->user_ns, CAP_SYS_ADMIN)]
    (kernel/sys.c:1424, :1478): [own_capable]'s shape aimed at the UTS
    namespace's owner. *)
Definition uts_capable (m : Model) (ctx : NsCtx) (st : NsState) (u : UtsNs) : bool :=
  cap_capable (ns_userns st) (task_cred m ctx) (utsns_owner u) CAP_SYS_ADMIN.

(** [copy_from_user(tmp, name, len)] for [0 <= len <= 64], through the
    released model's own reader of a user range, [State.copy_bytes_map]:
    [access_ok] over the whole range, then the bytes ([_inline_copy_from_user],
    include/linux/uaccess.h:159-185).  [None] is the copy failing, which
    Linux answers -EFAULT whether [access_ok] refused the range or a byte
    of it is not mapped -- the released arms answer both that way through
    this reader ([Net.Socket.bind_spec]) or its two halves
    ([Kernel.Signal.rt_sigprocmask_spec], [Kernel.Sys.prlimit64_spec]).
    At length 0 [copy_from_user] copies nothing and returns 0 whatever the
    pointer, which [copy_bytes_map] does not say for a pointer above
    [TASK_SIZE], so that case is answered first, as its note asks of a
    caller with a variable length. *)
Definition uts_copy_in (i : SyscallInput) (name : word) (len : Z) : option (list byte) :=
  if len =? 0 then Some [] else copy_bytes_map (in_mem i) name len.

(** [sethostname] (161) and [setdomainname] (162): one template over the
    member [k], in the kernel's order (Linux v6.18.46, kernel/sys.c:1419-1443
    [SYSCALL_DEFINE2(sethostname)] and :1473-1497
    [SYSCALL_DEFINE2(setdomainname)]):
    - EPERM unless the task holds CAP_SYS_ADMIN over the owner of its UTS
      namespace ([uts_capable], :1424-1425 and :1478-1479);
    - in the host's UTS namespace ([host_uts]) the call DECLINES past that
      check: a write there changes the host's name, which is the
      environment's pin ([State.m_utsname]);
    - EINVAL when [len], the sign-extended low 32 bits of a1 (an [int]),
      is below 0 or above [__NEW_UTS_LEN] (:1427-1428, :1480-1481);
    - the copy-in of [len] bytes ([uts_copy_in]): EFAULT, exact, when it
      fails, with no copy-in recorded, the released convention for a
      failed copy ([Kernel.Signal.rt_sigprocmask_spec]'s note); else the
      [len] bytes are the call's copy-in (none at length 0);
    - [add_device_randomness] (:1433, :1487) changes nothing a program
      can see that the model's [getrandom], a free choice, does not
      already admit;
    - the member becomes the [len] bytes and NULs to 65 bytes (:1436-1437,
      :1490-1491), and the call returns 0.
    Nothing in it can fail for the environment: it allocates nothing, and
    [down_write] and [up_write] do not fail; so it injects no refusal
    ([task_injected] has no row for 161 or 162).  A UTS namespace the
    tables do not hold declines.  Kind: exact; declines in the host's UTS
    namespace after the capability check. *)
Definition set_uts_fn (k : UtsField) (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState)
    : ext_outcome :=
  let name := in_arg i 0 in
  let len := s32 (in_arg i 1) in
  match find_utsns st (cx_uts ctx) with
  | None => EUnmodeled
  | Some u =>
      if negb (uts_capable m ctx st u) then ns_errno EPERM m ctx st
      else if Pos.eqb (utsns_id u) host_uts then EUnmodeled
      else if (len <? 0) || (NEW_UTS_LEN <? len) then ns_errno EINVAL m ctx st
      else match uts_copy_in i name len with
           | None => ns_errno EFAULT m ctx st
           | Some bs =>
               EOk (with_copyins (if len =? 0 then [] else [(name, Z.to_nat len)])
                                 (mkEffect (Z_to_bv 64 0) [] []))
                   m ctx (set_utsns st (uts_put k u (bs ++ repeat (Z_to_bv 8 0) (65 - Z.to_nat len)%nat)))
                   []
           end
  end.

Definition sethostname_arm : NsArm := fun i m ctx st o => o = set_uts_fn UtsNodename i m ctx st.

Definition setdomainname_arm : NsArm := fun i m ctx st o => o = set_uts_fn UtsDomainname i m ctx st.

(** The 390 bytes [uname] copies out with member [k]'s 65 bytes replaced
    by [v]. *)
Definition uts_splice (k : UtsField) (v : list byte) (bs : list byte) : list byte :=
  firstn (uts_offset k) bs ++ v ++ skipn (uts_offset k + 65)%nat bs.

(** What a task in UTS namespace [u] reads where the released [uname]
    delivers [bs]: each member [u] holds replaces the pin's. *)
Definition uts_overlay (u : UtsNs) (bs : list byte) : list byte :=
  let bs1 := match utsns_nodename u with Some v => uts_splice UtsNodename v bs | None => bs end in
  match utsns_domainname u with Some v => uts_splice UtsDomainname v bs1 | None => bs1 end.

Definition uts_view_eff (u : option UtsNs) (eff : SyscallEffect) : SyscallEffect :=
  match u with
  | Some x => mkEffectU (eff_ret eff) (map (fun p => (fst p, uts_overlay x (snd p))) (eff_writes eff))
                        (eff_zeros eff) (eff_unmaps eff) (eff_copies eff) (eff_copyins eff)
  | None => eff
  end.

Definition uts_view (u : option UtsNs) (o : ext_outcome) : ext_outcome :=
  match o with
  | EOk eff m' ctx' st' evs => EOk (uts_view_eff u eff) m' ctx' st' evs
  | EUnmodeled => EUnmodeled
  end.

(** [uname] (160): [SYSCALL_DEFINE1(newuname)] (Linux v6.18.46,
    kernel/sys.c:1351-1366) copies out [utsname()], the caller's UTS
    namespace's name ([current->nsproxy->uts_ns->name], :1355-1357).  The
    answer is the released [uname_spec]'s -- its EFAULT, its decline of a
    partial copy-out, its pin of the host's utsname, [override_release]
    and [override_architecture] (:1361-1364) as it has them -- with bytes
    65..129 replaced by the namespace's [nodename] and bytes 325..389 by
    its [domainname] where the namespace holds them.  It overlays whatever
    bytes the released answer delivers, so it stays right if the released
    arm chooses the free members afresh at each call.  In a namespace
    whose names are the pin's, the host's among them, it is exactly the
    released answer ([uname_arm_released]).  Kind: exact where the released
    arm is. *)
Definition uname_arm : NsArm := fun i m ctx st o =>
  exists o', released i m ctx st o' /\ o = uts_view (find_utsns st (cx_uts ctx)) o'.

Lemma uts_view_eff_unnamed : forall u eff,
  utsns_nodename u = None -> utsns_domainname u = None -> uts_view_eff (Some u) eff = eff.
Proof.
  intros u eff Hn Hd.
  assert (Ho : forall bs, uts_overlay u bs = bs).
  { intros bs. unfold uts_overlay. rewrite Hn, Hd. reflexivity. }
  destruct eff as [r ws zs us cs ci]. unfold uts_view_eff.
  cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
  assert (Hm : map (fun p => (fst p, uts_overlay u (snd p))) ws = ws).
  { induction ws as [|[a b] ws IH]; cbn [map]; [reflexivity|].
    cbn [fst snd]. rewrite IH, Ho. reflexivity. }
  rewrite Hm. reflexivity.
Qed.

(** In a UTS namespace whose names are both the pin's, or one the tables
    do not hold, [uname] has exactly the released answers. *)
Lemma uname_arm_released : forall i m ctx st o,
  match find_utsns st (cx_uts ctx) with
  | Some u => utsns_nodename u = None /\ utsns_domainname u = None
  | None => True
  end ->
  (uname_arm i m ctx st o <-> released i m ctx st o).
Proof.
  intros i m ctx st o Hu.
  assert (Hv : forall o', uts_view (find_utsns st (cx_uts ctx)) o' = o').
  { intros [eff m' ctx' st' evs|]; [|reflexivity]. cbn [uts_view].
    destruct (find_utsns st (cx_uts ctx)) as [u|] eqn:E; [|reflexivity].
    try rewrite E in Hu. destruct Hu as [Hn Hd].
    rewrite (uts_view_eff_unnamed u eff Hn Hd). reflexivity. }
  unfold uname_arm. split.
  - intros (o' & Hr & Ho). rewrite Ho, Hv. exact Hr.
  - intros Hr. exists o. split; [exact Hr | symmetry; apply Hv].
Qed.

Definition task_arms : list (Z * NsArm) :=
  [(90, capget_arm); (91, capset_arm); (157, setsid_arm); (160, uname_arm);
   (161, sethostname_arm); (162, setdomainname_arm); (166, umask_arm); (167, prctl_arm);
   (172, getpid_arm); (178, getpid_arm)].

(** The environment's refusals of these arms, for the forced-only filter:
    [prepare_creds]'s ENOMEM.  The tables' answers ([NsInjected]):
    [capset_fn]'s EFAULT, EINVAL and EPERM; [prctl_fn]'s EINVAL and EPERM,
    and the released answer's EINVAL and EFAULT for PR_SET_PDEATHSIG and
    PR_GET_PDEATHSIG ([Sys.Kernel.Sys]).  [sethostname] and [setdomainname]
    have no row: no environment refusal reaches them ([set_uts_fn]).
    Neither has [uname]: its answers are the released ones, whose table
    ([Run.injected_table]) has no row for 160 either.  [setsid]'s row is
    the released one ([Run.injected_table], 157, FamCred): in the host's
    pid namespace its EPERM is the environment's group membership, the
    released arm's untracked condition; after a success its EPERM is the
    tables' answer, so EPERM is also in [ni_forced]. *)
Definition task_injected : list NsInjected :=
  [mkNsInjected 91 [(fun e => e =? ENOMEM, FamAlloc)] [EFAULT; EINVAL; EPERM] [];
   mkNsInjected 157 [(fun e => e =? EPERM, FamCred)] [EPERM] [EPERM];
   mkNsInjected 167 [(fun e => e =? ENOMEM, FamAlloc)] [EINVAL; EPERM; EFAULT] []].
