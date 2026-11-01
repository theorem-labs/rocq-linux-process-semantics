(** * LinuxProcessSem.Ns.Task — arms on a task's own state

    The calls that read or change only what a task holds: its umask, its
    pid, its capability sets, its no_new_privs bit, its parent-death signal
    and its dumpable mode.  Each header names the Linux 6.18.44 functions it
    follows and its kind.

    The security modules are the capability module alone, as the released
    model's capability arms assume: [security_capget], [security_capset]
    and [security_task_prctl] are [cap_capget], [cap_capset] and
    [cap_task_prctl].  A read from user memory that [access_ok] admits but
    that finds an unmapped byte declines, as the released arms do; a write
    to user memory that is not wholly writable after [access_ok] declines
    too (a partial copy). *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Arm Userns.
Import ListNotations.
Local Open Scope Z_scope.

(* =========================================================================
   Setters on the task context
   ========================================================================= *)

Definition with_caps (ctx : NsCtx) (c : CapSets) : NsCtx :=
  mkNsCtx (cx_user ctx) (cx_mount ctx) (cx_pidns ctx) (cx_net ctx) (cx_pids ctx) (cx_root ctx)
          (cx_cwd ctx) (cx_umask ctx) c (cx_securebits ctx) (cx_cloexec ctx)
          (cx_no_new_privs ctx) (cx_pdeathsig ctx) (cx_dumpable ctx).

Definition with_pdeathsig (ctx : NsCtx) (s : Z) : NsCtx :=
  mkNsCtx (cx_user ctx) (cx_mount ctx) (cx_pidns ctx) (cx_net ctx) (cx_pids ctx) (cx_root ctx)
          (cx_cwd ctx) (cx_umask ctx) (cx_caps ctx) (cx_securebits ctx) (cx_cloexec ctx)
          (cx_no_new_privs ctx) s (cx_dumpable ctx).

Definition with_dumpable (ctx : NsCtx) (d : Z) : NsCtx :=
  mkNsCtx (cx_user ctx) (cx_mount ctx) (cx_pidns ctx) (cx_net ctx) (cx_pids ctx) (cx_root ctx)
          (cx_cwd ctx) (cx_umask ctx) (cx_caps ctx) (cx_securebits ctx) (cx_cloexec ctx)
          (cx_no_new_privs ctx) (cx_pdeathsig ctx) d.

Definition with_no_new_privs (ctx : NsCtx) : NsCtx :=
  mkNsCtx (cx_user ctx) (cx_mount ctx) (cx_pidns ctx) (cx_net ctx) (cx_pids ctx) (cx_root ctx)
          (cx_cwd ctx) (cx_umask ctx) (cx_caps ctx) (cx_securebits ctx) (cx_cloexec ctx)
          true (cx_pdeathsig ctx) (cx_dumpable ctx).

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
    in the task's namespace, then a valid number), PR_SET_PDEATHSIG (1,
    [valid_signal]), PR_GET_PDEATHSIG (2, [put_user] of the int),
    PR_GET_DUMPABLE (3), PR_SET_DUMPABLE (4, 0 or 1), PR_SET_NO_NEW_PRIVS
    (38) and PR_GET_NO_NEW_PRIVS (39), each with its argument checks.  The
    option is the low 32 bits of a0.  Any other option is DECLINED
    ([EUnmodeled]), never read as one of these eight.  Kind: exact, with
    [prepare_creds]'s ENOMEM for PR_CAPBSET_DROP, the environment's. *)
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
  else if opt =? 1 then
    (if 64 <? a2 then ns_errno EINVAL m ctx st else ns_ret (Z_to_bv 64 0) m (with_pdeathsig ctx a2) st)
  else if opt =? 2 then
    (match put_ok i (in_arg i 1) 4 with
     | PutFault => ns_errno EFAULT m ctx st
     | PutPartial => EUnmodeled
     | PutOk => EOk (mkEffect (Z_to_bv 64 0) [(in_arg i 1, u32_bytes (cx_pdeathsig ctx))] []) m ctx st []
     end)
  else if opt =? 3 then ns_ret (Z_to_bv 64 (cx_dumpable ctx)) m ctx st
  else if opt =? 4 then
    (if 1 <? a2 then ns_errno EINVAL m ctx st else ns_ret (Z_to_bv 64 0) m (with_dumpable ctx a2) st)
  else if opt =? 38 then
    (if negb ((a2 =? 1) && z3) then ns_errno EINVAL m ctx st
     else ns_ret (Z_to_bv 64 0) m (with_no_new_privs ctx) st)
  else if opt =? 39 then
    (if negb ((a2 =? 0) && z3) then ns_errno EINVAL m ctx st
     else ns_ret (Z_to_bv 64 (if cx_no_new_privs ctx then 1 else 0)) m ctx st)
  else EUnmodeled.

(** [cap_prctl_drop]'s [prepare_creds] ENOMEM, after its two checks. *)
Definition prctl_enomem (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState)
    : option ext_outcome :=
  if (s32 (in_arg i 0) =? 24) && own_capable m ctx st CAP_SETPCAP
     && (bv_unsigned (in_arg i 1) <=? 40)
  then Some (ns_errno ENOMEM m ctx st) else None.

Definition prctl_arm : NsArm := fun i m ctx st o =>
  o = prctl_fn i m ctx st \/ prctl_enomem i m ctx st = Some o.

Definition task_arms : list (Z * NsArm) :=
  [(90, capget_arm); (91, capset_arm); (166, umask_arm); (167, prctl_arm);
   (172, getpid_arm); (178, getpid_arm)].

(** The environment's refusals of these arms, for the forced-only filter:
    [prepare_creds]'s ENOMEM. *)
Definition task_injected : list NsInjected :=
  [mkNsInjected 91 [(fun e => e =? ENOMEM, FamAlloc)];
   mkNsInjected 167 [(fun e => e =? ENOMEM, FamAlloc)]].
