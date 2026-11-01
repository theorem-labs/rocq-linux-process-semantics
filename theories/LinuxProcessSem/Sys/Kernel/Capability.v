(** * LinuxProcessSem.Sys.Kernel.Capability — capget (90), capset (91)

    This file answers to Linux [kernel/capability.c]: it holds what the
    kernel defines there, and nothing else.  Which file a spec belongs in
    is therefore not a judgement call — look up where the kernel defines
    the syscall.  [Specs.v] carries the whole map.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows.

    The kernel functions both arms follow, each read at v6.18.44:
    kernel/capability.c [SYSCALL_DEFINE2(capget)] read at v6.18.44; identical at v6.18.46.
    kernel/capability.c [SYSCALL_DEFINE2(capset)] read at v6.18.44; identical at v6.18.46.
    kernel/capability.c [cap_validate_magic] read at v6.18.44; identical at v6.18.46.
    kernel/capability.c [cap_get_target_pid] read at v6.18.44; identical at v6.18.46.
    security/security.c [security_capget] read at v6.18.44; identical at v6.18.46.
    security/security.c [security_capset] read at v6.18.44; identical at v6.18.46.
    security/commoncap.c [cap_capget] read at v6.18.44; identical at v6.18.46.
    security/commoncap.c [cap_capset] read at v6.18.44; identical at v6.18.46.
    security/commoncap.c [cap_inh_is_capped] read at v6.18.44; identical at v6.18.46.
    kernel/cred.c [prepare_creds] read at v6.18.44; identical at v6.18.46.
    kernel/cred.c [commit_creds] read at v6.18.44; identical at v6.18.46.
    And for the capability sets the answers report:
    security/commoncap.c [cap_bprm_creds_from_file] read at v6.18.44; identical at v6.18.46.
    security/commoncap.c [handle_privileged_root] read at v6.18.44; identical at v6.18.46.
    security/commoncap.c [get_file_caps] read at v6.18.44; identical at v6.18.46.
    security/commoncap.c [cap_task_fix_setuid] read at v6.18.44; identical at v6.18.46.
    security/commoncap.c [cap_emulate_setxuid] read at v6.18.44; identical at v6.18.46.
    kernel/sys.c [__sys_setuid], [__sys_setresuid] read at v6.18.44; identical at v6.18.46.
    fs/exec.c [check_unsafe_exec] read at v6.18.44; identical at v6.18.46. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export
  Syscall Uapi.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** [CAP_VALID_MASK] (include/linux/capability.h, read at v6.18.44;
    identical at v6.18.46): [BIT_ULL(CAP_LAST_CAP+1)-1], every
    capability the kernel defines, 0 to 40.  It is also the value of
    [CAP_FULL_SET], which is what an UNNARROWED bounding set holds. *)
Definition CAP_VALID_MASK : Z := Z.ones (CAP_LAST_CAP + 1).

(** The bytes a version-3 call moves between the kernel and [dataptr]:
    [_LINUX_CAPABILITY_U32S_3] = 2 [struct __user_cap_data_struct]s of
    three [__u32] each (include/uapi/linux/capability.h). *)
Definition CAP_V3_DATA_SIZE : Z := 24%Z.

(** The [k]-th [__u32] of a data image, little-endian.  In order:
    [kdata[0].effective], [.permitted], [.inheritable] (the low halves of
    the three 64-bit sets), then [kdata[1].effective], [.permitted],
    [.inheritable] (the high halves). *)
Definition cap_data_word (bs : list byte) (k : nat) : Z :=
  bytes_le_to_Z (firstn 4 (skipn (4 * k) bs)).

(** Whether the PERMITTED set is full: one of the real, effective and
    saved user ids is 0.  The EFFECTIVE set is full exactly when
    [State.creds_privileged] holds (the effective uid is 0).  Why both
    are exact, under the assumptions [State.creds_privileged] states, is
    the note on [capget_spec]. *)
Definition cap_permitted_full_b (c : Creds) : bool :=
  bv_eqb (cr_uid c) (Z_to_bv 64 0)
  || bv_eqb (cr_euid c) (Z_to_bv 64 0)
  || bv_eqb (cr_suid c) (Z_to_bv 64 0).

(** The data images [capget] may write, given whether the effective
    ([eff]) and the permitted ([perm]) sets are full: 24 bytes, the
    effective and permitted halves fixed, the inheritable low half any
    [__u32] and the inheritable high half any value within the valid
    capability bits (caps 32 to 40, so at most 0x1ff).  Written over
    the two booleans so that the witness can be checked by computation
    for each of the four cases. *)
Definition capget_data_ok_for (eff perm : bool) (bs : list byte) : bool :=
  let e := if eff then CAP_VALID_MASK else 0%Z in
  let p := if perm then CAP_VALID_MASK else 0%Z in
  Nat.eqb (length bs) (Z.to_nat CAP_V3_DATA_SIZE)
  && Z.eqb (cap_data_word bs 0) (Z.land e (Z.ones 32))   (* kdata[0].effective *)
  && Z.eqb (cap_data_word bs 1) (Z.land p (Z.ones 32))   (* kdata[0].permitted *)
                                          (* kdata[0].inheritable: any __u32 *)
  && Z.eqb (cap_data_word bs 3) (Z.shiftr e 32)          (* kdata[1].effective *)
  && Z.eqb (cap_data_word bs 4) (Z.shiftr p 32)          (* kdata[1].permitted *)
  && Z.leb (cap_data_word bs 5) (Z.shiftr CAP_VALID_MASK 32). (* kdata[1].inheritable *)

Definition capget_data_ok (c : Creds) (bs : list byte) : bool :=
  capget_data_ok_for (creds_privileged c) (cap_permitted_full_b c) bs.

(** [capget(header, dataptr)] — syscall 90, answered for a version-3
    header naming pid 0, and for nothing else.

    THE KERNEL FUNCTION, in its own order ([SYSCALL_DEFINE2(capget)]):

      ret = cap_validate_magic(header, &tocopy);
          -- get_user(version, &header->version): -EFAULT on a fault;
          -- v1: tocopy = 1; v2 and v3: tocopy = 2; any other version:
             put_user(v3, &header->version), then -EINVAL
      if (dataptr == NULL || ret != 0)
          return (dataptr == NULL && ret == -EINVAL) ? 0 : ret;
      if (get_user(pid, &header->pid))        return -EFAULT;
      if (pid < 0)                            return -EINVAL;
      ret = cap_get_target_pid(pid, &pE, &pI, &pP);
          -- pid 0 or the caller's own pid: security_capget(current, ...)
      kdata[0] = low halves, kdata[1] = high halves;
      if (copy_to_user(dataptr, kdata, tocopy * 12)) return -EFAULT;
      return 0;

    THE ANSWERED SHAPE.  Version 3 and pid 0.  With [dataptr] NULL the
    call returns 0 after reading only the version (the pid is never
    read).  Otherwise it reads the pid and writes 24 bytes.  Every other
    version and every non-zero pid is DECLINED: version 1 copies 12
    bytes and version 2 is the deprecated twin of 3, an unknown version
    writes the header back, a negative pid is -EINVAL and a positive one
    names a task this model may not hold.  Each is a real answer the
    model could be taught; none is needed by the callers this arm exists
    for (bubblewrap's [has_caps] and BET-467's launcher pass version 3
    and pid 0), so each fails closed.

    THE THREE USER-MEMORY ACCESSES, each judged the way
    [Kernel.Sys.uname_spec] and [Kernel.Sched.Syscalls.sched_setscheduler_spec]
    judge theirs: [access_ok] is asked FIRST and its refusal is -EFAULT,
    exact, before any byte moves; a range [access_ok] admits that is not
    wholly mapped is DECLINED rather than answered -EFAULT.  For the two
    reads that is the same convention [uname_spec] follows, not a gap in
    what the model knows: a faulting [get_user] answers exactly -EFAULT
    and changes nothing the program can see.  For the copy-out it is
    forced: a partial [copy_to_user] commits a prefix the model cannot
    name and then answers -EFAULT.  A range that is mapped is read (or
    written).  The version word and the pid word are two separate
    [get_user]s of 4 bytes, so they are two separate copy-in ranges, each
    recorded on every path past it.  The copy-out is 24 bytes at
    [dataptr].

    THE ANSWER: [cap_capget] copies the caller's own [cap_effective],
    [cap_permitted] and [cap_inheritable].  The model carries no
    capability sets ([State.Creds]'s note), so the effective and
    permitted sets are DERIVED from the uids, and the derivation is
    exact under the assumptions [State.creds_privileged] states: the init
    user namespace, no file capabilities on the executed binary, no
    ambient capabilities, default securebits, an unnarrowed bounding set
    — and an ordinary exec at launch: the exec that started the process
    was not unsafe ([check_unsafe_exec], fs/exec.c: no tracer, no
    no_new_privs, and no [fs_struct] shared with another process), so
    [cap_bprm_creds_from_file] did not cut the permitted set back to the
    parent's.  That is the world [State.init_model] pins.  Under them:

    - AT EXEC ([cap_bprm_creds_from_file]): [get_file_caps] clears the
      permitted set; [handle_privileged_root] sets it to
      [cap_bset | cap_inheritable] = every valid capability when the
      real or the effective uid is 0, and raises the effective bit when
      the effective uid is 0; the effective set is the permitted set
      when that bit is up, else the (empty) ambient set.  The saved uid
      equals the effective uid after exec.  So at launch the permitted
      set is full exactly when some uid is 0 and the effective set is
      full exactly when the effective uid is 0.
    - ON EVERY MODELED UID CHANGE ([setuid], [setresuid] reach
      [cap_task_fix_setuid] with [LSM_SETID_ID] / [LSM_SETID_RES], so
      [cap_emulate_setxuid] runs; [setgid] and [setresgid] touch no
      capability): leaving euid 0 clears the effective set; reaching
      euid 0 sets effective = permitted; and the permitted set is cleared
      once ALL of uid, euid and suid have left 0, which is absorbing
      ([State.creds_privileged]'s note says why).  So both
      biconditionals survive every modeled transition.
    - NOTHING ELSE MODELED MOVES THEM: [capset] below is answered only
      where it changes neither set, [prctl]'s answered options read
      or set no capability, and [PR_SET_KEEPCAPS], [PR_SET_SECUREBITS]
      and [PR_CAP_AMBIENT] are declined.

    The effective set is therefore every capability 0 to 40 when the
    effective uid is 0 and none otherwise; the permitted set is every
    capability when any of the three uids is 0 and none otherwise.  The
    INHERITABLE set is inherited across exec unchanged and the model does
    not carry it, so it is the environment's choice, constrained only to
    the valid capability bits (the kernel masks every set it stores with
    [CAP_VALID_MASK]).  It is chosen afresh on each call and not pinned —
    a widening: a real process reads the same set twice, and after an
    answered [capset] it reads 0.

    The LSM: [security_capget] calls every registered [capget] hook, and
    this arm assumes the capability module's alone ([cap_capget],
    which returns 0), the standing assumption [Kernel.Sys]'s credentials
    section names.  SELinux's hook can refuse with -EACCES and AppArmor's
    narrows the reported sets; a kernel running either is outside the
    model. *)
Definition capget_spec (header dataptr : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  if negb (access_okb header 4) then err_ret EFAULT
  else
    match read_bytes_map (in_mem i) header (Z_to_bv 64 4) with
    | None => unmodeled              (* get_user may fault after access_ok *)
    | Some vb =>
        record_copyins [(header, 4%nat)]
        (if negb (Z.eqb (bytes_le_to_Z vb) LINUX_CAPABILITY_VERSION_3)
         then unmodeled
         else if w_is0 dataptr then ret_only (Z_to_bv 64 0)
         else if negb (access_okb (header + Z_to_bv 64 4) 4) then err_ret EFAULT
         else
           match read_bytes_map (in_mem i) (header + Z_to_bv 64 4) (Z_to_bv 64 4) with
           | None => unmodeled
           | Some pb =>
               record_copyins [(header + Z_to_bv 64 4, 4%nat)]
               (if negb (Z.eqb (bytes_le_to_Z pb) 0) then unmodeled
                else if negb (access_okb dataptr CAP_V3_DATA_SIZE)
                then err_ret EFAULT
                else
                  match read_bytes_map (in_wmem i) dataptr
                          (Z_to_bv 64 CAP_V3_DATA_SIZE) with
                  | None => unmodeled  (* a partial copy_to_user, then -EFAULT *)
                  | Some _ =>
                      bs <- choose (fun bs : list byte =>
                                      capget_data_ok (m_creds m) bs = true) ;;
                      pure (mkEffect (Z_to_bv 64 0) [(dataptr, bs)] [])
                  end)
           end)
    end.

(** [capset(header, data)] — syscall 91, answered for ONE shape: version
    3, pid 0, all six data words 0, from a caller whose real, effective
    and saved uids are all non-zero.  The answer is 0 or -ENOMEM.

    THE KERNEL FUNCTION, in its own order ([SYSCALL_DEFINE2(capset)]):

      ret = cap_validate_magic(header, &tocopy);   if (ret) return ret;
      if (get_user(pid, &header->pid))             return -EFAULT;
      if (pid != 0 && pid != task_pid_vnr(current)) return -EPERM;
      if (copy_from_user(&kdata, data, tocopy * 12)) return -EFAULT;
      effective, permitted, inheritable = the words, masked to
                                          CAP_VALID_MASK;
      new = prepare_creds();                       if (!new) return -ENOMEM;
      ret = security_capset(new, current_cred(), ...);
                                                   if (ret < 0) abort, ret;
      return commit_creds(new);                    -- always 0

    [cap_capset] (the capability module's hook; the same capability-only
    LSM assumption as [capget_spec]) refuses with -EPERM a raised
    inheritable bit outside the old inheritable and permitted (unless
    the caller holds CAP_SETPCAP) or outside the old inheritable and
    bounding sets, a permitted set not inside the old permitted set, and
    an effective set not inside the new permitted set; else it installs
    the three sets and masks the ambient set.  All-zero sets pass every
    test from any caller, so the call returns 0 unless [prepare_creds]
    failed (-ENOMEM: a slab allocation, or [security_prepare_creds]).

    WHY ONLY A CALLER WITH NO UID 0.  Such a caller already holds empty
    effective and permitted sets ([capget_spec]'s derivation), so the
    call changes neither: the model's euid-based privilege
    ([State.creds_privileged]) and [capget_spec]'s derivation both stay
    exact.  It does set the inheritable set to 0, which the model does
    not carry; [capget_spec] keeps choosing it, a widening.  A caller
    with any uid 0 holds the full permitted set, and all-zero sets would
    DROP it: afterwards a euid-0 caller has no CAP_SETUID, which the
    model's privilege test cannot follow, so that call is declined.

    EVERY OTHER SHAPE IS DECLINED: another version (or an unknown one,
    whose header write-back the model does not carry), a non-zero pid
    (-EPERM for another task, but the model may not know its own pid),
    any non-zero data word (the answer then turns on the caller's sets
    in ways the model could derive but no caller here needs).  The
    user-memory accesses are judged as in [capget_spec]; the data read
    is one [copy_from_user] of 24 bytes and is recorded as one range. *)
Definition capset_spec (header data : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  if negb (access_okb header 4) then err_ret EFAULT
  else
    match read_bytes_map (in_mem i) header (Z_to_bv 64 4) with
    | None => unmodeled
    | Some vb =>
        record_copyins [(header, 4%nat)]
        (if negb (Z.eqb (bytes_le_to_Z vb) LINUX_CAPABILITY_VERSION_3)
         then unmodeled
         else if negb (access_okb (header + Z_to_bv 64 4) 4) then err_ret EFAULT
         else
           match read_bytes_map (in_mem i) (header + Z_to_bv 64 4) (Z_to_bv 64 4) with
           | None => unmodeled
           | Some pb =>
               record_copyins [(header + Z_to_bv 64 4, 4%nat)]
               (if negb (Z.eqb (bytes_le_to_Z pb) 0) then unmodeled
                else if negb (access_okb data CAP_V3_DATA_SIZE) then err_ret EFAULT
                else
                  match read_bytes_map (in_mem i) data (Z_to_bv 64 CAP_V3_DATA_SIZE) with
                  | None => unmodeled  (* a partial copy_from_user *)
                  | Some db =>
                      record_copyins [(data, Z.to_nat CAP_V3_DATA_SIZE)]
                      (if negb (Z.eqb (bytes_le_to_Z db) 0) then unmodeled
                       else if cap_permitted_full_b (m_creds m) then unmodeled
                       else alt (err_ret ENOMEM) (ret_only (Z_to_bv 64 0)))
                  end)
           end)
    end.
