(** * LinuxProcessSem.Sys.Kernel.Capability — capget (90), capset (91)

    This file answers to Linux [kernel/capability.c]: it holds what the
    kernel defines there, and nothing else.  Which file a spec belongs in
    is therefore not a matter of choice — look up where the kernel defines
    the syscall.  [Specs.v] carries the whole map.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows.

    The kernel functions both arms follow, each read at v6.18.44:
    kernel/capability.c [SYSCALL_DEFINE2(capget)] read at v6.18.44; identical at v6.18.46.
    kernel/capability.c [SYSCALL_DEFINE2(capset)] read at v6.18.44; identical at v6.18.46.
    kernel/capability.c [cap_validate_magic] read at v6.18.44; identical at v6.18.46.
    kernel/capability.c [mk_kernel_cap] read at v6.18.44; identical at v6.18.46.
    kernel/capability.c [cap_get_target_pid] read at v6.18.44; identical at v6.18.46.
    security/security.c [security_capget] read at v6.18.44; identical at v6.18.46.
    security/security.c [security_capset] read at v6.18.44; identical at v6.18.46.
    security/commoncap.c [cap_capget] read at v6.18.44; identical at v6.18.46.
    security/commoncap.c [cap_capset] read at v6.18.44; identical at v6.18.46.
    security/commoncap.c [cap_inh_is_capped] read at v6.18.44; identical at v6.18.46.
    kernel/cred.c [prepare_creds] read at v6.18.44; identical at v6.18.46.
    kernel/cred.c [commit_creds] read at v6.18.44; identical at v6.18.46.
    kernel/cred.c [cred_cap_issubset] read at v6.18.44; identical at v6.18.46.
    include/linux/capability.h [cap_issubset], [cap_combine], [CAP_VALID_MASK] read at v6.18.44; identical at v6.18.46.
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
    capability the kernel defines, 0 to 40.  The kernel masks every set
    it stores with it. *)
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

(** Whether the PERMITTED set is non-empty: one of the real, effective
    and saved user ids is 0.  Under the assumptions
    [State.creds_privileged] states, a caller whose three uids are all
    non-zero holds empty effective and permitted sets, and a caller with
    a uid 0 holds [cap_bset | cap_inheritable] in its permitted set,
    which contains CAP_SETUID and CAP_SETGID but whose other bits the
    model does not know.  The note on [capget_spec] says why. *)
Definition cap_permitted_nonempty_b (c : Creds) : bool :=
  bv_eqb (cr_uid c) (Z_to_bv 64 0)
  || bv_eqb (cr_euid c) (Z_to_bv 64 0)
  || bv_eqb (cr_suid c) (Z_to_bv 64 0).

(** The inheritable set the caller holds, as Linux holds it: the stored
    word ([State.m_cap_inheritable]) within [CAP_VALID_MASK].  The kernel
    masks every set it stores with that mask, so a real process's set
    has no bit above [CAP_LAST_CAP]; a launch word may have one
    ([State.procst_cap_inheritable]: every word is a launch value), and
    such a bit names no capability.  For a launch word within the mask
    this is the stored word. *)
Definition cap_inheritable_set (m : Model) : Z :=
  Z.land (bv_unsigned (m_cap_inheritable m)) CAP_VALID_MASK.

(** The 24 bytes a version-3 [capget] copies out for a caller whose
    three uids are all non-zero, in [cap_data_word]'s order: the
    effective and permitted halves 0, and the inheritable set [inh] split
    as [SYSCALL_DEFINE2(capget)] splits it, [kdata[0].inheritable =
    pI.val] (the low 32 bits) and [kdata[1].inheritable = pI.val >> 32]. *)
Definition capget_image (inh : Z) : list byte :=
  Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 inh
  ++ Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 (Z.shiftr inh 32).

(** [capget(header, dataptr)] — syscall 90, answered for a version-3
    header naming pid 0, and for nothing else; the sets themselves are
    reported only to a caller whose three uids are all non-zero.

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
    read).  Otherwise it reads the pid and writes 24 bytes, for a caller
    with no uid 0; for one with a uid 0 the copy-out is declined (THE
    ANSWER, below).  Every other
    version and every non-zero pid is DECLINED: version 1 copies 12
    bytes and version 2 is the deprecated twin of 3, an unknown version
    writes the header back, a negative pid is -EINVAL and a positive one
    names a task this model may not hold.  Each is a real answer the
    model could be taught; none is needed by the callers this arm exists
    for (bubblewrap's [has_caps] and a sandbox launcher pass version 3
    and pid 0), so each fails closed.

    THE THREE USER-MEMORY ACCESSES, each decided the way
    [Kernel.Sys.uname_spec] and [Kernel.Sched.Syscalls.sched_setscheduler_spec]
    decide theirs: [access_ok] is asked FIRST and its refusal is -EFAULT,
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
    effective or permitted set ([State.Creds]'s note), so it answers only
    where the uids decide those two sets, and declines where they do
    not.  The derivation is exact under the assumptions
    [State.creds_privileged] states: the init user namespace, no file
    capabilities on the executed binary, no ambient capabilities,
    default securebits, a bounding set that holds CAP_SETUID and
    CAP_SETGID — and an ordinary exec at launch: the exec that started
    the process was not unsafe ([check_unsafe_exec], fs/exec.c: no
    tracer, no no_new_privs, and no [fs_struct] shared with another
    process), so [cap_bprm_creds_from_file] did not cut the permitted
    set back to the parent's.  That is the world [State.init_model]
    pins.  Under them:

    - AT EXEC ([cap_bprm_creds_from_file]): [get_file_caps] clears the
      permitted set; [handle_privileged_root] sets it to
      [cap_bset | cap_inheritable] when the real or the effective uid is
      0, and raises the effective bit when the effective uid is 0; the
      effective set is the permitted set when that bit is up, else the
      (empty) ambient set.  The saved uid equals the effective uid after
      exec.  So at launch the permitted set is empty exactly when no uid
      is 0, and the effective set is empty when the effective uid is not
      0.
    - ON EVERY MODELED UID CHANGE ([setuid], [setresuid] reach
      [cap_task_fix_setuid] with [LSM_SETID_ID] / [LSM_SETID_RES], so
      [cap_emulate_setxuid] runs; [setgid] and [setresgid] touch no
      capability): leaving euid 0 clears the effective set; reaching
      euid 0 sets effective = permitted; and the permitted set is cleared
      once ALL of uid, euid and suid have left 0, which is absorbing
      ([State.creds_privileged]'s note says why).  So a caller whose
      three uids are all non-zero holds empty effective and permitted
      sets, through every modeled transition.
    - NOTHING ELSE MODELED MOVES THEM: [capset] below is answered only
      where it changes neither set, [prctl]'s answered options read
      or set no capability set of the caller, and [PR_SET_KEEPCAPS],
      [PR_SET_SECUREBITS] and [PR_CAP_AMBIENT] are declined.

    A CALLER WITH A UID 0 IS DECLINED.  Its permitted set, and its
    effective set when the effective uid is 0, are [cap_bset |
    cap_inheritable].  The model assumes only that the bounding set holds
    CAP_SETUID and CAP_SETGID, and a container narrows the rest, so the
    other 39 bits of the answer are not known.  The
    decline comes where the sets are read, after the gates whose answers
    do not depend on them: the -EFAULTs, and the NULL-[dataptr] 0 that
    copies nothing out.

    For a caller with no uid 0 the effective and permitted sets are
    therefore empty.  The INHERITABLE set is the one the model holds
    ([State.m_cap_inheritable]): a launch value, kept across exec
    unchanged, copied by fork, and changed only by an answered
    [capset_spec] ([setuid], [setgid], [setresuid], [setresgid] and
    [setgroups] leave it, as [cap_task_fix_setuid] and [commit_creds]
    do).  The arm reads it within [CAP_VALID_MASK]
    ([cap_inheritable_set]) and copies it out split as the kernel splits
    it ([capget_image]).  So two calls with no [capset] between them
    report the same set, and a call after an answered [capset] reports
    the set that call installed.

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
                      if cap_permitted_nonempty_b (m_creds m)
                      then unmodeled   (* the sets read [cap_bset] *)
                      else
                        pure (mkEffect (Z_to_bv 64 0)
                                [(dataptr, capget_image (cap_inheritable_set m))] [])
                  end)
           end)
    end.

(** Whether the four effective and permitted words of a [capset] data
    image are 0: [kdata[0].effective], [kdata[0].permitted],
    [kdata[1].effective] and [kdata[1].permitted]. *)
Definition capset_ep_zero_b (db : list byte) : bool :=
  Z.eqb (cap_data_word db 0) 0 && Z.eqb (cap_data_word db 1) 0
  && Z.eqb (cap_data_word db 3) 0 && Z.eqb (cap_data_word db 4) 0.

(** The new inheritable set a [capset] data image names:
    [mk_kernel_cap(kdata[0].inheritable, kdata[1].inheritable)], the
    low and high halves joined and masked with [CAP_VALID_MASK]. *)
Definition capset_inheritable (db : list byte) : Z :=
  Z.land (Z.lor (cap_data_word db 2) (Z.shiftl (cap_data_word db 5) 32))
    CAP_VALID_MASK.

(** [cap_issubset(a, set)]: no bit of [a] outside [set]. *)
Definition cap_issubset_b (a set : Z) : bool :=
  Z.eqb (Z.land a (Z.lnot set)) 0.

(** [capset(header, data)] — syscall 91, answered for version 3, pid 0,
    effective and permitted words all 0 and any inheritable words, from
    a caller whose real, effective and saved uids are all non-zero.  The
    answer is -ENOMEM, -EPERM, or 0 with the new inheritable set
    installed.

    THE KERNEL FUNCTION, in its own order ([SYSCALL_DEFINE2(capset)]):

      ret = cap_validate_magic(header, &tocopy);   if (ret) return ret;
      if (get_user(pid, &header->pid))             return -EFAULT;
      if (pid != 0 && pid != task_pid_vnr(current)) return -EPERM;
      if (copy_from_user(&kdata, data, tocopy * 12)) return -EFAULT;
      effective, permitted, inheritable =
          mk_kernel_cap(kdata[0].x, kdata[1].x);   -- the halves joined,
                                                      masked to CAP_VALID_MASK
      new = prepare_creds();                       if (!new) return -ENOMEM;
      ret = security_capset(new, current_cred(), ...);
                                                   if (ret < 0) abort, ret;
      return commit_creds(new);                    -- always 0

    [cap_capset] (the capability module's hook; the same capability-only
    LSM assumption as [capget_spec]) refuses with -EPERM, in this order:
    a new inheritable set outside the old inheritable and permitted sets
    combined, unless [cap_inh_is_capped] finds CAP_SETPCAP in the
    caller's effective set; a new inheritable set outside the old
    inheritable and bounding sets combined; a permitted set not inside
    the old permitted set; an effective set not inside the new permitted
    set.  Else it installs the three sets and masks the ambient set.

    THE ANSWER, AND HOW EACH TEST IS DECIDED WITHOUT THE BOUNDING SET.
    The caller has no uid 0, so under the assumptions
    [State.creds_privileged] states its effective and permitted sets are
    empty ([capget_spec]'s derivation).  Then:
    - CAP_SETPCAP is not in its effective set ([cap_capable] reads the
      effective set in the init user namespace), [cap_inh_is_capped]
      holds, and the first test asks for the new inheritable set within
      the old inheritable set ([cap_inheritable_set]) combined with the
      empty permitted set: within the old inheritable set alone.
    - The second test asks for the new set within the old inheritable set
      combined with the bounding set.  Every set that passed the first
      test passes it, so the bounding set, which the model knows only to
      hold CAP_SETUID and CAP_SETGID, decides nothing here.
    - The permitted and effective words are 0, so the last two tests
      pass.
    So the arm answers -EPERM exactly when the new inheritable set
    ([capset_inheritable]) has a bit outside the held one
    ([cap_issubset_b]), and otherwise 0 with the new set installed
    ([State.with_cap_inheritable]).  The effective and permitted sets stay
    empty, and the ambient set, empty by assumption, stays empty.
    [prepare_creds] runs before [security_capset], so -ENOMEM (a slab
    allocation, or [security_prepare_creds]) is an answer for every data
    image the arm answers.

    WHY ONLY A CALLER WITH NO UID 0.  For such a caller the call changes
    neither the effective nor the permitted set, so the model's
    euid-based privilege ([State.creds_privileged]) and [capget_spec]'s
    derivation both stay exact.  A caller with any uid 0 holds a
    non-empty permitted set, [cap_bset | cap_inheritable], whose bits
    other than CAP_SETUID and CAP_SETGID the model does not know; the
    first and third tests read it, and a call that drops it leaves a
    euid-0 caller without CAP_SETUID, which the model's privilege test
    cannot follow.  So that call is declined.

    THE PARENT-DEATH SIGNAL AND THE DUMPABLE MODE STAY.  [commit_creds]
    (kernel/cred.c) resets [pdeath_signal] and the dumpable mode when the
    effective or filesystem ids move or when [cred_cap_issubset(old,
    new)] fails, that is, when the new permitted set is not inside the
    old one.  The answered call moves no id and leaves the permitted set
    empty, as it was.  So the arm leaves [State.m_pdeath_signal] and
    [State.m_dumpable] alone, with the rest of the model but the
    inheritable set.

    EVERY OTHER SHAPE IS DECLINED: another version (or an unknown one,
    whose header write-back the model does not carry), a non-zero pid
    (-EPERM for another task, but the model may not know its own pid),
    and a non-zero effective or permitted word (for this caller Linux
    then answers -ENOMEM or -EPERM when the masked word is non-zero, and
    as for a zero word when it is not; the arm keeps the shape it
    answered before).  The user-memory accesses are decided as in
    [capget_spec]; the data read is one [copy_from_user] of 24 bytes and
    is recorded as one range. *)
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
                      (if negb (capset_ep_zero_b db) then unmodeled
                       else if cap_permitted_nonempty_b (m_creds m) then unmodeled
                       else alt (err_ret ENOMEM)
                              (if cap_issubset_b (capset_inheritable db)
                                    (cap_inheritable_set m)
                               then modify (with_cap_inheritable
                                              (Z_to_bv 64 (capset_inheritable db))) ;;
                                    ret_only (Z_to_bv 64 0)
                               else err_ret EPERM))
                  end)
           end)
    end.
