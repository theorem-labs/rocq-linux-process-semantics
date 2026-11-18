(** * LinuxProcessSem.Sys.Fs.DPath — getcwd (17)

    This file answers to Linux [fs/d_path.c]: it holds what the kernel
    defines there, and nothing else.  Which file a spec belongs in is
    therefore not a judgement call — look up where the kernel defines
    the syscall.  [Specs.v] carries the whole map.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows.

    Ported from theorem-labs/linux-process-semantics
    r22/namespace-core at 6ff3d045 (issue #1011). *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export
  Syscall Uapi Uaccess.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** getcwd's one injectable failure.

    - ENOMEM — [__getname()], the very first statement, is a
      [GFP_KERNEL] allocation out of [names_cachep] and can fail.  It
      is the only error that returns without the RCU section running at
      all, and the only one this model cannot decide from its own
      state.

    (Linux v6.18.46, fs/d_path.c:416-419, [SYSCALL_DEFINE2(getcwd)].)

    ENOENT IS GONE, and the namespace is what removed it.  It is
    [d_unlinked(pwd.dentry)] (fs/d_path.c:424-426): the working
    directory has been removed from the dcache hash by someone else.
    Nothing inside the run can
    produce it — [Fs.Namei]'s rmdir DECLINES the cwd, an ancestor of the
    cwd and a directory an open [State.FdDir] names, so no modeled step
    reaches a state whose cwd is unlinked — and nothing outside the run
    can either, under the image-wide "no concurrent writer" premise
    [Fs]'s header states.  Injecting it would be admitting an answer no
    reachable state justifies.

    ENAMETOOLONG IS GONE FROM THIS LIST TOO, and for the opposite
    reason: it is now DERIVED rather than injected.  The assembled
    length is [length (m_cwd m) + 1], which the model holds, so the arm
    below compares it against PATH_MAX itself and answers
    -ENAMETOOLONG when it does not fit.  [Run.valid_input]'s [in_cwd]
    bound makes that branch unreachable from a valid input, but the
    spec is a statement about every [Model], so the branch is written
    rather than assumed away.

    EFAULT is not injectable either: it is the [copy_to_user] below,
    decided by the destination range. *)
Definition getcwd_errnos : list Z := [ENOMEM].

(** The bytes [getcwd] delivers for the working directory [cwd]: the
    path itself and the terminating NUL.  The kernel builds them
    backwards into a [PATH_MAX] page — [prepend_char(&b, 0)] writes the
    NUL first and [prepend_path] prepends the components — and hands
    the whole run to one [copy_to_user], so the delivered string is the
    absolute path followed by exactly one NUL. *)
Definition getcwd_bytes (cwd : Fs.path) : list byte :=
  cwd ++ [Fs.path_nul_byte].

(** The value [getcwd] returns on success and compares against [size]:
    the length of the string INCLUDING the terminating NUL.  The
    comment above [SYSCALL_DEFINE2(getcwd)] states the convention and
    the line [error = len;] is where it happens; [len = PATH_MAX -
    b.len] counts the NUL because [prepend_char(&b, 0)] consumed a byte
    for it. *)
Definition getcwd_len (cwd : Fs.path) : nat := S (length cwd).

(** [getcwd buf size]: copy the caller's working directory out, and
    return its length INCLUDING the terminating NUL.

    THE WORKING DIRECTORY IS NOW A TERM IN THE MODEL, and that is what
    lifted this arm off its decline.  [State.m_cwd] is the absolute
    canonical key [Run.valid_input] declares and [init_model] copies in,
    and nothing writes it afterwards — there is no chdir, no fchdir and
    no [CLONE_FS] arm in this model.  So the string this call returns is
    a function of modeled state, where before R22 it was not a function
    of anything at all.  The answer is the DECLARED working directory,
    which is the maintainer's ruling on issue #1011, section 15,
    question 9.

    THE ANSWER IS EXACT rather than approximate, on the one premise the
    declaration carries.  The kernel assembles the path by walking
    dentries from the working directory up to the caller's root, and the
    model's [m_cwd] is that walk's result already spelled out.  The two
    agree exactly when the run's root is the filesystem root, which is
    the same premise every other absolute key in the image rests on: the
    model has one namespace and no mount tree.  A chroot or a bind mount
    that made the declared key unreachable from the caller's root would
    make Linux answer a DIFFERENT string with a "(unreachable)" prefix,
    and the model would then be wrong rather than narrower — which is
    why the premise is written here instead of left to the reader.

    THE ORDER IS THE KERNEL'S, reading [SYSCALL_DEFINE2(getcwd)] in
    Linux v6.18.46, fs/d_path.c:412-448:

    - [__getname()] first (416-419), whose failure is -ENOMEM and the
      only injectable answer left;
    - then [d_unlinked(pwd.dentry)]'s -ENOENT (424-426), which no
      reachable state of this model satisfies (see [getcwd_errnos]);
    - then the path is built into a KERNEL page (429-433), so nothing
      about [buf] has been looked at yet;
    - then [len > PATH_MAX] is -ENAMETOOLONG (437-438);
    - then [len > size] is -ERANGE (439-440);
    - then, and only then, one [copy_to_user] (441-442).

    WHY [buf] IS NOT CONSULTED BEFORE THE SIZE TEST.  There is no
    [access_ok] and no probe of [buf] anywhere earlier, so
    [getcwd(NULL, 0)] really is -ERANGE and a spec that answered -EFAULT
    for it would be wrong.  The -EINVAL POSIX documents for a zero size
    is glibc's own — [sysdeps/unix/sysv/linux/getcwd.c] answers it
    before issuing the call — and the syscall body has no -EINVAL arm at
    all.

    THE DELIVERY, and its two failures.  [copy_to_user] checks the whole
    range before a byte moves, so a destination outside the user address
    space is -EFAULT with nothing written ([State.access_okb]).  A range
    that passes that test and then faults mid-copy leaves a partially
    written buffer this model has no vocabulary for, and that is
    [unmodeled] — the same shape [Fs.Stat.fstat_file_spec] and
    [Kernel.Sys.uname_spec] decline for the same reason.

    EACH DETERMINISTIC ANSWER IS OFFERED BESIDE THE -ENOMEM as an [alt]
    rather than ranked against it: [__getname()] runs before any of
    them, so in any single run exactly one applies, and which one is
    decided by an allocator condition the model does not carry.

    THE PARTIAL-COPY DECLINE IS HOISTED ABOVE THAT [alt], and the
    position is forced rather than stylistic.  [alt c unmodeled] admits
    BOTH an injected errno and [Unmodeled], which is two verdicts where
    an executable checker can give one; putting the decline outside
    makes the whole call [Unmodeled] in that state.  The cost is that a
    run whose destination faults mid-copy no longer admits the -ENOMEM
    it could have answered instead — a narrowing, which is the safe
    direction, and the state is one no example reaches. *)
Definition getcwd_spec (buf size : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  let cwd := m_cwd m in
  let bs := getcwd_bytes cwd in
  let len := getcwd_len cwd in
  let inject := (e <- errno_from getcwd_errnos ;; err_ret e) in
  if Nat.ltb path_max len then alt inject (err_ret ENAMETOOLONG)
    (* the assembled path did not fit the PATH_MAX page.  Not reachable
       from a valid input — [Run.valid_input] bounds [in_cwd] — but this
       is a statement about every [Model] *)
  else if (bv_unsigned size <? Z.of_nat len)%Z then
    alt inject (err_ret ERANGE)
    (* [len > size]: the caller's buffer is too small, whatever it
       points at *)
  else if negb (access_okb buf (Z.of_nat len)) then
    alt inject (err_ret EFAULT)
    (* [copy_to_user]'s own range test, before a byte moves *)
  else
    match read_bytes_map (in_wmem i) buf (len_word bs) with
    | None => unmodeled
        (* a [copy_to_user] that commits a prefix and then faults: a
           half-written buffer the model cannot describe *)
    | Some _ =>
        alt inject
            (pure (mkEffect (Z_to_bv 64 (Z.of_nat len))
                     (delivered_writes buf bs) []))
    end.

(** THE BAND EVERY CALLER THAT CANNOT SEE THE DESTINATION READS THIS
    ARM THROUGH: a buffer too small for the string reduces the whole
    call to the injected -ENOMEM beside the deterministic -ERANGE,
    whatever [buf] points at and whatever the working directory is.
    [Checks.SpuriousCfg] is the consumer — it asks which answers a
    configuration may refuse, and this is what says the -ERANGE is
    always one of them. *)
Lemma getcwd_spec_erange_band : forall buf size i m o,
  Nat.ltb path_max (getcwd_len (m_cwd m)) = false ->
  (bv_unsigned size <? Z.of_nat (getcwd_len (m_cwd m)))%Z = true ->
  (getcwd_spec buf size i m o
   <-> alt (e <- errno_from getcwd_errnos ;; err_ret e) (err_ret ERANGE) i m o).
Proof.
  intros buf size i m o Hlen Hsize.
  unfold getcwd_spec. rewrite bind_input_model. cbv zeta.
  now rewrite Hlen, Hsize.
Qed.
