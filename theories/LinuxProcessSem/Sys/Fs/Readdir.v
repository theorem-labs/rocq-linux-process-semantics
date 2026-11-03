(** * LinuxProcessSem.Sys.Fs.Readdir — getdents64 (61)

    This file answers to Linux [fs/readdir.c]: it holds what the kernel
    defines there, and nothing else.  Which file a spec belongs in is
    therefore not a judgement call — look up where the kernel defines
    the syscall.  [Specs.v] carries the whole map.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export
  Syscall Uapi.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** getdents64's injectable failure: one environment condition the model
    does not track, and the only one getdents(2) documents that a
    modeled arm could otherwise preempt.  [iterate_dir] (Linux
    fs/readdir.c, v6.18.46) answers -ENOENT for [IS_DEADDIR(inode)] — a
    directory removed since the fd was opened — and does so BEFORE it
    calls the filesystem's [.iterate_shared], hence before the -EINVAL
    below is reached.

    -EBADF and -ENOTDIR are NOT injectable: both are decided from state
    the model does carry (the fd table, and the fd's kind).  -EFAULT is
    not either: every arm this spec admits is settled before the kernel
    touches the destination buffer — see the note at
    [getdents64_spec]. *)
Definition getdents64_errnos : list Z := [ENOENT].

(** The SMALLEST record any directory entry can occupy in a
    [struct linux_dirent64] buffer, in bytes.

    [filldir64] (Linux fs/readdir.c, v6.18.46) computes

      reclen = ALIGN(offsetof(struct linux_dirent64, d_name) + namlen + 1,
                     sizeof(u64))

    and [struct linux_dirent64] (Linux include/linux/dirent.h, v6.18.46)
    is [u64 d_ino; s64 d_off; unsigned short d_reclen; unsigned char
    d_type; char d_name[]], so [offsetof(..., d_name)] is 19.  A name is
    at least one byte — [verify_dirent_name] (Linux fs/readdir.c,
    v6.18.46) refuses [len <= 0], and no filesystem emits an empty
    name — so
    [reclen >= ALIGN(19 + 1 + 1, 8) = 24], with equality for the
    one-byte name ".".

    This is a floor over ALL entries, not a fact about any one of them,
    which is what lets the spec use it without knowing what the
    directory holds. *)
Definition dirent64_min_reclen : Z := 24%Z.

(** The buffer size AS THE KERNEL COMPARES IT.  [count] arrives declared
    [unsigned int] ([SYSCALL_DEFINE3(getdents64, unsigned int, fd,
    struct linux_dirent64 __user *, dirent, unsigned int, count)], Linux
    fs/readdir.c, v6.18.46), so the high half of the register is gone
    before anything reads it — the same narrowing [Syscall.fd32]
    describes for a file descriptor.  It is then stored into
    [ctx.count], which [struct dir_context] (Linux include/linux/fs.h,
    v6.18.46) declares [int], and [filldir64]'s [reclen > ctx->count] is
    a SIGNED comparison.

    So the two conversions compose into "the low 32 bits, read as two's
    complement", which is exactly [Syscall.sint32] — and the composition
    is observable rather than pedantic: a [count] at or above 2^31 is a
    NEGATIVE [ctx->count], so [getdents64(dirfd, buf, 0x80000000)] is
    -EINVAL on Linux, not a large successful read.  Comparing the
    unsigned register instead would have admitted a success no kernel
    produces. *)
Definition getdents64_ctx_count (count : word) : Z := sint32 count.

(** Is the buffer too small for the first entry, whatever that entry
    turns out to be? *)
Definition getdents64_no_room (count : word) : bool :=
  (getdents64_ctx_count count <? dirent64_min_reclen)%Z.

(* -------------------------------------------------------------------------
   The /proc/self/fd listing ([State.OProcFdDir])
   ------------------------------------------------------------------------- *)

(** [d_reclen] of a record whose name is [namlen] bytes:
    [ALIGN(offsetof(struct linux_dirent64, d_name) + namlen + 1, 8)], with
    [offsetof(..., d_name)] = 19 ([dirent64_min_reclen]'s note).
      fs/readdir.c [filldir64]: read at v6.18.44; identical at v6.18.46. *)
Definition dirent64_reclen (namlen : nat) : Z :=
  ((19 + Z.of_nat namlen + 1 + 7) / 8 * 8)%Z.

(** The name [snprintf(name, sizeof(name), "%u", fd)] gives descriptor
    [n], most significant digit first.  [n] is below 2^31 wherever it is
    used ([procfd_getdents_spec]'s guard), so ten digits suffice. *)
Fixpoint dec_digits_rev (fuel : nat) (n : Z) : list byte :=
  match fuel with
  | O => []
  | S f => Z_to_bv 8 (48 + n mod 10)
           :: (if (n <? 10)%Z then [] else dec_digits_rev f (n / 10))
  end.

Definition procfd_name (n : Z) : list byte := rev (dec_digits_rev 10 n).

Definition dot_name : list byte := [Z_to_bv 8 46].
Definition dotdot_name : list byte := [Z_to_bv 8 46; Z_to_bv 8 46].

(** One entry of the listing: its name, the position [ctx->pos] holds
    while the entry is offered, and whether it is a descriptor (rather
    than "." or ".."). *)
Record procfd_ent := mkProcfdEnt {
  pfe_name : list byte;
  pfe_pos  : Z;
  pfe_isfd : bool
}.

(** The smallest key of [ks] at or above [lo]. *)
Definition min_key_ge (ks : list Z) (lo : Z) : option Z :=
  fold_left (fun acc k =>
               if (lo <=? k)%Z
               then match acc with
                    | None => Some k
                    | Some b => Some (Z.min b k)
                    end
               else acc) ks None.

(** The descriptors from [lo] up, in ascending order, as
    [proc_readfd_common]'s loop meets them: [fget_task_next] finds the
    next open descriptor at or after [fd], and [ctx->pos] is set to
    [fd + 2] before the entry is offered.  [fget_task_next] passes mask 0
    to [__fget_files_rcu], so every open file is listed, O_PATH ones
    included.  Each step takes a key above the last, so [S (length ks)]
    steps always reach the end.
      fs/proc/fd.c [proc_readfd_common], fs/file.c [fget_task_next]: read at v6.18.44; identical at v6.18.46. *)
Fixpoint procfd_fd_ents (fuel : nat) (ks : list Z) (lo : Z) : list procfd_ent :=
  match fuel with
  | O => []
  | S f =>
      match min_key_ge ks lo with
      | None => []
      | Some k => mkProcfdEnt (procfd_name k) (k + 2) true
                  :: procfd_fd_ents f ks (k + 1)
      end
  end.

(** Every entry left to list from position [p]: [dir_emit_dots] gives "."
    at 0 and ".." at 1, and the descriptors follow from [p - 2].
      include/linux/fs.h [dir_emit_dots]: read at v6.18.44; identical at v6.18.46. *)
Definition procfd_plan (fds : list (word * FdEntry)) (p : Z) : list procfd_ent :=
  let ks := map (fun kv => bv_unsigned (fst kv)) fds in
  (if (p =? 0)%Z then [mkProcfdEnt dot_name 0 false] else [])
  ++ (if (p <=? 1)%Z then [mkProcfdEnt dotdot_name 1 false] else [])
  ++ procfd_fd_ents (S (length ks)) ks (Z.max 0 (p - 2)).

(** How many entries [filldir64] accepts into [room] bytes: it refuses
    the first whose [reclen] exceeds what is left ([reclen > ctx->count]),
    and the iteration stops there. *)
Fixpoint procfd_fit (es : list procfd_ent) (room : Z) : nat :=
  match es with
  | [] => O
  | e :: r =>
      let rl := dirent64_reclen (length (pfe_name e)) in
      if (rl <=? room)%Z then S (procfd_fit r (room - rl)) else O
  end.

(** Where each written record starts. *)
Fixpoint procfd_addrs (dirent : word) (es : list procfd_ent) : list word :=
  match es with
  | [] => []
  | e :: r => dirent :: procfd_addrs (dirent + Z_to_bv 64 (dirent64_reclen (length (pfe_name e)))) r
  end.

(** The bytes the written records occupy, padding included: the return
    value [count - ctx.count]. *)
Definition procfd_total (es : list procfd_ent) : Z :=
  fold_right (fun e acc => dirent64_reclen (length (pfe_name e)) + acc)%Z 0%Z es.

(** One record as [filldir64] leaves it: [d_ino] (8 bytes), [d_off] (8),
    [d_reclen] (2), [d_type] (1), the name and its NUL.  The padding up to
    [d_reclen] is not written ([unsafe_copy_dirent_name] stops at the
    NUL), so it is not part of the record's bytes here.

    [d_ino] is the environment's.  [d_type] is [DT_DIR] for "." and
    "..", and for a descriptor [DT_LNK] (its inode is made [S_IFLNK] by
    [proc_fd_instantiate]), or [DT_UNKNOWN] with [d_ino] 1 when
    [proc_fill_cache] could not get a dentry.  [d_off] is the position of
    the NEXT entry: [filldir64] writes each entry's offset into the
    previous record, and [SYSCALL_DEFINE3(getdents64)] writes the final
    [ctx.pos] into the last one; [doff_ok] says which bytes it may hold.
    [d_off] and [d_reclen] are little-endian ([put_user] of an [s64] and
    an [unsigned short] on riscv64), so a known value is compared as its
    encoding.
      fs/readdir.c [filldir64], [SYSCALL_DEFINE3(getdents64)], fs/proc/base.c [proc_fill_cache],
      fs/proc/fd.c [proc_fd_instantiate]: read at v6.18.44; identical at v6.18.46. *)
Definition dirent64_rec_ok (e : procfd_ent) (doff_ok : list byte -> bool) (bs : list byte) : bool :=
  let nl := length (pfe_name e) in
  let ty := bv_unsigned (nth 18 bs (Z_to_bv 8 0)) in
  Nat.eqb (length bs) (20 + nl)
  && doff_ok (firstn 8 (skipn 8 bs))
  && path_eqb (firstn 2 (skipn 16 bs)) (Z_to_le_bytes 2 (dirent64_reclen nl))
  && (if pfe_isfd e
      then Z.eqb ty DT_LNK || (Z.eqb ty DT_UNKNOWN && Z.eqb (bytes_le_to_Z (firstn 8 bs)) 1)
      else Z.eqb ty DT_DIR)
  && path_eqb (firstn nl (skipn 19 bs)) (pfe_name e)
  && Z.eqb (bv_unsigned (nth (19 + nl) bs (Z_to_bv 8 1))) 0.

(** The final [ctx.pos] when the listing ran to its end: [fget_task_next]
    found no descriptor before [max_fds], so the position is
    [max_fds + 2].  The model does not know [max_fds]; it is above every
    open descriptor and at most [sysctl_nr_open], below 2^31.  Any such
    value is admitted: a widening, and a sound one.
      fs/file.c [fget_task_next], [sysctl_nr_open_max]: read at v6.18.44; identical at v6.18.46. *)
Definition procfd_end_ok (fds : list (word * FdEntry)) (z : Z) : bool :=
  (3 <=? z)%Z && (z <=? 2 ^ 31 + 2)%Z
  && forallb (fun kv => (bv_unsigned (fst kv) + 2 <? z)%Z) fds.

(** The [n] written records, each checked against the entry after it in
    the plan (or, for the last entry of the plan, the end). *)
Fixpoint procfd_recs_ok (end_ok : Z -> bool) (es : list procfd_ent) (n : nat)
    (bss : list (list byte)) : bool :=
  match n, es, bss with
  | O, _, [] => true
  | S n', e :: r, bs :: bss' =>
      let doff_ok := match r with
                     | e' :: _ => fun b8 => path_eqb b8 (Z_to_le_bytes 8 (pfe_pos e'))
                     | [] => fun b8 => end_ok (bytes_le_to_Z b8)
                     end in
      dirent64_rec_ok e doff_ok bs && procfd_recs_ok end_ok r n' bss'
  | _, _, _ => false
  end.

(** The position the call leaves: the last record's [d_off], which is
    the final [ctx.pos] [iterate_dir] stores back into [f_pos]. *)
Definition procfd_last_doff (bss : list (list byte)) : Z :=
  bytes_le_to_Z (firstn 8 (skipn 8 (last bss []))).

(** Every record's bytes land in writable memory. *)
Fixpoint procfd_writable (mp : word -> option byte) (addrs : list word)
    (es : list procfd_ent) : bool :=
  match addrs, es with
  | a :: addrs', e :: es' =>
      match read_bytes_map mp a (Z_to_bv 64 (20 + Z.of_nat (length (pfe_name e)))) with
      | Some _ => procfd_writable mp addrs' es'
      | None => false
      end
  | _, _ => true
  end.

(** The descriptor table and the position are below 2^31: the names are
    at most ten digits and the positions fit the arithmetic above.  A
    table or a position past that is declined. *)
Definition procfd_in_range (fds : list (word * FdEntry)) (p : Z) : bool :=
  (p <? 2 ^ 31)%Z && forallb (fun kv => (bv_unsigned (fst kv) <? 2 ^ 31)%Z) fds.

(** [getdents64] on the /proc/self/fd directory open at position [pos]
    (with open word [fl]) as descriptor [fd].

    The fd is open and is a directory with an [.iterate_shared]
    ([proc_fd_operations]), so [iterate_dir] runs [proc_readfd_common]
    from [f_pos] and stores [ctx->pos] back into [f_pos] whatever the
    result.  [get_proc_task] finds the caller itself, and the directory
    is not dead, so neither -ENOENT is reachable; the LSM and fanotify
    verdicts are approximated as on the [FdDir] arm.

    - Nothing left to list: 0, and [f_pos] becomes [max_fds + 2] (or
      stays), which the model does not know: the position becomes
      [None], and a later [getdents64] declines.
    - The first entry does not fit: -EINVAL, and [f_pos] is that entry's
      position.
    - The first record's range fails [access_ok]
      ([user_write_access_begin]): -EFAULT, nothing written, and [f_pos]
      is the first entry's position.
    - Every record that fits lands in writable memory: the records, the
      byte count, and [f_pos] is the last record's [d_off].
    - Otherwise a record would fault part way: declined.

    A position of [None] is declined, and so is a table or position at or
    past 2^31 ([procfd_in_range]).
      fs/readdir.c [iterate_dir], [SYSCALL_DEFINE3(getdents64)], [filldir64],
      fs/proc/fd.c [proc_readfd_common], [proc_fd_iterate]: read at v6.18.44; identical at v6.18.46. *)
Definition procfd_getdents_spec (fd fl : word) (pos : option word)
    (dirent count : word) : Sys SyscallEffect :=
  match pos with
  | None => unmodeled
  | Some pw =>
      m <- get_model ;;
      let p := bv_unsigned pw in
      if negb (procfd_in_range (m_fds m) p) then unmodeled
      else
      let es := procfd_plan (m_fds m) p in
      let n := procfd_fit es (getdents64_ctx_count count) in
      let setpos := fun np : option word =>
        set_fds (fd_insert (m_fds m) fd (FdOpaque (OProcFdDir fl np))) in
      match n, es with
      | O, [] => setpos None ;; ret_only (Z_to_bv 64 0)
      | O, e :: _ => setpos (Some (Z_to_bv 64 (pfe_pos e))) ;; err_ret EINVAL
      | S _, [] => unmodeled   (* unreachable: [procfd_fit] of [] is 0 *)
      | S _, e :: _ =>
          if negb (access_okb dirent (dirent64_reclen (length (pfe_name e))))
          then setpos (Some (Z_to_bv 64 (pfe_pos e))) ;; err_ret EFAULT
          else
          i <- input ;;
          let ws := firstn n es in
          let addrs := procfd_addrs dirent ws in
          if access_okb dirent (procfd_total ws)
             && procfd_writable (in_wmem i) addrs ws
          then
            bss <- choose (fun bss => procfd_recs_ok (procfd_end_ok (m_fds m)) es n bss = true) ;;
            setpos (Some (Z_to_bv 64 (procfd_last_doff bss))) ;;
            pure (mkEffect (Z_to_bv 64 (procfd_total ws)) (combine addrs bss) [])
          else unmodeled
      end
  end.

(** [getdents64] on a descriptor of [State.FdOpaque]. *)
Definition getdents64_opaque_spec (fd : word) (o : OpaqueFd) (dirent count : word)
    : Sys SyscallEffect :=
  match o with
  | OProcFdDir fl pos => procfd_getdents_spec fd fl pos dirent count
  | OProcPath _ | OProcFile _ | OEventFd _ | ONsFile _ | OSignalFd _ _ => unmodeled
      (* FAIL-CLOSED: [CLASS(fd_pos, f)] refuses an O_PATH file (-EBADF);
         the two sysctl files, an eventfd and a signalfd have no
         [.iterate_shared] (-ENOTDIR); an [ONsFile]'s object is of unknown
         type.  None of these is written (fs/readdir.c, fs/file.c,
         fs/eventfd.c, fs/proc/proc_sysctl.c, fs/signalfd.c, read at
         v6.18.44; identical at v6.18.46). *)
  end.

(** [getdents64 fd dirent count]: read directory entries into [dirent].

    ONE DIRECTORY IS LISTED: "/proc/self/fd" ([State.OProcFdDir]), whose
    entries the model DOES carry, because they are its own descriptor
    table.  [procfd_getdents_spec] below answers it.  Every other
    directory's listing is declined, for the reasons that follow.

    THE SUCCESS ARM IS NOT MODELED FOR [FdDir], AND CANNOT BE FROM WHAT
    THIS MODEL CARRIES.  A successful call fills the buffer with [struct
    linux_dirent64] records — [d_ino], [d_off], [d_reclen], [d_type] and
    the name — and returns the byte count.  Three INDEPENDENT things
    stand in the way, and closing any one of them leaves the other two:

    - [State.FdDir] IS NULLARY.  It records that the fd names a
      directory and nothing else, so the model cannot tell an fd opened
      on "." from one opened on ".." — the only two paths
      [Open.path_is_dirref] admits.  Enumerating the working directory
      for BOTH is a confident wrong answer for one of them, and the
      model has nothing to branch on.  [Open.openat_spec] answers ".."
      at all only because nothing the model can then do to the fd tells
      the two apart — read is -EISDIR for either, close is close, lseek
      is declined — and this spec is the clause of that argument that
      names getdents64.  A listing arm would break it, not merely be
      wrong on its own.
    - [Fs.Fs] IS A MAP FROM PATH TO CONTENTS and holds no metadata, so
      [d_ino] and [d_type] are not derivable from it, and neither is the
      [d_off] cookie, which is the filesystem's own opaque position.
      That is the same wall [Stat.newfstatat_spec] hits: "A spec that
      answered the call would be inventing the rest".
    - THE KEY SET IS NOT THE DIRECTORY.  Even granting the two above,
      the map's keys do not enumerate the working directory: a real
      EMPTY subdirectory leaves no key at all, "." and ".." are entries
      of every real directory and keys of none, and a key "a/b" implies
      a directory "a" the map cannot hold.  [Namei.unlinkat_spec]'s
      WORLD paragraph states that correspondence and its hole, a
      divergence kept rather than fixed.  A listing read off the
      keys would report a directory Linux would not.

    So the enumerate-the-image shape is declined, and the FAILING side —
    the part of the call that writes nothing — is what is modeled,
    exactly as [Stat.newfstatat_spec] models its own.

    [dirent] is used by the "/proc/self/fd" arm alone.  On the [FdDir]
    arm no modeled answer can deliver a byte, and hence none can fault on
    the destination either.  [filldir64] reaches
    [user_write_access_begin] only AFTER the [reclen > ctx->count] test,
    so on the one directory arm below the kernel has not touched the
    buffer: [getdents64(dirfd, NULL, 0)] is -EINVAL, not -EFAULT.

    ORDER, following the kernel's exactly (Linux fs/readdir.c,
    v6.18.46, [SYSCALL_DEFINE3(getdents64)] and [iterate_dir]):

    - the fd first.  [CLASS(fd_pos, f)(fd)] is [fdget_pos], and
      [fd_empty(f)] returns -EBADF before [iterate_dir] is entered, so a
      closed fd is -EBADF whatever kind of object the number would have
      named.  [fd] arrives already truncated to 32 bits (see
      [Syscall.fd32]), so [getdents64(2^32, ...)] names fd 0.
    - then the fd's KIND.  [iterate_dir] opens with

        int res = -ENOTDIR;
        if (!file->f_op->iterate_shared)
                goto out;

      so -ENOTDIR precedes [security_file_permission],
      [fsnotify_file_perm], the inode lock and the [IS_DEADDIR] test
      alike.  It is the FIRST thing that function does.
    - then, on a directory, the buffer size, in [filldir64].

    -ENOTDIR ON EVERY NON-DIRECTORY, and here the model spends nothing.
    [.iterate_shared] is the directory iterator: no file_operations
    table for a non-directory object defines one, so the answer does not
    turn on WHICH object a channel or a file fd is attached to.  That is
    strictly weaker than what [Sync.fsync_spec] needs — its -EINVAL for
    a channel rests on the channel being a pipe, and plain shell
    redirection falsifies it — so the same
    redirection leaves this arm untouched: a regular file on fd 1 is
    -ENOTDIR just as a pipe is.  Checked at v6.18.46: [pipefifo_fops]
    and [pipeanon_fops] (fs/pipe.c), [socket_file_ops] (net/socket.c),
    [ext4_file_operations] (fs/ext4/file.c), [shmem_file_operations]
    (mm/shmem.c), [null_fops] (drivers/char/mem.c) and [tty_fops]
    (drivers/tty/tty_io.c) — not one of those six files contains the
    token [iterate_shared] at all.

    -EINVAL FOR A BUFFER TOO SMALL FOR THE FIRST ENTRY.  [filldir64]
    sets [buf->error = -EINVAL] and returns false on
    [reclen > ctx->count], which [dir_emit_dots] (Linux
    include/linux/fs.h, v6.18.46) turns into a zero-length iteration and
    [SYSCALL_DEFINE3(getdents64)] then reports, since [buf.prev_reclen]
    is still 0 and the [error = count - buf.ctx.count] rewrite is
    skipped.  [dirent64_min_reclen] bounds [reclen] from below over
    every possible entry, so a [ctx->count] under 24 cannot fit ANY
    entry and the answer does not depend on the directory's contents.

    THAT ARM RESTS ON ONE PREMISE, stated here because it is what a
    later change has to re-check: THE ITERATION EMITS AT LEAST ONE
    ENTRY.  A directory with nothing left to emit returns 0, not
    -EINVAL.  Two facts make it hold:

    - The iteration at position 0 emits "." first.  [dir_emit_dots]
      (Linux include/linux/fs.h, v6.18.46) is the generic opener, and it
      is the FIRST STATEMENT of the readdir every filesystem a modeled
      run can sit on installs: tmpfs's [offset_readdir], reached through
      [simple_offset_dir_operations] (Linux fs/libfs.c, v6.18.46), and
      sysfs's [kernfs_fop_readdir] (Linux fs/kernfs/dir.c, v6.18.46) and
      procfs's [proc_readdir_de] (Linux fs/proc/generic.c, v6.18.46).
      THIS IS THE BOUND WORTH NAMING, in the shape [Sync.fsync_spec]'s
      directory arm names its own: it holds of THOSE filesystems, not of
      every filesystem, and one whose directory yielded nothing at
      position 0 would answer 0 where this arm says -EINVAL.
    - Every [FdDir] a modeled run can hold IS at position 0.
      [State.FdDir] carries no position field, and nothing modeled gives
      it one: [Open.openat_spec] mints it from a fresh open,
      [ReadWrite.lseek_spec] DECLINES a directory fd,
      [ReadWrite.read_spec] answers -EISDIR without moving anything,
      [Fork.clone_spec] shares a [struct file] neither branch can
      advance, and this spec's own only non-declining directory arm does
      not advance it either — [filldir64] refuses on the size and writes
      nothing at all, [dir_emit_dots] leaves [ctx->pos] at 0 when
      [dir_emit_dot] returns false, and [iterate_dir]'s
      [file->f_pos = ctx->pos] then writes back the 0 it read.

      GIVE [FdDir] A POSITION, or give this spec a success arm that
      advances one, and the premise stops being free: the -EINVAL would
      then have to be conditioned on the position, because a directory
      read to its end answers 0 to the very same call.

    APPROXIMATION, and it is a NARROWING rather than a wrong answer.
    Two untracked conditions sit between the -ENOTDIR and the -EINVAL —
    [security_file_permission]'s LSM verdict and [fsnotify_file_perm]'s
    fanotify permission response — and neither errno is documented for
    getdents(2), so neither is offered here.  Under an LSM that denies
    the read, or a fanotify listener that answers FAN_DENY, this spec
    REJECTS a conforming trace on the directory arm.  ([down_read_killable]'s
    -EINTR is a third, and is unreachable rather than approximated: it
    fires only on a fatal signal, which kills the task before any return
    value reaches userspace.)  The -EBADF and -ENOTDIR arms are behind
    none of the three and are unconditional.

    Nothing is written on the non-directory and [FdDir] arms, so each of
    their effects is a bare return with five empty ledgers, and none of
    them reads user memory either — hence no copy-in ledger.  The
    "/proc/self/fd" arm writes its records ([procfd_getdents_spec]). *)
Definition getdents64_spec (fd dirent count : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | None => err_ret EBADF                  (* fd not open: [fd_empty], before [iterate_dir] *)
  | Some (FdChannel _) => err_ret ENOTDIR  (* no [.iterate_shared] on any non-directory *)
  | Some (FdFile _ _)  => err_ret ENOTDIR
  | Some (FdFileW _ _) => err_ret ENOTDIR
  | Some (FdFileA _ _) => err_ret ENOTDIR  (* append mode changes where a write
                                              lands, not whether the inode has an
                                              [.iterate_shared] *)
  | Some (FdFileRW _ _) => err_ret ENOTDIR (* and neither does the access mode: the
                                              same regular file, opened O_RDWR *)
  | Some (FdPipe _ _)  => err_ret ENOTDIR
  | Some (FdSocket _)  => err_ret ENOTDIR
  | Some (FdDevNull _ _) => err_ret ENOTDIR (* [null_fops] (drivers/char/mem.c, v6.18.46)
                                              has no [.iterate_shared], so [iterate_dir]
                                              (fs/readdir.c) answers its opening -ENOTDIR *)
  | Some FdUrandom => err_ret ENOTDIR       (* and [urandom_fops] (drivers/char/random.c) has
                                              none either: the same -ENOTDIR *)
  | Some (FdOpaque o) => getdents64_opaque_spec fd o dirent count
                                           (* the /proc/self/fd listing; every
                                              other opaque kind declines *)
  | Some FdDir =>
      if getdents64_no_room count
      then alt (e <- errno_from getdents64_errnos ;; err_ret e)  (* the removed directory *)
               (err_ret EINVAL)                                  (* [filldir64]'s own answer *)
      else unmodeled  (* the listing itself: see the header's three reasons *)
  end.
