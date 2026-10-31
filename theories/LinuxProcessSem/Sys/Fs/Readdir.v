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

(** [getdents64 fd dirent count]: read directory entries into [dirent].

    THE SUCCESS ARM IS NOT MODELED, AND CANNOT BE FROM WHAT THIS MODEL
    CARRIES.  A successful call fills the buffer with [struct
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

    [dirent] IS NOT AN ARGUMENT OF THIS SPEC, and its arity is the
    statement that no modeled arm can deliver a byte, and hence that
    none can fault on the destination either.  [filldir64] reaches
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

    Nothing is written on any admitted arm, so every effect is a bare
    return with five empty ledgers, and no arm reads user memory either
    — hence no copy-in ledger. *)
Definition getdents64_spec (fd count : word) : Sys SyscallEffect :=
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
  | Some (FdStream _ _ _) => err_ret ENOTDIR (* [socket_file_ops] has no [.iterate_shared] *)
  | Some (FdDgram _)   => err_ret ENOTDIR    (* nor for a datagram socket's file *)
  | Some (FdEventfd _) => err_ret ENOTDIR    (* [eventfd_fops] (fs/eventfd.c, v6.18.46) has no
                                                [.iterate_shared] either *)
  | Some (FdDevNull _ _) => err_ret ENOTDIR (* [null_fops] (drivers/char/mem.c, v6.18.46)
                                              has no [.iterate_shared], so [iterate_dir]
                                              (fs/readdir.c) answers its opening -ENOTDIR *)
  | Some FdUrandom => err_ret ENOTDIR       (* and [urandom_fops] (drivers/char/random.c) has
                                              none either: the same -ENOTDIR *)
  | Some FdDir =>
      if getdents64_no_room count
      then alt (e <- errno_from getdents64_errnos ;; err_ret e)  (* the removed directory *)
               (err_ret EINVAL)                                  (* [filldir64]'s own answer *)
      else unmodeled  (* the listing itself: see the header's three reasons *)
  end.
