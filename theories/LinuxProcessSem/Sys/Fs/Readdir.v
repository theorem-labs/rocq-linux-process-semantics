(** * LinuxProcessSem.Sys.Fs.Readdir — getdents64 (61)

    This file answers to Linux [fs/readdir.c]: it holds what the kernel
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
    the name — and returns the byte count.  The names are not what is
    missing: [State.FdDir] carries the folder's canonical key, and
    [Fs.fs_tree] holds every entry of every folder, an empty folder
    included, so the names under the key, "." and "..", and each
    entry's [d_type] (from its [Fs.Entry] kind) are all derivable.
    Three INDEPENDENT things stand in the way, and closing any one of
    them leaves the other two:

    - THE ORDER AND THE [d_off] COOKIES ARE THE FILE SYSTEM'S OWN.  On
      tmpfs [offset_readdir] lists the entries in the order of the
      folder's dentry list: [offset_iterate_dir] moves from one entry to
      the next with [find_positive_dentry], that is [d_next_sibling]
      (fs/libfs.c:450-472, :503-523), and [d_alloc] puts each new dentry
      at the head of the list (fs/dcache.c:1778), so the newest dentry
      comes first.  A record's [d_off] is the continuation cookie, the
      position a later call resumes from, and not the offset
      [simple_offset_add] gave the record's own name:
      [offset_iterate_dir] hands each entry's offset to the actor
      (fs/libfs.c:514-515, Linux v6.18.46), [filldir64] writes it into the PREVIOUS
      record's [d_off] (fs/readdir.c:373-378), and [getdents64] writes
      the position it stopped at into the last record (:415-420), which
      after the folder's last entry is [DIR_OFFSET_EOD] (fs/libfs.c:529);
      [offset_dir_lookup] reads a cookie only to find where to resume
      (fs/libfs.c:476-493).  On ramfs [dcache_readdir] walks the same
      dentry list and counts positions (Linux fs/libfs.c, v6.18.46).
      [Fs.fs_tree] is sorted by key and
      records neither the dentry order nor any offset, so a listing
      would have to choose an order and cookies, and keep the choice for
      every later call on the folder.
    - [d_ino] IS THE [st_ino] A STAT REPORTS, and the model holds none.
      [Fs.Fs] gives a regular file an inode number of the model's own,
      not Linux's, and a folder, a device node and a link none at all;
      [Stat.stat_entry_spec] chooses [st_ino] at the first stat of an
      identity and pins it ([State.StatId], [State.procst_statpins]).  A
      listing would have to choose a number for every entry and for "."
      and "..", consistent with every pin and with every later stat.
    - [State.FdDir] HOLDS NO POSITION.  A listing moves [ctx->pos], and
      the next call starts where it stopped, so a second call on the
      same descriptor answers from a position the entry does not have.

    So the listing is declined, and the FAILING side — the part of the
    call that writes nothing — is what is modeled.

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
      [simple_offset_dir_operations], and ramfs's [dcache_readdir],
      reached through [simple_dir_operations] (Linux fs/libfs.c,
      v6.18.46), and
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

    NO DENIAL SITS BETWEEN THE TWO.  [security_file_permission] and
    [fsnotify_file_perm] run between the -ENOTDIR and the -EINVAL, and
    the configuration of record builds neither an LSM nor fanotify
    (SCOPE.md), so both are stubs that answer 0 and no supported kernel
    answers this arm -EACCES or -EPERM; refusing both is exact.
    ([down_read_killable]'s -EINTR is a third condition, and is
    unreachable rather than approximated: it fires only on a fatal
    signal, which kills the task before any return value reaches
    userspace.)  The -EBADF and -ENOTDIR arms are behind none of the
    three and are unconditional.

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
  | Some (FdUrandom _ _) => err_ret ENOTDIR (* and [urandom_fops] (drivers/char/random.c) has
                                              none either: the same -ENOTDIR *)
  | Some (FdDir _) =>
      if getdents64_no_room count
      then alt (e <- errno_from getdents64_errnos ;; err_ret e)  (* the removed directory *)
               (err_ret EINVAL)                                  (* [filldir64]'s own answer *)
      else unmodeled  (* the listing itself: see the header's three reasons *)
  end.
