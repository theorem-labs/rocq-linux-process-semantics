import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! # Checks.Cases.Sys.Uapi.Fs — the `Sys.Uapi.Fs` constants, read off
against Linux

Pins over `Sys/Uapi/Fs.lean`, what a file descriptor or a pathname
reaches. Not part of the trusted specification: this file is QA on the
definitions, written to be READ, and every claim in it is a claim about a
header or a function of Linux v6.18.46, commit
1f99e9ab748fc5c32120de9c4eca31abfe54a4d5, with the citation beside it.

Each pin states a value the kernel really has and, beside it, refutes the
concrete mistake the constant exists to prevent — a value from another
architecture's header, an off-by-one at a bound, a decimal read of an
octal, a mask taken for its neighbour.  They are stated about the cited
headers and sources, never about the Rocq definitions of the same names.
No Rocq file sits at this file's mirror path: the Rocq tree keeps its
Uapi constants unpinned (this stops being true the day a Rocq case
file pins them), so this file is the Lean port's own evidence rather
than a twin. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Sys.Uapi.Fs

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-- The thirteen open and status flags are the asm-generic OCTALS
(include/uapi/asm-generic/fcntl.h:20-62, Linux v6.18.46, commit
1f99e9ab748f). -/
theorem open_flags_are_the_asm_generic_octals :
    O_WRONLY = 0o1 ∧ O_RDWR = 0o2 ∧ O_CREAT = 0o100 ∧ O_EXCL = 0o200 ∧ O_TRUNC = 0o1000
    ∧ O_APPEND = 0o2000 ∧ O_NONBLOCK = 0o4000 ∧ FASYNC = 0o20000 ∧ O_DIRECT = 0o40000
    ∧ O_LARGEFILE = 0o100000 ∧ O_DIRECTORY = 0o200000 ∧ O_NOATIME = 0o1000000
    ∧ O_CLOEXEC = 0o2000000 := by decide

/-- The header writes `00004000`, `00200000` and `02000000`, and they are
octal: read as decimal, the three most-read flags would be wrong, and
`open(".", O_DIRECTORY)` would carry a bit `build_open_flags` (fs/open.c,
Linux v6.18.46) does not turn into LOOKUP_DIRECTORY. -/
theorem open_flags_are_not_decimal :
    O_NONBLOCK ≠ 4000 ∧ O_DIRECTORY ≠ 200000 ∧ O_CLOEXEC ≠ 2000000 := by decide

/-- The eleven single-bit flags sit on eleven DISTINCT bits — their OR is
their sum — so `f_flags` can carry any subset and `setfl` (fs/fcntl.c,
Linux v6.18.46) can mask each one out alone.  A value taken from another
architecture's fcntl.h lands on the wrong bit, and two of them on the same
bit would fail this. -/
theorem open_flags_are_disjoint_bits :
    (O_CREAT.toNat ||| O_EXCL.toNat ||| O_TRUNC.toNat ||| O_APPEND.toNat ||| O_NONBLOCK.toNat
      ||| FASYNC.toNat ||| O_DIRECT.toNat ||| O_LARGEFILE.toNat ||| O_DIRECTORY.toNat
      ||| O_NOATIME.toNat ||| O_CLOEXEC.toNat : Nat)
    = O_CREAT.toNat + O_EXCL.toNat + O_TRUNC.toNat + O_APPEND.toNat + O_NONBLOCK.toNat
      + FASYNC.toNat + O_DIRECT.toNat + O_LARGEFILE.toNat + O_DIRECTORY.toNat
      + O_NOATIME.toNat + O_CLOEXEC.toNat := by decide

/-- `#define AT_FDCWD -100` (include/uapi/linux/fcntl.h:94, Linux v6.18.46)
arrives
sign-extended in a 64-bit register, and `int dfd` keeps its low half. -/
theorem AT_FDCWD_is_minus_100 :
    bv_unsigned AT_FDCWD = 2 ^ 64 - 100 ∧ bv_unsigned AT_FDCWD32 = 2 ^ 32 - 100 := by decide

/-- The mistakes: comparing the untruncated register — `openat(2^32 - 100,
...)` names the working directory in Linux and would not — and reading the
header's `-100` as 100. -/
theorem AT_FDCWD_is_neither_the_register_nor_positive :
    AT_FDCWD32 ≠ AT_FDCWD ∧ bv_unsigned AT_FDCWD ≠ 100 := by decide

/-- The `AT_` words (include/uapi/linux/fcntl.h:120, :126, :165, :168, Linux
v6.18.46).
`AT_EACCESS` and `AT_REMOVEDIR` are ONE number, 0x200, read by two
syscalls; neither is an open flag — `unlinkat(fd, p, O_DIRECTORY)` is an
-EINVAL in Linux and a model that let `AT_REMOVEDIR` alias `O_DIRECTORY`
would remove the directory. -/
theorem at_words :
    AT_SYMLINK_NOFOLLOW = 0x100 ∧ AT_EACCESS = 0x200 ∧ AT_EMPTY_PATH = 0x1000
    ∧ AT_REMOVEDIR = AT_EACCESS ∧ AT_REMOVEDIR ≠ O_DIRECTORY := by decide

/-- `S_IRWXO` is `MAY_READ | MAY_WRITE | MAY_EXEC` (4 | 2 | 1,
include/linux/fs.h:100-102, Linux v6.18.46), which is what lets
`do_faccessat` (fs/open.c) pass `mode` straight through; it is the
OTHERS' triple, not the owner's `S_IRWXU` (00700, include/uapi/linux/stat.h:29). -/
theorem S_IRWXO_is_the_may_mask : S_IRWXO = (4 ||| 2 ||| 1 : Nat) ∧ S_IRWXO ≠ 0o700 := by decide

/-- The two paths spell "." and "/dev/null" in ASCII, and "." is not
"..", which is `Fs.Namei.dotdot_path` and resolves through the parent. -/
theorem the_two_paths_spell_themselves :
    dot_path.map (fun b => Char.ofNat b.toNat) = ['.']
    ∧ devnull_path.map (fun b => Char.ofNat b.toNat) = ['/', 'd', 'e', 'v', '/', 'n', 'u', 'l', 'l']
    ∧ dot_path ≠ [Z_to_bv 8 46, Z_to_bv 8 46] := by decide

/-- The third path spells "/dev/urandom" in ASCII; it is not "/dev/null", and
it is not "/dev/random", the blocking device beside it in the `devlist`
table `memory_open` indexes (drivers/char/mem.c:700-701, Linux v6.18.46),
which stays the ordinary decline; `chr_dev_init` (drivers/char/mem.c:768-769)
makes the nodes under MEM_MAJOR from that same table.
kernel: drivers/char/mem.c:chr_dev_init,memory_open@v6.18.46 -/
theorem urandom_path_spells_itself :
    urandom_path.map (fun b => Char.ofNat b.toNat)
        = ['/', 'd', 'e', 'v', '/', 'u', 'r', 'a', 'n', 'd', 'o', 'm']
    ∧ urandom_path ≠ devnull_path
    ∧ urandom_path.map (fun b => Char.ofNat b.toNat)
        ≠ ['/', 'd', 'e', 'v', '/', 'r', 'a', 'n', 'd', 'o', 'm'] := by
  decide

/-- `SEEK_MAX` is `SEEK_HOLE`, 4, not `SEEK_END`: `ksys_lseek`
(fs/read_write.c:401, Linux v6.18.46) lets whence 3 and 4 through to
`vfs_llseek`, so a model that stopped at `SEEK_END` would answer -EINVAL
where Linux consults the file. -/
theorem seek_words :
    SEEK_SET = 0 ∧ SEEK_CUR = 1 ∧ SEEK_END = 2 ∧ SEEK_MAX = 4 ∧ SEEK_MAX ≠ SEEK_END := by decide

/-- `GRND_NONBLOCK` and `GRND_RANDOM` are bits 0 and 1
(include/uapi/linux/random.h:54-55, Linux v6.18.46); `GRND_INSECURE`
(0x0004, line 56) is
neither and is not named here because no arm reads it. -/
theorem grnd_words :
    GRND_NONBLOCK = 1 ∧ GRND_RANDOM = 2
    ∧ ((GRND_NONBLOCK.toNat ||| GRND_RANDOM.toNat) &&& 4 : Nat) = 0 := by decide

/-- The eight terminal requests, decoded by include/uapi/asm-generic/ioctl.h's
layout (Linux v6.18.46): the six `_IO('T', n)` requests are `0x54 << 8 | n`,
and the two pty requests carry direction 2 (`_IOR`) and 1 (`_IOW`) in bits
30-31 and a 4-byte argument size in bits 16-29. -/
theorem tty_ioctls_decode :
    (bv_unsigned TCGETS).toNat = (0x54 <<< 8) ||| 0x01
    ∧ (bv_unsigned TCSETS).toNat = (0x54 <<< 8) ||| 0x02
    ∧ (bv_unsigned TIOCSCTTY).toNat = (0x54 <<< 8) ||| 0x0E
    ∧ (bv_unsigned TIOCGWINSZ).toNat = (0x54 <<< 8) ||| 0x13
    ∧ (bv_unsigned TIOCSWINSZ).toNat = (0x54 <<< 8) ||| 0x14
    ∧ (bv_unsigned TIOCNOTTY).toNat = (0x54 <<< 8) ||| 0x22
    ∧ (bv_unsigned TIOCGPTN).toNat = (2 <<< 30) ||| (4 <<< 16) ||| (0x54 <<< 8) ||| 0x30
    ∧ (bv_unsigned TIOCSPTLCK).toNat = (1 <<< 30) ||| (4 <<< 16) ||| (0x54 <<< 8) ||| 0x31 := by
  decide

/-- The mistake for the pty pair is the direction: `TIOCGPTN` is `_IOR`,
not `_IOW`, and it is not the bare `_IO('T', 0x30)` either — a request
word with the wrong direction is a different ioctl number and
`tty_ioctl`'s switch (drivers/tty/tty_io.c) never sees it. -/
theorem TIOCGPTN_is_a_read :
    (bv_unsigned TIOCGPTN).toNat ≠ (1 <<< 30) ||| (4 <<< 16) ||| (0x54 <<< 8) ||| 0x30
    ∧ (bv_unsigned TIOCGPTN).toNat ≠ (0x54 <<< 8) ||| 0x30 := by decide

/-- The four fcntl commands (include/uapi/asm-generic/fcntl.h:99-102, Linux
v6.18.46), and that command 0 is `F_DUPFD` (line 98), not `F_GETFD`: an off-by-one here
would answer a `dup` request with the close-on-exec flag. -/
theorem fcntl_commands :
    bv_unsigned F_GETFD = 1 ∧ bv_unsigned F_SETFD = 2 ∧ bv_unsigned F_GETFL = 3
    ∧ bv_unsigned F_SETFL = 4 ∧ F_GETFD ≠ Z_to_bv 64 0 := by decide

/-- The flock words (include/uapi/asm-generic/fcntl.h:176-186), and that
`LOCK_MAND` is a bit OUTSIDE the four operations: `SYSCALL_DEFINE2(flock)`
(fs/locks.c:2148, Linux v6.18.46) tests `cmd & LOCK_MAND` first and returns
0, so had the bit overlapped an operation, that operation would have been
the silent no-op. -/
theorem flock_words :
    LOCK_SH = 1 ∧ LOCK_EX = 2 ∧ LOCK_NB = 4 ∧ LOCK_UN = 8 ∧ LOCK_MAND = 32
    ∧ (LOCK_MAND.toNat &&& (LOCK_SH.toNat ||| LOCK_EX.toNat ||| LOCK_NB.toNat ||| LOCK_UN.toNat)
        : Nat) = 0 := by decide

/-- The two create masks differ by exactly bit 0 (include/linux/timerfd.h:16
and include/linux/eventfd.h:27, Linux v6.18.46): `eventfd2(0, 1)` succeeds
and `timerfd_create(CLOCK_MONOTONIC, 1)` is -EINVAL, so spelling one gate
with the other's mask is wrong on exactly one input each way. -/
theorem create_masks_differ_by_the_semaphore_bit :
    TFD_CREATE_FLAGS = 0o2004000 ∧ EFD_FLAGS_SET = 0o2004001
    ∧ TFD_CREATE_FLAGS ≠ EFD_FLAGS_SET
    ∧ (TFD_CREATE_FLAGS.toNat &&& EFD_SEMAPHORE.toNat : Nat) = 0 := by decide

/-- `NAME_MAX` is 255 (include/uapi/linux/limits.h:12, Linux v6.18.46), not
`PATH_MAX`'s 4096 (line 13): a component bound of 4096 would accept names `ext4_lookup`
and `simple_lookup` refuse with -ENAMETOOLONG. -/
theorem NAME_MAX_is_a_component_bound : NAME_MAX = 255 ∧ NAME_MAX ≠ 4096 := by decide

/-- `NR_OPEN_DEFAULT` is `BITS_PER_LONG` (include/linux/fdtable.h:24, Linux
v6.18.46): 64 on riscv64, not the 32 of a 32-bit kernel, under which
`expand_files` (fs/file.c:299, Linux v6.18.46) would allocate for
`dup3(0, 40, 0)`. -/
theorem NR_OPEN_DEFAULT_is_lp64 : NR_OPEN_DEFAULT = 64 ∧ NR_OPEN_DEFAULT ≠ 32 := by decide

/-- The generic 64-bit `struct stat` (include/uapi/asm-generic/stat.h:24-45,
Linux v6.18.46): 128 bytes, `st_mode` at 16.  x86-64's struct (arch/x86/include/uapi/asm/stat.h,
`#else /* __i386__ */` block) puts an 8-byte `st_nlink` at 16 and `st_mode`
at 24, so a model reading that layout would find the type bits inside the
link count. -/
theorem stat_layout :
    STAT_SIZE = 128 ∧ ST_MODE_OFF = 16 ∧ ST_RDEV_OFF = 32 ∧ ST_PAD1_OFF = 40
    ∧ ST_SIZE_OFF = 48 ∧ ST_BLKSIZE_OFF = 56 ∧ ST_PAD2_OFF = 60 ∧ ST_BLOCKS_OFF = 64
    ∧ ST_UNUSED45_OFF = 120 ∧ ST_MODE_OFF ≠ 24 := by decide

/-- `S_IFMT` is 0170000 and the seven types are seven distinct values
inside it, disjoint from the permission bits (include/uapi/linux/stat.h:9-16
and :39, Linux v6.18.46). -/
theorem file_types_are_distinct_and_inside_S_IFMT :
    S_IFMT = 0o170000
    ∧ [S_IFSOCK, S_IFLNK, S_IFREG, S_IFBLK, S_IFDIR, S_IFCHR, S_IFIFO].Nodup
    ∧ [S_IFSOCK, S_IFLNK, S_IFREG, S_IFBLK, S_IFDIR, S_IFCHR, S_IFIFO].all
        (fun t => (t.toNat &&& S_IFMT.toNat : Nat) == t.toNat && t != 0)
    ∧ (S_IFMT.toNat &&& S_IRWXO.toNat : Nat) = 0 := by decide

/-- `DEVNULL_RDEV` is `new_encode_dev(MKDEV(1, 3))` (include/linux/kdev_t.h:12
and :39-44, Linux v6.18.46): minor in the low byte, major in the next.  It
is neither the pair swapped nor the kernel-internal `dev_t` itself, whose
major sits at `MINORBITS` = 20. -/
theorem DEVNULL_RDEV_is_the_encoded_dev :
    DEVNULL_RDEV = ((3 &&& 0xff) ||| (1 <<< 8) : Nat)
    ∧ DEVNULL_RDEV ≠ ((1 &&& 0xff) ||| (3 <<< 8) : Nat)
    ∧ DEVNULL_RDEV ≠ ((1 <<< 20) ||| 3 : Nat) := by decide

/-- `URANDOM_RDEV` is `new_encode_dev(MKDEV(1, 9))` (include/linux/kdev_t.h:12
and :39-44, Linux v6.18.46): minor 9 in the low byte, major 1 in the next —
devlist[9] of drivers/char/mem.c:701 under MEM_MAJOR 1
(include/uapi/linux/major.h:11).  It is not /dev/null's 259, not the pair
swapped, and not the kernel-internal `dev_t` with its major at `MINORBITS` = 20.
kernel: include/linux/kdev_t.h:new_encode_dev@v6.18.46 -/
theorem URANDOM_RDEV_is_the_encoded_dev :
    URANDOM_RDEV = ((9 &&& 0xff) ||| (1 <<< 8) : Nat)
    ∧ URANDOM_RDEV ≠ DEVNULL_RDEV
    ∧ URANDOM_RDEV ≠ ((1 &&& 0xff) ||| (9 <<< 8) : Nat)
    ∧ URANDOM_RDEV ≠ ((1 <<< 20) ||| 9 : Nat) := by decide

/-- A `struct stat` in the asm-generic layout, written member by member at
the offsets above — the shape testing/syscall-check's `fstat` probes and
Rocq's `Checks/Cases/Fs/Stat.v` build.  The six arguments are what the
pins vary; every other member is a plausible constant and none of it is
claimed to be what a kernel would report.  A fixture for the pins, not a
definition of the model. -/
private def stat_fixture (ino mode rdev size blocks tim : Int) : List byte :=
  Z_to_le_bytes 8 2049 ++ Z_to_le_bytes 8 ino ++ Z_to_le_bytes 4 mode ++ Z_to_le_bytes 4 1
  ++ Z_to_le_bytes 4 1000 ++ Z_to_le_bytes 4 1000 ++ Z_to_le_bytes 8 rdev ++ Z_to_le_bytes 8 0
  ++ Z_to_le_bytes 8 size ++ Z_to_le_bytes 4 4096 ++ Z_to_le_bytes 4 0 ++ Z_to_le_bytes 8 blocks
  ++ Z_to_le_bytes 8 tim ++ Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 tim ++ Z_to_le_bytes 8 0
  ++ Z_to_le_bytes 8 tim ++ Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 0

set_option maxRecDepth 4096 in
/-- The truthful answer for a nine-byte regular file is inside the
envelope, and its length obligation holds at 9 and fails at 10: a stale
`st_size` after a write is what `stat_size_ok` exists to reject. -/
theorem stat_regular_file_answer :
    stat_buf_wf (stat_fixture 4711 S_IFREG 0 9 8 1700000000) = true
    ∧ stat_is_reg (stat_fixture 4711 S_IFREG 0 9 8 1700000000) = true
    ∧ stat_size_ok 9 (stat_fixture 4711 S_IFREG 0 9 8 1700000000) = true
    ∧ stat_size_ok 10 (stat_fixture 4711 S_IFREG 0 9 8 1700000000) = false := by decide

set_option maxRecDepth 4096 in
/-- Three buffers `cp_new_stat` (fs/stat.c:470, Linux v6.18.46) cannot have
produced FOR A DESCRIPTOR `Fs.Stat.fstat_spec` ANSWERS — a regular file or
one of the two character devices: all zeros (no type bits — a kernel that
wrote nothing), 127 bytes (the single `copy_to_user` is 128), and a
type-less mode.  The last is NOT impossible in Linux at large: an
anonymous inode has no type at all — `alloc_anon_inode` sets `i_mode =
S_IRUSR | S_IWUSR` (fs/libfs.c:1678, "Historically anonymous inodes don't
have a type at all and userspace has come to rely on this") — so `fstat`
of an eventfd, timerfd or epoll descriptor really reports 0600.  Refusing
it is sound only because `fstat_spec` (`Sys/Fs/Stat.lean`) declines every
descriptor kind but files and the two devices; the day an arm answers
`fstat` on an anon-inode descriptor through `stat_buf_wf` unchanged, this
pin and `stat_ifmt_valid` are the priority-1 bug.
kernel: fs/stat.c:cp_new_stat; fs/libfs.c:alloc_anon_inode; include/uapi/linux/stat.h:S_IFREG@v6.18.46 -/
theorem stat_impossible_answers_rejected :
    stat_buf_wf (List.replicate 128 (Z_to_bv 8 0)) = false
    ∧ stat_buf_wf ((stat_fixture 4711 S_IFREG 0 9 8 1700000000).take 127) = false
    ∧ stat_buf_wf (stat_fixture 4711 0 0 9 8 1700000000) = false := by decide

set_option maxRecDepth 4096 in
/-- `st_mode` carries the PERMISSION bits beside the type — `cp_new_stat`
writes `tmp.st_mode = stat->mode` whole (fs/stat.c:488, Linux v6.18.46,
commit 1f99e9ab748f) — and `stat_ifmt` masks them off with `S_IFMT`
(`#define S_IFMT 00170000`, include/uapi/linux/stat.h:9).  The other
fixtures here pass a bare type or 0, so a `stat_ifmt` that forgot the mask
closed every pin.  Four modes a kernel really reports, with different low
bits each: a `0644` regular file (0100644 = 33188) is `S_IFREG`, inside the
envelope, and the unmasked mode is NOT what `stat_ifmt` returns; `/tmp`
(0041777 = 17407, `S_ISVTX` beside `rwx`) is `S_IFDIR`; a setuid, setgid,
sticky file with every permission bit set (0107777 = 36863) is `S_IFREG`;
`/dev/null` (0020666 = 8630) is `S_IFCHR` and passes `stat_devnull_ok`.
The third sets all twelve bits below `S_IFMT`, the set-id and sticky bits
included (`S_ISUID`, `S_ISGID`, `S_ISVTX`, include/uapi/linux/stat.h:17-19),
so a mask one digit off — 0177000, which keeps those three — fails on it
where 0644 alone, whose set bits are 2, 5, 7 and 8, could not tell.
`openat_rdwr.c` (testing/syscall-check) asserts `(st_mode & S_IFMT) ==
S_IFREG` on a 0644 file the pinned kernel stat'ed, and `fstat_spec.c` hands
the checker the same 0100644 mode.
kernel: fs/stat.c:cp_new_stat; include/uapi/linux/stat.h:S_IFMT,S_IFREG,S_IFDIR,S_IFCHR@v6.18.46 -/
theorem stat_ifmt_masks_permission_bits :
    stat_ifmt (stat_fixture 4711 33188 0 9 8 1700000000) = S_IFREG
    ∧ stat_is_reg (stat_fixture 4711 33188 0 9 8 1700000000) = true
    ∧ stat_buf_wf (stat_fixture 4711 33188 0 9 8 1700000000) = true
    ∧ stat_ifmt (stat_fixture 4711 33188 0 9 8 1700000000) ≠ 33188
    ∧ stat_ifmt (stat_fixture 2 0o41777 0 4096 8 1700000000) = S_IFDIR
    ∧ stat_buf_wf (stat_fixture 2 0o41777 0 4096 8 1700000000) = true
    ∧ stat_ifmt (stat_fixture 4711 0o107777 0 9 8 1700000000) = S_IFREG
    ∧ stat_is_reg (stat_fixture 4711 0o107777 0 9 8 1700000000) = true
    ∧ stat_ifmt (stat_fixture 5 0o20666 259 0 0 1700000000) = S_IFCHR
    ∧ stat_devnull_ok (stat_fixture 5 0o20666 259 0 0 1700000000) = true := by decide

set_option maxRecDepth 4096 in
/-- The padding is load-bearing to its LAST byte: `INIT_STRUCT_STAT_PADDING`
(fs/stat.c:467, Linux v6.18.46) clears the whole `struct stat` before
`cp_new_stat` fills it, and no member assignment covers `__pad1` (bytes
40..47), `__pad2` (60..63) or `__unused4`/`__unused5` (120..127), so a
nonzero byte anywhere in them is an answer no kernel wrote.  Poisoned at
the HIGH byte of each pad, where `Checks/Cases/Fs/Stat.lean` poisons the
low one: a `stat_buf_wf` that read a pad narrower than the member closed
every low-byte pin, and no fixture in this file poisoned a pad at all, so
dropping any of the three conjuncts closed every pin here.
kernel: fs/stat.c:INIT_STRUCT_STAT_PADDING,cp_new_stat@v6.18.46 -/
theorem stat_padding_is_load_bearing_to_the_last_byte :
    stat_buf_wf ((stat_fixture 4711 S_IFREG 0 9 8 1700000000).set 47 (Z_to_bv 8 1)) = false
    ∧ stat_buf_wf ((stat_fixture 4711 S_IFREG 0 9 8 1700000000).set 63 (Z_to_bv 8 1)) = false
    ∧ stat_buf_wf ((stat_fixture 4711 S_IFREG 0 9 8 1700000000).set 127 (Z_to_bv 8 1)) = false := by
  decide

set_option maxRecDepth 4096 in
/-- The seven file types `S_IFSOCK` to `S_IFIFO` are the header's seven
octals (include/uapi/linux/stat.h:10-16, Linux v6.18.46) — pinned by VALUE
here, because `file_types_are_distinct_and_inside_S_IFMT` fixes only
`S_IFMT` and the shape of the set, and the fixtures below are built from
the very names they are tested against, so a wrong constant passed them —
and all seven pass the model's type test, beside the `S_IFREG` and `S_IFCHR`
the other fixtures use; two non-types do not: `S_IFMT` itself (0170000,
every type bit set) and 0130000 = 45056, a value between `S_IFLNK`
(0120000) and `S_IFSOCK` (0140000) that no `#define` names.  A
`stat_ifmt_valid` missing an alternative would refuse a real `fstat` of a
file of that type; a `S_IFSOCK` read as decimal 140000 lies outside the
mask and would match no real socket.  Only the `S_IFREG` alternative has
a probe (`openat_rdwr.c`, `fstat_spec.c`): `fstat_spec` declines the
directory, socket and pipe descriptors that would carry `S_IFDIR`,
`S_IFSOCK` or `S_IFIFO`, and the model opens no symlink or block device.
kernel: include/uapi/linux/stat.h:S_IFMT,S_IFSOCK,S_IFLNK,S_IFREG,S_IFBLK,S_IFDIR,S_IFCHR,S_IFIFO@v6.18.46 -/
theorem stat_ifmt_valid_names_exactly_the_seven_types :
    S_IFSOCK = 0o140000 ∧ S_IFLNK = 0o120000 ∧ S_IFREG = 0o100000 ∧ S_IFBLK = 0o060000
    ∧ S_IFDIR = 0o040000 ∧ S_IFCHR = 0o020000 ∧ S_IFIFO = 0o010000
    ∧ S_IFSOCK ≠ 140000
    ∧ stat_ifmt_valid (stat_fixture 1 S_IFSOCK 0 0 0 1700000000) = true
    ∧ stat_ifmt_valid (stat_fixture 1 S_IFLNK 0 0 0 1700000000) = true
    ∧ stat_ifmt_valid (stat_fixture 1 S_IFREG 0 0 0 1700000000) = true
    ∧ stat_ifmt_valid (stat_fixture 1 S_IFBLK 0 0 0 1700000000) = true
    ∧ stat_ifmt_valid (stat_fixture 1 S_IFDIR 0 0 0 1700000000) = true
    ∧ stat_ifmt_valid (stat_fixture 1 S_IFCHR 0 0 0 1700000000) = true
    ∧ stat_ifmt_valid (stat_fixture 1 S_IFIFO 0 0 0 1700000000) = true
    ∧ stat_ifmt_valid (stat_fixture 1 S_IFMT 0 0 0 1700000000) = false
    ∧ stat_ifmt_valid (stat_fixture 1 45056 0 0 0 1700000000) = false := by decide

/-- A character device the model holds five bytes for
(bugs/fs-paths-assumed-regular-files.md): Linux answers S_IFCHR with
`st_size` 0, and the implication in `stat_size_ok` admits it rather than
demanding the byte list's length. -/
theorem stat_character_device_answer_admitted :
    stat_is_reg (stat_fixture 1 S_IFCHR 259 0 0 1700000000) = false
    ∧ stat_size_ok 5 (stat_fixture 1 S_IFCHR 259 0 0 1700000000) = true := by decide

/-- /dev/null's answer carries S_IFCHR and `st_rdev` 259; the major/minor
pair swapped (769) or a regular-file type is not /dev/null. -/
theorem stat_devnull_answer :
    stat_devnull_ok (stat_fixture 5 S_IFCHR 259 0 0 1700000000) = true
    ∧ stat_devnull_ok (stat_fixture 5 S_IFCHR 769 0 0 1700000000) = false
    ∧ stat_devnull_ok (stat_fixture 5 S_IFREG 259 0 0 1700000000) = false := by decide

/-- /dev/urandom's `struct stat` carries S_IFCHR — `init_special_inode`
(fs/inode.c:2552-2559, Linux v6.18.46) set the type bits when the node was
made and `cp_new_stat` (fs/stat.c:488) copies them — and `st_rdev` 265,
`new_encode_dev` of `MKDEV(1, 9)` (fs/stat.c:494; include/linux/kdev_t.h:12,
:39-44).  Refused: /dev/null's 259, the pair swapped (2305), a regular-file
type, and, on the null device's instance, the random device's number — the
one member the two instances of `stat_chrdev_ok` differ in.
kernel: include/uapi/linux/stat.h:S_IFCHR,S_IFREG; include/linux/kdev_t.h:MKDEV,new_encode_dev; fs/stat.c:cp_new_stat; fs/inode.c:init_special_inode@v6.18.46 -/
theorem stat_urandom_answer :
    stat_urandom_ok (stat_fixture 9 S_IFCHR 265 0 0 1700000000) = true
    ∧ stat_urandom_ok (stat_fixture 9 S_IFCHR 259 0 0 1700000000) = false
    ∧ stat_urandom_ok (stat_fixture 9 S_IFCHR 2305 0 0 1700000000) = false
    ∧ stat_urandom_ok (stat_fixture 9 S_IFREG 265 0 0 1700000000) = false
    ∧ stat_devnull_ok (stat_fixture 5 S_IFCHR 265 0 0 1700000000) = false := by
  decide

/-- The size and block conjuncts of `stat_chrdev_ok` are load-bearing on both
instances: `generic_fillattr` (fs/stat.c:95, :106, Linux v6.18.46) fills
`st_size` from `i_size_read` and `st_blocks` from `i_blocks`, zero for a
node made by mknod or devtmpfs and never resized
(bugs/openat-urandom-assumed-random-device.md), and a predicate that dropped
either conjunct would accept a resized node.  Rocq's
`urandom_fstat_asserts_the_device` refuses the same nonzero size.
kernel: include/uapi/linux/stat.h:S_IFCHR; fs/stat.c:generic_fillattr,cp_new_stat@v6.18.46 -/
theorem stat_chrdev_size_and_blocks_are_zero :
    stat_urandom_ok (stat_fixture 9 S_IFCHR 265 5 0 1700000000) = false
    ∧ stat_urandom_ok (stat_fixture 9 S_IFCHR 265 0 8 1700000000) = false
    ∧ stat_devnull_ok (stat_fixture 5 S_IFCHR 259 5 0 1700000000) = false
    ∧ stat_devnull_ok (stat_fixture 5 S_IFCHR 259 0 8 1700000000) = false := by
  decide

set_option maxRecDepth 4096 in
/-- Two `fstat`s of one file may differ in length, blocks and timestamps
and still be the same file; two answers that disagree on the inode number
are not, nor two that disagree in `__pad1` — zero in both from
`INIT_STRUCT_STAT_PADDING` (fs/stat.c:467, Linux v6.18.46) — or in
`st_blksize`, which `generic_fillattr` (fs/stat.c:105) takes from the
inode's block size and which `stat_stable_eqb`'s docstring argues no
syscall moves.  Without the last two, dropping either of the predicate's
slice conjuncts closed every pin in this file.
kernel: fs/stat.c:INIT_STRUCT_STAT_PADDING,generic_fillattr,cp_new_stat@v6.18.46 -/
theorem stat_stable_members :
    stat_stable_eqb (stat_fixture 4711 S_IFREG 0 9 8 1700000000)
                    (stat_fixture 4711 S_IFREG 0 12 16 1700000009) = true
    ∧ stat_stable_eqb (stat_fixture 4711 S_IFREG 0 9 8 1700000000)
                      (stat_fixture 4712 S_IFREG 0 9 8 1700000000) = false
    ∧ stat_stable_eqb (stat_fixture 4711 S_IFREG 0 9 8 1700000000)
                      ((stat_fixture 4711 S_IFREG 0 9 8 1700000000).set 47 (Z_to_bv 8 1)) = false
    ∧ stat_stable_eqb (stat_fixture 4711 S_IFREG 0 9 8 1700000000)
                      ((stat_fixture 4711 S_IFREG 0 9 8 1700000000).set 56 (Z_to_bv 8 1)) = false := by
  decide

set_option maxRecDepth 4096 in
/-- `stat_set_size` writes the new length at offset 48 and nothing else. -/
theorem stat_set_size_writes_the_length :
    stat_field_le ST_SIZE_OFF 8 (stat_set_size 12 (stat_fixture 4711 S_IFREG 0 9 8 1700000000)) = 12
    ∧ stat_size_ok 12 (stat_set_size 12 (stat_fixture 4711 S_IFREG 0 9 8 1700000000)) = true
    ∧ stat_buf_wf (stat_set_size 12 (stat_fixture 4711 S_IFREG 0 9 8 1700000000)) = true := by
  decide

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Sys.Uapi.Fs
