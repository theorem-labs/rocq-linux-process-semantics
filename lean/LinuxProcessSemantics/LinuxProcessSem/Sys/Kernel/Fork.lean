import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Kernel.Fork — set_tid_address (96), clone (220), clone3 (435)

Mirrors `theories/LinuxProcessSem/Sys/Kernel/Fork.v`.  This file answers
to Linux `kernel/fork.c`: it holds what the kernel defines there, and
nothing else.

TRUST BOUNDARY: this file is part of the trusted specification.

Every definition keeps the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f) — and point at the Rocq
definition for the argument in full, so there is one place to correct it.
The baseline above is the Rocq commit this twin was checked against: the
`set_tid_address` half is unchanged since f44244ad6b80, the commit the port
was first read at, and what moved in between (#712's `FdUrandom` arm of
`clone_no_shared_file_b`) is ported below.
The Rocq file read its kernel side at v6.16 and says so; every line cited
here was re-read at v6.18.46, and the one place the two versions differ
in SHAPE is named on `PID_MAX_ENVELOPE` below.  Line citations are
spelled `path:line`, unbracketed, because that is the one shape
`tools/check_kernel_citations.py` pairs with its line number.

The Rocq file reads its clone side across mainline v6.6..v7.2 and three
stable branches and says so on each definition; every line cited here was
read at v6.18.46, and where that version's spelling differs from the one
Rocq's prose describes (the -EMFILE site of `dup_fd`) the difference is
named on the definition.

Three spellings differ from Rocq without changing a value.  `forallb` is
`List.all`; the `Z.ltb` tests of `clone_pid_ok_b` are Lean's decidable
`<` on `Int` read as `Bool` (its `bv_eqb r t0` is kept as Rocq spells it),
and `negb` is `!`; and `firstn 8 (skipn (8 * k) bs)` is
`(bs.drop (8 * k)).take 8`. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall

/-- The upper bound on the tid the environment may choose, EXCLUSIVE, so
the envelope is `1 ≤ tid < 2^22`.  The argument in full — why an
over-approximation in this direction is the safe one, and why admitting 0
would not be harmless — is on the Rocq definition
`Kernel.Fork.PID_MAX_ENVELOPE` and is not repeated here.  What follows is
the kernel line each half rests on, read at Linux v6.18.46 (commit
1f99e9ab748f).

POSITIVE.  A live task never holds tid 0.  `alloc_pid` allocates through
`idr_alloc_cyclic(&tmp->idr, NULL, pid_min, pid_max, GFP_ATOMIC)`
(kernel/pid.c:238-239, v6.18.46) with `int pid_min = 1` (kernel/pid.c:226, v6.18.46), raised
only to `RESERVED_PIDS` (kernel/pid.c:231-232, v6.18.46), which is 300
(include/linux/pid.h:48, v6.18.46); a REQUESTED tid passes `if (tid < 1 || tid >=
pid_max)` first, yielding -EINVAL (kernel/pid.c:199, v6.18.46).  That bounds the
number `alloc_pid` stores.  What `set_tid_address` RETURNS is
`task_pid_vnr(current)`, and the chain between the two carries two
`nr = 0` defaults a reader has to rule out: `__task_pid_nr_ns`
(kernel/pid.c:510-523, v6.18.46) answers 0 when its `ns` is still NULL after the
substitution at kernel/pid.c:516-517 (v6.18.46), and `pid_nr_ns`
(kernel/pid.c:490-501, v6.18.46) answers 0 when the task is not visible in the
namespace asked about.  Neither fires here because the argument is
`current`.  The `NULL` in `task_pid_vnr` (include/linux/pid.h:244-247, v6.18.46)
is what that substitution replaces by `task_active_pid_ns(current)`;
`task_active_pid_ns` (kernel/pid.c:526-529, v6.18.46) is `ns_of_pid(task_pid(tsk))`,
and `ns_of_pid` (include/linux/pid.h:149, v6.18.46) names the namespace of the pid's
own deepest `upid` — so the `upid->ns == ns` test inside `pid_nr_ns`
(kernel/pid.c:497, v6.18.46) holds and `nr` is the allocated one.  Applied to a
task OTHER than `current` the same function can answer 0; the sentence
that opens this paragraph is true of this call, not of `task_pid_vnr`.

BELOW `2^22`.  `idr_alloc_cyclic`'s `end` argument is EXCLUSIVE
(lib/idr.c:102, the kerneldoc of the definition at lib/idr.c:119, v6.18.46) —
`max = end > 0 ? end - 1 : INT_MAX` (lib/idr.c:122, v6.18.46) — so `pid_max`
itself is never allocated PROVIDED `pid_max > 0`: an `end <= 0` is
treated as one larger than `INT_MAX` (lib/idr.c:106, v6.18.46), and that escape
would put the answer far outside this envelope.  So two facts have to
hold of every `pid_max`, `0 < pid_max` and `pid_max ≤ PID_MAX_LIMIT`, and
every write to a namespace's `pid_max` at v6.18.46 keeps both.  There are
five.  `pid_max_max` is initialised to `PID_MAX_LIMIT` (kernel/pid.c:65, v6.18.46)
and written nowhere else, `pid_max_min` to `RESERVED_PIDS + 1`
(kernel/pid.c:64, v6.18.46).  The `init_pid_ns` initialiser sets `.pid_max =
PID_MAX_DEFAULT` (kernel/pid.c:84, v6.18.46), which is 0x8000, or 0x1000 under
`CONFIG_BASE_SMALL` (include/linux/threads.h:28, v6.18.46); both keep the bound.
`create_pid_namespace` sets every other namespace's to `PID_MAX_LIMIT`
outright (kernel/pid_namespace.c:110, v6.18.46) — a bare assignment of the bound
itself, and the write that makes `2^22 - 1` a tid a real kernel hands
out.  The `pid_max` sysctl is floored by `.extra1 = &pid_max_min` and
capped by `.extra2 = &pid_max_max` (kernel/pid.c:743-749, v6.18.46).  And two
`min(pid_max_max, …)` clamps run at set-up, in `register_pidns_sysctls`
(kernel/pid.c:773, v6.18.46, inside the `#ifdef CONFIG_SYSCTL` that opens at
kernel/pid.c:764) and in `pid_idr_init` (kernel/pid.c:805, unconditional).
`PID_MAX_LIMIT` (include/linux/threads.h:34-35, v6.18.46) is
`IS_ENABLED(CONFIG_BASE_SMALL) ? PAGE_SIZE * 8 : (sizeof(long) > 4 ? 4 *
1024 * 1024 : PID_MAX_DEFAULT)`.  That is TWO arms, and `2^22` is the
ceiling of both on a 64-bit kernel rather than the value of one: the
second arm is exactly `4 * 1024 * 1024 = 2^22`, and the
`CONFIG_BASE_SMALL` arm is `PAGE_SIZE * 8`, which on riscv64 is 32768 —
arch/riscv/Kconfig:186 (v6.18.46) selects `HAVE_PAGE_SIZE_4KB`, the only
`HAVE_PAGE_SIZE_*` option the architecture selects, so `PAGE_SIZE` is
4096.  A `CONFIG_BASE_SMALL=y` kernel, or any smaller runtime `pid_max`,
therefore stays strictly inside this envelope.

THE SHAPE MOVED BETWEEN THE ROCQ READING AND THIS ONE, AND THE BOUND DID
NOT.  Rocq read `pid_max` as a single global `int` through v6.13 and a
per-namespace field from v6.14, and stated the range v6.12..v6.16.  At
v6.18.46 it is the per-namespace field
(include/linux/pid_namespace.h:33, read as `int pid_max =
READ_ONCE(tmp->pid_max)` in `alloc_pid`, kernel/pid.c:193), so the second
of Rocq's two shapes is the one this tree is pinned to, and the five
writes above are read in that shape.  That is what makes `2^22` safe to
state as a constant rather than as one kernel's answer. -/
def PID_MAX_ENVELOPE : Int := 2 ^ 22

/-- `set_tid_address tidptr` (96) — returns the caller's tid, and does
nothing else the model can observe.

THE VALUE IS THE ENVIRONMENT'S CHOICE, MADE ONCE.  `SYSCALL_DEFINE1(
set_tid_address, int __user *, tidptr)` (kernel/fork.c:1747-1752, Linux
v6.18.46, commit 1f99e9ab748f) is two statements — `current->
clear_child_tid = tidptr;` then `return task_pid_vnr(current);` — with no
validation of `tidptr` and no error path at all, which is why the spec
accepts the argument positionally through the dispatcher and reads none
of it.  The model cannot predict the tid, so the first call draws one
inside `PID_MAX_ENVELOPE` and records it in `m_tid`, and every later call
returns the recorded value, as `task_pid_vnr` does for a task whose pid
does not move.

WHEN A TASK'S PID DOES MOVE, AND WHY NOT HERE.  A thread-group leader
keeps its pid for life.  A NON-leader thread that calls `execve` takes
the leader's pid through `exchange_tids` (kernel/pid.c:384-403, v6.18.46), which
`de_thread` (fs/exec.c:908-1041, v6.18.46) runs at fs/exec.c:995 (v6.18.46), and the number
this call returns for that thread changes from then on.  This model holds
one task, and the `clone` arm below admits only the plain-fork word —
`clone_fork_flags_b` declines `CLONE_THREAD` — so no second thread exists
to exchange with; the memoisation stops being justified the day a
`clone(CLONE_THREAD)` arm and an `execve` arm both land.  The slot it
memoises into is shared: Rocq's `getpid` (172), `gettid` (178) and
`setsid` (157) read or write the same `m_tid` (`Kernel.Sys.gettid_spec`
IS `set_tid_address_spec`), and the three agree with this call only while
the task is its own thread-group leader — the premise
`testing/syscall-check/tests/unmodeled_clone.c` pins on the Rocq side.
Ticket S-Kernel-Sys-ids ports the three and inherits that premise, stated
on `Kernel.Sys.getpid_spec` as a condition on every clone arm.

NO MEMORY EFFECT, AND THE REASON IS NOT THE ONE A READER EXPECTS.  The
call records `tidptr` in the CALLER's `current->clear_child_tid` and
dereferences nothing, so no byte moves at the call.  The write THROUGH
that pointer is a different event: `put_user(0, tsk->clear_child_tid)`
in `mm_release` (kernel/fork.c:1424-1455, v6.18.46, the write at
kernel/fork.c:1442), which is `static` and reached only from
`exit_mm_release` (kernel/fork.c:1457-1461, v6.18.46) and `exec_mm_release`
(kernel/fork.c:1463, v6.18.46), both passing the task itself — so it fires when
THIS task exits or execs, not when any child does — and it is guarded on
`atomic_read(&mm->mm_users) > 1` (kernel/fork.c:1437, v6.18.46), together with the
`do_futex(…, FUTEX_WAKE, …)` beside it (kernel/fork.c:1443-1444, v6.18.46).  This
model admits no second holder of an mm, so `mm_users` is 1 and the write
cannot fire.  That is a closed-world statement about the ENVIRONMENT and
is deliberately broader than any flag test; the Rocq definition
`Kernel.Fork.set_tid_address_spec` argues why naming `CLONE_VM` instead
would give a false all-clear, and why the argument does not rest on 220
being declined.  One detail a description of the write alone would hide:
`tsk->clear_child_tid = NULL` (kernel/fork.c:1446, v6.18.46) runs REGARDLESS of the
`mm_users` test, so the field is cleared even when nothing is written. -/
def set_tid_address_spec : Sys SyscallEffect :=
  m <- get_model ;;
  match m_tid m with
  | some tid => ret_only tid
  | none =>
      tid <- choose (fun tid => 0 < bv_unsigned tid ∧ bv_unsigned tid < PID_MAX_ENVELOPE) ;;
      set_tid tid ;;
      ret_only tid

/-! ## Process creation — the CALLER's resolution, and nothing else

`clone` (220) and `clone3` (435) are modeled ONLY in the answer the
calling process receives: a child pid, or a failure.  No second process is
created — `Run.config` holds one machine state and one `Model`, and the
child is never a configuration this development can be in.  The argument
in full — why the child is out of scope, why ignoring it is not
automatically safe, which channels a flag test closes and which five stay
open under `bugs/`, why the flag gate is an allowlist of one word, why the
answer is never zero, and the out-of-tree measurement behind the admitted
word — is on the Rocq block above `Kernel.Fork.SIGCHLD` (the section's
header comment, which precedes the constant, not `clone_spec`) and is not
repeated here.  What follows is the kernel line each decision rests on, read at
Linux v6.18.46 (commit 1f99e9ab748f).

THE ENTRY POINT.  riscv64 selects `CLONE_BACKWARDS` (arch/riscv/Kconfig:97),
so `SYSCALL_DEFINE5(clone, unsigned long, clone_flags, unsigned long, newsp,
int __user *, parent_tidptr, unsigned long, tls, int __user *,
child_tidptr)` (kernel/fork.c:2720-2723, Linux v6.18.46) is the prototype; it builds
`kernel_clone_args` from `lower_32_bits(clone_flags)` split at `CSIGNAL`
(:2742-2751) and hands it to `kernel_clone` (:2570-2655), which returns
`pid_vnr(pid)` of the task `copy_process` (:1934-2503) created (:2624,
:2654).  With `flags = SIGCHLD` the tid pointers and `tls` are never
dereferenced — the uses are gated on `CLONE_PARENT_SETTID` (:2626-2627, a
`put_user` into the caller's memory, not a read), `CLONE_CHILD_SETTID`
(:2040) and `CLONE_SETTLS` (arch/riscv/kernel/process.c:253-254, Linux v6.18.46) — so the
spec does not fetch them, and `newsp` is seated in the CHILD's registers
only (`copy_thread`, arch/riscv/kernel/process.c:251-252), so the caller's
answer is the same whatever it holds. -/

/-- The exit signal a plain `fork` requests.  `SIGCHLD` is 17
(`include/uapi/asm-generic/signal.h`:28, Linux v6.18.46, commit
1f99e9ab748f), the numbering riscv64 takes; `kernel_clone` reads it back
as the ptrace event selector (`args->exit_signal != SIGCHLD`,
kernel/fork.c:2602-2605) and `copy_process` stores it as the child's
`exit_signal` (:2342).  Why this ONE word is the whole allowlist is on
Rocq's `Kernel.Fork.SIGCHLD` and `Kernel.Fork.clone_fork_flags_b`. -/
def SIGCHLD : Int := 17

/-- The clone failures this model admits, for the one flag word it
answers: every error return of `kernel_clone` and `copy_process`
(kernel/fork.c, Linux v6.18.46, commit 1f99e9ab748f) that survives
`flags = SIGCHLD` from a user process, walked in source order.  Rocq's
`Kernel.Fork.clone_errnos` carries the version history (mainline
v6.6..v7.2 and three stable branches) and the argument for each exclusion;
the lines below are the v6.18.46 reading.

- EAGAIN.  `copy_process`'s `RLIMIT_NPROC` test (`is_rlimit_overlimit`,
  :2058-2064) and its `nr_threads >= max_threads` ceiling (:2071-2073);
  `alloc_pid` remapping `idr_alloc_cyclic`'s -ENOSPC on the path a plain
  fork takes (kernel/pid.c:245, Linux v6.18.46 — the -EEXIST remap at :224 is the
  `set_tid` path, which needs `set_tid_size > 0` and so is clone3-only,
  so -ENOSPC never escapes either way); `sched_fork` refusing to fork a
  `SCHED_DEADLINE` task (kernel/sched/core.c:4725-4726, Linux v6.18.46); and
  `pids_can_fork` (kernel/cgroup/pids.c:273, Linux v6.18.46) through `pids_try_charge`'s
  refusal (:197).
- ENOMEM.  Every allocation on the path: `dup_task_struct` (:2019-2021),
  `copy_creds` (:2054) through `prepare_creds` failing its slab
  allocation (kernel/cred.c:212-214, Linux v6.18.46), `mpol_dup` → `__mpol_dup` (mm/mempolicy.c:2756, Linux v6.18.46), `audit_alloc`
  (kernel/auditsc.c:1057, Linux v6.18.46), `lsm_task_alloc` inside `security_task_alloc`
  (security/security.c:3337-3342, Linux v6.18.46), `dup_fd`'s own `files_struct`
  allocation (fs/file.c:390-392, Linux v6.18.46) under `copy_files` (:1601), `copy_fs`'s
  `copy_fs_struct` (:1573-1575), `copy_sighand` (:1617-1620),
  `copy_signal` (:1665-1668), `copy_mm` — `dup_mm` FLATTENS `dup_mmap`'s
  failure into a NULL return (:1479-1518) that `copy_mm` reports as
  -ENOMEM (:1547-1549), so `dup_mmap`'s -EINTR is not separately
  reachable — `copy_namespaces` past its fast path (kernel/nsproxy.c:155-160, Linux v6.18.46
  returns 0 while `time_ns_for_children == time_ns`; a parent that
  unshared a time namespace reaches `create_new_namespaces`, :175-177),
  `__copy_io` for a parent holding an `io_context` (block/blk-ioc.c:289, Linux v6.18.46),
  `alloc_pid`'s own slab allocation (kernel/pid.c:184-186, Linux v6.18.46) and
  its `PIDNS_ADDING` re-test under `pidmap_lock` (:262, :276-277), and a
  dying pid namespace seen again by `copy_process` (:2356-2358).
- EMFILE.  `copy_files` → `dup_fd` (fs/file.c:383, Linux v6.18.46) → `alloc_fdtable`
  (:162) when the parent holds more open descriptors than the CURRENT
  `sysctl_nr_open` allows after rounding it down to a `BITS_PER_LONG`
  boundary (:194-197), and past `INT_MAX / sizeof(struct file *)`
  (:212-213).  Rocq's prose places the first test inline in `dup_fd` for
  mainline up to v6.12 and inside `alloc_fdtable` from v6.13; v6.18.46 is
  the `alloc_fdtable` form, which is what is cited here.
- EACCES.  `security_task_alloc` (security/security.c:3337-3347) →
  `selinux_task_alloc` (security/selinux/hooks.c:4264-4273), which
  copies the task's security blob and returns `avc_has_perm(sid, sid,
  SECCLASS_PROCESS, PROCESS__FORK, NULL)` (security/selinux/avc.c:1188, Linux v6.18.46),
  whose denial is `avc_denied`'s -EACCES (:995-1005).  AppArmor's and
  TOMOYO's `task_alloc` return 0 unconditionally, so SELinux is the only
  in-tree source.

NOT ADMITTED, and why each is unreachable rather than absorbed: -EINVAL,
-EPERM and -EBUSY are gated on flag bits this word does not set
(`copy_process`'s flag checks, :1951-1998; `cpuset_can_fork`
short-circuits on `same_cs`, kernel/cgroup/cpuset.c:3730-3734, Linux v6.18.46, leaving
`pids_can_fork`'s -EAGAIN as the only cgroup answer); -EFAULT cannot
arise because legacy `clone` dereferences no user pointer for this word;
-ENOSPC is remapped by `alloc_pid`; and -ERESTARTNOINTR (:2015-2017) and
-EINTR (:2362-2364) are reachable inside `copy_process` but never reach a
register the program can read — riscv64's `arch_do_signal_or_restart`
(arch/riscv/kernel/signal.c:396, Linux v6.18.46) restarts -ERESTARTNOINTR
unconditionally (:417-420), its "revert the decision to restart" branch
covering only -ERESTARTNOHAND, -ERESTART_RESTARTBLOCK and a
non-SA_RESTART -ERESTARTSYS (:438-441), and the -EINTR arm is reached
only with a fatal signal pending, which group-exits the task before it
returns to userspace.

THREE ENVIRONMENT RESTRICTIONS are stated rather than modeled, each able
to make a real kernel answer something outside this list: a parent
holding inheritable perf events (`perf_event_init_task`,
kernel/events/core.c:14669, Linux v6.18.46), a BPF LSM program attached to `task_alloc`,
and a BPF scheduler's task init through `sched_cgroup_fork` (:2299).
Recorded in bugs/clone-errnos-omits-three-environment-failures.md; the
argument is on the Rocq definition. -/
def clone_errnos : List Int := [EAGAIN, ENOMEM, EMFILE, EACCES]

/-- The one flag word this model answers: a child that shares nothing,
reporting `SIGCHLD` on exit.  This is what `fork` is.

THE TEST IS ON THE WHOLE 64-BIT REGISTER, which is STRICTER than the
kernel's own reading and deliberately so.  `SYSCALL_DEFINE5(clone, ...)`
(kernel/fork.c:2720-2753, Linux v6.18.46, commit 1f99e9ab748f) splits
`lower_32_bits(clone_flags)` into two disjoint halves — `.flags` gets it
masked with `~CSIGNAL` (:2743) and `.exit_signal` gets it masked with
`CSIGNAL` (:2747) — and reads nothing above bit 31, so a register of
0x1_00000011 is a plain fork to Linux and is DECLINED here.  Declining is
the fail-closed direction; the cost to the claim, and why the
thread-creating words (`CLONE_VM | CLONE_FS | CLONE_FILES | CLONE_SIGHAND
| CLONE_THREAD | ...`, which Linux ACCEPTS) must decline rather than
answer -EAGAIN, are on Rocq's `Kernel.Fork.clone_fork_flags_b`.  `clone3`
does NOT truncate — `copy_clone_args_from_user` assigns the struct's
`flags` field whole (:2803) — so `clone3_fork_args_b`'s 64-bit test is
exact where this one is strict. -/
def clone_fork_flags_b (flags : word) : Bool :=
  bv_eqb flags (Z_to_bv 64 SIGCHLD)

/-- No descriptor this model would give the child a PRIVATE offset for.
`copy_files` (kernel/fork.c:1579-1607, Linux v6.18.46, commit
1f99e9ab748f) hands the child a table of second references to the same
`struct file`s — `dup_fd`'s `get_file(f)` (fs/file.c:458) — so a plain
fork shares every open description's `f_pos`, and `State.FdEntry` inlines
the offset into the descriptor.  Rocq's `Kernel.Fork.clone_no_shared_file_b`
argues each kind; the verdicts:

- `FdFile`, `FdFileW`: DECLINE — a copied `m_fds` would hand the child an
  offset of its own where `copy_files` gave it a shared one, a wrong
  answer rather than a declined one.
- `FdDir`: PASSES — `f_pos` is shared on a real kernel too, but no
  modeled syscall can OBSERVE a directory position, so there is no answer
  for the sharing to make wrong.
- `FdChannel`: PASSES, and is the honest hole — a channel's position is
  the run's `InputStream`, not the descriptor's, so the gate cannot name
  it; recorded in bugs/clone-child-io-on-inherited-channels.md.
- `FdSocket`: DECLINE — the entry inlines the connection's remaining
  receive script, so a copy would report a peer's reset once to each
  process where Linux reports it once for the connection.
- `FdPipe`: DECLINE — both references name one `pipe_inode_info`: a child
  that reads drains bytes the parent then cannot read, and a child that
  CLOSES its copy does not drop the writer count (`pipe_release`,
  fs/pipe.c:730-733, Linux v6.18.46), which is what decides whether the peer sees EOF or
  blocks (`anon_pipe_read`'s `!pipe->writers` test, :370).  An `FdEntry`
  carries no per-description state and nothing counts ends.
- `FdDevNull`: PASSES — the shared `f_pos` is pinned at 0 by `null_lseek`
  (drivers/char/mem.c:561, Linux v6.18.46) and never moved by `read_null`/`write_null`
  (:412-421), and the node has no reader or writer count, so nothing
  shared can be observed.
- `FdUrandom`: PASSES for the same reason — `urandom_fops`
  (drivers/char/random.c:1572-1581, Linux v6.18.46) seats `noop_llseek` as its `.llseek`
  (:1578), which leaves `f_pos` where it is, `urandom_read_iter` (:1453)
  reads no position at all, and the bytes a read hands out come from the
  run's declared stream (`State.m_urandom`) rather than from the file.  The child is not executed by this model
  (`clone` describes the parent), so nothing it might read off the device
  is a consumption the declaration has to account for: the stream is what
  the device hands THIS process.  The arm is the one Rocq's Fork.v gained
  with the /dev/urandom mirror, read at the baseline commit above. -/
def clone_no_shared_file_b (fds : List (word × FdEntry)) : Bool :=
  fds.all (fun e => match e.2 with
    | .FdFile _ _ | .FdFileW _ _ | .FdFileA _ _ | .FdFileRW _ _ | .FdSocket _ => false
    | .FdChannel _ | .FdDir => true
    | .FdPipe _ _ => false
    | .FdDevNull _ _ => true
    | .FdUrandom => true)

/-- The pids a successful `clone` may report.  `kernel_clone` returns
`pid_vnr(pid)` (kernel/fork.c:2624, :2654, Linux v6.18.46, commit
1f99e9ab748f) of the `struct pid` that `alloc_pid` (kernel/pid.c:163)
drew with `idr_alloc_cyclic(&tmp->idr, NULL, pid_min, pid_max,
GFP_ATOMIC)` (:238-239): strictly positive, since `pid_min` starts at 1
(:226) — and the model's never-zero DECISION, argued on Rocq's
`Kernel.Fork.SIGCHLD` block, because 0 is the CHILD's answer
(`childregs->a0 = 0`, arch/riscv/kernel/process.c:255, Linux v6.18.46); below
`PID_MAX_ENVELOPE`, the exclusive end `idr_alloc_cyclic` never reaches
(lib/idr.c:102, Linux v6.18.46) applied to the same clamp `set_tid_address_spec` draws
under; and different from the caller's own tid once that tid has been
observed, because `alloc_pid` hands out a FREE pid and the caller's own is
in use.  THE LAST CONJUNCT IS VACUOUS UNTIL THE TID IS OBSERVED: `m_tid`
starts `none`, so a clone made before any `getpid` or `set_tid_address`
admits the caller's own pid — a widening, not an unsound acceptance,
recorded in bugs/clone-retires-no-pid.md. -/
def clone_pid_ok_b (m : Model) (r : word) : Bool :=
  0 < bv_unsigned r && bv_unsigned r < PID_MAX_ENVELOPE &&
  (match m_tid m with | none => true | some t0 => !(bv_eqb r t0))

/-- The resolution both entry points share, once the arguments are known
to describe a plain fork.  The caller's identity, descriptors, file system
and clock are untouched by its own `clone`, and the child is not a thing
this model holds — but the FACT that a child now exists is, because
`Kernel.Exit.wait4_spec` answers -ECHILD only while `State.m_has_children`
is clear: `__do_wait` (kernel/exit.c:1675, Linux v6.18.46) seeds -ECHILD
and only a child on `current->children` — where `copy_process` links the
new task (`list_add_tail(&p->sibling, &p->real_parent->children)`,
kernel/fork.c:2398) — clears it, or a tracee through `ptrace_do_wait`
(:1694), which no modeled syscall can create.  So the success branch, and only the
success branch, records it with `State.with_children`: the errno
alternative created nothing (`copy_process` unwinds every allocation on
its `bad_fork_*` labels, :2438-2503, and returns `ERR_PTR(retval)`), and
the `clone_no_shared_file_b` decline never reaches a resolution at all.
Without this call the pair is unsound in a way neither side's proofs can
see; the argument is on Rocq's `Kernel.Fork.clone_resolve`. -/
def clone_resolve : Sys SyscallEffect :=
  m <- get_model ;;
  if !(clone_no_shared_file_b (m_fds m)) then unmodeled
  else
    alt (e <- errno_from clone_errnos ;; err_ret e)
        (pid <- choose (fun p => clone_pid_ok_b m p = true) ;;
         modify with_children ;;
         ret_only pid)

/-- `clone flags` (220): the flag gate, then the shared resolution.  The
order is the kernel's — `SYSCALL_DEFINE5(clone, ...)` (kernel/fork.c:2720,
Linux v6.18.46, commit 1f99e9ab748f) splits the flag word before
`kernel_clone` copies anything, and `copy_files` (:2173) runs inside
`copy_process` after it — and the gate declines rather than answers, so no
errno of the resolution is reachable for a word outside the allowlist. -/
def clone_spec (flags : word) : Sys SyscallEffect :=
  if clone_fork_flags_b flags then clone_resolve else unmodeled

/-! ## `clone3` (435): the same resolution through a struct in user memory -/

/-- `sizeof(struct clone_args)`.  The struct (include/uapi/linux/sched.h:92-104,
Linux v6.18.46, commit 1f99e9ab748f) is eleven `__aligned_u64` fields —
flags, pidfd, child_tid, parent_tid, exit_signal, stack, stack_size, tls,
set_tid, set_tid_size, cgroup — and its size is `CLONE_ARGS_SIZE_VER2 = 88`
(:109), which `copy_clone_args_from_user`'s `BUILD_BUG_ON(sizeof(struct
clone_args) != CLONE_ARGS_SIZE_VER2)` (kernel/fork.c:2770, Linux v6.18.46) pins.
That function accepts a `size` in `[CLONE_ARGS_SIZE_VER0, PAGE_SIZE]` and
rejects outside it, in that order: `usize > PAGE_SIZE` is -E2BIG first
(:2772-2773), then `usize < CLONE_ARGS_SIZE_VER0` is -EINVAL (:2774-2775).
Inside that range `copy_struct_from_user` (include/linux/uaccess.h:389-411, Linux v6.18.46)
zero-fills what a shorter caller did not supply (:400-401) and requires
the excess of a longer one to be zero, answering -E2BIG otherwise
(:402-405).

THIS MODEL ANSWERS ONE SIZE, the full struct, and declines the short
forms: a short `size` is a different kernel path, and reproducing it
would mean modeling how many fields the caller's headers had.  Declining
is fail-closed in the ordinary way and costs nothing observed — no libc
emits a fork-shaped `clone3`; the walk through glibc's three callers and
musl is on Rocq's `Kernel.Fork.CLONE_ARGS_SIZE`, with the log-exhaustive
argument that the struct has not changed since v5.7.  A constant rather
than a literal because the places outside this file that repeat it
(`testing/syscall-check`'s pre-syscall capture width, its `--replay`
copy-in width and its README) must move with it. -/
def CLONE_ARGS_SIZE : Int := 88

/-- Field `k` of a `struct clone_args` image, little-endian: eight bytes
at offset `8 * k`, the layout `__aligned_u64` fixes
(include/uapi/linux/sched.h:92-104, Linux v6.18.46). -/
def clone_args_field (bs : List byte) (k : Nat) : word :=
  le_bytes_to_word ((bs.drop (8 * k)).take 8)

/-- The admitted image: the whole struct zero except `exit_signal`, at
offset 32 (field 4), equal to `SIGCHLD` — which is `clone(SIGCHLD, 0)`
told a different way, and reaches `kernel_clone` with the same arguments
through `clone3` (kernel/fork.c:2892-2914, Linux v6.18.46, commit
1f99e9ab748f; the call is :2913).  The kernel's
own checks on the image, every one of which this shape passes: every bit
of `exit_signal` above `CSIGNAL` clear and `valid_signal` (:2794-2796, the latter
`sig <= _NSIG`, include/linux/signal.h:272-275, Linux v6.18.46); `set_tid` and
`set_tid_size` consistent (:2781-2788); `CLONE_INTO_CGROUP` absent
(:2798-2800); `clone3_args_valid`'s flag mask and its `CLONE_DETACHED`/
`CSIGNAL` reservations (:2853-2879); and `clone3_stack_valid`, which
accepts `stack = 0` only with `stack_size = 0` (:2833-2837).

In particular `flags` must be zero, so the sharing bits the legacy gate
keeps out are excluded here by the same allowlist, and the test on that
field is EXACT: `copy_clone_args_from_user` assigns it whole (:2803) and
`CLONE_CLEAR_SIGHAND` really is bit 32 (include/uapi/linux/sched.h:37, Linux v6.18.46).
ONE ASYMMETRY BETWEEN THE ENTRY POINTS IS THIS MODEL'S OWN: the legacy arm
answers `clone(SIGCHLD, newsp)` for ANY `newsp`, this image requires
`stack` and `stack_size` to be zero, so the same request through 435 is
declined.  Both directions are sound — `copy_thread` seats the stack in
the CHILD's registers only (arch/riscv/kernel/process.c:251-252, Linux v6.18.46) — and
the legacy arm is the more permissive; the Rocq block on
`Kernel.Fork.CLONE_ARGS_SIZE` says why neither is moved. -/
def clone3_fork_args_b (bs : List byte) : Bool :=
  w_is0 (clone_args_field bs 0)                          -- flags
  && w_is0 (clone_args_field bs 1)                       -- pidfd
  && w_is0 (clone_args_field bs 2)                       -- child_tid
  && w_is0 (clone_args_field bs 3)                       -- parent_tid
  && bv_eqb (clone_args_field bs 4) (Z_to_bv 64 SIGCHLD) -- exit_signal
  && w_is0 (clone_args_field bs 5)                       -- stack
  && w_is0 (clone_args_field bs 6)                       -- stack_size
  && w_is0 (clone_args_field bs 7)                       -- tls
  && w_is0 (clone_args_field bs 8)                       -- set_tid
  && w_is0 (clone_args_field bs 9)                       -- set_tid_size
  && w_is0 (clone_args_field bs 10)                      -- cgroup

/-- `CLONE_ARGS_SIZE` as a `Nat`, for the copy-in ledger.  The mirror is a
theorem rather than a second literal, so the two cannot drift. -/
def CLONE_ARGS_SIZE_nat : Nat := 88

theorem clone_args_size_nat_ok : (CLONE_ARGS_SIZE_nat : Int) = CLONE_ARGS_SIZE := rfl

/-- THE STRUCT IS READ, AND THE LEDGER SAYS SO.  `clone3` differs from
legacy `clone` in exactly one observable way before the resolution: it
copies `struct clone_args` out of user memory — `copy_struct_from_user`'s
`copy_from_user(dst, src, size)` (include/linux/uaccess.h:408-409, Linux
v6.18.46, commit 1f99e9ab748f) — and that faults every page of it in.
Recording the range is what stops the model admitting an allocation the
kernel refuses: `SyscallEffect.eff_copyins` feeds
`State.materialize_model_accesses`, where a struct straddling a
`MAP_NORESERVE` boundary charges its second page.

The ledger goes on the paths PAST a successful read and nowhere else.  A
`size` the model declines never reaches the copy; an unreadable struct is
a copy that FAILED, and Linux charges nothing for it either (`-EFAULT` at
:409 returns before `kernel_clone` is reached).  Both are `unmodeled`
here, which carries no effect at all, so the boundary is exactly "the read
succeeded" — and the errno arm is past it, so it carries the ledger too. -/
def clone3_resolve (uargs : word) : Sys SyscallEffect :=
  record_copyins [(uargs, CLONE_ARGS_SIZE_nat)] clone_resolve

/-- The ledger is the ONLY thing `clone3_resolve` adds: strip it and what
is left is the very outcome `clone_resolve` admits, with the same return,
model and events.  Everything proved about the shared resolution
therefore carries over to `clone3` unchanged.  Twin of Rocq's
`Kernel.Fork.clone3_resolve_inv`. -/
theorem clone3_resolve_inv (uargs : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (h : clone3_resolve uargs i m (Ok eff m' evs)) :
    ∃ e0, clone_resolve i m (Ok e0 m' evs) ∧ eff.eff_ret = e0.eff_ret := by
  unfold clone3_resolve record_copyins Monad.bind at h
  obtain ⟨e0, m0, evs0, evs2, h0, hp, hevs⟩ := h
  simp only [Monad.pure, outcome.Ok.injEq] at hp
  obtain ⟨rfl, rfl, rfl⟩ := hp
  rw [List.append_nil] at hevs
  subst hevs
  exact ⟨e0, h0, rfl⟩

/-- `clone3 uargs size` (435): the size gate, the read, the image gate,
then the shared resolution under the copy-in ledger.  The order is
`SYSCALL_DEFINE2(clone3, struct clone_args __user *, uargs, size_t,
size)` (kernel/fork.c:2892-2914, Linux v6.18.46, commit 1f99e9ab748f):
`copy_clone_args_from_user` tests `size` (:2772-2775) before it copies
(:2777), `clone3_args_valid` (:2910) reads the copied image, and only
then does `kernel_clone` run (:2913).  Three declines, none an answer: a
`size` other than the whole struct, a struct not wholly readable, and an
image other than the plain-fork one.  `size` is a `size_t` and is NOT
narrowed: a register of `88 + 2^32` is not 88 to the kernel either.

The answers are LINUX's alone.  QEMU's user-mode emulation at v11.1.1 has
no `clone3` handler and answers -ENOSYS to every 435 with nothing read
(`linux-user/syscall.c`'s `default:` arm), an answer neither this arm nor
Rocq's offers or declines; bugs/clone3-enosys-arm-admits-linux-alone.md
records the gap and what closes it. -/
def clone3_spec (uargs size : word) : Sys SyscallEffect :=
  if !(bv_eqb size (Z_to_bv 64 CLONE_ARGS_SIZE)) then unmodeled
  else
    i <- input ;;
    match read_bytes_map i.in_mem uargs (Z_to_bv 64 CLONE_ARGS_SIZE) with
    | none => unmodeled       -- the struct is not wholly readable
    | some bs =>
        if clone3_fork_args_b bs then clone3_resolve uargs else unmodeled

end LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork
