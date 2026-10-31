-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/State.v
import LinuxProcessSemantics.LinuxProcessSem.Fs
import LinuxProcessSemantics.LinuxProcessSem.State.Fd
import LinuxProcessSemantics.LinuxProcessSem.State.Vm

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058 -/

/-! # LinuxProcessSem.State.Model — the seven subsystems and the model

One part of `State.v`'s twin, re-exported by `State.lean`, whose header
says how the ten parts divide the Rocq file, what a part may hold and
where the pins live.

WHAT GOES HERE: the record layout of `Model` and its seven subsystems,
the accessors and the field-update helpers (the signal and terminal
state of ticket A12 among them), the observable events, the process
input and `init_model`, and the setter/accessor facts `Checks.Examples`
and `MustExit` rely on (Rocq's `model` rewrite database is not ported;
the docstring on the first of them says so).  Every field keeps the
Rocq name and type, so a spec ported later reads the same state the
Rocq one does.

TRUST BOUNDARY: this file is part of the trusted specification. -/

namespace LinuxProcessSemantics.LinuxProcessSem.State

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Fs

/-! ## The seven subsystems -/

structure FdState where
  mkFdState ::
  fdst_table : List (word × FdEntry)
  fdst_pipes : List (word × PipeBuf)

structure VmState where
  mkVmState ::
  vmst_maps : VmMaps
  vmst_lazy : List (word × word)
  vmst_materialized : List word

structure IoState where
  mkIoState ::
  iost_stdin : InputStream
  /-- The unconsumed remainder of the random device's declared stream
  (see the Rocq field note). -/
  iost_urandom : InputStream
  iost_net : NetQueue
  iost_conn_ix : word

structure FsState where
  mkFsState ::
  fsst_image : Fs.Fs

structure Creds where
  mkCreds ::
  cr_uid  : word
  cr_euid : word
  cr_suid : word
  cr_gid  : word
  cr_egid : word
  cr_sgid : word
  cr_groups : List word

structure ProcState where
  mkProcState ::
  procst_halted : Option word       -- `some code` once exit/exit_group is seen, or
                                    -- `some sig` once `with_killed` ran; `m_killed` tells
  procst_tid : Option word
  procst_creds : Creds
  procst_setsid_succeeded : Bool
  procst_sigmask : word
  procst_children : Bool
  /-- The UTS name the process is told about, as the 390 bytes `uname`
  (160) copies out (`struct new_utsname`, include/uapi/linux/utsname.h,
  Linux v6.18.46, commit 1f99e9ab748f); `none` until a `uname` has
  observed it.  Pinned rather than chosen afresh, and process state
  rather than namespace state: the arguments are on the Rocq field,
  `State.procst_utsname`.  (Ticket A11.) -/
  procst_utsname : Option (List byte)
  /-- Whether a `sigaltstack` has left `sas_ss_size` NON-ZERO: an
  alternate stack is installed, not merely assigned.  `false` in
  `mkModel`, because `execve` clears the stack (`begin_new_exec` sets
  `me->sas_ss_sp = me->sas_ss_size = 0`, fs/exec.c, Linux v6.18.46,
  commit 1f99e9ab748f).  One bit, and why one is all that is usable —
  both readers of the record, `on_sig_stack` and `sas_ss_flags`
  (include/linux/sched/signal.h, same version), take the user stack
  pointer, which `SyscallInput` does not carry — and why a successful
  SS_DISABLE write leaves it `false` (`do_sigaltstack`, kernel/signal.c,
  Linux v6.18.46, zeroes `ss_size` and `ss_sp` first) are argued on the
  Rocq field, `State.procst_sigaltstack_installed`.  (Ticket A12.) -/
  procst_sigaltstack_installed : Bool
  /-- Whether the halt in `procst_halted` is a DEATH BY SIGNAL rather
  than an exit: the process was terminated by the signal that field
  carries, with the default disposition (`get_signal` reaches
  `do_group_exit(signr)`, kernel/signal.c, Linux v6.18.46, commit
  1f99e9ab748f), which a waiting parent reads back as `status & 0x7f`
  (`wait_task_zombie`, kernel/exit.c, same version).  A flag beside
  `procst_halted` rather than a second `Option word`, so that "a killed
  process is over" holds by construction — `m_killed` reads this
  through `procst_halted`, and `m_killed_of_m_halted_none` needs no
  side condition.  Only `with_killed` sets it; the argument is on the
  Rocq field, `State.procst_killed`.  (Ticket A12.) -/
  procst_killed : Bool
  /-- SIGABRT has been sent to this process and is BLOCKED, so it sits in
  `task->pending.signal` (`__send_signal_locked` adds it with
  `sigaddset(&pending->signal, sig)`, kernel/signal.c, Linux v6.18.46,
  commit 1f99e9ab748f) waiting for the mask to let it through.  A `Bool`
  and not a sigset because at most one signal can ever be in it, and why
  the state exists at all — musl's `abort` raises with SIGABRT blocked —
  are argued on the Rocq field, `State.procst_sigabrt_pending`.
  (Ticket A12.) -/
  procst_sigabrt_pending : Bool
  /-- THE ONE FIELD OF THIS RECORD THAT IS NOT KERNEL STATE: the task's
  declaration of whether the model covers the abort path, seeded by
  `init_model` from `ProcInput.in_abort_terminal` and written by nothing
  else.  `false` (what `Run.valid_input` pins) declines every `tkill`
  call once that arm is ported, the behaviour this tree has today.  Why
  it rides in the model rather than beside the run's configuration is on
  the Rocq field, `State.procst_abort_terminal`.  (Ticket A12.) -/
  procst_abort_terminal : Bool
  /-- The `struct stat` each statted file was first seen with, keyed by
  path: the 128 bytes a first `fstat` delivered, kept so a later stat of
  the same file cannot disagree about which file it is.  Chosen once and
  recorded rather than afresh, for `procst_utsname`'s reason; why it is
  process state and not part of `Fs`, and why a path is this model's
  inode, are argued on the Rocq field, `State.procst_statpins`.
  (Ticket A12.) -/
  procst_statpins : List (Fs.path × List byte)

structure LimState where
  mkLimState ::
  limst_core : Option (List byte)
  limst_nofile : word

structure TimeState where
  mkTimeState ::
  timest_clock : word

structure Model where
  mkModelOf ::
  m_fd   : FdState
  m_vm   : VmState
  m_io   : IoState
  m_fsys : FsState
  m_proc : ProcState
  m_lim  : LimState
  m_time : TimeState

/-- The accessors the rest of the development uses, unchanged in name and
type by the nesting. -/
def m_fds (m : Model) : List (word × FdEntry) := m.m_fd.fdst_table
def m_pipes (m : Model) : List (word × PipeBuf) := m.m_fd.fdst_pipes
def m_vmmaps (m : Model) : VmMaps := m.m_vm.vmst_maps
def m_vm_lazy (m : Model) : List (word × word) := m.m_vm.vmst_lazy
def m_vm_materialized (m : Model) : List word := m.m_vm.vmst_materialized
def m_stdin (m : Model) : InputStream := m.m_io.iost_stdin
def m_urandom (m : Model) : InputStream := m.m_io.iost_urandom
def m_net (m : Model) : NetQueue := m.m_io.iost_net
def m_conn_ix (m : Model) : word := m.m_io.iost_conn_ix
def m_fs (m : Model) : Fs.Fs := m.m_fsys.fsst_image
def m_halted (m : Model) : Option word := m.m_proc.procst_halted
def m_tid (m : Model) : Option word := m.m_proc.procst_tid
def m_setsid_succeeded (m : Model) : Bool := m.m_proc.procst_setsid_succeeded
def m_has_children (m : Model) : Bool := m.m_proc.procst_children
def m_sigmask (m : Model) : word := m.m_proc.procst_sigmask
def m_rlimit_core (m : Model) : Option (List byte) := m.m_lim.limst_core
def m_nofile (m : Model) : word := m.m_lim.limst_nofile
def m_clock (m : Model) : word := m.m_time.timest_clock
def m_creds (m : Model) : Creds := m.m_proc.procst_creds
def m_utsname (m : Model) : Option (List byte) := m.m_proc.procst_utsname
def m_sigaltstack_installed (m : Model) : Bool := m.m_proc.procst_sigaltstack_installed
/-- The signal that killed the process, or `none` if it exited or is still
running.  READ THROUGH `procst_halted` on purpose: the payload is the
halt's, and the flag only says how to read it.  That is what makes
`m_killed_of_m_halted_none` hold with no side condition. -/
def m_killed (m : Model) : Option word :=
  if m.m_proc.procst_killed then m.m_proc.procst_halted else none
def m_sigabrt_pending (m : Model) : Bool := m.m_proc.procst_sigabrt_pending
def m_abort_terminal (m : Model) : Bool := m.m_proc.procst_abort_terminal
def m_statpins (m : Model) : List (Fs.path × List byte) := m.m_proc.procst_statpins

/-- `DEFAULT_OVERFLOWUID` / `DEFAULT_OVERFLOWGID` (include/linux/highuid.h). -/
def overflow_id : word := Z_to_bv 64 65534

/-- `INR_OPEN_CUR` (include/uapi/linux/fs.h), the init task's soft NOFILE. -/
def default_nofile : word := Z_to_bv 64 1024

/-- `mkModel` keeps the flat constructor's argument order. -/
def mkModel (fds : List (word × FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : Option word)
    (tid : Option word) (rlim : Option (List byte)) : Model :=
  Model.mkModelOf (FdState.mkFdState fds []) (VmState.mkVmState vm [] [])
            (IoState.mkIoState stdin IEof net_silent (Z_to_bv 64 0)) (FsState.mkFsState fs)
            (ProcState.mkProcState halted tid
               (Creds.mkCreds overflow_id overflow_id overflow_id
                        overflow_id overflow_id overflow_id [])
               false (Z_to_bv 64 0) false none false false false false [])
            (LimState.mkLimState rlim default_nofile)
            (TimeState.mkTimeState (Z_to_bv 64 0))

/-! ## Field-update helpers.  Each rebuilds only its own subsystem. -/

def with_fds (fds : List (word × FdEntry)) (m : Model) : Model :=
  Model.mkModelOf (FdState.mkFdState fds (m_pipes m)) m.m_vm m.m_io m.m_fsys m.m_proc
    m.m_lim m.m_time
def with_pipes (ps : List (word × PipeBuf)) (m : Model) : Model :=
  Model.mkModelOf (FdState.mkFdState (m_fds m) ps) m.m_vm m.m_io m.m_fsys m.m_proc
    m.m_lim m.m_time
def with_vmmaps (h : VmMaps) (m : Model) : Model :=
  Model.mkModelOf m.m_fd
    (VmState.mkVmState h (m_vm_lazy m) (m_vm_materialized m))
    m.m_io m.m_fsys m.m_proc m.m_lim m.m_time
def with_vm_backing (lazy : List (word × word))
    (materialized : List word) (m : Model) : Model :=
  Model.mkModelOf m.m_fd (VmState.mkVmState (m_vmmaps m) lazy materialized)
    m.m_io m.m_fsys m.m_proc m.m_lim m.m_time
def with_stdin (s : InputStream) (m : Model) : Model :=
  Model.mkModelOf m.m_fd m.m_vm (IoState.mkIoState s (m_urandom m) (m_net m) (m_conn_ix m))
            m.m_fsys m.m_proc m.m_lim m.m_time
def with_urandom (s : InputStream) (m : Model) : Model :=
  Model.mkModelOf m.m_fd m.m_vm (IoState.mkIoState (m_stdin m) s (m_net m) (m_conn_ix m))
            m.m_fsys m.m_proc m.m_lim m.m_time
def with_net (q : NetQueue) (m : Model) : Model :=
  Model.mkModelOf m.m_fd m.m_vm (IoState.mkIoState (m_stdin m) (m_urandom m) q (m_conn_ix m))
            m.m_fsys m.m_proc m.m_lim m.m_time
/-- Install a new file-system image, DROPPING THE STAT PIN of every path
the new image does not hold.  The filter is the pin's correctness
condition, not bookkeeping: `unlinkat` (35) removes the NAME a pin was
taken under — `vfs_unlink` (fs/namei.c, Linux v6.18.46, commit
1f99e9ab748f) calls the file system's own unlink method, and it is that
method which drops the link count (`shmem_unlink`, mm/shmem.c, and
`simple_unlink`, fs/libfs.c, Linux v6.18.46) — so a file created at that
name afterwards is a new inode, and a pin that survived the unlink would
be held against it.  The inode itself lives on while a descriptor holds
it, and Linux answers an `fstat` through that descriptor from it with
`st_nlink` 0 (`generic_fillattr`, fs/stat.c, Linux v6.18.46); the model
declines that `fstat` instead (the arm of `Sys.Fs.Stat.fstat_file_spec`
for a path `Fs` no longer holds), so no pin is ever read against the
surviving inode.  Every other writer keeps the key, so the filter is
inert for them.  Why a create over an existing file keeps its pin is
`with_fs_keeps_a_pin_whose_file_survives` in `Checks/Cases/State.lean`,
and the unlink case is `with_fs_drops_the_pin_of_an_unlinked_file`
beside it.  Rocq: `State.statpins_restrict`. -/
def statpins_restrict (fs : Fs.Fs) (ps : List (Fs.path × List byte))
    : List (Fs.path × List byte) :=
  ps.filter (fun e => match Fs.fs_lookup fs e.1 with
                      | some _ => true
                      | none => false)

def with_fs (fs : Fs.Fs) (m : Model) : Model :=
  Model.mkModelOf m.m_fd m.m_vm m.m_io (FsState.mkFsState fs)
            (ProcState.mkProcState (m_halted m) (m_tid m) (m_creds m)
                         (m_setsid_succeeded m) (m_sigmask m)
                         (m_has_children m) (m_utsname m)
                         (m_sigaltstack_installed m)
                         m.m_proc.procst_killed (m_sigabrt_pending m)
                         (m_abort_terminal m)
                         (statpins_restrict fs (m_statpins m)))
            m.m_lim m.m_time
/-- Halt the process by an EXIT, the other half of what the kill flag
distinguishes: this CLEARS `procst_killed`, so a model this produced has
`m_killed` `none` whatever it had before, which is what keeps
`Run.sstep_exit` and `Run.sstep_killed` disjoint (Rocq:
`State.with_halted`). -/
def with_halted (code : word) (m : Model) : Model :=
  Model.mkModelOf m.m_fd m.m_vm m.m_io m.m_fsys
            (ProcState.mkProcState (some code) (m_tid m) (m_creds m)
                         (m_setsid_succeeded m) (m_sigmask m)
                         m.m_proc.procst_children (m_utsname m)
                         (m_sigaltstack_installed m)
                         false (m_sigabrt_pending m)
                         (m_abort_terminal m) (m_statpins m))
            m.m_lim m.m_time
def with_tid (tid : word) (m : Model) : Model :=
  Model.mkModelOf m.m_fd m.m_vm m.m_io m.m_fsys
            (ProcState.mkProcState (m_halted m) (some tid) (m_creds m)
                         (m_setsid_succeeded m) (m_sigmask m)
                         m.m_proc.procst_children (m_utsname m)
                         (m_sigaltstack_installed m)
                         m.m_proc.procst_killed (m_sigabrt_pending m)
                         (m_abort_terminal m) (m_statpins m))
            m.m_lim m.m_time
def with_rlimit_core (bs : List byte) (m : Model) : Model :=
  Model.mkModelOf m.m_fd m.m_vm m.m_io m.m_fsys m.m_proc
            (LimState.mkLimState (some bs) (m_nofile m)) m.m_time
def with_nofile (n : word) (m : Model) : Model :=
  Model.mkModelOf m.m_fd m.m_vm m.m_io m.m_fsys m.m_proc
            (LimState.mkLimState (m_rlimit_core m) n) m.m_time
def with_creds (c : Creds) (m : Model) : Model :=
  Model.mkModelOf m.m_fd m.m_vm m.m_io m.m_fsys
            (ProcState.mkProcState (m_halted m) (m_tid m) c
                         (m_setsid_succeeded m) (m_sigmask m)
                         m.m_proc.procst_children (m_utsname m)
                         (m_sigaltstack_installed m)
                         m.m_proc.procst_killed (m_sigabrt_pending m)
                         (m_abort_terminal m) (m_statpins m))
            m.m_lim m.m_time
def with_setsid_succeeded (m : Model) : Model :=
  Model.mkModelOf m.m_fd m.m_vm m.m_io m.m_fsys
            (ProcState.mkProcState (m_halted m) (m_tid m) (m_creds m)
                         true (m_sigmask m) m.m_proc.procst_children
                         (m_utsname m) (m_sigaltstack_installed m)
                         m.m_proc.procst_killed (m_sigabrt_pending m)
                         (m_abort_terminal m) (m_statpins m))
            m.m_lim m.m_time
def with_children (m : Model) : Model :=
  Model.mkModelOf m.m_fd m.m_vm m.m_io m.m_fsys
            (ProcState.mkProcState (m_halted m) (m_tid m) (m_creds m)
                         (m_setsid_succeeded m) (m_sigmask m) true
                         (m_utsname m) (m_sigaltstack_installed m)
                         m.m_proc.procst_killed (m_sigabrt_pending m)
                         (m_abort_terminal m) (m_statpins m))
            m.m_lim m.m_time
def with_sigmask (s : word) (m : Model) : Model :=
  Model.mkModelOf m.m_fd m.m_vm m.m_io m.m_fsys
            (ProcState.mkProcState (m_halted m) (m_tid m) (m_creds m)
                         (m_setsid_succeeded m) s (m_has_children m)
                         (m_utsname m) (m_sigaltstack_installed m)
                         m.m_proc.procst_killed (m_sigabrt_pending m)
                         (m_abort_terminal m) (m_statpins m))
            m.m_lim m.m_time

/-! ### Ticket A12: the setters of the signal and terminal state

In Rocq these sit among the setters above, each beside the accessor block
it serves; here they are one block, between `with_sigmask` and
`with_clock`, in Rocq's order among themselves.  Each docstring keeps the
kernel citation and points at the Rocq definition for the argument. -/

/-- Look a file's stat pin up by path; `none` means no `fstat` has
delivered a `struct stat` for that file yet, which is the branch that
creates one.  Linear over an association list, like `Fs.fs_lookup` and
`fd_lookup`.  Rocq: `State.statpin_lookup`. -/
def statpin_lookup (ps : List (Fs.path × List byte)) (p : Fs.path) : Option (List byte) :=
  match ps with
  | [] => none
  | (q, bs) :: rest => if Fs.path_eqb q p then some bs else statpin_lookup rest p

/-- Record the `struct stat` a file was first seen with.  Written once per
path and never overwritten — the one caller, `Fs.Stat.fstat_spec` once
ported, calls this only where `statpin_lookup` was `none` — and CONSED
rather than merged, because nothing observes this field's representation.
A second writer would have to argue why a pin may move, and no `chmod`,
`chown` or `link` arm exists to make that argument.  Rocq:
`State.with_statpin`. -/
def with_statpin (p : Fs.path) (bs : List byte) (m : Model) : Model :=
  Model.mkModelOf m.m_fd m.m_vm m.m_io m.m_fsys
            (ProcState.mkProcState (m_halted m) (m_tid m) (m_creds m)
                         (m_setsid_succeeded m) (m_sigmask m)
                         (m_has_children m) (m_utsname m)
                         (m_sigaltstack_installed m)
                         m.m_proc.procst_killed (m_sigabrt_pending m)
                         (m_abort_terminal m)
                         ((p, bs) :: m_statpins m))
            m.m_lim m.m_time

/-- Seed the task's abort-path declaration.  Its only caller is
`init_model`: the declaration is a parameter of the RUN, so the one place
that may install it is the one that turns a `ProcInput` into a model, and
nothing writes it after that — which is what lets `Run.valid_input` pin a
whole statement's stance by pinning one field of the input.  Rocq:
`State.with_abort_terminal`. -/
def with_abort_terminal (b : Bool) (m : Model) : Model :=
  Model.mkModelOf m.m_fd m.m_vm m.m_io m.m_fsys
            (ProcState.mkProcState (m_halted m) (m_tid m) (m_creds m)
                         (m_setsid_succeeded m) (m_sigmask m)
                         (m_has_children m) (m_utsname m)
                         (m_sigaltstack_installed m)
                         m.m_proc.procst_killed (m_sigabrt_pending m) b
                         (m_statpins m))
            m.m_lim m.m_time

/-- Record that a `sigaltstack` has installed an alternate stack: the
branch of `do_sigaltstack` (kernel/signal.c, Linux v6.18.46, commit
1f99e9ab748f) that stores a NON-ZERO `t->sas_ss_size` — never an errno
branch, never the no-change fast path, and never the SS_DISABLE branch,
which zeroes `ss_size` and `ss_sp` before the same store.  Monotone once
set, for a stronger reason than `with_children`: the one call that could
shrink the size back to zero is declined by this very bit.  Rocq:
`State.with_sigaltstack_installed`. -/
def with_sigaltstack_installed (m : Model) : Model :=
  Model.mkModelOf m.m_fd m.m_vm m.m_io m.m_fsys
            (ProcState.mkProcState (m_halted m) (m_tid m) (m_creds m)
                         (m_setsid_succeeded m) (m_sigmask m)
                         (m_has_children m) (m_utsname m) true
                         m.m_proc.procst_killed (m_sigabrt_pending m)
                         (m_abort_terminal m) (m_statpins m))
            m.m_lim m.m_time

/-- Record that SIGABRT has been sent and is BLOCKED, so it waits in
`task->pending.signal` instead of ending the process
(`__send_signal_locked` adds it to the pending set and `recalc_sigpending`
leaves a blocked signal there, kernel/signal.c, Linux v6.18.46, commit
1f99e9ab748f).  NOTHING CLEARS IT, and that is not an omission: the only
delivery this model has is the fatal one, so the step that would clear
the field is the step that ends the process.  Rocq:
`State.with_sigabrt_pending`. -/
def with_sigabrt_pending (m : Model) : Model :=
  Model.mkModelOf m.m_fd m.m_vm m.m_io m.m_fsys
            (ProcState.mkProcState (m_halted m) (m_tid m) (m_creds m)
                         (m_setsid_succeeded m) (m_sigmask m)
                         (m_has_children m) (m_utsname m)
                         (m_sigaltstack_installed m)
                         m.m_proc.procst_killed true (m_abort_terminal m)
                         (m_statpins m))
            m.m_lim m.m_time

/-- End the process by a fatal signal.  It writes the signal number into
`procst_halted`, because a killed process is over and every rule that asks
whether the process is still running asks that field; which of the two
terminal rules fires is then decided by `procst_killed` alone —
`Run.sstep_exit` declines a death by signal and `Run.sstep_killed` takes
it — so the two cannot both apply.  Its two callers in Rocq, the send
behind the task's declaration and the delivery inside `rt_sigprocmask`
that is NOT behind it, are argued on the Rocq definition,
`State.with_killed`; SIGABRT is the only argument either gives it. -/
def with_killed (sig : word) (m : Model) : Model :=
  Model.mkModelOf m.m_fd m.m_vm m.m_io m.m_fsys
            (ProcState.mkProcState (some sig) (m_tid m) (m_creds m)
                         (m_setsid_succeeded m) (m_sigmask m)
                         (m_has_children m) (m_utsname m)
                         (m_sigaltstack_installed m)
                         true (m_sigabrt_pending m)
                         (m_abort_terminal m) (m_statpins m))
            m.m_lim m.m_time

/-- The invariant the two fields are written under, stated where the
setter is: a killed process is a halted process, and the two payloads
agree.  Rocq: `State.killed_is_halted`. -/
theorem killed_is_halted (sig : word) (m : Model) :
    m_halted (with_killed sig m) = some sig ∧ m_killed (with_killed sig m) = some sig :=
  ⟨rfl, rfl⟩

/-- A PROCESS THAT IS STILL RUNNING HAS NOT BEEN KILLED, with no side
condition: what the flag representation buys, and what every one-step
inversion consumes to rule `Run.sstep_killed` out of a configuration
whose `m_halted` is `none`.  Rocq: `State.m_killed_of_m_halted_none`. -/
theorem m_killed_of_m_halted_none (m : Model) :
    m_halted m = none → m_killed m = none := by
  intro h
  unfold m_killed
  cases m.m_proc.procst_killed with
  | false => rfl
  | true => exact h
def with_clock (t : word) (m : Model) : Model :=
  Model.mkModelOf m.m_fd m.m_vm m.m_io m.m_fsys m.m_proc m.m_lim
            (TimeState.mkTimeState t)
def with_accepted (fds : List (word × FdEntry)) (m : Model) : Model :=
  Model.mkModelOf (FdState.mkFdState fds (m_pipes m)) m.m_vm
    (IoState.mkIoState (m_stdin m) (m_urandom m) (nq_rest (m_net m))
               (m_conn_ix m + Z_to_bv 64 1))
    m.m_fsys m.m_proc m.m_lim m.m_time

/-! ## Observable trace events -/

inductive event : Type
  | ReadEv  (ch : word) (b : byte)
  | WriteEv (ch : word) (b : byte)
  | ExitEv  (code : word) (fs : Fs.Fs)
  /-- The OTHER way a process ends: killed by `sig` with the default
  disposition, which a waiting parent reads as `status & 0x7f`
  (`wait_task_zombie`, kernel/exit.c, Linux v6.18.46, commit
  1f99e9ab748f).  A SEPARATE constructor because `exit(134)` and a death
  by SIGABRT are different events to everything that observes this
  process, and folding the second into the first would let a program
  fake its own abort; the only rule that emits one is `Run.sstep_killed`
  (Rocq: `State.KillEv`). -/
  | KillEv  (sig : word) (fs : Fs.Fs)

export event (ReadEv WriteEv ExitEv KillEv)

/-! ## The run's private /tmp, as keys of the flat file system -/

/-- `"/tmp/"` — the prefix under which the run's declared PRIVATE
temporary directory is carried in the flat map.  The model has no
directory structure, so "the file `out.gif` inside /tmp" is a key like
any other, spelled exactly as the program spells it; see the Rocq note
on `State.tmp_prefix`. -/
def tmp_prefix : Fs.path :=
  [Z_to_bv 8 47, Z_to_bv 8 116, Z_to_bv 8 109, Z_to_bv 8 112, Z_to_bv 8 47]

/-- The flat-map key of the /tmp entry named `name`. -/
def tmp_key (name : Fs.path) : Fs.path := tmp_prefix ++ name

/-- A name with a NUL byte in it is not a name: `read_cstr` stops at the
first NUL, so no pathname a program can pass names such an entry.  The
seeding drops it, which is also what keeps the seeded image inside
`Fs.valid_fs`. -/
def tmp_nul_free (name : Fs.path) : Bool :=
  !(name.any (fun b => bv_eqb b (Z_to_bv 8 0)))

/-- Seed a declared private /tmp into a file-system image, one entry at a
time through `Fs.fs_set`, so the result is in the canonical form for
EVERY list the declaration happens to be.  That is what lets `in_tmp`
carry no validity clause of its own. -/
def fs_seed_tmp (fs : Fs.Fs) (t : Fs.Fs) : Fs.Fs :=
  t.foldl
    (fun acc e =>
       if tmp_nul_free e.1 then Fs.fs_set acc (tmp_key e.1) e.2 else acc)
    fs

/-- The seeding prefix carries no NUL.  Rocq: `State.tmp_prefix_nul_free`. -/
theorem tmp_prefix_nul_free : (Z_to_bv 8 0) ∉ tmp_prefix := by decide

/-- Nor does a key the seeding mints from a NUL-free name.
Rocq: `State.tmp_key_nul_free`. -/
theorem tmp_key_nul_free (name : Fs.path) (hn : tmp_nul_free name = true) :
    (Z_to_bv 8 0) ∉ tmp_key name := by
  intro hin
  unfold tmp_key at hin
  rcases List.mem_append.1 hin with h | h
  · exact tmp_prefix_nul_free h
  · have hn' : name.any (fun b => bv_eqb b (Z_to_bv 8 0)) = false := by
      simpa [tmp_nul_free] using hn
    have hc : name.any (fun b => bv_eqb b (Z_to_bv 8 0)) = true :=
      List.any_eq_true.2 ⟨Z_to_bv 8 0, h, (bv_eqb_eq _ _).2 rfl⟩
    rw [hc] at hn'
    exact Bool.noConfusion hn'

/-- A fact that holds of every key of the image and of every key the
seeding can mint holds of every key of the seeded image.  The read-side
counterpart of `Fs.fs_set_keys`, lifted over the fold.
Rocq: `State.fs_seed_tmp_keys`. -/
theorem fs_seed_tmp_keys (P : Fs.path → Prop) (t fs : Fs.Fs)
    (hfs : ∀ pf ∈ fs, P pf.1) (hk : ∀ n, P (tmp_key n)) :
    ∀ pf ∈ fs_seed_tmp fs t, P pf.1 := by
  induction t generalizing fs with
  | nil => exact hfs
  | cons e t ih =>
    obtain ⟨name, data⟩ := e
    have hstep : fs_seed_tmp fs ((name, data) :: t)
        = fs_seed_tmp (if tmp_nul_free name then Fs.fs_set fs (tmp_key name) data else fs) t :=
      rfl
    rw [hstep]
    cases hn : tmp_nul_free name with
    | false =>
      simp only [hn, Bool.false_eq_true, ↓reduceIte]
      exact ih fs hfs
    | true =>
      simp only [hn, ↓reduceIte]
      exact ih _ (Fs.fs_set_keys P fs (tmp_key name) data hfs (hk name))

/-- The seeded image is still a valid image: the fold inserts through
`Fs.fs_set`, which keeps the canonical form, and it drops a name that
carries a NUL.  Rocq: `State.fs_seed_tmp_valid`. -/
theorem fs_seed_tmp_valid (t fs : Fs.Fs) (hv : Fs.valid_fs fs) :
    Fs.valid_fs (fs_seed_tmp fs t) := by
  induction t generalizing fs with
  | nil => exact hv
  | cons e t ih =>
    obtain ⟨name, data⟩ := e
    have hstep : fs_seed_tmp fs ((name, data) :: t)
        = fs_seed_tmp (if tmp_nul_free name then Fs.fs_set fs (tmp_key name) data else fs) t :=
      rfl
    rw [hstep]
    cases hn : tmp_nul_free name with
    | false =>
      simp only [hn, Bool.false_eq_true, ↓reduceIte]
      exact ih fs hv
    | true =>
      simp only [hn, ↓reduceIte]
      refine ih _ ⟨Fs.fs_set_sorted fs (tmp_key name) data hv.1, ?_⟩
      exact Fs.fs_set_keys (fun q => (Z_to_bv 8 0) ∉ q) fs (tmp_key name) data hv.2
        (tmp_key_nul_free name hn)

/-- Every key of a seeded image is either cwd-relative, because it came
from the image, or a key the seeding minted under "/tmp/".  This is the
seeding half of the argument that the device arms' image guards are
unreachable; the other half is `Run.absolute_divergent_not_seeded`.
Rocq: `State.seeded_absolute_key_is_tmp`. -/
theorem seeded_absolute_key_is_tmp (t fs : Fs.Fs) (hrel : Fs.fs_keys_relative fs) :
    ∀ pf ∈ fs_seed_tmp fs t, Fs.key_is_relative pf.1 ∨ ∃ n, pf.1 = tmp_key n :=
  fs_seed_tmp_keys (fun q => Fs.key_is_relative q ∨ ∃ n, q = tmp_key n) t fs
    (fun pf hpf => Or.inl (hrel pf hpf)) (fun n => Or.inr ⟨n, rfl⟩)

/-! ## Process input and the initial model -/

structure ProcInput where
  mkProcInput_full ::
  in_argv  : List (List byte)
  in_envp  : List (List byte)
  /-- The file-system image the run is launched over, WITHOUT the run's
  private /tmp.  Read it through `in_fs` below, which is what every
  consumer means by "the file system the run starts with". -/
  in_image_fs : Fs.Fs
  in_stdin : InputStream
  in_uid   : word     -- the real user id the process is launched with
  in_gid   : word     -- the real group id the process is launched with
  in_groups : List word
  in_net   : NetQueue
  in_nofile : word    -- the SOFT RLIMIT_NOFILE the process is launched with
  in_sigmask : word   -- the signals BLOCKED at the moment the process starts
  in_hwcap : word     -- shared hart capability input; see StackLayout.auxv_entries
  /-- THE TASK'S DECLARATION, the one field of this record that is not a
  fact about the environment: whether the model covers the abort path
  (`tkill` 130, `tgkill` 131 and the fatal SIGABRT they can leave
  pending) or declines it.  `Run.valid_input` pins it `false`;
  `init_model` copies it into `procst_abort_terminal`, where the arm
  reads it once ported.  The argument is on the Rocq field,
  `State.in_abort_terminal`. -/
  in_abort_terminal : Bool
  /-- The task's address-space declaration (`State.VaSize`); `Run.valid_input`
  pins `Sv48`, and `Run.valid_entry` reads it for the window. -/
  in_va_size : VaSize
  /-- The environment's declaration of the bytes the random device hands
  out, in order: an arbitrary but fixed stream, a parameter of the run
  like argv and envp, the same on both sides of an equivalence (see the
  Rocq field note; issue #696).  LAST but one, with `in_tmp`, so that the
  thirteen-place `mkProcInput` below keeps its old argument order. -/
  in_urandom : InputStream
  /-- The environment's declaration of the run's PRIVATE /tmp at launch,
  keyed by the ONE component of each name: an arbitrary but fixed table,
  a parameter of the run like argv and envp, the same directory on both
  sides of an equivalence (see the Rocq field note; issue #562, rung 4
  of #696). -/
  in_tmp   : Fs.Fs

/-- THE POSITIONAL-LITERAL FORM, written against the record as it stood
before the two ENVIRONMENT fields at the end of it existed (`in_urandom`,
issue #696; `in_tmp`, issue #562): the thirteen fields the record had
then, in that order, with the two that came after filled by THE DEFAULT
RANDOM STREAM and THE EMPTY /tmp — `default_urandom`, which is zero bytes
forever, and a private /tmp that starts empty.  A literal through this
name denotes exactly the input it always denoted, in an environment that
holds no file of its own.  The random field used to be `IEof` and could
not stay: since `Run.valid_urandom` every valid input declares an endless
stream, so a fixture built here with `IEof` would fail its own validity
pin.  The Rocq twin, `State.mkProcInput`, carries the argument for it; a
literal that wants to set either field uses `mkProcInput_full` or the
brace form. -/
def ProcInput.mkProcInput (argv envp : List (List byte)) (image_fs : Fs.Fs)
    (stdin : InputStream) (uid gid : word) (groups : List word)
    (net : NetQueue) (nofile sigmask hwcap : word) (abort_terminal : Bool)
    (va_size : VaSize) : ProcInput :=
  ProcInput.mkProcInput_full argv envp image_fs stdin uid gid groups net
    nofile sigmask hwcap abort_terminal va_size default_urandom []

/-- THE FILE SYSTEM THE RUN STARTS WITH: the image, with the run's declared
private /tmp seeded into it under absolute keys.  A function of two
projections rather than a projection, so that `m_fs (init_model …) =
inp.in_fs` still holds by `rfl`; an input whose `in_tmp` is empty gives
back the image itself. -/
def ProcInput.in_fs (inp : ProcInput) : Fs.Fs :=
  fs_seed_tmp inp.in_image_fs inp.in_tmp

/-- Initial model: fds 0/1/2 bound to the three standard channels; the six
credential ids built from the two the input carries (an ordinary execve
leaves real, effective and saved ids equal — security/commoncap.c
`cap_bprm_creds_from_file`, Linux v6.18.46, commit 1f99e9ab748f). -/
def init_model (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) : Model :=
  with_abort_terminal inp.in_abort_terminal
  (with_sigmask inp.in_sigmask
  (with_nofile inp.in_nofile
   (with_net inp.in_net
   (with_urandom inp.in_urandom
   (with_creds
    (Creds.mkCreds inp.in_uid inp.in_uid inp.in_uid
             inp.in_gid inp.in_gid inp.in_gid inp.in_groups)
    (mkModel
       [ (Z_to_bv 64 0, .FdChannel (Z_to_bv 64 0)),
         (Z_to_bv 64 1, .FdChannel (Z_to_bv 64 1)),
         (Z_to_bv 64 2, .FdChannel (Z_to_bv 64 2)) ]
       (VmMaps.mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp)
       inp.in_stdin
       inp.in_fs
       none
       none
       none))))))

/-- The setter/accessor facts `Checks.Examples` and `MustExit` rely on; the
Rocq `model` rewrite database is not ported. -/
theorem m_halted_with_halted (v : word) (m : Model) : m_halted (with_halted v m) = some v := rfl
theorem m_vmmaps_with_vmmaps (h : VmMaps) (m : Model) : m_vmmaps (with_vmmaps h m) = h := rfl
theorem with_vm_backing_with_vmmaps (l : List (word × word)) (mat : List word) (h : VmMaps)
    (m : Model) : with_vm_backing l mat (with_vmmaps h m) = with_vmmaps h (with_vm_backing l mat m) := rfl
theorem Z_to_bv_64_zero : Z_to_bv 64 0 = (0 : word) := by decide
theorem with_vm_backing_with_vm_backing (l l' : List (word × word)) (mat mat' : List word)
    (m : Model) : with_vm_backing l mat (with_vm_backing l' mat' m) = with_vm_backing l mat m := rfl
theorem m_vm_lazy_with_vm_backing (l : List (word × word)) (mat : List word) (m : Model) :
    m_vm_lazy (with_vm_backing l mat m) = l := rfl
theorem m_vm_materialized_with_vm_backing (l : List (word × word)) (mat : List word) (m : Model) :
    m_vm_materialized (with_vm_backing l mat m) = mat := rfl
theorem maps_subtract_nil (lo hi : Int) : maps_subtract [] lo hi = [] := rfl
theorem m_vmmaps_with_vm_backing (l : List (word × word)) (mat : List word) (m : Model) :
    m_vmmaps (with_vm_backing l mat m) = m_vmmaps m := rfl
theorem with_vmmaps_with_vm_backing (h : VmMaps) (l : List (word × word)) (mat : List word)
    (m : Model) : with_vmmaps h (with_vm_backing l mat m) = with_vm_backing l mat (with_vmmaps h m) := rfl
theorem m_vm_lazy_with_vmmaps (h : VmMaps) (m : Model) : m_vm_lazy (with_vmmaps h m) = m_vm_lazy m := rfl
theorem m_vm_materialized_with_vmmaps (h : VmMaps) (m : Model) :
    m_vm_materialized (with_vmmaps h m) = m_vm_materialized m := rfl
theorem with_vmmaps_with_vmmaps (h h' : VmMaps) (m : Model) :
    with_vmmaps h (with_vmmaps h' m) = with_vmmaps h m := rfl
theorem m_fs_with_halted (v : word) (m : Model) : m_fs (with_halted v m) = m_fs m := rfl
theorem m_halted_init_model (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    m_halted (init_model reserved brk0 mbase sp lim inp) = none := rfl
theorem m_vm_lazy_init_model (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    m_vm_lazy (init_model reserved brk0 mbase sp lim inp) = [] := rfl

/-! ### Ticket A11: the privilege test and the UTS pin

One delimited block, appended as BRIEF.md section 4 asks rather than
interleaved where Rocq keeps each — `creds_privileged` immediately
before the `ProcState` record, `with_utsname` with the other setters.
The `ProcState` field `procst_utsname` and the accessor `m_utsname`
are the exception: a field cannot live in an appended block, so they
sit in the record and in the accessor block above.  Each docstring
points at the Rocq definition for the argument in full. -/

/-- What "privileged" means here.  The kernel never asks whether a caller
is root: each credential setter asks `ns_capable_setid(old->user_ns,
CAP_SETUID)` (or CAP_SETGID), one bit of `cred->cap_effective`
(kernel/capability.c `ns_capable_setid`; security/commoncap.c
`cap_capable_helper`, Linux v6.18.46, commit 1f99e9ab748f).  The model
carries no capability sets and answers with the effective uid instead,
which is exact PROVIDED the init user namespace, no file or ambient
capabilities, default securebits and an unnarrowed bounding set: under
those, `cap_emulate_setxuid` (security/commoncap.c, Linux v6.18.46)
maintains
`CAP_SETUID ∈ cap_effective ↔ euid = 0` across every `set*uid`.  Each
excluded condition breaks that biconditional in a different direction;
the argument, and the tripwire probe that guards the assumption, are on
the Rocq definition, `State.creds_privileged`. -/
def creds_privileged (c : Creds) : Bool :=
  bv_eqb c.cr_euid (Z_to_bv 64 0)

/-- Record the UTS name the environment revealed.  Rocq's
`Kernel.Sys.uname_spec` (Sys/Kernel/Sys.v at f44244ad), the only caller
once ported, calls this only where `m_utsname` was `none`, so the pin is
written once and never overwritten: `uname` (160) is a pure read, and
the two syscalls that WRITE a utsname field — `sethostname` (161) and
`setdomainname` (162), kernel/sys.c, Linux v6.18.46, commit
1f99e9ab748f — have no arm in the table.  Adding either means giving
this a second writer in the same commit.  What the model does NOT
control: the record is per UTS namespace (`utsname()` is
`&current->nsproxy->uts_ns->name`, include/linux/utsname.h), so a
`sethostname` by another task in the SAME namespace, or its write to
/proc/sys/kernel/hostname (`proc_do_uts_string` writes through `get_uts`,
which reads `current->nsproxy->uts_ns`, kernel/utsname_sysctl.c:18-27,
v6.18.46), changes what the next `uname` reads, and a task in another
namespace cannot; the write-once claim assumes a quiescent namespace,
recorded in
`linux-process-semantics@ff0313ba4f:bugs/uname-pin-rests-on-uts-namespace-quiescence.md`.  Rocq:
`State.with_utsname`. -/
def with_utsname (bs : List byte) (m : Model) : Model :=
  Model.mkModelOf m.m_fd m.m_vm m.m_io m.m_fsys
    (ProcState.mkProcState (m_halted m) (m_tid m) (m_creds m)
      (m_setsid_succeeded m) (m_sigmask m) (m_has_children m) (some bs)
      (m_sigaltstack_installed m) m.m_proc.procst_killed (m_sigabrt_pending m)
      (m_abort_terminal m) (m_statpins m))
    m.m_lim m.m_time

/-! ### Twins of the Rocq `utsname` setter/accessor lemmas (State.v's
`model` rewrite database): every pair whose two endpoints exist in Lean.
The kernel pins are in `Checks/Cases/State`. -/

theorem m_utsname_with_urandom (v : InputStream) (m : Model) :
    m_utsname (with_urandom v m) = m_utsname m := rfl
theorem m_urandom_with_utsname (v : List byte) (m : Model) :
    m_urandom (with_utsname v m) = m_urandom m := rfl

theorem m_utsname_with_utsname (v : List byte) (m : Model) :
    m_utsname (with_utsname v m) = some v := rfl
theorem m_utsname_mkModel (fds : List (word × FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : Option word)
    (tid : Option word) (rlim : Option (List byte)) :
    m_utsname (mkModel fds vm stdin fs halted tid rlim) = none := rfl
theorem m_utsname_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_utsname (with_fds v m) = m_utsname m := rfl
theorem m_utsname_with_pipes (v : List (word × PipeBuf)) (m : Model) :
    m_utsname (with_pipes v m) = m_utsname m := rfl
theorem m_utsname_with_vmmaps (v : VmMaps) (m : Model) :
    m_utsname (with_vmmaps v m) = m_utsname m := rfl
theorem m_utsname_with_vm_backing (lz : List (word × word)) (mz : List word) (m : Model) :
    m_utsname (with_vm_backing lz mz m) = m_utsname m := rfl
theorem m_utsname_with_stdin (v : InputStream) (m : Model) :
    m_utsname (with_stdin v m) = m_utsname m := rfl
theorem m_utsname_with_net (v : NetQueue) (m : Model) :
    m_utsname (with_net v m) = m_utsname m := rfl
theorem m_utsname_with_accepted (v : List (word × FdEntry)) (m : Model) :
    m_utsname (with_accepted v m) = m_utsname m := rfl
theorem m_utsname_with_fs (v : Fs.Fs) (m : Model) :
    m_utsname (with_fs v m) = m_utsname m := rfl
theorem m_utsname_with_halted (v : word) (m : Model) :
    m_utsname (with_halted v m) = m_utsname m := rfl
theorem m_utsname_with_tid (v : word) (m : Model) :
    m_utsname (with_tid v m) = m_utsname m := rfl
theorem m_utsname_with_rlimit_core (v : List byte) (m : Model) :
    m_utsname (with_rlimit_core v m) = m_utsname m := rfl
theorem m_utsname_with_nofile (v : word) (m : Model) :
    m_utsname (with_nofile v m) = m_utsname m := rfl
theorem m_utsname_with_creds (v : Creds) (m : Model) :
    m_utsname (with_creds v m) = m_utsname m := rfl
theorem m_utsname_with_setsid_succeeded (m : Model) :
    m_utsname (with_setsid_succeeded m) = m_utsname m := rfl
theorem m_utsname_with_children (m : Model) :
    m_utsname (with_children m) = m_utsname m := rfl
theorem m_utsname_with_sigmask (v : word) (m : Model) :
    m_utsname (with_sigmask v m) = m_utsname m := rfl
theorem m_utsname_with_clock (v : word) (m : Model) :
    m_utsname (with_clock v m) = m_utsname m := rfl
theorem m_fds_with_utsname (v : List byte) (m : Model) :
    m_fds (with_utsname v m) = m_fds m := rfl
theorem m_pipes_with_utsname (v : List byte) (m : Model) :
    m_pipes (with_utsname v m) = m_pipes m := rfl
theorem m_vmmaps_with_utsname (v : List byte) (m : Model) :
    m_vmmaps (with_utsname v m) = m_vmmaps m := rfl
theorem m_vm_lazy_with_utsname (v : List byte) (m : Model) :
    m_vm_lazy (with_utsname v m) = m_vm_lazy m := rfl
theorem m_vm_materialized_with_utsname (v : List byte) (m : Model) :
    m_vm_materialized (with_utsname v m) = m_vm_materialized m := rfl
theorem m_stdin_with_utsname (v : List byte) (m : Model) :
    m_stdin (with_utsname v m) = m_stdin m := rfl
theorem m_net_with_utsname (v : List byte) (m : Model) :
    m_net (with_utsname v m) = m_net m := rfl
theorem m_conn_ix_with_utsname (v : List byte) (m : Model) :
    m_conn_ix (with_utsname v m) = m_conn_ix m := rfl
theorem m_fs_with_utsname (v : List byte) (m : Model) :
    m_fs (with_utsname v m) = m_fs m := rfl
theorem m_halted_with_utsname (v : List byte) (m : Model) :
    m_halted (with_utsname v m) = m_halted m := rfl
theorem m_tid_with_utsname (v : List byte) (m : Model) :
    m_tid (with_utsname v m) = m_tid m := rfl
theorem m_setsid_succeeded_with_utsname (v : List byte) (m : Model) :
    m_setsid_succeeded (with_utsname v m) = m_setsid_succeeded m := rfl
theorem m_has_children_with_utsname (v : List byte) (m : Model) :
    m_has_children (with_utsname v m) = m_has_children m := rfl
theorem m_sigmask_with_utsname (v : List byte) (m : Model) :
    m_sigmask (with_utsname v m) = m_sigmask m := rfl
theorem m_rlimit_core_with_utsname (v : List byte) (m : Model) :
    m_rlimit_core (with_utsname v m) = m_rlimit_core m := rfl
theorem m_nofile_with_utsname (v : List byte) (m : Model) :
    m_nofile (with_utsname v m) = m_nofile m := rfl
theorem m_clock_with_utsname (v : List byte) (m : Model) :
    m_clock (with_utsname v m) = m_clock m := rfl
theorem m_creds_with_utsname (v : List byte) (m : Model) :
    m_creds (with_utsname v m) = m_creds m := rfl

/-! ## Ticket A12: twins of the Rocq `model` lemmas for the signal and terminal state

Appended, like the A11 section, so that concurrent additions to this
file meet only at its end.  These are State.v's rewrite-database rows and
columns for the five fields A12 adds — each new accessor against every
setter, every accessor against the four new setters, the `init_model`
and `mkModel` facts, and the cross pairs the two Rocq changes that added
fields owe each other — one `rfl` each, exactly as Rocq closes them by
`reflexivity`.  Their second job is the one Rocq's block header names:
`procst_killed`, `procst_sigabrt_pending` and `procst_abort_terminal`
are the fields a run with the declaration OFF must never see move, and
these rows are what says no setter but their own moves them
(`Run.decl_off_frame` is where that is consumed).  The kernel pins are in
`Checks/Cases/State`. -/

theorem m_sigaltstack_installed_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_sigaltstack_installed (with_fds v m) = m_sigaltstack_installed m := rfl
theorem m_sigaltstack_installed_with_pipes (v : List (word × PipeBuf)) (m : Model) :
    m_sigaltstack_installed (with_pipes v m) = m_sigaltstack_installed m := rfl
theorem m_sigaltstack_installed_with_vmmaps (v : VmMaps) (m : Model) :
    m_sigaltstack_installed (with_vmmaps v m) = m_sigaltstack_installed m := rfl
theorem m_sigaltstack_installed_with_vm_backing (l : List (word × word)) (mt : List word) (m : Model) :
    m_sigaltstack_installed (with_vm_backing l mt m) = m_sigaltstack_installed m := rfl
theorem m_sigaltstack_installed_with_stdin (v : InputStream) (m : Model) :
    m_sigaltstack_installed (with_stdin v m) = m_sigaltstack_installed m := rfl
theorem m_sigaltstack_installed_with_net (v : NetQueue) (m : Model) :
    m_sigaltstack_installed (with_net v m) = m_sigaltstack_installed m := rfl
theorem m_sigaltstack_installed_with_fs (v : Fs.Fs) (m : Model) :
    m_sigaltstack_installed (with_fs v m) = m_sigaltstack_installed m := rfl
theorem m_sigaltstack_installed_with_halted (v : word) (m : Model) :
    m_sigaltstack_installed (with_halted v m) = m_sigaltstack_installed m := rfl
theorem m_sigaltstack_installed_with_tid (v : word) (m : Model) :
    m_sigaltstack_installed (with_tid v m) = m_sigaltstack_installed m := rfl
theorem m_sigaltstack_installed_with_rlimit_core (v : List byte) (m : Model) :
    m_sigaltstack_installed (with_rlimit_core v m) = m_sigaltstack_installed m := rfl
theorem m_sigaltstack_installed_with_nofile (v : word) (m : Model) :
    m_sigaltstack_installed (with_nofile v m) = m_sigaltstack_installed m := rfl
theorem m_sigaltstack_installed_with_creds (v : Creds) (m : Model) :
    m_sigaltstack_installed (with_creds v m) = m_sigaltstack_installed m := rfl
theorem m_sigaltstack_installed_with_setsid_succeeded (m : Model) :
    m_sigaltstack_installed (with_setsid_succeeded m) = m_sigaltstack_installed m := rfl
theorem m_sigaltstack_installed_with_children (m : Model) :
    m_sigaltstack_installed (with_children m) = m_sigaltstack_installed m := rfl
theorem m_sigaltstack_installed_with_sigmask (v : word) (m : Model) :
    m_sigaltstack_installed (with_sigmask v m) = m_sigaltstack_installed m := rfl
theorem m_sigaltstack_installed_with_clock (v : word) (m : Model) :
    m_sigaltstack_installed (with_clock v m) = m_sigaltstack_installed m := rfl
theorem m_sigaltstack_installed_with_accepted (v : List (word × FdEntry)) (m : Model) :
    m_sigaltstack_installed (with_accepted v m) = m_sigaltstack_installed m := rfl
theorem m_sigaltstack_installed_with_utsname (v : List byte) (m : Model) :
    m_sigaltstack_installed (with_utsname v m) = m_sigaltstack_installed m := rfl
theorem m_sigaltstack_installed_with_sigaltstack_installed (m : Model) :
    m_sigaltstack_installed (with_sigaltstack_installed m) = true := rfl
theorem m_fds_with_sigaltstack_installed (m : Model) :
    m_fds (with_sigaltstack_installed m) = m_fds m := rfl
theorem m_pipes_with_sigaltstack_installed (m : Model) :
    m_pipes (with_sigaltstack_installed m) = m_pipes m := rfl
theorem m_vmmaps_with_sigaltstack_installed (m : Model) :
    m_vmmaps (with_sigaltstack_installed m) = m_vmmaps m := rfl
theorem m_vm_lazy_with_sigaltstack_installed (m : Model) :
    m_vm_lazy (with_sigaltstack_installed m) = m_vm_lazy m := rfl
theorem m_vm_materialized_with_sigaltstack_installed (m : Model) :
    m_vm_materialized (with_sigaltstack_installed m) = m_vm_materialized m := rfl
theorem m_stdin_with_sigaltstack_installed (m : Model) :
    m_stdin (with_sigaltstack_installed m) = m_stdin m := rfl
theorem m_net_with_sigaltstack_installed (m : Model) :
    m_net (with_sigaltstack_installed m) = m_net m := rfl
theorem m_conn_ix_with_sigaltstack_installed (m : Model) :
    m_conn_ix (with_sigaltstack_installed m) = m_conn_ix m := rfl
theorem m_fs_with_sigaltstack_installed (m : Model) :
    m_fs (with_sigaltstack_installed m) = m_fs m := rfl
theorem m_halted_with_sigaltstack_installed (m : Model) :
    m_halted (with_sigaltstack_installed m) = m_halted m := rfl
theorem m_tid_with_sigaltstack_installed (m : Model) :
    m_tid (with_sigaltstack_installed m) = m_tid m := rfl
theorem m_setsid_succeeded_with_sigaltstack_installed (m : Model) :
    m_setsid_succeeded (with_sigaltstack_installed m) = m_setsid_succeeded m := rfl
theorem m_has_children_with_sigaltstack_installed (m : Model) :
    m_has_children (with_sigaltstack_installed m) = m_has_children m := rfl
theorem m_sigmask_with_sigaltstack_installed (m : Model) :
    m_sigmask (with_sigaltstack_installed m) = m_sigmask m := rfl
theorem m_rlimit_core_with_sigaltstack_installed (m : Model) :
    m_rlimit_core (with_sigaltstack_installed m) = m_rlimit_core m := rfl
theorem m_nofile_with_sigaltstack_installed (m : Model) :
    m_nofile (with_sigaltstack_installed m) = m_nofile m := rfl
theorem m_clock_with_sigaltstack_installed (m : Model) :
    m_clock (with_sigaltstack_installed m) = m_clock m := rfl
theorem m_creds_with_sigaltstack_installed (m : Model) :
    m_creds (with_sigaltstack_installed m) = m_creds m := rfl
theorem m_utsname_with_sigaltstack_installed (m : Model) :
    m_utsname (with_sigaltstack_installed m) = m_utsname m := rfl
theorem m_statpins_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_statpins (with_fds v m) = m_statpins m := rfl
theorem m_statpins_with_pipes (v : List (word × PipeBuf)) (m : Model) :
    m_statpins (with_pipes v m) = m_statpins m := rfl
theorem m_statpins_with_vmmaps (v : VmMaps) (m : Model) :
    m_statpins (with_vmmaps v m) = m_statpins m := rfl
theorem m_statpins_with_vm_backing (lz : List (word × word)) (mz : List word) (m : Model) :
    m_statpins (with_vm_backing lz mz m) = m_statpins m := rfl
theorem m_statpins_with_stdin (v : InputStream) (m : Model) :
    m_statpins (with_stdin v m) = m_statpins m := rfl
theorem m_statpins_with_net (v : NetQueue) (m : Model) :
    m_statpins (with_net v m) = m_statpins m := rfl
theorem m_statpins_with_accepted (v : List (word × FdEntry)) (m : Model) :
    m_statpins (with_accepted v m) = m_statpins m := rfl
theorem m_statpins_with_fs (v : Fs.Fs) (m : Model) :
    m_statpins (with_fs v m) = statpins_restrict v (m_statpins m) := rfl
theorem m_statpins_with_halted (v : word) (m : Model) :
    m_statpins (with_halted v m) = m_statpins m := rfl
theorem m_statpins_with_tid (v : word) (m : Model) :
    m_statpins (with_tid v m) = m_statpins m := rfl
theorem m_statpins_with_rlimit_core (v : List byte) (m : Model) :
    m_statpins (with_rlimit_core v m) = m_statpins m := rfl
theorem m_statpins_with_nofile (v : word) (m : Model) :
    m_statpins (with_nofile v m) = m_statpins m := rfl
theorem m_statpins_with_creds (v : Creds) (m : Model) :
    m_statpins (with_creds v m) = m_statpins m := rfl
theorem m_statpins_with_setsid_succeeded (m : Model) :
    m_statpins (with_setsid_succeeded m) = m_statpins m := rfl
theorem m_statpins_with_children (m : Model) :
    m_statpins (with_children m) = m_statpins m := rfl
theorem m_statpins_with_sigmask (v : word) (m : Model) :
    m_statpins (with_sigmask v m) = m_statpins m := rfl
theorem m_statpins_with_clock (v : word) (m : Model) :
    m_statpins (with_clock v m) = m_statpins m := rfl
theorem m_statpins_with_utsname (v : List byte) (m : Model) :
    m_statpins (with_utsname v m) = m_statpins m := rfl
theorem m_fds_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_fds (with_statpin p bs m) = m_fds m := rfl
theorem m_pipes_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_pipes (with_statpin p bs m) = m_pipes m := rfl
theorem m_vmmaps_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_vmmaps (with_statpin p bs m) = m_vmmaps m := rfl
theorem m_vm_lazy_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_vm_lazy (with_statpin p bs m) = m_vm_lazy m := rfl
theorem m_vm_materialized_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_vm_materialized (with_statpin p bs m) = m_vm_materialized m := rfl
theorem m_stdin_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_stdin (with_statpin p bs m) = m_stdin m := rfl
theorem m_net_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_net (with_statpin p bs m) = m_net m := rfl
theorem m_conn_ix_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_conn_ix (with_statpin p bs m) = m_conn_ix m := rfl
theorem m_fs_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_fs (with_statpin p bs m) = m_fs m := rfl
theorem m_halted_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_halted (with_statpin p bs m) = m_halted m := rfl
theorem m_tid_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_tid (with_statpin p bs m) = m_tid m := rfl
theorem m_setsid_succeeded_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_setsid_succeeded (with_statpin p bs m) = m_setsid_succeeded m := rfl
theorem m_has_children_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_has_children (with_statpin p bs m) = m_has_children m := rfl
theorem m_sigmask_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_sigmask (with_statpin p bs m) = m_sigmask m := rfl
theorem m_utsname_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_utsname (with_statpin p bs m) = m_utsname m := rfl
theorem m_rlimit_core_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_rlimit_core (with_statpin p bs m) = m_rlimit_core m := rfl
theorem m_nofile_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_nofile (with_statpin p bs m) = m_nofile m := rfl
theorem m_clock_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_clock (with_statpin p bs m) = m_clock m := rfl
theorem m_creds_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_creds (with_statpin p bs m) = m_creds m := rfl
theorem m_statpins_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_statpins (with_statpin p bs m) = (p, bs) :: m_statpins m := rfl
theorem m_statpins_mkModel (fds : List (word × FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : Option word)
    (tid : Option word) (rlim : Option (List byte)) :
    m_statpins (mkModel fds vm stdin fs halted tid rlim) = [] := rfl
theorem m_fds_with_abort_terminal (v : Bool) (m : Model) :
    m_fds (with_abort_terminal v m) = m_fds m := rfl
theorem m_fds_with_sigabrt_pending (m : Model) :
    m_fds (with_sigabrt_pending m) = m_fds m := rfl
theorem m_fds_with_killed (v : word) (m : Model) :
    m_fds (with_killed v m) = m_fds m := rfl
theorem m_pipes_with_abort_terminal (v : Bool) (m : Model) :
    m_pipes (with_abort_terminal v m) = m_pipes m := rfl
theorem m_pipes_with_sigabrt_pending (m : Model) :
    m_pipes (with_sigabrt_pending m) = m_pipes m := rfl
theorem m_pipes_with_killed (v : word) (m : Model) :
    m_pipes (with_killed v m) = m_pipes m := rfl
theorem m_vmmaps_with_abort_terminal (v : Bool) (m : Model) :
    m_vmmaps (with_abort_terminal v m) = m_vmmaps m := rfl
theorem m_vmmaps_with_sigabrt_pending (m : Model) :
    m_vmmaps (with_sigabrt_pending m) = m_vmmaps m := rfl
theorem m_vmmaps_with_killed (v : word) (m : Model) :
    m_vmmaps (with_killed v m) = m_vmmaps m := rfl
theorem m_vm_lazy_with_abort_terminal (v : Bool) (m : Model) :
    m_vm_lazy (with_abort_terminal v m) = m_vm_lazy m := rfl
theorem m_vm_lazy_with_sigabrt_pending (m : Model) :
    m_vm_lazy (with_sigabrt_pending m) = m_vm_lazy m := rfl
theorem m_vm_lazy_with_killed (v : word) (m : Model) :
    m_vm_lazy (with_killed v m) = m_vm_lazy m := rfl
theorem m_vm_materialized_with_abort_terminal (v : Bool) (m : Model) :
    m_vm_materialized (with_abort_terminal v m) = m_vm_materialized m := rfl
theorem m_vm_materialized_with_sigabrt_pending (m : Model) :
    m_vm_materialized (with_sigabrt_pending m) = m_vm_materialized m := rfl
theorem m_vm_materialized_with_killed (v : word) (m : Model) :
    m_vm_materialized (with_killed v m) = m_vm_materialized m := rfl
theorem m_stdin_with_abort_terminal (v : Bool) (m : Model) :
    m_stdin (with_abort_terminal v m) = m_stdin m := rfl
theorem m_stdin_with_sigabrt_pending (m : Model) :
    m_stdin (with_sigabrt_pending m) = m_stdin m := rfl
theorem m_stdin_with_killed (v : word) (m : Model) :
    m_stdin (with_killed v m) = m_stdin m := rfl
theorem m_net_with_abort_terminal (v : Bool) (m : Model) :
    m_net (with_abort_terminal v m) = m_net m := rfl
theorem m_net_with_sigabrt_pending (m : Model) :
    m_net (with_sigabrt_pending m) = m_net m := rfl
theorem m_net_with_killed (v : word) (m : Model) :
    m_net (with_killed v m) = m_net m := rfl
theorem m_conn_ix_with_abort_terminal (v : Bool) (m : Model) :
    m_conn_ix (with_abort_terminal v m) = m_conn_ix m := rfl
theorem m_conn_ix_with_sigabrt_pending (m : Model) :
    m_conn_ix (with_sigabrt_pending m) = m_conn_ix m := rfl
theorem m_conn_ix_with_killed (v : word) (m : Model) :
    m_conn_ix (with_killed v m) = m_conn_ix m := rfl
theorem m_fs_with_abort_terminal (v : Bool) (m : Model) :
    m_fs (with_abort_terminal v m) = m_fs m := rfl
theorem m_fs_with_sigabrt_pending (m : Model) :
    m_fs (with_sigabrt_pending m) = m_fs m := rfl
theorem m_fs_with_killed (v : word) (m : Model) :
    m_fs (with_killed v m) = m_fs m := rfl
theorem m_halted_with_abort_terminal (v : Bool) (m : Model) :
    m_halted (with_abort_terminal v m) = m_halted m := rfl
theorem m_halted_with_sigabrt_pending (m : Model) :
    m_halted (with_sigabrt_pending m) = m_halted m := rfl
theorem m_halted_with_killed (v : word) (m : Model) :
    m_halted (with_killed v m) = some v := rfl
theorem m_tid_with_abort_terminal (v : Bool) (m : Model) :
    m_tid (with_abort_terminal v m) = m_tid m := rfl
theorem m_tid_with_sigabrt_pending (m : Model) :
    m_tid (with_sigabrt_pending m) = m_tid m := rfl
theorem m_tid_with_killed (v : word) (m : Model) :
    m_tid (with_killed v m) = m_tid m := rfl
theorem m_setsid_succeeded_with_abort_terminal (v : Bool) (m : Model) :
    m_setsid_succeeded (with_abort_terminal v m) = m_setsid_succeeded m := rfl
theorem m_setsid_succeeded_with_sigabrt_pending (m : Model) :
    m_setsid_succeeded (with_sigabrt_pending m) = m_setsid_succeeded m := rfl
theorem m_setsid_succeeded_with_killed (v : word) (m : Model) :
    m_setsid_succeeded (with_killed v m) = m_setsid_succeeded m := rfl
theorem m_has_children_with_abort_terminal (v : Bool) (m : Model) :
    m_has_children (with_abort_terminal v m) = m_has_children m := rfl
theorem m_has_children_with_sigabrt_pending (m : Model) :
    m_has_children (with_sigabrt_pending m) = m_has_children m := rfl
theorem m_has_children_with_killed (v : word) (m : Model) :
    m_has_children (with_killed v m) = m_has_children m := rfl
theorem m_sigmask_with_abort_terminal (v : Bool) (m : Model) :
    m_sigmask (with_abort_terminal v m) = m_sigmask m := rfl
theorem m_sigmask_with_sigabrt_pending (m : Model) :
    m_sigmask (with_sigabrt_pending m) = m_sigmask m := rfl
theorem m_sigmask_with_killed (v : word) (m : Model) :
    m_sigmask (with_killed v m) = m_sigmask m := rfl
theorem m_utsname_with_abort_terminal (v : Bool) (m : Model) :
    m_utsname (with_abort_terminal v m) = m_utsname m := rfl
theorem m_utsname_with_sigabrt_pending (m : Model) :
    m_utsname (with_sigabrt_pending m) = m_utsname m := rfl
theorem m_utsname_with_killed (v : word) (m : Model) :
    m_utsname (with_killed v m) = m_utsname m := rfl
theorem m_rlimit_core_with_abort_terminal (v : Bool) (m : Model) :
    m_rlimit_core (with_abort_terminal v m) = m_rlimit_core m := rfl
theorem m_rlimit_core_with_sigabrt_pending (m : Model) :
    m_rlimit_core (with_sigabrt_pending m) = m_rlimit_core m := rfl
theorem m_rlimit_core_with_killed (v : word) (m : Model) :
    m_rlimit_core (with_killed v m) = m_rlimit_core m := rfl
theorem m_nofile_with_abort_terminal (v : Bool) (m : Model) :
    m_nofile (with_abort_terminal v m) = m_nofile m := rfl
theorem m_nofile_with_sigabrt_pending (m : Model) :
    m_nofile (with_sigabrt_pending m) = m_nofile m := rfl
theorem m_nofile_with_killed (v : word) (m : Model) :
    m_nofile (with_killed v m) = m_nofile m := rfl
theorem m_clock_with_abort_terminal (v : Bool) (m : Model) :
    m_clock (with_abort_terminal v m) = m_clock m := rfl
theorem m_clock_with_sigabrt_pending (m : Model) :
    m_clock (with_sigabrt_pending m) = m_clock m := rfl
theorem m_clock_with_killed (v : word) (m : Model) :
    m_clock (with_killed v m) = m_clock m := rfl
theorem m_creds_with_abort_terminal (v : Bool) (m : Model) :
    m_creds (with_abort_terminal v m) = m_creds m := rfl
theorem m_creds_with_sigabrt_pending (m : Model) :
    m_creds (with_sigabrt_pending m) = m_creds m := rfl
theorem m_creds_with_killed (v : word) (m : Model) :
    m_creds (with_killed v m) = m_creds m := rfl
theorem m_killed_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_killed (with_fds v m) = m_killed m := rfl
theorem m_killed_with_pipes (v : List (word × PipeBuf)) (m : Model) :
    m_killed (with_pipes v m) = m_killed m := rfl
theorem m_killed_with_vmmaps (v : VmMaps) (m : Model) :
    m_killed (with_vmmaps v m) = m_killed m := rfl
theorem m_killed_with_vm_backing (lz : List (word × word)) (mt : List word) (m : Model) :
    m_killed (with_vm_backing lz mt m) = m_killed m := rfl
theorem m_killed_with_stdin (v : InputStream) (m : Model) :
    m_killed (with_stdin v m) = m_killed m := rfl
theorem m_killed_with_net (v : NetQueue) (m : Model) :
    m_killed (with_net v m) = m_killed m := rfl
theorem m_killed_with_fs (v : Fs.Fs) (m : Model) :
    m_killed (with_fs v m) = m_killed m := rfl
theorem m_killed_with_halted (v : word) (m : Model) :
    m_killed (with_halted v m) = none := rfl
theorem m_killed_with_tid (v : word) (m : Model) :
    m_killed (with_tid v m) = m_killed m := rfl
theorem m_killed_with_rlimit_core (v : List byte) (m : Model) :
    m_killed (with_rlimit_core v m) = m_killed m := rfl
theorem m_killed_with_utsname (v : List byte) (m : Model) :
    m_killed (with_utsname v m) = m_killed m := rfl
theorem m_killed_with_nofile (v : word) (m : Model) :
    m_killed (with_nofile v m) = m_killed m := rfl
theorem m_killed_with_creds (v : Creds) (m : Model) :
    m_killed (with_creds v m) = m_killed m := rfl
theorem m_killed_with_setsid_succeeded (m : Model) :
    m_killed (with_setsid_succeeded m) = m_killed m := rfl
theorem m_killed_with_children (m : Model) :
    m_killed (with_children m) = m_killed m := rfl
theorem m_killed_with_sigmask (v : word) (m : Model) :
    m_killed (with_sigmask v m) = m_killed m := rfl
theorem m_killed_with_clock (v : word) (m : Model) :
    m_killed (with_clock v m) = m_killed m := rfl
theorem m_killed_with_accepted (v : List (word × FdEntry)) (m : Model) :
    m_killed (with_accepted v m) = m_killed m := rfl
theorem m_killed_with_abort_terminal (v : Bool) (m : Model) :
    m_killed (with_abort_terminal v m) = m_killed m := rfl
theorem m_killed_with_sigabrt_pending (m : Model) :
    m_killed (with_sigabrt_pending m) = m_killed m := rfl
theorem m_killed_with_killed (v : word) (m : Model) :
    m_killed (with_killed v m) = some v := rfl
theorem m_sigabrt_pending_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_sigabrt_pending (with_fds v m) = m_sigabrt_pending m := rfl
theorem m_sigabrt_pending_with_pipes (v : List (word × PipeBuf)) (m : Model) :
    m_sigabrt_pending (with_pipes v m) = m_sigabrt_pending m := rfl
theorem m_sigabrt_pending_with_vmmaps (v : VmMaps) (m : Model) :
    m_sigabrt_pending (with_vmmaps v m) = m_sigabrt_pending m := rfl
theorem m_sigabrt_pending_with_vm_backing (lz : List (word × word)) (mt : List word) (m : Model) :
    m_sigabrt_pending (with_vm_backing lz mt m) = m_sigabrt_pending m := rfl
theorem m_sigabrt_pending_with_stdin (v : InputStream) (m : Model) :
    m_sigabrt_pending (with_stdin v m) = m_sigabrt_pending m := rfl
theorem m_sigabrt_pending_with_net (v : NetQueue) (m : Model) :
    m_sigabrt_pending (with_net v m) = m_sigabrt_pending m := rfl
theorem m_sigabrt_pending_with_fs (v : Fs.Fs) (m : Model) :
    m_sigabrt_pending (with_fs v m) = m_sigabrt_pending m := rfl
theorem m_sigabrt_pending_with_halted (v : word) (m : Model) :
    m_sigabrt_pending (with_halted v m) = m_sigabrt_pending m := rfl
theorem m_sigabrt_pending_with_tid (v : word) (m : Model) :
    m_sigabrt_pending (with_tid v m) = m_sigabrt_pending m := rfl
theorem m_sigabrt_pending_with_rlimit_core (v : List byte) (m : Model) :
    m_sigabrt_pending (with_rlimit_core v m) = m_sigabrt_pending m := rfl
theorem m_sigabrt_pending_with_utsname (v : List byte) (m : Model) :
    m_sigabrt_pending (with_utsname v m) = m_sigabrt_pending m := rfl
theorem m_sigabrt_pending_with_nofile (v : word) (m : Model) :
    m_sigabrt_pending (with_nofile v m) = m_sigabrt_pending m := rfl
theorem m_sigabrt_pending_with_creds (v : Creds) (m : Model) :
    m_sigabrt_pending (with_creds v m) = m_sigabrt_pending m := rfl
theorem m_sigabrt_pending_with_setsid_succeeded (m : Model) :
    m_sigabrt_pending (with_setsid_succeeded m) = m_sigabrt_pending m := rfl
theorem m_sigabrt_pending_with_children (m : Model) :
    m_sigabrt_pending (with_children m) = m_sigabrt_pending m := rfl
theorem m_sigabrt_pending_with_sigmask (v : word) (m : Model) :
    m_sigabrt_pending (with_sigmask v m) = m_sigabrt_pending m := rfl
theorem m_sigabrt_pending_with_clock (v : word) (m : Model) :
    m_sigabrt_pending (with_clock v m) = m_sigabrt_pending m := rfl
theorem m_sigabrt_pending_with_accepted (v : List (word × FdEntry)) (m : Model) :
    m_sigabrt_pending (with_accepted v m) = m_sigabrt_pending m := rfl
theorem m_sigabrt_pending_with_abort_terminal (v : Bool) (m : Model) :
    m_sigabrt_pending (with_abort_terminal v m) = m_sigabrt_pending m := rfl
theorem m_sigabrt_pending_with_sigabrt_pending (m : Model) :
    m_sigabrt_pending (with_sigabrt_pending m) = true := rfl
theorem m_sigabrt_pending_with_killed (v : word) (m : Model) :
    m_sigabrt_pending (with_killed v m) = m_sigabrt_pending m := rfl
theorem m_abort_terminal_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_abort_terminal (with_fds v m) = m_abort_terminal m := rfl
theorem m_abort_terminal_with_pipes (v : List (word × PipeBuf)) (m : Model) :
    m_abort_terminal (with_pipes v m) = m_abort_terminal m := rfl
theorem m_abort_terminal_with_vmmaps (v : VmMaps) (m : Model) :
    m_abort_terminal (with_vmmaps v m) = m_abort_terminal m := rfl
theorem m_abort_terminal_with_vm_backing (lz : List (word × word)) (mt : List word) (m : Model) :
    m_abort_terminal (with_vm_backing lz mt m) = m_abort_terminal m := rfl
theorem m_abort_terminal_with_stdin (v : InputStream) (m : Model) :
    m_abort_terminal (with_stdin v m) = m_abort_terminal m := rfl
theorem m_abort_terminal_with_net (v : NetQueue) (m : Model) :
    m_abort_terminal (with_net v m) = m_abort_terminal m := rfl
theorem m_abort_terminal_with_fs (v : Fs.Fs) (m : Model) :
    m_abort_terminal (with_fs v m) = m_abort_terminal m := rfl
theorem m_abort_terminal_with_halted (v : word) (m : Model) :
    m_abort_terminal (with_halted v m) = m_abort_terminal m := rfl
theorem m_abort_terminal_with_tid (v : word) (m : Model) :
    m_abort_terminal (with_tid v m) = m_abort_terminal m := rfl
theorem m_abort_terminal_with_rlimit_core (v : List byte) (m : Model) :
    m_abort_terminal (with_rlimit_core v m) = m_abort_terminal m := rfl
theorem m_abort_terminal_with_utsname (v : List byte) (m : Model) :
    m_abort_terminal (with_utsname v m) = m_abort_terminal m := rfl
theorem m_abort_terminal_with_nofile (v : word) (m : Model) :
    m_abort_terminal (with_nofile v m) = m_abort_terminal m := rfl
theorem m_abort_terminal_with_creds (v : Creds) (m : Model) :
    m_abort_terminal (with_creds v m) = m_abort_terminal m := rfl
theorem m_abort_terminal_with_setsid_succeeded (m : Model) :
    m_abort_terminal (with_setsid_succeeded m) = m_abort_terminal m := rfl
theorem m_abort_terminal_with_children (m : Model) :
    m_abort_terminal (with_children m) = m_abort_terminal m := rfl
theorem m_abort_terminal_with_sigmask (v : word) (m : Model) :
    m_abort_terminal (with_sigmask v m) = m_abort_terminal m := rfl
theorem m_abort_terminal_with_clock (v : word) (m : Model) :
    m_abort_terminal (with_clock v m) = m_abort_terminal m := rfl
theorem m_abort_terminal_with_accepted (v : List (word × FdEntry)) (m : Model) :
    m_abort_terminal (with_accepted v m) = m_abort_terminal m := rfl
theorem m_abort_terminal_with_abort_terminal (v : Bool) (m : Model) :
    m_abort_terminal (with_abort_terminal v m) = v := rfl
theorem m_abort_terminal_with_sigabrt_pending (m : Model) :
    m_abort_terminal (with_sigabrt_pending m) = m_abort_terminal m := rfl
theorem m_abort_terminal_with_killed (v : word) (m : Model) :
    m_abort_terminal (with_killed v m) = m_abort_terminal m := rfl
theorem m_killed_with_sigaltstack_installed (m : Model) :
    m_killed (with_sigaltstack_installed m) = m_killed m := rfl
theorem m_sigabrt_pending_with_sigaltstack_installed (m : Model) :
    m_sigabrt_pending (with_sigaltstack_installed m) = m_sigabrt_pending m := rfl
theorem m_abort_terminal_with_sigaltstack_installed (m : Model) :
    m_abort_terminal (with_sigaltstack_installed m) = m_abort_terminal m := rfl
theorem m_sigaltstack_installed_with_killed (v : word) (m : Model) :
    m_sigaltstack_installed (with_killed v m) = m_sigaltstack_installed m := rfl
theorem m_sigaltstack_installed_with_sigabrt_pending (m : Model) :
    m_sigaltstack_installed (with_sigabrt_pending m) = m_sigaltstack_installed m := rfl
theorem m_sigaltstack_installed_with_abort_terminal (v : Bool) (m : Model) :
    m_sigaltstack_installed (with_abort_terminal v m) = m_sigaltstack_installed m := rfl
theorem m_sigaltstack_installed_init_model (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    m_sigaltstack_installed (init_model reserved brk0 mbase sp lim inp) = false := rfl
theorem m_killed_init_model (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    m_killed (init_model reserved brk0 mbase sp lim inp) = none := rfl
theorem m_sigabrt_pending_init_model (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    m_sigabrt_pending (init_model reserved brk0 mbase sp lim inp) = false := rfl
theorem m_abort_terminal_init_model (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    m_abort_terminal (init_model reserved brk0 mbase sp lim inp) = inp.in_abort_terminal := rfl

/-- The initial ledger declares no protected interval, so its protected
entries are trivially nonempty — the base case the memory arms carry the
invariant from.  Rocq: `State.init_model_noaccess_nonzero`. -/
theorem init_model_noaccess_nonzero (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    vm_noaccess_entries_nonzero (m_vmmaps (init_model reserved brk0 mbase sp lim inp)) :=
  entries_nonzero_nil

end LinuxProcessSemantics.LinuxProcessSem.State
