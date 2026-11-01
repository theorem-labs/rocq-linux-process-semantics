(** * LinuxProcessSem.Checks.Cases.ParentTrace — bubblewrap parent's calls before clone

    These executable examples replay, in order, the system-call words that
    bubblewrap's parent makes before its namespace clone in a full-system
    trace.  The fixtures keep the observed uid and gid, the descriptors
    acquired so far, and every string or buffer read by a call. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Decode DecodeC.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel Require Import
  Capability Fork Signal Sys.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs Require Import
  EventFd File Ioctl Open ReadWrite.

(** The observed initial break is 0x51000.  The mapping base and stack are
    concrete user addresses so the virtual-memory fixtures below can carry
    the observed mapping words without affecting the descriptor and
    credential state used by the remaining calls. *)
Definition parent_trace_base : Model :=
  with_creds (mkCreds 65534 65534 65534 65534 65534 65534 [])
    (init_model [] 0x51000 0x7fff9428e000 0x7ffffffffdf0 demo_limit
       (demo_input [] IEof)).

Definition parent_trace_after_set_tid : Model :=
  with_tid 319 parent_trace_base.

Definition parent_trace_call (no a0 a1 a2 a3 a4 a5 : word) : SyscallInput :=
  mkInput no [a0; a1; a2; a3; a4; a5] (fun _ => None) (fun _ => None).

(** The descriptor returned for the first sysctl read. *)
Definition parent_trace_uid_sysctl : Model :=
  proc_opened parent_trace_after_set_tid 3 (OProcFile s_overflowuid).

(** A post-brk address state.  It has the traced open descriptor, the grown
    break and its two pages. *)
Definition parent_trace_vm (maps noaccess : list (word * word)) : VmMaps :=
  mkVmMapsFull [] maps noaccess 0x51000 0x53000 demo_limit 0x7fff9428e000
    0x7ffffffffdf0.

Definition parent_trace_after_brk : Model :=
  with_vmmaps (parent_trace_vm [(0x51000, 8192)] []) parent_trace_uid_sysctl.

Definition parent_trace_anon_map : word := 0x7fff9428a000.
Definition parent_trace_page_map : word := 0x7fff9428d000.

Definition parent_trace_after_guard : Model :=
  with_vmmaps (parent_trace_vm [(0x51000, 8192)] [(0x51000, 4096)])
    parent_trace_uid_sysctl.

Definition parent_trace_after_first_mmaps : Model :=
  with_vmmaps
    (parent_trace_vm [(parent_trace_anon_map, 16384); (0x51000, 8192)]
       [(0x51000, 4096)]) parent_trace_uid_sysctl.

Definition parent_trace_after_uid_close : Model :=
  with_fds (fd_remove (m_fds parent_trace_after_first_mmaps) 3)
    parent_trace_after_first_mmaps.

Definition parent_trace_gid_sysctl : Model :=
  proc_opened parent_trace_after_uid_close 3 (OProcFile s_overflowgid).

Definition parent_trace_after_gid_close : Model :=
  with_fds (fd_remove (m_fds parent_trace_gid_sysctl) 3)
    parent_trace_gid_sysctl.

Definition parent_trace_after_munmap : Model :=
  with_vmmaps (parent_trace_vm [(0x51000, 8192)] [(0x51000, 4096)])
    parent_trace_after_gid_close.

Definition parent_trace_after_final_mmap : Model :=
  with_vmmaps
    (parent_trace_vm [(parent_trace_page_map, 4096); (0x51000, 8192)]
       [(0x51000, 4096)]) parent_trace_after_munmap.

Definition parent_trace_proc : Model :=
  proc_opened parent_trace_after_final_mmap 3 (OProcPath s_proc).

Definition parent_trace_after_eventfd4 : Model :=
  with_fds (fd_insert (m_fds parent_trace_proc) 4
              (FdOpaque (OEventFd (Z_to_bv 64 0x80800)))) parent_trace_proc.

(** [sigmask(SIGCHLD)] is bit 16, represented by this little-endian
    eight-byte signal set. *)
Definition parent_trace_sigchld_set : word -> option byte :=
  bytes_at 0x3000 [0; 0; 1; 0; 0; 0; 0; 0].

Definition parent_trace_after_sigprocmask : Model :=
  with_sigmask (Z_to_bv 64 65536) parent_trace_after_eventfd4.

Definition parent_trace_after_eventfd5 : Model :=
  with_fds (fd_insert (m_fds parent_trace_after_sigprocmask) 5
              (FdOpaque (OEventFd (Z_to_bv 64 0x80000))))
    parent_trace_after_sigprocmask.

(** [set_tid_address(0x4fd20) = 319]. *)
Example parent_trace_set_tid_address :
  check_syscall (parent_trace_call 96 0x4fd20 0 0 0 0 0) (mkEffect 319 [] [])
    parent_trace_base
  = CheckOk parent_trace_after_set_tid [].
Proof. check_eq. Qed.

(** The six [PR_CAPBSET_READ] words retain their traced answers. *)
Example parent_trace_capbset_read_20 :
  check_syscall (prctl_in 23 0x20 0 0 0) (mkEffect 1 [] [])
    parent_trace_after_set_tid = CheckOk parent_trace_after_set_tid [].
Proof. check_eq. Qed.

Example parent_trace_capbset_read_30 :
  check_syscall (prctl_in 23 0x30 0 0 0) (mkEffect (errno_ret EINVAL) [] [])
    parent_trace_after_set_tid = CheckOk parent_trace_after_set_tid [].
Proof. check_eq. Qed.

Example parent_trace_capbset_read_28 :
  check_syscall (prctl_in 23 0x28 0 0 0) (mkEffect 1 [] [])
    parent_trace_after_set_tid = CheckOk parent_trace_after_set_tid [].
Proof. check_eq. Qed.

Example parent_trace_capbset_read_2c :
  check_syscall (prctl_in 23 0x2c 0 0 0) (mkEffect (errno_ret EINVAL) [] [])
    parent_trace_after_set_tid = CheckOk parent_trace_after_set_tid [].
Proof. check_eq. Qed.

Example parent_trace_capbset_read_2a :
  check_syscall (prctl_in 23 0x2a 0 0 0) (mkEffect (errno_ret EINVAL) [] [])
    parent_trace_after_set_tid = CheckOk parent_trace_after_set_tid [].
Proof. check_eq. Qed.

Example parent_trace_capbset_read_29 :
  check_syscall (prctl_in 23 0x29 0 0 0) (mkEffect (errno_ret EINVAL) [] [])
    parent_trace_after_set_tid = CheckOk parent_trace_after_set_tid [].
Proof. check_eq. Qed.

(** [rt_sigaction(SIGCHLD, {SIG_DFL, 0, 0}, NULL, 8) = 0] copies the full
    24-byte action structure. *)
Example parent_trace_sigaction_sigchld :
  check_syscall
    (mkInput 134 [17; 4096; 0; 8; 0; 0] mem_sigaction_zero (fun _ => None))
    (with_copyins [(4096, 24%nat)] (mkEffect 0 [] []))
    parent_trace_after_set_tid
  = CheckOk parent_trace_after_set_tid [].
Proof. check_eq. Qed.

Example parent_trace_getuid :
  check_syscall (parent_trace_call 174 0 0 0 0 0 0) (mkEffect 65534 [] [])
    parent_trace_after_set_tid
  = CheckOk parent_trace_after_set_tid [].
Proof. check_eq. Qed.

Example parent_trace_getgid :
  check_syscall (parent_trace_call 176 0 0 0 0 0 0) (mkEffect 65534 [] [])
    parent_trace_after_set_tid
  = CheckOk parent_trace_after_set_tid [].
Proof. check_eq. Qed.

Example parent_trace_geteuid :
  check_syscall (parent_trace_call 175 0 0 0 0 0 0) (mkEffect 65534 [] [])
    parent_trace_after_set_tid
  = CheckOk parent_trace_after_set_tid [].
Proof. check_eq. Qed.

(** Version 3, pid 0 and 24 bytes of zero capability sets. *)
Example parent_trace_capget :
  check_syscall (capget_input LINUX_CAPABILITY_VERSION_3 cap_dataptr)
    (mkEffectU 0 [(cap_dataptr, cap_image 0 0 0 0 0 0)] [] [] [] cap_ledger2)
    parent_trace_after_set_tid
  = CheckOk parent_trace_after_set_tid [].
Proof. check_eq. Qed.

Example parent_trace_no_new_privs :
  check_syscall (prctl_in 38 1 0 0 0) (mkEffect 0 [] [])
    parent_trace_after_set_tid = CheckOk parent_trace_after_set_tid [].
Proof. check_eq. Qed.

Example parent_trace_open_overflowuid :
  check_syscall (proc_open_in AT_FDCWD s_overflowuid 0x88000)
    (with_copyins [(8192, 29%nat)] (mkEffect 3 [] []))
    parent_trace_after_set_tid
  = CheckOk parent_trace_uid_sysctl [].
Proof. check_eq. Qed.

(** Address-space calls are pinned as reached arms rather than with a full
    ASLR-specific output ledger.  Their checker requires the complete
    virtual-memory transition; reproducing that ledger here would obscure the
    full-system trace's call surface.  Each state retains the observed break,
    map words and descriptor table, and each assertion rules out
    [CheckUnmodeled]. *)
Example parent_trace_brk_query_is_answered :
  check_syscall (parent_trace_call 214 0 0 0 0 0 0) (mkEffect 0x51000 [] [])
    parent_trace_uid_sysctl
  = CheckOk parent_trace_uid_sysctl [].
Proof. check_eq. Qed.

Example parent_trace_brk_grow_is_answered :
  check_syscall (parent_trace_call 214 0x53000 0 0 0 0 0)
    (mkEffect 0x53000 [] []) parent_trace_uid_sysctl <> CheckUnmodeled.
Proof. vm_compute. discriminate. Qed.

Example parent_trace_mmap_brk_guard_is_answered :
  check_syscall
    (parent_trace_call 222 0x51000 4096 0 0x32 (Z_to_bv 64 (-1)) 0)
    (mkEffect 0x51000 [] []) parent_trace_after_brk <> CheckUnmodeled.
Proof. vm_compute. discriminate. Qed.

Example parent_trace_mmap_16384_is_answered :
  check_syscall
    (parent_trace_call 222 0 16384 3 0x22 (Z_to_bv 64 (-1)) 0)
    (mkEffect parent_trace_anon_map [] []) parent_trace_after_guard
  <> CheckUnmodeled.
Proof. vm_compute. discriminate. Qed.

Example parent_trace_read_overflowuid :
  check_syscall (sysctl_read_in 3 4079)
    (mkEffect 6 [(0x10000, [54; 53; 53; 51; 52; 10])] [])
    parent_trace_uid_sysctl
  = CheckOk parent_trace_uid_sysctl [].
Proof. check_eq. Qed.

Example parent_trace_read_overflowuid_eof :
  check_syscall (sysctl_read_in 3 4073) (mkEffect 0 [] []) parent_trace_uid_sysctl
  = CheckOk parent_trace_uid_sysctl [].
Proof. check_eq. Qed.

Example parent_trace_close_overflowuid :
  check_syscall (parent_trace_call 57 3 0 0 0 0 0) (mkEffect 0 [] [])
    parent_trace_after_first_mmaps
  = CheckOk parent_trace_after_uid_close [].
Proof. check_eq. Qed.

Example parent_trace_open_overflowgid :
  check_syscall (proc_open_in AT_FDCWD s_overflowgid 0x88000)
    (with_copyins [(8192, 29%nat)] (mkEffect 3 [] []))
    parent_trace_after_uid_close
  = CheckOk parent_trace_gid_sysctl [].
Proof. check_eq. Qed.

Example parent_trace_read_overflowgid :
  check_syscall (sysctl_read_in 3 4079)
    (mkEffect 6 [(0x10000, [54; 53; 53; 51; 52; 10])] [])
    parent_trace_gid_sysctl
  = CheckOk parent_trace_gid_sysctl [].
Proof. check_eq. Qed.

Example parent_trace_read_overflowgid_eof :
  check_syscall (sysctl_read_in 3 4073) (mkEffect 0 [] []) parent_trace_gid_sysctl
  = CheckOk parent_trace_gid_sysctl [].
Proof. check_eq. Qed.

Example parent_trace_close_overflowgid :
  check_syscall (parent_trace_call 57 3 0 0 0 0 0) (mkEffect 0 [] [])
    parent_trace_gid_sysctl
  = CheckOk parent_trace_after_gid_close [].
Proof. check_eq. Qed.

Example parent_trace_munmap_16384_is_answered :
  check_syscall (parent_trace_call 215 parent_trace_anon_map 16384 0 0 0 0)
    (mkEffect 0 [] []) parent_trace_after_gid_close <> CheckUnmodeled.
Proof. vm_compute. discriminate. Qed.

Example parent_trace_ioctl_tiocgwinsz :
  check_syscall (parent_trace_call 29 1 0x5413 0x7ffffe5dcc70 0 0 0)
    (mkEffect (errno_ret ENOTTY) [] []) parent_trace_after_munmap
  = CheckOk parent_trace_after_munmap [].
Proof. check_eq. Qed.

Example parent_trace_mmap_page_is_answered :
  check_syscall
    (parent_trace_call 222 0 4096 3 0x22 (Z_to_bv 64 (-1)) 0)
    (mkEffect parent_trace_page_map [] []) parent_trace_after_munmap
  <> CheckUnmodeled.
Proof. vm_compute. discriminate. Qed.

Example parent_trace_getuid_after_mmap :
  check_syscall (parent_trace_call 174 0 0 0 0 0 0) (mkEffect 65534 [] [])
    parent_trace_after_final_mmap
  = CheckOk parent_trace_after_final_mmap [].
Proof. check_eq. Qed.

Example parent_trace_open_proc :
  check_syscall (proc_open_in AT_FDCWD s_proc 0x208000)
    (with_copyins [(8192, 6%nat)] (mkEffect 3 [] [])) parent_trace_after_final_mmap
  = CheckOk parent_trace_proc [].
Proof. check_eq. Qed.

Example parent_trace_eventfd_nonblock :
  check_syscall (parent_trace_call 19 0 0x80800 0 0 0 0) (mkEffect 4 [] [])
    parent_trace_proc
  = CheckOk parent_trace_after_eventfd4 [].
Proof. check_eq. Qed.

Example parent_trace_sigprocmask_block_sigchld :
  check_syscall
    (mkInput 135 [0; 0x3000; 0; 8; 0; 0] parent_trace_sigchld_set
       (fun _ => None))
    (with_copyins [(0x3000, 8%nat)] (mkEffect 0 [] []))
    parent_trace_after_eventfd4
  = CheckOk parent_trace_after_sigprocmask [].
Proof. check_eq. Qed.

Example parent_trace_wait4_no_child :
  check_syscall
    (parent_trace_call 260 (Z_to_bv 64 WAIT_ANY32) 0x7ffffe5ddeb0 1 0 0 0)
    (mkEffect (errno_ret ECHILD) [] []) parent_trace_after_sigprocmask
  = CheckOk parent_trace_after_sigprocmask [].
Proof. check_eq. Qed.

Example parent_trace_eventfd_cloexec :
  check_syscall (parent_trace_call 19 0 0x80000 0 0 0 0) (mkEffect 5 [] [])
    parent_trace_after_sigprocmask
  = CheckOk parent_trace_after_eventfd5 [].
Proof. check_eq. Qed.

(** The clone state carries exactly the descriptors reached by the parent:
    the O_PATH descriptor at 3 and the two eventfds at 4 and 5. *)
Example parent_trace_namespace_clone :
  check_syscall
    (parent_trace_call 220 bwrap_clone_flags 0 0 0 0 0) (mkEffect 320 [] [])
    parent_trace_after_eventfd5
  = CheckOk (with_children parent_trace_after_eventfd5) [].
Proof. check_eq. Qed.

(** Trace-call index:

    - [set_tid_address]: [parent_trace_set_tid_address].
    - [prctl(PR_CAPBSET_READ, 0x20/0x30/0x28/0x2c/0x2a/0x29)]:
      [parent_trace_capbset_read_20], [parent_trace_capbset_read_30],
      [parent_trace_capbset_read_28], [parent_trace_capbset_read_2c],
      [parent_trace_capbset_read_2a], [parent_trace_capbset_read_29].
    - [rt_sigaction], [getuid], [getgid], [geteuid], [capget] and
      [prctl(PR_SET_NO_NEW_PRIVS)]: [parent_trace_sigaction_sigchld],
      [parent_trace_getuid], [parent_trace_getgid], [parent_trace_geteuid],
      [parent_trace_capget], [parent_trace_no_new_privs].
    - The first [openat], [brk] pair, fixed guard mapping and 16384-byte
      mapping: [parent_trace_open_overflowuid], [parent_trace_brk_query_is_answered],
      [parent_trace_brk_grow_is_answered], [parent_trace_mmap_brk_guard_is_answered],
      [parent_trace_mmap_16384_is_answered].
    - Both reads and closes around the second [openat]:
      [parent_trace_read_overflowuid], [parent_trace_read_overflowuid_eof],
      [parent_trace_close_overflowuid], [parent_trace_open_overflowgid],
      [parent_trace_read_overflowgid], [parent_trace_read_overflowgid_eof],
      [parent_trace_close_overflowgid].
    - [munmap], [ioctl], the final page mapping, the repeated [getuid],
      [openat], two [eventfd2] calls, [rt_sigprocmask], [wait4], and [clone]:
      [parent_trace_munmap_16384_is_answered], [parent_trace_ioctl_tiocgwinsz],
      [parent_trace_mmap_page_is_answered], [parent_trace_getuid_after_mmap],
      [parent_trace_open_proc], [parent_trace_eventfd_nonblock],
      [parent_trace_sigprocmask_block_sigchld], [parent_trace_wait4_no_child],
      [parent_trace_eventfd_cloexec], [parent_trace_namespace_clone]. *)
