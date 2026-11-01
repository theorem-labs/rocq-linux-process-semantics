(** * LinuxProcessSem.Ns.Arm — what the namespace model's arms share

    The arm type, the released answer, and the helpers every arm uses: an
    answer that only sets the return register, the open file a descriptor
    names, a fresh handle, the task's pid, and the context setters. *)

From Stdlib Require Import ZArith List Bool NArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext.
Import ListNotations.

(** One call number's answer in a world with a mount tree. *)
Definition NsArm : Type := SyscallInput -> Model -> NsCtx -> NsState -> ext_outcome -> Prop.

(** The released answer, with the namespace context and state unchanged. *)
Definition released : NsArm := fun i m ctx st o =>
  match o with
  | EOk eff m' ctx' st' evs => ctx' = ctx /\ st' = st /\ syscall_spec i m (Ok eff m' evs)
  | EUnmodeled => syscall_spec i m Unmodeled
  end.

(* =========================================================================
   What arms share
   ========================================================================= *)

(** An answer that sets the return register and changes nothing else. *)
Definition ns_ret (r : word) (m : Model) (ctx : NsCtx) (st : NsState) : ext_outcome :=
  EOk (mkEffect r [] []) m ctx st [].

Definition ns_errno (e : Z) (m : Model) (ctx : NsCtx) (st : NsState) : ext_outcome :=
  ns_ret (errno_ret e) m ctx st.

Fixpoint lookup_file (fs : list (N * NsFile)) (h : N) : option NsFile :=
  match fs with
  | [] => None
  | (k, f) :: r => if N.eqb k h then Some f else lookup_file r h
  end.

(** The open file of the namespace model that descriptor [fd] names, with
    its handle; [None] for a descriptor of another kind or no descriptor. *)
Definition ns_file_of (m : Model) (st : NsState) (fd : word) : option (N * NsFile) :=
  match fd_lookup (m_fds m) fd with
  | Some (FdOpaque (ONsFile h)) => option_map (fun f => (h, f)) (lookup_file (ns_files st) h)
  | _ => None
  end.

(** A handle no open file has. *)
Definition fresh_handle (st : NsState) : N :=
  N.succ (fold_left N.max (map fst (ns_files st)) 0%N).

(** The task's pid in a pid namespace, and in its own. *)
Fixpoint pid_in (ps : list (positive * Z)) (n : positive) : option Z :=
  match ps with
  | [] => None
  | (k, p) :: r => if Pos.eqb k n then Some p else pid_in r n
  end.

Definition task_pid (ctx : NsCtx) : option Z := pid_in (cx_pids ctx) (cx_pidns ctx).

Definition with_umask (ctx : NsCtx) (u : Z) : NsCtx :=
  mkNsCtx (cx_user ctx) (cx_mount ctx) (cx_pidns ctx) (cx_net ctx) (cx_pids ctx) (cx_root ctx)
          (cx_cwd ctx) u (cx_caps ctx) (cx_securebits ctx) (cx_cloexec ctx)
          (cx_no_new_privs ctx) (cx_pdeathsig ctx) (cx_dumpable ctx).

