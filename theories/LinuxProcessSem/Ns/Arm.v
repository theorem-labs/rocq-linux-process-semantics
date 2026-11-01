(** * LinuxProcessSem.Ns.Arm — what the namespace model's arms share

    The arm type, the released answer, and the helpers every arm uses: an
    answer that only sets the return register, the open file a descriptor
    names, a fresh handle, the task's pid, the context setters, and what a
    path walk needs from the process ([walk_creds], [fd_loc_of]). *)

From Stdlib Require Import ZArith List Bool NArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Mount Walk.
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

(** The descriptor entry of the namespace model's open file [h], and the
    handle an entry names ([None] for another kind of entry). *)
Definition ns_fd_entry (h : N) : FdEntry := FdOpaque (ONsFile h).

Definition fd_entry_handle (e : FdEntry) : option N :=
  match e with FdOpaque (ONsFile h) => Some h | _ => None end.

(** The creation flags of the released model's eventfd at descriptor
    [fd], if that is what the descriptor is. *)
Definition eventfd_flags_of (m : Model) (fd : word) : option word :=
  match fd_lookup (m_fds m) fd with
  | Some (FdOpaque (OEventFd fl)) => Some fl
  | _ => None
  end.

(** A handle no open file has. *)
Definition fresh_handle (st : NsState) : N :=
  N.succ (fold_left N.max (map fst (ns_files st)) 0%N).

(** The task's pid in its own pid namespace ([Walk.pid_in]). *)
Definition task_pid (ctx : NsCtx) : option Z := pid_in (cx_pids ctx) (cx_pidns ctx).

(** Where an open file of the namespace model is, for a walk: the path of
    an O_PATH file, a directory or a file; [None] for a socket, an eventfd
    or a signalfd. *)
Definition nsfile_loc (f : NsFile) : option Loc :=
  match nf_kind f with
  | NfPath l | NfDir l _ | NfFile l _ | NfUserNsFile l _ _ | NfMountinfo l _ _ _ => Some l
  | _ => None
  end.

(** Where a descriptor the released model opened is.  A task in the
    released world opened it (a namespace arm would have minted an
    [ONsFile]), so its path is a path of the host's mount namespace,
    resolved from that namespace's root as the released arm resolved it
    when it checked the open.  No task of the model changes the host's
    mount namespace (a task in it is in the released world, whose mount
    arm declines), so the walk now is the walk then.  The walk runs with
    every capability of the initial user namespace, since the released
    arm already checked the opener's permission, and with no pid, so a
    path through procfs [self] does not resolve; a relative path, and any
    walk that does not end at a location, give [None]. *)
Definition host_loc (st : NsState) (p : list byte) : option Loc :=
  let absolute := match p with c :: _ => (bv_unsigned c =? 47)%Z | [] => false end in
  match absolute,
        find (fun n => mntns_released n) (ns_mntns st),
        find (fun u => match uns_parent u with None => true | Some _ => false end) (ns_userns st) with
  | true, Some n, Some u =>
      match find_mount (ns_mounts st) (mntns_root n) with
      | Some r =>
          let root := (mnt_id r, mnt_root r) in
          let full := (2 ^ 41 - 1)%Z in
          let hctx := mkNsCtx (uns_id u) (mntns_id n) (cx_pidns init_nsctx) (cx_net init_nsctx) []
                              root root (cx_umask init_nsctx) (mkCaps full full 0 full 0) 0 []
                              false 0 1 in
          match walk st hctx (mkWalkCreds 0 0 []) (fun _ => None) (LDentry (fst root) (snd root)) p
                     (mkWalkFlags true false false false false) with
          | (WOk l, _) => Some l
          | _ => None
          end
      | None => None
      end
  | _, _, _ => None
  end.

(** The walk's descriptor resolver ([Walk.walk]'s [fd_loc]): [None] for a
    number that is not open, [Some None] for an open descriptor the model
    holds no path for (a socket, a pipe, a released directory, which
    carries no path), [Some (Some l)] for one at [l]: an open file of the
    namespace model, or a released O_PATH or regular-file descriptor whose
    path [host_loc] resolves. *)
Definition fd_loc_of (m : Model) (st : NsState) (fd : Z) : option (option Loc) :=
  match fd_lookup (m_fds m) (Z_to_bv 64 fd) with
  | None => None
  | Some (FdOpaque (ONsFile h)) =>
      Some (match lookup_file (ns_files st) h with Some f => nsfile_loc f | None => None end)
  | Some (FdOpaque (OProcPath p)) => Some (host_loc st p)
  | Some (FdFile p _) | Some (FdFileW p _) | Some (FdFileA p _) | Some (FdFileRW p _) =>
      Some (host_loc st p)
  | Some _ => Some None
  end.

(** The credential a walk checks permissions with: the fsuid and fsgid,
    which the model keeps equal to the euid and egid (it has no setfsuid),
    and the supplementary groups, as kernel ids. *)
Definition walk_creds (m : Model) : WalkCreds :=
  mkWalkCreds (bv_unsigned (cr_euid (m_creds m))) (bv_unsigned (cr_egid (m_creds m)))
              (map bv_unsigned (cr_groups (m_creds m))).

(* =========================================================================
   Reading and writing user memory
   ========================================================================= *)

(** [get_user] of a 32-bit value: EFAULT outside [access_ok]; an unmapped
    byte inside it declines, as the released arms do. *)
Inductive UserRead := GetFault | GetUnmapped | GetVal (v : Z).

Definition get_u32 (i : SyscallInput) (a : word) : UserRead :=
  if negb (access_okb a 4) then GetFault
  else match read_bytes_map (in_mem i) a (Z_to_bv 64 4) with
       | Some bs => GetVal (bytes_le_to_Z bs)
       | None => GetUnmapped
       end.

(** [copy_to_user] of [n] bytes: EFAULT outside [access_ok]; a range not
    wholly writable after it declines (a partial copy). *)
Inductive UserWrite := PutFault | PutPartial | PutOk.

Definition put_ok (i : SyscallInput) (a : word) (n : Z) : UserWrite :=
  if negb (access_okb a n) then PutFault
  else match read_bytes_map (in_wmem i) a (Z_to_bv 64 n) with
       | Some _ => PutOk
       | None => PutPartial
       end.

Definition u32_bytes (v : Z) : list byte := Z_to_le_bytes 4 v.

(** A signed 32-bit reading of a word's low half. *)
Definition s32 (w : word) : Z :=
  let v := Z.land (bv_unsigned w) 4294967295 in
  if (v <? 2147483648)%Z then v else (v - 4294967296)%Z.

Definition with_umask (ctx : NsCtx) (u : Z) : NsCtx :=
  mkNsCtx (cx_user ctx) (cx_mount ctx) (cx_pidns ctx) (cx_net ctx) (cx_pids ctx) (cx_root ctx)
          (cx_cwd ctx) u (cx_caps ctx) (cx_securebits ctx) (cx_cloexec ctx)
          (cx_no_new_privs ctx) (cx_pdeathsig ctx) (cx_dumpable ctx).

(** The descriptors marked close-on-exec replaced by [l]. *)
Definition with_cloexec (ctx : NsCtx) (l : list Z) : NsCtx :=
  mkNsCtx (cx_user ctx) (cx_mount ctx) (cx_pidns ctx) (cx_net ctx) (cx_pids ctx) (cx_root ctx)
          (cx_cwd ctx) (cx_umask ctx) (cx_caps ctx) (cx_securebits ctx) l
          (cx_no_new_privs ctx) (cx_pdeathsig ctx) (cx_dumpable ctx).

(** Descriptor [fd] marked close-on-exec when [on], unmarked otherwise. *)
Definition set_cloexec (ctx : NsCtx) (fd : Z) (on : bool) : NsCtx :=
  let l := List.filter (fun x => negb (Z.eqb x fd)) (cx_cloexec ctx) in
  with_cloexec ctx (if on then fd :: l else l).

(** The open file [h] replaced by [f]. *)
Definition set_file (st : NsState) (h : N) (f : NsFile) : NsState :=
  with_files st (map (fun p => if N.eqb (fst p) h then (h, f) else p) (ns_files st)).

(** THE ONE PLACE an open file of the model is freed: after a descriptor
    naming handle [h] went, leaving the caller's table [fds'], the file
    goes when no descriptor of [fds'] names it.  This sees only the
    caller's table, so a file another process also names (inherited
    across a fork) is freed early, and that process's later use fails
    closed; a count across processes replaces this function and nothing
    else.  No other path frees a file: an unmount and the end of a
    namespace leave open files in place, as Linux keeps them alive. *)
Definition release_handle (fds' : list (word * FdEntry)) (st : NsState) (h : N) : NsState :=
  if existsb (fun p => match fd_entry_handle (snd p) with
                       | Some h' => N.eqb h h'
                       | None => false
                       end) fds'
  then st
  else with_files st (List.filter (fun p => negb (N.eqb (fst p) h)) (ns_files st)).

Definition find_mntns (st : NsState) (n : positive) : option MntNs :=
  find (fun x => Pos.eqb (mntns_id x) n) (ns_mntns st).

(** The environment's refusals of one call number: a list of pairs, each an
    errno predicate and the family that injects it.  One errno can be in
    two pairs (an allocation failure and any errno of a security module). *)
Record NsInjected := mkNsInjected {
  ni_no    : Z;
  ni_pairs : list ((Z -> bool) * SpuriousFamily)
}.

(** A failure chosen by the environment after a deterministic arm has
    reached its operation.  It keeps the copy-ins already made, writes
    nothing, and leaves the namespace state unchanged. *)
Definition injected_after (P : Z -> bool) (r : ext_outcome)
    (m : Model) (ctx : NsCtx) (st : NsState) (o : ext_outcome) : Prop :=
  match r with
  | EOk eff _ _ _ _ =>
      exists e, P e = true /\
        o = EOk (with_copyins (eff_copyins eff) (mkEffect (errno_ret e) [] [])) m ctx st []
  | EUnmodeled => False
  end.

(** Lift an arm's successful answer into its environment refusal.  The
    witness is the successful outcome reached after every earlier argument,
    path, descriptor, and permission check; [injected_after] keeps exactly
    that outcome's copy-ins. *)
Definition with_injected (P : Z -> bool) (a : NsArm) : NsArm :=
  fun i m ctx st o =>
    a i m ctx st o
    \/ exists ok, a i m ctx st ok /\ injected_after P ok m ctx st o.

