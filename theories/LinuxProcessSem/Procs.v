(** * LinuxProcessSem.Procs — the multi-process core

    TRUST BOUNDARY: this file is part of the trusted specification.

    WHAT THIS FILE IS.  [Run.config] is one [machine_state] and one
    [State.Model], and [Run.sstep_cfg] steps exactly one of them.  This file
    adds a relation over a LIST of per-process entries, so that a program
    which calls [clone] has a child that is a configuration rather than a
    boolean.  Several planned developments consume these names rather than
    restating them beside the core, so what is named here is an interface.

    WHAT IT DELIBERATELY DOES NOT DO.  It does not edit [Run.config],
    [Run.sstep], [Run.sstep_cfg], [State.Model], [Sys.Kernel.Fork],
    [Sys.Kernel.Exit], [Sys.SyscallTable] or any file under [Checks/].  That
    is the central design choice, and the reason is how much depends on the
    shape of [Run.config]: far more statements, here and in the developments
    built on this one, name [Run.mkCfg], [cfg_ms] and [cfg_model] than name
    anything this file adds.  Every one of them keeps its exact present form,
    because the released relation is reused WHOLE by [pstep_other] below
    rather than restated.

    THE WARNING THIS FILE OWES A READER, and why it does not fire.
    [Sys.Kernel.Exit.wait4_spec]'s header says, of a child becoming a
    configuration: "If a child ever becomes a configuration in this model,
    this spec is wrong rather than incomplete, and it is the first thing that
    has to change" (Exit.v:237-243).  [Sys.Kernel.Fork]'s header says the same
    from the other side: "No second process is created.  [Run.config] holds
    one [machine_state] and one [Model], and nothing here adds a second of
    either" (Fork.v:138-145).  BOTH REMAIN TRUE.  A child here is an ENTRY OF
    A NEW RELATION, not a configuration of the released one: [Run.config] is
    unchanged, no [Run.sstep_cfg] rule produces a second of either, and
    [wait4_spec] keeps answering the single-process question with the answer
    it always gave.  The two never apply to the same configuration -- the
    released arm is [unmodeled] unless the option word is WNOHANG, unless the
    pid is the any-child value, unless the usage pointer is null, and then
    [unmodeled] AGAIN if the model has children (Exit.v:244-252), while the
    reap arm of this file requires the option word to be 0 and requires an own
    halted child.  There is no configuration at which both say anything.

    WHY THE CLONE ARM CONSUMES THE RELEASED STEP.  It fires only under
    [clone_success_b], which reads the value [Run.apply_effect] put in a0
    against [Fork.clone_errnos] through [Run.ret_in_errnos] -- the same
    predicate [Run.refusal_b] uses.  So a FAILING clone keeps the released
    behaviour exactly, and the new arm cannot drift from the released errno
    list even if that list changes.

    TWO THINGS A PORTER OF THIS FILE MUST NOT GUESS.

    [ms_gpr st i] is the i-th syscall ARGUMENT register, x(10+i)
    (RiscvSemantics.v:115-118), so a0 is index 0.  Index 10 is x20.
    [Run.apply_effect] writes the return value with [set_reg ms 10], which
    takes a PHYSICAL register number, and physical x10 is a0: the two
    numberings meet at a0 and nowhere else.  A port that reads index 10 here
    builds, never fires the clone arm, and looks like a model disagreement.

    [set_fsys] below is NOT [State.with_fs].  [State.with_fs] additionally
    applies [statpins_restrict], dropping the stat pin of every path the new
    image does not have -- which is right for a syscall that replaces the
    image and WRONG for a splice, where the image is the one the entry
    already had and the pins must survive untouched.  The splice therefore
    uses the plain record rebuild below.  A port that reuses the model's
    image-installing setter silently loses stat pins at every step.

    BUILD ORDER.  [pstep_single] and [pstep_instr_single] below are proved
    before any arm but [pstep_other], because every derived step relation
    rests on them and because every one-process statement does. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
(** [reg_get], which [RiscvSemantics.ms_gpr] is defined through and which
    the a0 lemmas below unfold. *)
From LinuxProcessSemantics.Riscv Require Import Sem.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Exit Fork.
(** [NsState] and [NsCtx].  This file DEPENDS ON [Ns/Tables.v] and does not
    vendor it: two representations of one thing are what diverge. *)
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope bool_scope.

(* =========================================================================
   Identifiers
   ========================================================================= *)

(** A pid and an open-description id are both [word].

    NOT [positive], and the reason is portability rather than taste: the
    mirror of this development has no [positive], every boundary would be a
    conversion, and the obvious rendering [Nat] silently re-admits pid 0 and
    so undoes [Checks.ProcessCreation.clone_never_returns_zero].  With [word]
    the lookup and insert below are the model's own fd-table operations on
    the same key type, and nothing is lost on this side: freshness is still
    [look P q = None], and 0 is still excluded by [Fork.clone_pid_ok_b]. *)
Definition Pid   : Type := word.
Definition OfdId : Type := word.

(* =========================================================================
   Shared kernel objects that leave the per-process model
   ========================================================================= *)

(** The access mode of a shared regular file, which is what the four
    [State.FdFile*] constructors differ by. *)
Inductive FileMode : Type := FmR | FmW | FmA | FmRW.

(** What a shared description is OF.  The payloads MIRROR [State.FdEntry]'s
    exactly, so promoting a private descriptor loses nothing and a later
    demotion is total.

    The kinds here are the [State.FdEntry] constructors that carry a mutable
    kernel-side OFFSET inside the entry: the four regular-file forms, a pipe
    end and a socket.  [FdDir], [FdDevNull] and [FdUrandom] carry none and
    stay private in [State.m_fd].

    [FdChannel] is NOT here, and that is the interesting case.  A channel's
    position is not in the descriptor at all: it is [State.iost_stdin] inside
    [m_io] (State.v:2964-2965, 3504).  [m_io] is already a field of [shared],
    so an inherited standard descriptor is shared ACROSS A CLONE BY
    CONSTRUCTION and needs no promotion.  That is why no clone gate excludes
    one: a parent that keeps its standard descriptors open across a clone is
    handled, not declined. *)
Inductive OfdWhat : Type :=
  | OfdFile   (p : Fs.path) (mode : FileMode)
  | OfdPipe   (id : word) (writer : bool)
  | OfdSocket (sk : SockState).

(** A shared open file description: Linux's [struct file].  THE OFFSET LIVES
    HERE, once, however many descriptors in however many processes name it.
    That is the whole point of the record and the reason it is not a
    [State.FdEntry]: [Sys.Kernel.Fork]'s header (Fork.v:180-193) says what
    survives even a plain fork is the FILE OFFSET, because [copy_files]
    duplicates the table while both tables point at the same [struct file],
    and an offset inside [FdEntry] cannot express that.

    MEASURED ALTERNATIVE, so the choice is on the record: moving the offset
    out of [State.FdEntry] itself costs 1357 constructor-pattern sites across
    69 files in this repository, each in a [Checks/Sys], [Checks/Witness] or
    [Checks/Cases] mirror with its own four soundness proofs, and a larger
    number again in the developments built on this one.  This overlay costs
    none of them.

    [ofd_refs] counts the descriptors that name it, across every process.  It
    is what makes a pipe's EOF expressible: a read sees EOF when the WRITE
    end's count reaches zero, which no per-process copy could ever report. *)
Record Ofd := mkOfd {
  ofd_what  : OfdWhat;
  ofd_off   : word;
  ofd_flags : word;
  ofd_refs  : word
}.

(** THE NAMESPACE STATE IS NOT DEFINED HERE, AND MUST NOT BE.

    It is [LinuxProcessSem.Ns.Tables], imported above: [NsState], the mounts
    with their flags and locks and the user namespaces with their maps, and
    [NsCtx], the task-private user and mount ids with root and cwd as a
    mount-and-dentry pair.  This file takes those types and carries no second
    copy of them, because two representations of one thing are what diverge.

    WHY A TASK-PRIVATE CONTEXT AT ALL, rather than a projection over the run:
    a path walk, a capability check and [getpid] each read a private
    reference AND a shared object in the SAME step.  A pure projection can
    decide none of /proc/self, a mount root, a uid mapping or a capability
    set, because [Fs.Fs] is [list (path * list byte)] (Fs.v:86) with no
    mount, no inode identity and no owner.

    [pconfig] is deliberately NOT parametric in the namespace state.  A
    parameter for one field would reach every definition and every theorem
    here, and the cost would land on the projection theorem, which is the one
    thing every consumer and the released corpus both depend on.  The PID
    type is parametric in the consumer's module type, which is where a
    parameter belongs; here it is [word]. *)

(* =========================================================================
   The entries, the shared state, and the configuration
   ========================================================================= *)

(** One process.

    [pe_model] carries ONLY the per-process part of [State.Model]: [m_fd],
    [m_vm], [m_proc], [m_lim], [m_time].  Its [m_fsys] and [m_io] slots are
    canonically empty and are never read: [pe_cfg] splices the SHARED ones in
    before every step and [pe_absorb] reads them back out after, so the shared
    copy is the only live one. *)
Record ProcessEntry := mkEntry {
  pe_pid    : Pid;
  pe_parent : option Pid;
  pe_ms     : machine_state;
  pe_model  : Model;
  pe_ofd    : list (word * OfdId);
  pe_nsctx  : NsCtx
}.

(** Shared Run state: one of each, for the whole system. *)
Record shared := mkShared {
  sh_fsys  : FsState;
  sh_io    : IoState;
  sh_ofd   : list (OfdId * Ofd);
  (** THE PIPE BUFFERS, a NAMED field beside [sh_ofd] rather than a slot
      inside it or inside the namespace state: the projections below are what
      a consumer reads, and a buffer hidden in another field's slot cannot be
      named by one. *)
  sh_pipes : list (word * PipeBuf);
  sh_ns    : NsState
}.

(** The process table is keyed exactly as [State.m_fds] is, so the lookup and
    the insert below are the model's own on the same key type.  The key and
    [pe_pid] are the same pid; [pconfig_wf] is where that is said once. *)
Record pconfig := mkPCfg {
  pcfg_procs  : list (Pid * ProcessEntry);
  pcfg_root   : Pid;
  pcfg_shared : shared
}.

Inductive pstep_to := PNext (P : pconfig) | PError.

(* =========================================================================
   The splice: how the shared state reaches a released step
   ========================================================================= *)

(** A plain record rebuild.  NOT [State.with_fs]: see this file's header for
    why a splice must not apply [statpins_restrict]. *)
Definition set_fsys (f : FsState) (m : Model) : Model :=
  mkModelOf (m_fd m) (m_vm m) (m_io m) f (m_proc m) (m_lim m) (m_time m).

Definition set_io (i : IoState) (m : Model) : Model :=
  mkModelOf (m_fd m) (m_vm m) i (m_fsys m) (m_proc m) (m_lim m) (m_time m).

Definition empty_fsys : FsState := mkFsState [].
Definition empty_io : IoState :=
  mkIoState IEof IEof net_silent (Z_to_bv 64 0).

(** Blank the two slots the shared state owns, so a reader cannot mistake the
    per-entry copy for data. *)
Definition clear_shared (m : Model) : Model :=
  set_fsys empty_fsys (set_io empty_io m).

(** The released single-process view of one entry.  THE ONLY PLACE
    [Run.sstep_cfg] is applied. *)
Definition pe_cfg (S : shared) (e : ProcessEntry) : config :=
  mkCfg (pe_ms e) (set_fsys (sh_fsys S) (set_io (sh_io S) (pe_model e))).

Definition pe_absorb (e : ProcessEntry) (c : config) : ProcessEntry :=
  mkEntry (pe_pid e) (pe_parent e) (cfg_ms c) (clear_shared (cfg_model c))
          (pe_ofd e) (pe_nsctx e).

Definition shared_absorb (S : shared) (c : config) : shared :=
  mkShared (m_fsys (cfg_model c)) (m_io (cfg_model c))
           (sh_ofd S) (sh_pipes S) (sh_ns S).

(** The splice and the absorb are inverse, which is the whole reason the
    per-entry [m_fsys] and [m_io] slots may be blank. *)
Lemma pe_cfg_absorb : forall S e c,
  pe_cfg (shared_absorb S c) (pe_absorb e c) = c.
Proof. intros S e c. destruct c as [ms m]. destruct m. reflexivity. Qed.

(* =========================================================================
   The process table: lookup and replace, on the fd table's key type
   ========================================================================= *)

Fixpoint look_in (ps : list (Pid * ProcessEntry)) (p : Pid)
    : option ProcessEntry :=
  match ps with
  | [] => None
  | kv :: r => if bv_eqb (fst kv) p then Some (snd kv) else look_in r p
  end.

(** [Riscv.Prelude] defines [bv_eqb] as [Z.eqb] on the unsigned readings and
    states no lemma about it, so the two this file needs are proved here. *)
Lemma bv_eqb_same : forall n (a : bv n), bv_eqb a a = true.
Proof. intros n a. unfold bv_eqb. apply Z.eqb_refl. Qed.

Lemma bv_eqb_true_eq : forall n (a b : bv n), bv_eqb a b = true -> a = b.
Proof.
  intros n a b H. unfold bv_eqb in H. apply Z.eqb_eq in H.
  apply bv_eq. exact H.
Qed.

Definition look (P : pconfig) (p : Pid) : option ProcessEntry :=
  look_in (pcfg_procs P) p.

Fixpoint replace_in (ps : list (Pid * ProcessEntry)) (p : Pid)
    (e' : ProcessEntry) : list (Pid * ProcessEntry) :=
  match ps with
  | [] => []
  | kv :: r =>
      if bv_eqb (fst kv) p then (p, e') :: r
      else kv :: replace_in r p e'
  end.

Fixpoint drop_in (ps : list (Pid * ProcessEntry)) (p : Pid)
    : list (Pid * ProcessEntry) :=
  match ps with
  | [] => []
  | kv :: r => if bv_eqb (fst kv) p then r else kv :: drop_in r p
  end.

(* =========================================================================
   Projections
   ========================================================================= *)

Definition pe_running (e : ProcessEntry) : Prop := m_halted (pe_model e) = None.

(** A zombie is an entry whose model is halted.  There is no zombie LIST and
    no zombie flag: every [Run.sstep_cfg] arm requires [m_halted model = None]
    (Run.v:1785, 1790, 1795, 1800, 1810, 1818, 1826, 1833), so a halted entry
    is already stuck in the released relation.  "Dead" is absence from
    [pcfg_procs]. *)
Definition pe_zombie (e : ProcessEntry) : option word := m_halted (pe_model e).

Definition root_view (P : pconfig) : option config :=
  match look P (pcfg_root P) with
  | Some e => Some (pe_cfg (pcfg_shared P) e)
  | None => None
  end.

Definition children_of (P : pconfig) (p : Pid) : list ProcessEntry :=
  (* [List.filter], NOT the bare name: this development imports stdpp, whose
     [filter] takes a [Decision] instance rather than a boolean. *)
  List.map snd
    (List.filter (fun kv => match pe_parent (snd kv) with
                            | Some q => bv_eqb q p
                            | None => false
                            end) (pcfg_procs P)).

(** The entry's a0 is zero: how a clone's child sees the call. *)
Definition entry_a0_zero (e : ProcessEntry) : Prop :=
  ms_gpr (pe_ms e) 0 = Z_to_bv 64 0.

(* =========================================================================
   The multi-process surface
   ========================================================================= *)

(** The syscalls this core answers while more than one entry is live.
    Everything else fails closed, because a syscall touching a kernel object
    Linux SHARES, that this model has not yet moved into [shared], would
    otherwise be answered against a private copy.  A development that adds
    the pipe and file syscalls 59, 63, 64 and 57 to this list must add them
    TOGETHER WITH the [Ofd] machinery that makes them sound, never before. *)
Definition multiproc_sysnos : list Z := [93; 94; 220; 260; 435]%Z.

Definition multiproc_allowed (P : pconfig) (c : config) : bool :=
  match ms_svc_pending (cfg_ms c) with
  | None => true
  | Some x8 =>
      Nat.leb (List.length (pcfg_procs P)) 1%nat
      || List.existsb (Z.eqb (bv_unsigned x8)) multiproc_sysnos
  end.

(* =========================================================================
   The two intercepted steps, as decidable tests
   ========================================================================= *)

Definition clone_sysno (n : Z) : bool := (n =? 220)%Z || (n =? 435)%Z.

(** The step [c -> c'] was a clone that really created a child.  A BOOLEAN,
    so a port needs no decidability instance and the arms below are guarded
    by equations rather than by negated existentials.

    [Run.apply_effect] sets a0 from [eff_ret] (Run.v:177), so the delivered
    value is read off the successor, at ARGUMENT INDEX 0 (see the header).
    A clone created a child exactly when it did not return an errno:
    [State.addr_is_error_b], the [-4095, -1] range.
    [Checks.ProcessCreation.clone_success_sets_children] is what makes
    this exact, keyed on the same test: an error-encoded answer leaves the
    model untouched, any other answer sets [State.m_has_children].  The
    test this replaces, membership in [Fork.clone_errnos], was exact only
    while 220 answered the fork word alone: clone3's -EFAULT is not in the
    list, and the namespace word ([Fork.clone_ns_resolve]) fails with any
    errno but -EINTR, so its -EPERM would read as a child with pid
    2^64-1. *)
Definition clone_success_b (c c' : config) : bool :=
  match ms_svc_pending (cfg_ms c) with
  | None => false
  | Some x8 =>
      clone_sysno (bv_unsigned x8)
      && negb (addr_is_error_b (ms_gpr (cfg_ms c') 0))
  end.

(** THE CHILD PID PREDICATE: a DEFINITION with an explicit extension
    parameter, NOT an inductive, and the difference is a soundness one.  An
    inductive is strengthened by adding a CONSTRUCTOR, and a consumer who adds
    one WIDENS the predicate -- a wider child predicate lets a proof create a
    child where Linux creates none.  A definition conjoined with [ext] can
    only narrow.  A pid namespace, which gives the child two numbers, passes
    an [ext] relating them; it does not add an alternative. *)
Definition child_pid (ext : config -> Pid -> Prop) (c' : config) (q : Pid)
    : Prop :=
  ms_gpr (cfg_ms c') 0 = q /\ ext c' q.

Definition child_pid_core : config -> Pid -> Prop :=
  child_pid (fun _ _ => True).

(** The argument shape the reap arm answers: wait4(-1, stat_addr, 0, NULL).
    [Exit.WAIT_ANY32] is Exit.v:33.  [Exit.wait4_spec] answers the WNOHANG
    shape and declines this one. *)
Definition wait4_blocking_args (ms : machine_state) : option word :=
  if negb (Z.eqb (bv_unsigned (pid32 (ms_gpr ms 0))) WAIT_ANY32) then None
  else if negb (w_is0 (waitopts32 (ms_gpr ms 2))) then None
  else if negb (w_is0 (ms_gpr ms 3)) then None
  else Some (ms_gpr ms 1).

(** A boolean, for the reason [clone_success_b] is one.  It REQUIRES a
    pending 260: reading the argument registers alone would let the arm fire
    at an ordinary instruction whose registers happen to match, and
    [Run.advance_past_svc] adds 4 to the pc unconditionally (Run.v:191-197),
    so that would skip an instruction and then make a different call. *)
Definition wait4_intercept_b (c : config) : bool :=
  match ms_svc_pending (cfg_ms c) with
  | None => false
  | Some x8 =>
      Z.eqb (bv_unsigned x8) 260%Z
      && match wait4_blocking_args (cfg_ms c) with
         | Some _ => true
         | None => false
         end
  end.

(* =========================================================================
   Promotion: a private descriptor becomes a shared description at a clone
   ========================================================================= *)

(** The shared reading of a private entry, and the offset it was holding.
    [None] for the kinds with no mutable kernel-side offset, which stay in
    [State.m_fd]; see [OfdWhat] for why [FdChannel] is among them.  An
    opaque descriptor ([FdOpaque], C1) stays per-process too: a namespace
    file's state is in [sh_ns] already, named by its handle, so both
    processes see one object; the other opaque kinds are per-process
    copies, whose arms answer a read of another process's state as the
    environment's. *)
Definition fd_shared_view (e : FdEntry) : option (OfdWhat * word) :=
  match e with
  | FdFile p off   => Some (OfdFile p FmR,  off)
  | FdFileW p off  => Some (OfdFile p FmW,  off)
  | FdFileA p off  => Some (OfdFile p FmA,  off)
  | FdFileRW p off => Some (OfdFile p FmRW, off)
  | FdPipe id w    => Some (OfdPipe id w,   Z_to_bv 64 0)
  | FdSocket sk    => Some (OfdSocket sk,   Z_to_bv 64 0)
  | FdChannel _ | FdDir | FdDevNull _ _ | FdUrandom | FdOpaque _ => None
  end.

(** PROMOTE one descriptor out of a private table into the shared one, with
    [ofd_refs] counting BOTH tables.  Two is right and not one: after the
    clone the parent and the child each name it. *)
Definition promote_one (S : shared) (i : OfdId) (fd : word) (e : FdEntry)
    : option (shared * (word * OfdId)) :=
  match fd_shared_view e with
  | None => None
  | Some (what, off) =>
      Some (mkShared (sh_fsys S) (sh_io S)
                     ((i, mkOfd what off (Z_to_bv 64 0) (Z_to_bv 64 2))
                        :: sh_ofd S)
                     (sh_pipes S) (sh_ns S),
            (fd, i))
  end.

(* =========================================================================
   The child a successful clone creates
   ========================================================================= *)

(** The child's machine state: the parent's successor with a0 = 0, and the
    stack pointer the call asked for.  [set_reg] takes a PHYSICAL register
    number; a0 is x10 and sp is x2.

    [newsp] is honoured when it is non-zero.  Legacy [clone] accepts an
    arbitrary one and it changes the CHILD's stack pointer (Fork.v:753-764);
    zero means the child keeps the parent's, which is what [fork] does. *)
Definition child_ms (c c' : config) : machine_state :=
  let newsp := ms_gpr (cfg_ms c) 1 in
  let base := set_reg (cfg_ms c') 10 (Z_to_bv 64 0) in
  if w_is0 newsp then base else set_reg base 2 newsp.

(** The child's process record: the parent's, with the fields that are the
    CHILD's own cleared.

    [procst_children] because the child has none -- and copying the parent's
    pre-clone record is not enough, because on a SECOND clone the parent's is
    already set.  [procst_tid] because the child's differs on Linux, and
    because clone admission itself reads it (Fork.v:679-681), so declining
    [getpid] does not make an inherited one unobservable.  On C1's record,
    [procst_sigpipe_pending] is false (a new thread group starts with no
    pending signal), [procst_pdeath_signal] is 0 ([copy_process] clears
    it), and the two launch facts ([procst_channel_reader],
    [procst_sigpipe_default]) are copied. *)
Definition child_proc (ps : ProcState) : ProcState :=
  mkProcState (procst_halted ps) None (procst_creds ps)
              (procst_setsid_succeeded ps) (procst_sigmask ps)
              false (procst_utsname ps) (procst_sigaltstack_installed ps)
              (* [procst_sigabrt_pending] is FALSE in the child, not
                 copied: a new thread group starts with no pending signal
                 (Linux [copy_process]).  Copying the parent's would give
                 the child a signal it never received.  [forkwait] raises
                 none, so no statement of this branch changes, but the
                 child-entry lemmas read [child_proc] and must not read a
                 wrong value.  (Found in review, 2026-11-01.) *)
              (procst_killed ps) false
              (procst_abort_terminal ps) (procst_statpins ps)
              false (procst_channel_reader ps) (procst_sigpipe_default ps)
              (Z_to_bv 64 0).

Definition with_proc (ps : ProcState) (m : Model) : Model :=
  mkModelOf (m_fd m) (m_vm m) (m_io m) (m_fsys m) ps (m_lim m) (m_time m).

Definition child_entry (e : ProcessEntry) (c c' : config) (q : Pid)
    : ProcessEntry :=
  mkEntry q (Some (pe_pid e)) (child_ms c c')
          (clear_shared (with_proc (child_proc (m_proc (pe_model e)))
                                   (pe_model e)))
          (pe_ofd e) (pe_nsctx e).

(** The configuration a successful clone steps to. *)
Definition clone_result (P : pconfig) (e : ProcessEntry) (c' : config)
    (q : Pid) : pconfig :=
  mkPCfg (replace_in (pcfg_procs P) (pe_pid e) (pe_absorb e c')
            ++ [(q, child_entry e (pe_cfg (pcfg_shared P) e) c' q)])
         (pcfg_root P)
         (shared_absorb (pcfg_shared P) c').

(** The entry a step added, if it added one.  [clone_result] appends, so the
    added entry is the last one, and the length test is what says a step
    added anything at all. *)
Definition child_projection (P P' : pconfig) : option (ProcessEntry * shared) :=
  if Nat.ltb (List.length (pcfg_procs P)) (List.length (pcfg_procs P'))
  then match List.last (List.map (fun kv => Some (snd kv)) (pcfg_procs P'))
               None with
       | Some e => Some (e, pcfg_shared P')
       | None => None
       end
  else None.

(* =========================================================================
   The wait status an entry reports once it is over
   ========================================================================= *)

(** A FUNCTION, and it must stay one: every reap proof and the projection
    theorem read it, and turning it into a relation later costs a re-walk of
    both.

    A normal exit reports the masked code shifted left 8.  [Exit.exit_spec]
    already applied the mask before [set_halted], and the shift is what
    [exit_group] does to its argument:

      kernel/exit.c:1131, Linux v6.18.46 (commit 1f99e9ab748f)
        do_group_exit((error_code & 0xff) << 8);

    A death by signal reports the signal in the low seven bits.  [dumped] is
    the WCOREDUMP bit, 0x80, which [coredump_finish] ORs in when the dump was
    written and no further fatal signal is pending:

      fs/coredump.c:557-558, same version
        if (core_dumped && !__fatal_signal_pending(current))
                current->signal->group_exit_code |= 0x80;

    Whether it was written depends on RLIMIT_CORE, the task's dumpable flag
    and core_pattern, none of which this model carries, so the bit is a
    PARAMETER here rather than a derived value.  [State.limst_core] already
    pins RLIMIT_CORE at its first read, so a later refinement constrains the
    choice instead of replacing it. *)
Definition pe_status (dumped : bool) (e : ProcessEntry) : option word :=
  match m_halted (pe_model e), m_killed (pe_model e) with
  | Some code, None =>
      Some (bv_mul (bv_and code (Z_to_bv 64 255)) (Z_to_bv 64 256))
  | Some sig, Some _ =>
      Some (bv_or (bv_and sig (Z_to_bv 64 127))
                  (if dumped then Z_to_bv 64 128 else Z_to_bv 64 0))
  | None, _ => None
  end.


(* =========================================================================
   The relation
   ========================================================================= *)

Definition absorb (P : pconfig) (e : ProcessEntry) (c' : config) : pconfig :=
  mkPCfg (replace_in (pcfg_procs P) (pe_pid e) (pe_absorb e c'))
         (pcfg_root P)
         (shared_absorb (pcfg_shared P) c').

(** ONE TRANSITION OF THE SYSTEM, WITH THE STEPPING PID AS AN INDEX.

    The index is not decoration.  An earlier draft defined the per-process
    relation on top of an unindexed one as
      [exists e, look P p = Some e /\ pe_pid e = p /\ pstep_cfg ... ]
    and that is WRONG: the last conjunct says only that SOME entry stepped, so
    a step by any entry satisfies it for every [p] in the table, and a
    consumer's lineage-restricted relation built on it would not restrict to
    the lineage at all.  Indexing the inductive is what makes
    [pstep_at_stepped_by] below true rather than merely plausible.

    The scheduler choice is the index: two choices of entry give two
    successors, and that is the whole of the interleaving nondeterminism. *)
Inductive pstep_at (segs : list Segment) (cfg : SpuriousCfg)
  : Pid -> pconfig -> list event -> pstep_to -> Prop :=
| pstep_other : forall P e evs c',
    look P (pe_pid e) = Some e ->
    sstep_cfg segs cfg (pe_cfg (pcfg_shared P) e) evs (SNext c') ->
    clone_success_b (pe_cfg (pcfg_shared P) e) c' = false ->
    wait4_intercept_b (pe_cfg (pcfg_shared P) e) = false ->
    multiproc_allowed P (pe_cfg (pcfg_shared P) e) = true ->
    pstep_at segs cfg (pe_pid e) P evs (PNext (absorb P e c'))
(** THE ERROR TRANSITION, and it must EXCLUDE the intercepted wait.
    A blocking [wait4(-1, _, 0, NULL)] is [unmodeled] in the released spec
    (Exit.v:247) and [Run.sstep_cfg_syscall_unmodeled] (Run.v:1832-1836) turns
    that into [SError].  Lifting every [SError] unqualified would send the
    waiting parent to [PError] and the sleep of this core would never happen.
    So the intercepted shape is excluded here, and it is the SECOND place --
    beside a successful clone -- where this relation and the released one
    differ.  [pstep_single]'s second hypothesis is exactly that exclusion. *)
(** THE CLONE ARM.  The parent's half is the RELEASED step, unedited: flag
    word, errno list, pid envelope, [State.with_children] and the
    [Fork.clone_no_shared_file_b] gate are all [Sys.Kernel.Fork]'s.  This arm
    only adds the child, and it fires only when the released step really
    created one -- so a FAILING clone is [pstep_other]'s business and keeps
    the released behaviour exactly. *)
| pstep_clone : forall P e evs c' q,
    look P (pe_pid e) = Some e ->
    sstep_cfg segs cfg (pe_cfg (pcfg_shared P) e) evs (SNext c') ->
    clone_success_b (pe_cfg (pcfg_shared P) e) c' = true ->
    child_pid_core c' q ->
    look P q = None ->
    multiproc_allowed P (pe_cfg (pcfg_shared P) e) = true ->
    pstep_at segs cfg (pe_pid e) P evs (PNext (clone_result P e c' q))
(** THE REAP ARM, the one operation with no single-process counterpart.

    It REQUIRES a pending 260 through [wait4_intercept_b]: reading the
    argument registers alone would let it fire at an ordinary instruction
    whose registers happened to match, and [Run.advance_past_svc] adds 4 to
    the pc unconditionally.

    The copy-out is checked BEFORE the reap, under the same writability test
    the spec layer uses.  Linux is lossy the other way -- [kernel_wait4]
    reaps and drops the pid reference before [put_user], so a failed copy
    destroys the status (Exit.v:240-243) -- and that path is declined here
    rather than approximated.  [materialize_model_accesses] is applied
    exactly as [Run.sstep_cfg_syscall] applies it (Run.v:1805-1806), so a
    copy-out into a lazy anonymous mapping is charged against the budget.

    A killed child is declined: its status is the WIFSIGNALED encoding, and
    [pe_status]'s second arm is written but not reachable until the premise
    below comes off.  No event is emitted: a reap is none of [State.ReadEv],
    [WriteEv], [ExitEv] or [KillEv], and the child's own [ExitEv] already
    recorded the status. *)
| pstep_wait_reap : forall P e q ez x8 stat_addr status eff model'' dumped,
    look P (pe_pid e) = Some e ->
    m_halted (pe_model e) = None ->
    ms_svc_pending (pe_ms e) = Some x8 ->
    wait4_intercept_b (pe_cfg (pcfg_shared P) e) = true ->
    wait4_blocking_args (pe_ms e) = Some stat_addr ->
    look P q = Some ez ->
    (* THE REAPED CHILD IS NOT THE REAPING PARENT.  Without this the arm
       can, on a malformed configuration, drop the entry it is also
       replacing: that needs [pe_parent e = Some (pe_pid e)], a process
       that is its own parent, which [pconfig_wf] excludes -- but
       [pconfig_wf] is not a premise here, and every other condition of
       this relation is in the arm rather than in an invariant.  It
       reaches no statement: [pinit_config] gives [pconfig_wf] and no arm
       breaks it, so the excluded case is unreachable from any start state
       a statement quantifies over.  (Found by trying to prove that the
       entry count decides which arm fired, 2026-11-01.) *)
    q <> pe_pid e ->
    pe_parent ez = Some (pe_pid e) ->
    m_killed (pe_model ez) = None ->
    pe_status dumped ez = Some status ->
    read_bytes_map (in_wmem (sys_input segs (pe_ms e) x8)) stat_addr
      (Z_to_bv 64 4) <> None ->
    eff = mkEffect q [(stat_addr, Z_to_le_bytes 4 (bv_unsigned status))] [] ->
    materialize_model_accesses (cfg_model (pe_cfg (pcfg_shared P) e))
      (syscall_effect_accesses eff) = Some model'' ->
    pstep_at segs cfg (pe_pid e) P []
      (PNext (mkPCfg
                (drop_in
                   (replace_in (pcfg_procs P) (pe_pid e)
                      (mkEntry (pe_pid e) (pe_parent e)
                         (advance_past_svc (apply_effect (pe_ms e) eff))
                         (clear_shared model'') (pe_ofd e) (pe_nsctx e)))
                   q)
                (pcfg_root P)
                (shared_absorb (pcfg_shared P) (mkCfg (pe_ms e) model''))))
| pstep_error : forall P e evs,
    look P (pe_pid e) = Some e ->
    sstep_cfg segs cfg (pe_cfg (pcfg_shared P) e) evs SError ->
    wait4_intercept_b (pe_cfg (pcfg_shared P) e) = false ->
    pstep_at segs cfg (pe_pid e) P evs PError
| pstep_outside : forall P e,
    look P (pe_pid e) = Some e ->
    m_halted (pe_model e) = None ->
    multiproc_allowed P (pe_cfg (pcfg_shared P) e) = false ->
    pstep_at segs cfg (pe_pid e) P [] PError.

(** The system steps when SOME entry does. *)
Definition pstep_cfg (segs : list Segment) (cfg : SpuriousCfg)
    (P : pconfig) (evs : list event) (r : pstep_to) : Prop :=
  exists p, pstep_at segs cfg p P evs r.

(** [p] is the entry that took this transition. *)
Definition stepped_by (segs : list Segment) (cfg : SpuriousCfg)
    (P : pconfig) (evs : list event) (r : pstep_to) (p : Pid) : Prop :=
  pstep_at segs cfg p P evs r.

Lemma pstep_at_sub : forall segs cfg p P evs r,
  pstep_at segs cfg p P evs r -> pstep_cfg segs cfg P evs r.
Proof. intros segs cfg p P evs r H. exists p. exact H. Qed.

Lemma pstep_at_stepped_by : forall segs cfg p P evs r,
  pstep_at segs cfg p P evs r -> stepped_by segs cfg P evs r p.
Proof. intros segs cfg p P evs r H. exact H. Qed.

(** Every transition has an actor.  Immediate now, and false for the draft
    the note above describes. *)
Lemma pstep_cfg_has_actor : forall segs cfg P evs r,
  pstep_cfg segs cfg P evs r -> exists p, pstep_at segs cfg p P evs r.
Proof. intros segs cfg P evs r H. exact H. Qed.

Lemma pstep_to_cases : forall r : pstep_to,
  (exists P, r = PNext P) \/ r = PError.
Proof. intros [P|]; [left; exists P; reflexivity | right; reflexivity]. Qed.

(* =========================================================================
   The single-process projection theorem
   ========================================================================= *)

(** The pid of the one process a released configuration becomes. *)
Definition one_pid : Pid := Z_to_bv 64 1.

(** The namespace context and state of a system that has entered no
    namespace come from [Ns.Tables] as [init_nsctx] and [empty_nsstate],
    NEVER from [mkNsCtx] or [mkNsState].  Those records grow -- within one
    hour of the first version, [NsState] went from two fields to seven and
    [NsCtx] from four to eight -- and a constructor application breaks on
    every new field, while a builder costs nothing.  [flat_view
    empty_nsstate = true], so [one_proc] is in the released world, which is
    what the single-process theorems rest on. *)

Definition one_entry (c : config) : ProcessEntry :=
  mkEntry one_pid None (cfg_ms c) (clear_shared (cfg_model c)) [] init_nsctx.

Definition one_proc (c : config) : pconfig :=
  mkPCfg [(one_pid, one_entry c)] one_pid
         (mkShared (m_fsys (cfg_model c)) (m_io (cfg_model c)) [] []
                   empty_nsstate).

Lemma one_proc_entry : forall c,
  look (one_proc c) one_pid = Some (one_entry c).
Proof.
  intros c. unfold look, one_proc, look_in. cbn.
  rewrite bv_eqb_same. reflexivity.
Qed.

(** Whatever pid a step picked, a one-process system has only this entry. *)
Lemma look_one_proc_inv : forall c p e,
  look (one_proc c) p = Some e -> e = one_entry c.
Proof.
  intros c p e H. unfold look, one_proc, look_in in H. cbn in H.
  destruct (bv_eqb one_pid p); congruence.
Qed.

(** And it picked [one_pid]. *)
Lemma look_one_proc_pid : forall c p e,
  look (one_proc c) p = Some e -> p = one_pid.
Proof.
  intros c p e H. unfold look, one_proc, look_in in H. cbn in H.
  destruct (bv_eqb one_pid p) eqn:Hb; [|discriminate].
  symmetry. apply bv_eqb_true_eq. exact Hb.
Qed.

(** The splice round-trips at a one-process system: the released view of the
    only entry is the configuration it was built from. *)
Lemma one_proc_view : forall c,
  pe_cfg (pcfg_shared (one_proc c)) (one_entry c) = c.
Proof. intros c. destruct c as [ms m]. destruct m. reflexivity. Qed.

(** At one entry the surface guard is unconditionally open, by its own first
    disjunct.  This is why the instruction case needs no side condition. *)
Lemma multiproc_allowed_one : forall c c',
  multiproc_allowed (one_proc c) c' = true.
Proof.
  intros c c'. unfold multiproc_allowed.
  destruct (ms_svc_pending (cfg_ms c')); reflexivity.
Qed.

Lemma absorb_one_proc : forall c c',
  absorb (one_proc c) (one_entry c) c' = one_proc c'.
Proof.
  intros c c'. unfold absorb, one_proc, one_entry, replace_in. cbn.
  rewrite bv_eqb_same.
  destruct c' as [ms' m']. destruct m'. reflexivity.
Qed.

(** No system call is pending: the next step is an instruction. *)
Definition at_instruction (c : config) : Prop :=
  ms_svc_pending (cfg_ms c) = None.

Lemma pstep_at_one_pid : forall segs cfg p c evs r,
  pstep_at segs cfg p (one_proc c) evs r -> p = one_pid.
Proof.
  intros segs cfg p c evs r Hp.
  inversion Hp; subst;
    match goal with
    | [ Hlook : look (one_proc c) _ = Some _ |- _ ] =>
        exact (look_one_proc_pid _ _ _ Hlook)
    end.
Qed.

(** In a one-process system, a step of [one_pid] is any step of the system. *)
Lemma pstep_at_one : forall segs cfg c evs r,
  pstep_at segs cfg one_pid (one_proc c) evs r
  <-> pstep_cfg segs cfg (one_proc c) evs r.
Proof.
  intros segs cfg c evs r. split.
  - apply pstep_at_sub.
  - intros [p Hp]. rewrite <- (pstep_at_one_pid _ _ _ _ _ _ Hp). exact Hp.
Qed.

(** THE PROJECTION, in four directions and then the two [iff]s.  Split that
    way on purpose: each half inverts a [pstep_at] whose outcome is already
    [PNext] or [PError], so two of the three arms are ruled out by their own
    conclusion and never have to be discharged by hand. *)

Lemma pstep_single_next_fwd : forall segs cfg c evs P',
  (forall c', sstep_cfg segs cfg c evs (SNext c') -> clone_success_b c c' = false) ->
  wait4_intercept_b c = false ->
  pstep_cfg segs cfg (one_proc c) evs (PNext P') ->
  exists c', P' = one_proc c' /\ sstep_cfg segs cfg c evs (SNext c').
Proof.
  intros segs cfg c evs P' Hcl Hwt Hp. destruct Hp as [p Hp].
  inversion Hp; subst;
    (* EVERY lookup hypothesis, not the first that matches: the reap arm has
       two of them, and normalising only one leaves its stepping entry
       abstract, so [one_proc_view] then has nothing to rewrite. *)
    repeat match goal with
           | [ H : look (one_proc c) _ = Some ?x |- _ ] =>
               rewrite (look_one_proc_inv _ _ _ H) in *
           end;
    rewrite one_proc_view in *.
  - (* pstep_other: the step this lemma is about *)
    match goal with
    | [ Hss : sstep_cfg _ _ _ _ (SNext ?c1) |- _ ] =>
        exists c1; split; [apply absorb_one_proc | exact Hss]
    end.
  - (* pstep_clone is excluded by the first hypothesis *)
    exfalso.
    match goal with
    | [ Hss : sstep_cfg _ _ _ _ (SNext ?c1),
        Hcs : clone_success_b _ ?c1 = true |- _ ] =>
        rewrite (Hcl _ Hss) in Hcs; discriminate
    end.
  - (* pstep_wait_reap is excluded by the second *)
    exfalso.
    match goal with
    | [ Hwi : wait4_intercept_b _ = true |- _ ] =>
        rewrite Hwt in Hwi; discriminate
    end.
Qed.

Lemma pstep_single_next_bwd : forall segs cfg c evs c',
  clone_success_b c c' = false ->
  wait4_intercept_b c = false ->
  sstep_cfg segs cfg c evs (SNext c') ->
  pstep_cfg segs cfg (one_proc c) evs (PNext (one_proc c')).
Proof.
  intros segs cfg c evs c' Hcl Hwt Hss.
  rewrite <- (absorb_one_proc c c').
  apply pstep_at_sub with (p := one_pid).
  apply pstep_other with (e := one_entry c).
  - apply one_proc_entry.
  - rewrite one_proc_view. exact Hss.
  - rewrite one_proc_view. exact Hcl.
  - rewrite one_proc_view. exact Hwt.
  - apply multiproc_allowed_one.
Qed.

Lemma pstep_single_err_fwd : forall segs cfg c evs,
  pstep_cfg segs cfg (one_proc c) evs PError ->
  sstep_cfg segs cfg c evs SError.
Proof.
  intros segs cfg c evs Hp. destruct Hp as [p Hp].
  inversion Hp; subst.
  - match goal with
    | [ Hlook : look (one_proc c) _ = Some _ |- _ ] =>
        rewrite (look_one_proc_inv _ _ _ Hlook) in *
    end.
    rewrite one_proc_view in *. assumption.
  - exfalso.
    match goal with
    | [ Hall : multiproc_allowed (one_proc c) _ = false |- _ ] =>
        rewrite multiproc_allowed_one in Hall; discriminate
    end.
Qed.

Lemma pstep_single_err_bwd : forall segs cfg c evs,
  wait4_intercept_b c = false ->
  sstep_cfg segs cfg c evs SError ->
  pstep_cfg segs cfg (one_proc c) evs PError.
Proof.
  intros segs cfg c evs Hwt Hss.
  apply pstep_at_sub with (p := one_pid).
  apply pstep_error with (e := one_entry c).
  - apply one_proc_entry.
  - rewrite one_proc_view. exact Hss.
  - rewrite one_proc_view. exact Hwt.
Qed.

(** A one-process system steps exactly as [Run.sstep_cfg] does, outside the
    two places this relation and the released one are MEANT to differ: a
    successful clone (the released one lets the parent continue with a child
    that does not exist) and an intercepted blocking [wait4] (which the
    released one answers [unmodeled]). *)
Theorem pstep_single_next : forall segs cfg c evs P',
  (forall c', sstep_cfg segs cfg c evs (SNext c') -> clone_success_b c c' = false) ->
  wait4_intercept_b c = false ->
  (pstep_cfg segs cfg (one_proc c) evs (PNext P')
   <-> exists c', P' = one_proc c' /\ sstep_cfg segs cfg c evs (SNext c')).
Proof.
  intros segs cfg c evs P' Hcl Hwt. split.
  - apply pstep_single_next_fwd; [exact Hcl | exact Hwt].
  - intros (c' & -> & Hss).
    apply pstep_single_next_bwd; [exact (Hcl _ Hss) | exact Hwt | exact Hss].
Qed.

Theorem pstep_single_err : forall segs cfg c evs,
  wait4_intercept_b c = false ->
  (pstep_cfg segs cfg (one_proc c) evs PError
   <-> sstep_cfg segs cfg c evs SError).
Proof.
  intros segs cfg c evs Hwt. split.
  - apply pstep_single_err_fwd.
  - apply (pstep_single_err_bwd _ _ _ _ Hwt).
Qed.

(** At an instruction both hypotheses are discharged, because each test
    begins by matching on [ms_svc_pending]. *)
Lemma clone_success_b_instr : forall c c',
  at_instruction c -> clone_success_b c c' = false.
Proof.
  intros c c' H. unfold clone_success_b, at_instruction in *.
  rewrite H. reflexivity.
Qed.

Lemma wait4_intercept_b_instr : forall c,
  at_instruction c -> wait4_intercept_b c = false.
Proof.
  intros c H. unfold wait4_intercept_b, at_instruction in *.
  rewrite H. reflexivity.
Qed.

Theorem pstep_instr_single_next : forall segs cfg c evs P',
  at_instruction c ->
  (pstep_cfg segs cfg (one_proc c) evs (PNext P')
   <-> exists c', P' = one_proc c' /\ sstep_cfg segs cfg c evs (SNext c')).
Proof.
  intros segs cfg c evs P' H. apply pstep_single_next.
  - intros c' _. apply clone_success_b_instr. exact H.
  - apply wait4_intercept_b_instr. exact H.
Qed.

Theorem pstep_instr_single_err : forall segs cfg c evs,
  at_instruction c ->
  (pstep_cfg segs cfg (one_proc c) evs PError
   <-> sstep_cfg segs cfg c evs SError).
Proof.
  intros segs cfg c evs H. apply pstep_single_err.
  apply wait4_intercept_b_instr. exact H.
Qed.

(** THE FILE SYSTEM IS GLOBAL, and this says so: the per-entry copy is blank
    at the one entry a one-process system has, so nothing can read it. *)
Lemma fs_only_in_shared_one : forall c,
  m_fsys (pe_model (one_entry c)) = empty_fsys.
Proof. intros c. reflexivity. Qed.

(** THE OFFSETS ROUND-TRIP TOO, and this says so rather than leaving a
    consumer to notice.  A parent that keeps its standard descriptors open
    across a clone, and passes further descriptors to its child at exec,
    needs the projection to carry back the POSITION of each description and
    not merely the entries.  At one process every descriptor is private, its
    offset is inside its [State.FdEntry] in [m_fd], and [pe_ofd] is empty;
    the whole table comes back because the whole configuration does. *)
Lemma one_proc_offsets : forall c,
  m_fds (cfg_model (pe_cfg (pcfg_shared (one_proc c)) (one_entry c)))
    = m_fds (cfg_model c)
  /\ m_pipes (cfg_model (pe_cfg (pcfg_shared (one_proc c)) (one_entry c)))
    = m_pipes (cfg_model c)
  /\ pe_ofd (one_entry c) = [].
Proof.
  intros c. rewrite one_proc_view.
  split; [reflexivity | split; reflexivity].
Qed.

(* =========================================================================
   Well-formedness
   ========================================================================= *)

(** The structural invariant every arm must preserve.  Stated once, because
    several results silently assume parts of it: the key of the table is the
    entry's own pid, the root is present and parentless, and every parent
    link resolves. *)
Definition pconfig_wf (P : pconfig) : Prop :=
  (forall kv, List.In kv (pcfg_procs P) -> fst kv = pe_pid (snd kv))
  /\ (exists e, look P (pcfg_root P) = Some e /\ pe_parent e = None)
  /\ (forall kv, List.In kv (pcfg_procs P) ->
        match pe_parent (snd kv) with
        | None => pe_pid (snd kv) = pcfg_root P
        | Some q => exists f, look P q = Some f
        end).

Lemma pconfig_wf_one_proc : forall c, pconfig_wf (one_proc c).
Proof.
  intros c. unfold pconfig_wf. split; [|split].
  - intros kv Hkv. cbn in Hkv. destruct Hkv as [<-|[]]. reflexivity.
  - exists (one_entry c). split; [apply one_proc_entry | reflexivity].
  - intros kv Hkv. cbn in Hkv. destruct Hkv as [<-|[]]. reflexivity.
Qed.

(* =========================================================================
   One inversion lemma per arm
   ========================================================================= *)

(** WHY THESE EXIST, and it is a fact about extending this relation rather
    than a convenience for one proof.

    A proof about a concrete program inverts a step at every configuration it
    walks through -- forty sites for a program of this size.  Each [inversion]
    names every constructor, so ADDING A CONSTRUCTOR BREAKS EVERY SITE.  The
    planned [ext] parameter adds two constructors and a premise to three
    others, which would be forty rewrites of proof script.

    Routed through the lemmas below instead, the cost of that change is
    re-proving these three and nothing else: a program proof sees only
    [pstep_next_cases] and [pstep_error_cases], whose STATEMENTS do not
    mention the constructor set.  At [no_ext] the two new constructors die by
    [discriminate] on [ext_claims i = true], once, inside each lemma.

    Keep that property when adding an arm: give the arm a disjunct here, and
    do not let a program proof invert [pstep_at] directly. *)

(** A step to a successor is one of the three producing arms. *)
Lemma pstep_next_cases : forall segs cfg p P evs P',
  pstep_at segs cfg p P evs (PNext P') ->
  exists e,
    look P p = Some e /\ pe_pid e = p /\
    ( (exists c',
         sstep_cfg segs cfg (pe_cfg (pcfg_shared P) e) evs (SNext c')
         /\ clone_success_b (pe_cfg (pcfg_shared P) e) c' = false
         /\ wait4_intercept_b (pe_cfg (pcfg_shared P) e) = false
         /\ P' = absorb P e c')
      \/ (exists c' q,
            sstep_cfg segs cfg (pe_cfg (pcfg_shared P) e) evs (SNext c')
            /\ clone_success_b (pe_cfg (pcfg_shared P) e) c' = true
            /\ child_pid_core c' q
            /\ look P q = None
            /\ P' = clone_result P e c' q)
      \/ (wait4_intercept_b (pe_cfg (pcfg_shared P) e) = true /\ evs = []) ).
Proof.
  intros segs cfg p P evs P' Hp.
  inversion Hp; subst.
  - (* pstep_other *)
    eexists. split; [eassumption | split; [reflexivity|]].
    left. eexists.
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    reflexivity.
  - (* pstep_clone.  The splits are explicit rather than [repeat split]:
       [child_pid_core] unfolds to a conjunction, so [repeat split] would
       take it apart and leave goals no hypothesis matches. *)
    eexists. split; [eassumption | split; [reflexivity|]].
    right; left. do 2 eexists.
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. reflexivity.
  - (* pstep_wait_reap *)
    eexists. split; [eassumption | split; [reflexivity|]].
    right; right. split; [assumption | reflexivity].
Qed.

(** A step to the error transition is one of the two refusing arms. *)
Lemma pstep_error_cases : forall segs cfg p P evs,
  pstep_at segs cfg p P evs PError ->
  exists e,
    look P p = Some e /\ pe_pid e = p /\
    ( (sstep_cfg segs cfg (pe_cfg (pcfg_shared P) e) evs SError
       /\ wait4_intercept_b (pe_cfg (pcfg_shared P) e) = false)
      \/ (multiproc_allowed P (pe_cfg (pcfg_shared P) e) = false /\ evs = []) ).
Proof.
  intros segs cfg p P evs Hp.
  inversion Hp; subst.
  - eexists. split; [eassumption | split; [reflexivity|]].
    left. split; assumption.
  - eexists. split; [eassumption | split; [reflexivity|]].
    right. split; [assumption | reflexivity].
Qed.

(** The splice does not disturb the halt flag: [set_fsys] and [set_io]
    rebuild the model around the same [State.ProcState]. *)
Lemma m_halted_pe_cfg : forall S e,
  m_halted (cfg_model (pe_cfg S e)) = m_halted (pe_model e).
Proof. intros S e. reflexivity. Qed.

(** A released step requires its configuration to be running.  Proved here
    rather than imported: the same fact is [MustExit.sstep_cfg_not_halted],
    but [EquivalenceDefinition] depends on this directory and not the other
    way round, so this file cannot reach it.  Every [Run.sstep_cfg]
    constructor carries the premise (Run.v:1785 and its siblings). *)
Lemma sstep_cfg_halted_none : forall segs cfg c evs st,
  sstep_cfg segs cfg c evs st -> m_halted (cfg_model c) = None.
Proof. intros segs cfg c evs st H. inversion H; subst; assumption. Qed.

(** The entry that steps is present and is running.  Stated as an existential
    rather than against a supplied entry, so each arm supplies its own and no
    branch has to reconcile two lookups of the same pid. *)
Lemma pstep_at_not_halted : forall segs cfg p P evs r,
  pstep_at segs cfg p P evs r ->
  exists e, look P p = Some e /\ m_halted (pe_model e) = None.
Proof.
  intros segs cfg p P evs r Hp.
  inversion Hp; subst; eexists; split; try eassumption;
    match goal with
    | [ Hss : sstep_cfg _ _ _ _ _ |- _ ] =>
        let Hh := fresh "Hh" in
        pose proof (sstep_cfg_halted_none _ _ _ _ _ Hss) as Hh;
        rewrite m_halted_pe_cfg in Hh; exact Hh
    end.
Qed.

(* =========================================================================
   A step extension: answers the released step does not give, inside the core
   ========================================================================= *)

(** [pstep_x_at ext cenv] is [pstep_at] with an extension
    ([Ns.Ext.ExtSpec]): a pending call the extension CLAIMS is answered by
    [ext_spec] on the SPLICED model ([pe_cfg], never [pe_model], whose file
    system and I/O are blank), the entry's namespace context and the shared
    namespace state, filtered by [ext_refusal] as the released step is by
    [Run.spurious_refusal_cfg]; the context and state it returns are
    written into [pe_nsctx] and [sh_ns].  An unclaimed call is the released
    step, unchanged.  A clone is the released clone, and [ext_clone] says
    what it does to the namespace model: the child's context and the next
    state, the state after a failure, or no answer.  A claimed call while
    other entries are live is admitted when the core's own guard or
    [ext_multiproc] admits it.

    [cenv] ([Ns.Ext.CloneEnv]) names the clone failures a run admits.  It
    is an explicit argument so that a statement shows it:
    [Ns.Ext.any_clone_failure] admits every failure
    ([pstep_x_at_any_clone_failure]: it is the largest), and a narrower one
    is an environment premise of the statement that names it.

    [pstep_at] is untouched; [pstep_at_no_ext_iff] is the two relations'
    equality at [no_ext] and [any_clone_failure], and
    [pstep_x_at_released_iff] at any extension that leaves every entry of a
    configuration to the released step. *)

Definition pending_input (segs : list Segment) (c : config) : option SyscallInput :=
  match ms_svc_pending (cfg_ms c) with
  | Some x8 => Some (sys_input segs (cfg_ms c) x8)
  | None => None
  end.

Definition claimed_at (ext : ExtSpec) (segs : list Segment) (c : config) : bool :=
  match pending_input segs c with
  | Some i => ext_claims ext i
  | None => false
  end.

(** One process's step under the extension, with the context and state it
    leaves.  Each claimed arm mirrors the [Run.sstep_cfg] arm of the same
    shape. *)
Inductive xsstep (ext : ExtSpec) (segs : list Segment) (cfg : SpuriousCfg)
    (ctx : NsCtx) (st : NsState)
  : config -> list event -> step_to -> NsCtx -> NsState -> Prop :=
| xs_released : forall c evs r,
    claimed_at ext segs c = false ->
    sstep_cfg segs cfg c evs r ->
    xsstep ext segs cfg ctx st c evs r ctx st
| xs_ok : forall ms model x8 eff model' model'' ctx' st' evs,
    m_halted model = None ->
    ms_svc_pending ms = Some x8 ->
    ext_claims ext (sys_input segs ms x8) = true ->
    ext_spec ext (sys_input segs ms x8) model ctx st (EOk eff model' ctx' st' evs) ->
    ~ ext_refusal ext cfg (sys_input segs ms x8) model ctx st eff ->
    m_halted model' = None ->
    materialize_model_accesses model' (syscall_effect_accesses eff) = Some model'' ->
    xsstep ext segs cfg ctx st (mkCfg ms model) evs
      (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model'')) ctx' st'
| xs_materialization_fault : forall ms model x8 eff model' ctx' st' evs,
    m_halted model = None ->
    ms_svc_pending ms = Some x8 ->
    ext_claims ext (sys_input segs ms x8) = true ->
    ext_spec ext (sys_input segs ms x8) model ctx st (EOk eff model' ctx' st' evs) ->
    ~ ext_refusal ext cfg (sys_input segs ms x8) model ctx st eff ->
    m_halted model' = None ->
    materialize_model_accesses model' (syscall_effect_accesses eff) = None ->
    xsstep ext segs cfg ctx st (mkCfg ms model) [] SError ctx st
| xs_exit : forall ms model x8 eff model' ctx' st' evs code,
    m_halted model = None ->
    ms_svc_pending ms = Some x8 ->
    ext_claims ext (sys_input segs ms x8) = true ->
    ext_spec ext (sys_input segs ms x8) model ctx st (EOk eff model' ctx' st' evs) ->
    m_halted model' = Some code ->
    m_killed model' = None ->
    xsstep ext segs cfg ctx st (mkCfg ms model) (evs ++ [ExitEv code (m_fs model')])
      (SNext (mkCfg ms model')) ctx' st'
| xs_killed : forall ms model x8 eff model' ctx' st' evs sig,
    m_halted model = None ->
    ms_svc_pending ms = Some x8 ->
    ext_claims ext (sys_input segs ms x8) = true ->
    ext_spec ext (sys_input segs ms x8) model ctx st (EOk eff model' ctx' st' evs) ->
    m_killed model' = Some sig ->
    xsstep ext segs cfg ctx st (mkCfg ms model) (evs ++ [KillEv sig (m_fs model')])
      (SNext (mkCfg ms model')) ctx' st'
| xs_unmodeled : forall ms model x8,
    m_halted model = None ->
    ms_svc_pending ms = Some x8 ->
    ext_claims ext (sys_input segs ms x8) = true ->
    ext_spec ext (sys_input segs ms x8) model ctx st EUnmodeled ->
    xsstep ext segs cfg ctx st (mkCfg ms model) [] SError ctx st.

Definition with_sh_ns (S : shared) (st : NsState) : shared :=
  mkShared (sh_fsys S) (sh_io S) (sh_ofd S) (sh_pipes S) st.

Definition with_nsctx (e : ProcessEntry) (ctx : NsCtx) : ProcessEntry :=
  mkEntry (pe_pid e) (pe_parent e) (pe_ms e) (pe_model e) (pe_ofd e) ctx.

Definition absorb_x (P : pconfig) (e : ProcessEntry) (c' : config) (ctx' : NsCtx)
    (st' : NsState) : pconfig :=
  mkPCfg (replace_in (pcfg_procs P) (pe_pid e) (with_nsctx (pe_absorb e c') ctx'))
         (pcfg_root P)
         (with_sh_ns (shared_absorb (pcfg_shared P) c') st').

Definition clone_result_x (P : pconfig) (e : ProcessEntry) (c' : config) (q : Pid)
    (child : NsCtx) (st' : NsState) : pconfig :=
  mkPCfg (replace_in (pcfg_procs P) (pe_pid e) (pe_absorb e c')
            ++ [(q, with_nsctx (child_entry e (pe_cfg (pcfg_shared P) e) c' q) child)])
         (pcfg_root P)
         (with_sh_ns (shared_absorb (pcfg_shared P) c') st').

(** The parent's configuration after a clone, when the extension gives
    its call a return value of its own ([CnOk]'s [ret]: the child's pid in
    the caller's pid namespace): a0 holds that value instead of the core's
    pid. *)
Definition with_ret (c : config) (ret : option Z) : config :=
  match ret with
  | None => c
  | Some v => mkCfg (set_reg (cfg_ms c) 10 (Z_to_bv 64 v)) (cfg_model c)
  end.

Definition clone_pending_b (c : config) : bool :=
  match ms_svc_pending (cfg_ms c) with
  | Some x8 => clone_sysno (bv_unsigned x8)
  | None => false
  end.

(** The flag word of a pending clone: argument 0 of [clone] (220);
    [clone3] (435) answers only the fork image, whose word is [SIGCHLD]. *)
Definition clone_flags_of (c : config) : Z :=
  match ms_svc_pending (cfg_ms c) with
  | Some x8 => if Z.eqb (bv_unsigned x8) 220 then bv_unsigned (ms_gpr (cfg_ms c) 0) else SIGCHLD
  | None => 0%Z
  end.

Definition multiproc_ok (ext : ExtSpec) (segs : list Segment) (P : pconfig)
    (e : ProcessEntry) : bool :=
  let c := pe_cfg (pcfg_shared P) e in
  multiproc_allowed P c
  || match pending_input segs c with
     | Some i => ext_claims ext i
                 && ext_multiproc ext i (cfg_model c) (pe_nsctx e) (sh_ns (pcfg_shared P))
     | None => false
     end.

(** ONE TRANSITION OF THE SYSTEM UNDER AN EXTENSION, indexed by the pid
    that steps, as [pstep_at] is. *)
Inductive pstep_x_at (ext : ExtSpec) (cenv : CloneEnv) (segs : list Segment) (cfg : SpuriousCfg)
  : Pid -> pconfig -> list event -> pstep_to -> Prop :=
| px_other : forall P e evs c' ctx' st',
    look P (pe_pid e) = Some e ->
    xsstep ext segs cfg (pe_nsctx e) (sh_ns (pcfg_shared P))
      (pe_cfg (pcfg_shared P) e) evs (SNext c') ctx' st' ->
    clone_pending_b (pe_cfg (pcfg_shared P) e) = false ->
    wait4_intercept_b (pe_cfg (pcfg_shared P) e) = false ->
    multiproc_ok ext segs P e = true ->
    pstep_x_at ext cenv segs cfg (pe_pid e) P evs (PNext (absorb_x P e c' ctx' st'))
| px_clone : forall P e evs c' q child ret st',
    look P (pe_pid e) = Some e ->
    claimed_at ext segs (pe_cfg (pcfg_shared P) e) = false ->
    sstep_cfg segs cfg (pe_cfg (pcfg_shared P) e) evs (SNext c') ->
    clone_success_b (pe_cfg (pcfg_shared P) e) c' = true ->
    child_pid_core c' q ->
    look P q = None ->
    multiproc_allowed P (pe_cfg (pcfg_shared P) e) = true ->
    ext_clone ext (clone_flags_of (pe_cfg (pcfg_shared P) e))
      (cfg_model (pe_cfg (pcfg_shared P) e)) (pe_nsctx e) (sh_ns (pcfg_shared P))
      (bv_unsigned q) (CnOk child ret st') ->
    pstep_x_at ext cenv segs cfg (pe_pid e) P evs
      (PNext (clone_result_x P e (with_ret c' ret) q child st'))
(** A FAILED clone is the released failure, with the state [ext_clone]
    says the failure leaves.  Its errno comes from the released step
    ([sstep_cfg] above), so under a forced-only configuration a refusal the
    released filter ([Run.spurious_refusal_cfg], Run.v:2019) drops is no
    step here either; and the run's clone environment [cenv] must admit
    the failure. *)
| px_clone_fail : forall P e evs c' en hq st',
    look P (pe_pid e) = Some e ->
    claimed_at ext segs (pe_cfg (pcfg_shared P) e) = false ->
    sstep_cfg segs cfg (pe_cfg (pcfg_shared P) e) evs (SNext c') ->
    clone_pending_b (pe_cfg (pcfg_shared P) e) = true ->
    clone_success_b (pe_cfg (pcfg_shared P) e) c' = false ->
    ms_gpr (cfg_ms c') 0 = errno_ret en ->
    multiproc_allowed P (pe_cfg (pcfg_shared P) e) = true ->
    ext_clone ext (clone_flags_of (pe_cfg (pcfg_shared P) e))
      (cfg_model (pe_cfg (pcfg_shared P) e)) (pe_nsctx e) (sh_ns (pcfg_shared P))
      hq (CnErr en st') ->
    cenv (clone_flags_of (pe_cfg (pcfg_shared P) e))
      (cfg_model (pe_cfg (pcfg_shared P) e)) (pe_nsctx e) (sh_ns (pcfg_shared P)) hq en st' ->
    pstep_x_at ext cenv segs cfg (pe_pid e) P evs (PNext (absorb_x P e c' (pe_nsctx e) st'))
| px_clone_unmodeled : forall P e evs c' hq,
    look P (pe_pid e) = Some e ->
    claimed_at ext segs (pe_cfg (pcfg_shared P) e) = false ->
    sstep_cfg segs cfg (pe_cfg (pcfg_shared P) e) evs (SNext c') ->
    clone_pending_b (pe_cfg (pcfg_shared P) e) = true ->
    multiproc_allowed P (pe_cfg (pcfg_shared P) e) = true ->
    ext_clone ext (clone_flags_of (pe_cfg (pcfg_shared P) e))
      (cfg_model (pe_cfg (pcfg_shared P) e)) (pe_nsctx e) (sh_ns (pcfg_shared P))
      hq CnUnmodeled ->
    pstep_x_at ext cenv segs cfg (pe_pid e) P [] PError
(** A clone the extension claims has no answer: the core creates children,
    an extension does not. *)
| px_clone_claimed : forall P e,
    look P (pe_pid e) = Some e ->
    m_halted (pe_model e) = None ->
    clone_pending_b (pe_cfg (pcfg_shared P) e) = true ->
    claimed_at ext segs (pe_cfg (pcfg_shared P) e) = true ->
    pstep_x_at ext cenv segs cfg (pe_pid e) P [] PError
| px_wait_reap : forall P e q ez x8 stat_addr status eff model'' dumped,
    look P (pe_pid e) = Some e ->
    claimed_at ext segs (pe_cfg (pcfg_shared P) e) = false ->
    m_halted (pe_model e) = None ->
    ms_svc_pending (pe_ms e) = Some x8 ->
    wait4_intercept_b (pe_cfg (pcfg_shared P) e) = true ->
    wait4_blocking_args (pe_ms e) = Some stat_addr ->
    look P q = Some ez ->
    q <> pe_pid e ->
    pe_parent ez = Some (pe_pid e) ->
    m_killed (pe_model ez) = None ->
    pe_status dumped ez = Some status ->
    read_bytes_map (in_wmem (sys_input segs (pe_ms e) x8)) stat_addr
      (Z_to_bv 64 4) <> None ->
    eff = mkEffect q [(stat_addr, Z_to_le_bytes 4 (bv_unsigned status))] [] ->
    materialize_model_accesses (cfg_model (pe_cfg (pcfg_shared P) e))
      (syscall_effect_accesses eff) = Some model'' ->
    pstep_x_at ext cenv segs cfg (pe_pid e) P []
      (PNext (mkPCfg
                (drop_in
                   (replace_in (pcfg_procs P) (pe_pid e)
                      (mkEntry (pe_pid e) (pe_parent e)
                         (advance_past_svc (apply_effect (pe_ms e) eff))
                         (clear_shared model'') (pe_ofd e) (pe_nsctx e)))
                   q)
                (pcfg_root P)
                (shared_absorb (pcfg_shared P) (mkCfg (pe_ms e) model''))))
| px_error : forall P e evs ctx' st',
    look P (pe_pid e) = Some e ->
    xsstep ext segs cfg (pe_nsctx e) (sh_ns (pcfg_shared P))
      (pe_cfg (pcfg_shared P) e) evs SError ctx' st' ->
    wait4_intercept_b (pe_cfg (pcfg_shared P) e) = false ->
    pstep_x_at ext cenv segs cfg (pe_pid e) P evs PError
| px_outside : forall P e,
    look P (pe_pid e) = Some e ->
    m_halted (pe_model e) = None ->
    multiproc_ok ext segs P e = false ->
    pstep_x_at ext cenv segs cfg (pe_pid e) P [] PError.

Definition pstep_x_cfg (ext : ExtSpec) (cenv : CloneEnv) (segs : list Segment) (cfg : SpuriousCfg)
    (P : pconfig) (evs : list event) (r : pstep_to) : Prop :=
  exists p, pstep_x_at ext cenv segs cfg p P evs r.

(** A narrower clone environment admits fewer steps, and
    [any_clone_failure] admits every step of every clone environment: with
    it the relation is unrestricted. *)
Lemma pstep_x_at_cenv_mono : forall ext (cenv1 cenv2 : CloneEnv) segs cfg p P evs r,
  (forall f m ctx st hq e st', cenv1 f m ctx st hq e st' -> cenv2 f m ctx st hq e st') ->
  pstep_x_at ext cenv1 segs cfg p P evs r -> pstep_x_at ext cenv2 segs cfg p P evs r.
Proof.
  intros ext cenv1 cenv2 segs cfg p P evs r Hsub H.
  destruct H; [eapply px_other | eapply px_clone | eapply px_clone_fail | eapply px_clone_unmodeled
              | eapply px_clone_claimed | eapply px_wait_reap | eapply px_error | eapply px_outside];
    eauto.
Qed.

Lemma pstep_x_at_any_clone_failure : forall ext cenv segs cfg p P evs r,
  pstep_x_at ext cenv segs cfg p P evs r -> pstep_x_at ext any_clone_failure segs cfg p P evs r.
Proof.
  intros ext cenv segs cfg p P evs r. apply pstep_x_at_cenv_mono. intros. exact I.
Qed.

(* -------------------------------------------------- facts the proofs use *)

Lemma claimed_at_no_ext : forall segs c, claimed_at no_ext segs c = false.
Proof. intros segs c. unfold claimed_at. destruct (pending_input segs c); reflexivity. Qed.

Lemma xsstep_unclaimed : forall ext segs cfg ctx st c evs r ctx' st',
  claimed_at ext segs c = false ->
  (xsstep ext segs cfg ctx st c evs r ctx' st'
   <-> sstep_cfg segs cfg c evs r /\ ctx' = ctx /\ st' = st).
Proof.
  intros ext segs cfg ctx st c evs r ctx' st' Hc. split.
  - intros H. inversion H; subst;
      [ split; [assumption | split; reflexivity] | .. ];
      exfalso; unfold claimed_at, pending_input in Hc; cbn [cfg_ms] in Hc;
      match goal with
      | [ Hs : ms_svc_pending _ = Some _, Hcl : ext_claims _ _ = true |- _ ] =>
          rewrite Hs in Hc; cbv beta iota in Hc; rewrite Hcl in Hc; discriminate Hc
      end.
  - intros (Hs & -> & ->). apply xs_released; assumption.
Qed.

Lemma absorb_x_same : forall P e c',
  absorb_x P e c' (pe_nsctx e) (sh_ns (pcfg_shared P)) = absorb P e c'.
Proof. reflexivity. Qed.

Lemma clone_result_x_same : forall P e c' q,
  clone_result_x P e c' q (pe_nsctx e) (sh_ns (pcfg_shared P)) = clone_result P e c' q.
Proof. reflexivity. Qed.

Lemma multiproc_ok_unclaimed : forall ext segs P e,
  claimed_at ext segs (pe_cfg (pcfg_shared P) e) = false ->
  multiproc_ok ext segs P e = multiproc_allowed P (pe_cfg (pcfg_shared P) e).
Proof.
  intros ext segs P e H. unfold multiproc_ok, claimed_at in *. cbv zeta.
  destruct (pending_input segs (pe_cfg (pcfg_shared P) e)) as [i|];
    cbv beta iota in H |- *; [rewrite H; cbn [andb]|]; apply orb_false_r.
Qed.

Lemma clone_pending_success : forall c c',
  clone_pending_b c = false -> clone_success_b c c' = false.
Proof.
  intros c c' H. unfold clone_pending_b, clone_success_b in *.
  destruct (ms_svc_pending (cfg_ms c)); cbv beta iota in H |- *;
    [rewrite H; reflexivity | reflexivity].
Qed.

Lemma clone_success_pending : forall c c',
  clone_success_b c c' = true -> clone_pending_b c = true.
Proof.
  intros c c' H. destruct (clone_pending_b c) eqn:Hp; [reflexivity|].
  rewrite (clone_pending_success c c' Hp) in H. discriminate H.
Qed.

Lemma clone_pending_not_wait4 : forall c,
  clone_pending_b c = true -> wait4_intercept_b c = false.
Proof.
  intros c H. unfold clone_pending_b, wait4_intercept_b in *.
  destruct (ms_svc_pending (cfg_ms c)) as [x8|]; cbv beta iota in H |- *; [|reflexivity].
  unfold clone_sysno in H. apply orb_true_iff in H as [H|H]; apply Z.eqb_eq in H;
    rewrite H; reflexivity.
Qed.

(** A return in the errno range is [-en] for an [en] in [1, 4095]. *)
Lemma addr_error_errno : forall r,
  addr_is_error_b r = true -> exists en, (1 <= en <= 4095)%Z /\ r = errno_ret en.
Proof.
  intros r H. unfold addr_is_error_b in H. apply Z.ltb_lt in H.
  pose proof (bv_unsigned_range_u64 r) as Hr.
  exists (two_pow_64 - bv_unsigned r)%Z. split; [lia|].
  unfold errno_ret. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with two_pow_64.
  replace (- (two_pow_64 - bv_unsigned r))%Z with (bv_unsigned r + (-1) * two_pow_64)%Z by lia.
  rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. exact Hr.
Qed.

Lemma clone_fail_errno : forall c c',
  clone_pending_b c = true -> clone_success_b c c' = false ->
  exists en, (1 <= en <= 4095)%Z /\ ms_gpr (cfg_ms c') 0 = errno_ret en.
Proof.
  intros c c' Hp Hs. unfold clone_pending_b, clone_success_b in *.
  destruct (ms_svc_pending (cfg_ms c)) as [x8|]; cbv beta iota in Hp, Hs;
    [|discriminate Hp].
  apply andb_false_iff in Hs as [Hs|Hs]; [rewrite Hp in Hs; discriminate Hs|].
  apply negb_false_iff in Hs. apply addr_error_errno. exact Hs.
Qed.

(* ----------------------------------------------- the released world *)

(** In the released world an extension's step IS the released step: a
    claimed call has the released outcomes ([Ext.ext_coherent]), filtered
    as the released step filters them ([Ext.ext_refusal_coherent]), and the
    namespace context and state do not change. *)
Lemma xsstep_flat : forall ext segs cfg ctx st c evs r ctx' st',
  flat_view ctx st = true ->
  (xsstep ext segs cfg ctx st c evs r ctx' st'
   <-> sstep_cfg segs cfg c evs r /\ ctx' = ctx /\ st' = st).
Proof.
  intros ext segs cfg ctx st c evs r ctx' st' Hf. split.
  - intros H. destruct H as
      [ c0 evs0 r0 Hcl Hs
      | ms model x8 eff model' model'' ctx1 st1 evs0 Hh Hx8 Hcl Hsp Hrf Hh' Hmat
      | ms model x8 eff model' ctx1 st1 evs0 Hh Hx8 Hcl Hsp Hrf Hh' Hmat
      | ms model x8 eff model' ctx1 st1 evs0 code Hh Hx8 Hcl Hsp Hh' Hk
      | ms model x8 eff model' ctx1 st1 evs0 sig Hh Hx8 Hcl Hsp Hk
      | ms model x8 Hh Hx8 Hcl Hsp ].
    + split; [exact Hs | split; reflexivity].
    + apply (proj1 (ext_coherent ext _ _ _ _ Hf Hcl _)) in Hsp.
      destruct Hsp as (-> & -> & Hsp).
      split; [|split; reflexivity].
      apply sstep_cfg_syscall with (x8 := x8) (model' := model'); try assumption.
      intros Hc. apply Hrf. apply (proj2 (ext_refusal_coherent ext cfg _ _ _ _ eff Hf Hcl)).
      exact Hc.
    + apply (proj1 (ext_coherent ext _ _ _ _ Hf Hcl _)) in Hsp.
      destruct Hsp as (_ & _ & Hsp).
      split; [|split; reflexivity].
      apply sstep_cfg_syscall_materialization_fault
        with (x8 := x8) (eff := eff) (model' := model') (evs := evs0); try assumption.
      intros Hc. apply Hrf. apply (proj2 (ext_refusal_coherent ext cfg _ _ _ _ eff Hf Hcl)).
      exact Hc.
    + apply (proj1 (ext_coherent ext _ _ _ _ Hf Hcl _)) in Hsp.
      destruct Hsp as (-> & -> & Hsp).
      split; [|split; reflexivity].
      apply sstep_cfg_exit with (x8 := x8) (eff := eff); assumption.
    + apply (proj1 (ext_coherent ext _ _ _ _ Hf Hcl _)) in Hsp.
      destruct Hsp as (-> & -> & Hsp).
      split; [|split; reflexivity].
      apply sstep_cfg_killed with (x8 := x8) (eff := eff); assumption.
    + apply (proj1 (ext_coherent ext _ _ _ _ Hf Hcl _)) in Hsp.
      split; [|split; reflexivity].
      apply sstep_cfg_syscall_unmodeled with (x8 := x8); [exact Hh | exact Hx8 | exact Hsp].
  - intros (Hs & -> & ->).
    destruct (claimed_at ext segs c) eqn:Hcl; [|apply xs_released; assumption].
    revert Hcl. destruct Hs as
      [ ms model ms' model' Hh Hx8 Hm
      | ms model Hh Hx8 Hm
      | ms model Hh Hx8 Hm
      | ms model x8 eff model' model'' evs0 Hh Hx8 Hsp Hrf Hh' Hmat
      | ms model x8 eff model' evs0 Hh Hx8 Hsp Hrf Hh' Hmat
      | ms model x8 eff model' evs0 code Hh Hx8 Hsp Hh' Hk
      | ms model x8 eff model' evs0 sig Hh Hx8 Hsp Hk
      | ms model x8 Hh Hx8 Hsp ]; intros Hcl;
      unfold claimed_at, pending_input in Hcl; cbn [cfg_ms] in Hcl; rewrite Hx8 in Hcl;
      cbv beta iota in Hcl; try discriminate Hcl.
    + apply xs_ok with (x8 := x8) (model' := model'); try assumption.
      * apply (proj2 (ext_coherent ext _ _ _ _ Hf Hcl _)).
        exact (conj eq_refl (conj eq_refl Hsp)).
      * intros Hc. apply Hrf. apply (proj1 (ext_refusal_coherent ext cfg _ _ _ _ eff Hf Hcl)).
        exact Hc.
    + apply xs_materialization_fault
        with (x8 := x8) (eff := eff) (model' := model') (ctx' := ctx) (st' := st) (evs := evs0);
        try assumption.
      * apply (proj2 (ext_coherent ext _ _ _ _ Hf Hcl _)).
        exact (conj eq_refl (conj eq_refl Hsp)).
      * intros Hc. apply Hrf. apply (proj1 (ext_refusal_coherent ext cfg _ _ _ _ eff Hf Hcl)).
        exact Hc.
    + apply xs_exit with (x8 := x8) (eff := eff); try assumption.
      apply (proj2 (ext_coherent ext _ _ _ _ Hf Hcl _)).
      exact (conj eq_refl (conj eq_refl Hsp)).
    + apply xs_killed with (x8 := x8) (eff := eff); try assumption.
      apply (proj2 (ext_coherent ext _ _ _ _ Hf Hcl _)).
      exact (conj eq_refl (conj eq_refl Hsp)).
    + apply xs_unmodeled with (x8 := x8); try assumption.
      apply (proj2 (ext_coherent ext _ _ _ _ Hf Hcl _)). exact Hsp.
Qed.

Lemma multiproc_ok_flat : forall ext segs P e,
  flat_view (pe_nsctx e) (sh_ns (pcfg_shared P)) = true ->
  multiproc_ok ext segs P e = multiproc_allowed P (pe_cfg (pcfg_shared P) e).
Proof.
  intros ext segs P e Hf. unfold multiproc_ok. cbv zeta.
  destruct (pending_input segs (pe_cfg (pcfg_shared P) e)) as [i|]; cbv beta iota;
    [rewrite (ext_multiproc_coherent ext i _ _ _ Hf), andb_false_r|]; apply orb_false_r.
Qed.

(* --------------------------------------------- where the two relations agree *)

(** The extension changes nothing at the entries of [P]: an entry's step
    under the extension is its released step, with its namespace context
    and the shared state unchanged; a pending clone or intercepted wait is
    not claimed; the extension admits no call the core's guard refuses; a
    clone does to the namespace model what the core's own clone does; and
    the clone environment admits every failure of a pending clone. *)
Definition ext_agrees (ext : ExtSpec) (cenv : CloneEnv) (segs : list Segment) (P : pconfig) : Prop :=
  forall e, look P (pe_pid e) = Some e ->
    (forall cfg evs r ctx' st',
       xsstep ext segs cfg (pe_nsctx e) (sh_ns (pcfg_shared P))
         (pe_cfg (pcfg_shared P) e) evs r ctx' st'
       <-> sstep_cfg segs cfg (pe_cfg (pcfg_shared P) e) evs r
           /\ ctx' = pe_nsctx e /\ st' = sh_ns (pcfg_shared P))
    /\ (clone_pending_b (pe_cfg (pcfg_shared P) e) = true ->
        claimed_at ext segs (pe_cfg (pcfg_shared P) e) = false)
    /\ (wait4_intercept_b (pe_cfg (pcfg_shared P) e) = true ->
        claimed_at ext segs (pe_cfg (pcfg_shared P) e) = false)
    /\ multiproc_ok ext segs P e = multiproc_allowed P (pe_cfg (pcfg_shared P) e)
    /\ (forall hq o,
          ext_clone ext (clone_flags_of (pe_cfg (pcfg_shared P) e))
            (cfg_model (pe_cfg (pcfg_shared P) e)) (pe_nsctx e) (sh_ns (pcfg_shared P)) hq o
          <-> released_clone (pe_nsctx e) (sh_ns (pcfg_shared P)) o)
    /\ (clone_pending_b (pe_cfg (pcfg_shared P) e) = true ->
        forall hq en st',
          cenv (clone_flags_of (pe_cfg (pcfg_shared P) e))
            (cfg_model (pe_cfg (pcfg_shared P) e)) (pe_nsctx e) (sh_ns (pcfg_shared P)) hq en st').

Theorem pstep_x_at_agree_iff : forall ext cenv segs cfg p P evs r,
  ext_agrees ext cenv segs P ->
  (pstep_x_at ext cenv segs cfg p P evs r <-> pstep_at segs cfg p P evs r).
Proof.
  intros ext cenv segs cfg p P evs r Hag. split.
  - intros H. revert Hag. destruct H as
      [ Q e ev c' ctx' st' Hl Hx Hcp Hwt Hmp
      | Q e ev c' q child ret st' Hl Hcl Hs Hsucc Hq Hfree Hma Hec
      | Q e ev c' en hq st' Hl Hcl Hs Hcp Hsucc Hret Hma Hec Hnr
      | Q e ev c' hq Hl Hcl Hs Hcp Hma Hec
      | Q e Hl Hh Hcp Hcl
      | Q e q ez x8 stat_addr status eff model'' dumped
          Hl Hcl Hh Hx8 Hwt Hargs Hq Hne Hpar Hk Hst Hrd Heff Hmat
      | Q e ev ctx' st' Hl Hx Hwt
      | Q e Hl Hh Hmp ]; intros Hag;
      destruct (Hag e Hl) as (Hxs & Hclp & Hwtp & Hmpe & Hcln & Hnrf).
    + (* px_other *)
      apply (proj1 (Hxs _ _ _ _ _)) in Hx. destruct Hx as (Hs & -> & ->).
      rewrite absorb_x_same. apply pstep_other; try assumption.
      * apply clone_pending_success. exact Hcp.
      * rewrite <- Hmpe. exact Hmp.
    + (* px_clone *)
      apply (proj1 (Hcln _ _)) in Hec.
      destruct Hec as [Heq | (en & _ & Heq)]; [|discriminate Heq].
      injection Heq as -> -> ->. cbn [with_ret]. rewrite clone_result_x_same.
      apply pstep_clone; assumption.
    + (* px_clone_fail *)
      apply (proj1 (Hcln _ _)) in Hec.
      destruct Hec as [Heq | (en' & _ & Heq)]; [discriminate Heq|].
      injection Heq as _ ->. rewrite absorb_x_same.
      apply pstep_other; try assumption.
      apply clone_pending_not_wait4. exact Hcp.
    + (* px_clone_unmodeled *)
      apply (proj1 (Hcln _ _)) in Hec.
      destruct Hec as [Heq | (en & _ & Heq)]; discriminate Heq.
    + (* px_clone_claimed *)
      rewrite (Hclp Hcp) in Hcl. discriminate Hcl.
    + (* px_wait_reap *)
      eapply pstep_wait_reap; eassumption.
    + (* px_error *)
      apply (proj1 (Hxs _ _ _ _ _)) in Hx. destruct Hx as (Hs & _ & _).
      apply pstep_error; assumption.
    + (* px_outside *)
      rewrite Hmpe in Hmp. apply pstep_outside; assumption.
  - intros H. revert Hag. destruct H as
      [ Q e ev c' Hl Hs Hsucc Hwt Hma
      | Q e ev c' q Hl Hs Hsucc Hq Hfree Hma
      | Q e q ez x8 stat_addr status eff model'' dumped
          Hl Hh Hx8 Hwt Hargs Hq Hne Hpar Hk Hst Hrd Heff Hmat
      | Q e ev Hl Hs Hwt
      | Q e Hl Hh Hma ]; intros Hag;
      destruct (Hag e Hl) as (Hxs & Hclp & Hwtp & Hmpe & Hcln & Hnrf).
    + (* pstep_other *)
      destruct (clone_pending_b (pe_cfg (pcfg_shared Q) e)) eqn:Hp.
      * destruct (clone_fail_errno _ _ Hp Hsucc) as (en & Hen & Hret).
        rewrite <- absorb_x_same.
        apply px_clone_fail with (en := en) (hq := 0%Z); try assumption.
        -- exact (Hclp eq_refl).
        -- apply (proj2 (Hcln _ _)). right. exists en. split; [exact Hen | reflexivity].
        -- exact (Hnrf eq_refl _ _ _).
      * rewrite <- absorb_x_same.
        apply px_other; try assumption.
        -- apply (proj2 (Hxs _ _ _ _ _)). split; [exact Hs | split; reflexivity].
        -- rewrite Hmpe. exact Hma.
    + (* pstep_clone *)
      rewrite <- clone_result_x_same.
      replace (clone_result_x Q e c' q (pe_nsctx e) (sh_ns (pcfg_shared Q)))
        with (clone_result_x Q e (with_ret c' None) q (pe_nsctx e) (sh_ns (pcfg_shared Q)))
        by reflexivity.
      apply px_clone; try assumption.
      * exact (Hclp (clone_success_pending _ _ Hsucc)).
      * apply (proj2 (Hcln _ _)). left. reflexivity.
    + (* pstep_wait_reap *)
      eapply px_wait_reap; try eassumption. exact (Hwtp Hwt).
    + (* pstep_error *)
      apply px_error with (ctx' := pe_nsctx e) (st' := sh_ns (pcfg_shared Q)); try assumption.
      apply (proj2 (Hxs _ _ _ _ _)). split; [exact Hs | split; reflexivity].
    + (* pstep_outside *)
      apply px_outside; try assumption. rewrite Hmpe. exact Hma.
Qed.

(** An extension that claims no pending call of an entry of [P] and whose
    clone does what the core's own clone does to the namespace model, in a
    clone environment that admits every failure of a pending clone. *)
Definition ext_released_at (ext : ExtSpec) (cenv : CloneEnv) (segs : list Segment) (P : pconfig)
    : Prop :=
  forall e, look P (pe_pid e) = Some e ->
    claimed_at ext segs (pe_cfg (pcfg_shared P) e) = false
    /\ (forall hq o,
          ext_clone ext (clone_flags_of (pe_cfg (pcfg_shared P) e))
            (cfg_model (pe_cfg (pcfg_shared P) e)) (pe_nsctx e) (sh_ns (pcfg_shared P)) hq o
          <-> released_clone (pe_nsctx e) (sh_ns (pcfg_shared P)) o)
    /\ (clone_pending_b (pe_cfg (pcfg_shared P) e) = true ->
        forall hq en st',
          cenv (clone_flags_of (pe_cfg (pcfg_shared P) e))
            (cfg_model (pe_cfg (pcfg_shared P) e)) (pe_nsctx e) (sh_ns (pcfg_shared P)) hq en st').

Lemma ext_released_agrees : forall ext cenv segs P,
  ext_released_at ext cenv segs P -> ext_agrees ext cenv segs P.
Proof.
  intros ext cenv segs P H e Hl. destruct (H e Hl) as (Hcl & Hcln & Hnrf).
  split; [|split; [|split; [|split; [|split]]]].
  - intros cfg evs r ctx' st'. apply xsstep_unclaimed. exact Hcl.
  - intros _. exact Hcl.
  - intros _. exact Hcl.
  - apply multiproc_ok_unclaimed. exact Hcl.
  - exact Hcln.
  - exact Hnrf.
Qed.

Theorem pstep_x_at_released_iff : forall ext cenv segs cfg p P evs r,
  ext_released_at ext cenv segs P ->
  (pstep_x_at ext cenv segs cfg p P evs r <-> pstep_at segs cfg p P evs r).
Proof.
  intros ext cenv segs cfg p P evs r H. apply pstep_x_at_agree_iff.
  apply ext_released_agrees. exact H.
Qed.

(** Every entry of [P] is in the released world, makes no namespace with
    a pending clone, has its pending clone or intercepted wait left to the
    core, and the clone environment admits every failure of its pending
    clone. *)
Definition ext_flat_at (ext : ExtSpec) (cenv : CloneEnv) (segs : list Segment) (P : pconfig)
    : Prop :=
  forall e, look P (pe_pid e) = Some e ->
    flat_view (pe_nsctx e) (sh_ns (pcfg_shared P)) = true
    /\ has_ns_bits (clone_flags_of (pe_cfg (pcfg_shared P) e)) = false
    /\ (clone_pending_b (pe_cfg (pcfg_shared P) e) = true ->
        claimed_at ext segs (pe_cfg (pcfg_shared P) e) = false)
    /\ (wait4_intercept_b (pe_cfg (pcfg_shared P) e) = true ->
        claimed_at ext segs (pe_cfg (pcfg_shared P) e) = false)
    /\ (clone_pending_b (pe_cfg (pcfg_shared P) e) = true ->
        forall hq en st',
          cenv (clone_flags_of (pe_cfg (pcfg_shared P) e))
            (cfg_model (pe_cfg (pcfg_shared P) e)) (pe_nsctx e) (sh_ns (pcfg_shared P)) hq en st').

Lemma ext_flat_agrees : forall ext cenv segs P,
  ext_flat_at ext cenv segs P -> ext_agrees ext cenv segs P.
Proof.
  intros ext cenv segs P H e Hl. destruct (H e Hl) as (Hf & Hns & Hcp & Hwt & Hce).
  split; [|split; [|split; [|split; [|split]]]].
  - intros cfg evs r ctx' st'. apply xsstep_flat. exact Hf.
  - exact Hcp.
  - exact Hwt.
  - apply multiproc_ok_flat. exact Hf.
  - intros hq o. apply (ext_clone_coherent ext); [exact Hf | exact Hns].
  - exact Hce.
Qed.

(** IN THE RELEASED WORLD THE EXTENDED RELATION IS THE CORE'S OWN, claimed
    calls included: an extension changes the system's steps only for a
    process in a namespace the released model does not describe, or at a
    clone that makes one. *)
Theorem pstep_x_at_flat_iff : forall ext cenv segs cfg p P evs r,
  ext_flat_at ext cenv segs P ->
  (pstep_x_at ext cenv segs cfg p P evs r <-> pstep_at segs cfg p P evs r).
Proof.
  intros ext cenv segs cfg p P evs r H. apply pstep_x_at_agree_iff.
  apply ext_flat_agrees. exact H.
Qed.

Lemma ext_released_at_no_ext : forall segs P, ext_released_at no_ext any_clone_failure segs P.
Proof.
  intros segs P e _. split; [apply claimed_at_no_ext|]. split; [intros hq o; reflexivity|].
  intros _ hq en st'. exact I.
Qed.

(** AT [no_ext], WITH EVERY CLONE FAILURE ADMITTED ([any_clone_failure]),
    THE EXTENDED RELATION IS THE CORE'S OWN. *)
Theorem pstep_at_no_ext_iff : forall segs cfg p P evs r,
  pstep_x_at no_ext any_clone_failure segs cfg p P evs r <-> pstep_at segs cfg p P evs r.
Proof.
  intros segs cfg p P evs r. apply pstep_x_at_released_iff. apply ext_released_at_no_ext.
Qed.

Corollary pstep_x_cfg_no_ext_iff : forall segs cfg P evs r,
  pstep_x_cfg no_ext any_clone_failure segs cfg P evs r <-> pstep_cfg segs cfg P evs r.
Proof.
  intros segs cfg P evs r. unfold pstep_x_cfg, pstep_cfg.
  split; intros [p Hp]; exists p; apply pstep_at_no_ext_iff; exact Hp.
Qed.

(* ---------------------------------------- the single-process projections *)

(** At [no_ext] and [any_clone_failure], the statements of
    [pstep_single_next] and [pstep_single_err], unchanged. *)
Theorem pstep_x_single_next_no_ext : forall segs cfg c evs P',
  (forall c', sstep_cfg segs cfg c evs (SNext c') -> clone_success_b c c' = false) ->
  wait4_intercept_b c = false ->
  (pstep_x_cfg no_ext any_clone_failure segs cfg (one_proc c) evs (PNext P')
   <-> exists c', P' = one_proc c' /\ sstep_cfg segs cfg c evs (SNext c')).
Proof.
  intros segs cfg c evs P' Hcl Hwt.
  apply iff_trans with (B := pstep_cfg segs cfg (one_proc c) evs (PNext P')).
  - apply pstep_x_cfg_no_ext_iff.
  - apply pstep_single_next; assumption.
Qed.

Theorem pstep_x_single_err_no_ext : forall segs cfg c evs,
  wait4_intercept_b c = false ->
  (pstep_x_cfg no_ext any_clone_failure segs cfg (one_proc c) evs PError
   <-> sstep_cfg segs cfg c evs SError).
Proof.
  intros segs cfg c evs Hwt.
  apply iff_trans with (B := pstep_cfg segs cfg (one_proc c) evs PError).
  - apply pstep_x_cfg_no_ext_iff.
  - apply pstep_single_err; assumption.
Qed.

(** A one-process system is in the released world ([one_proc] uses
    [init_nsctx] and [empty_nsstate]). *)
Lemma ext_flat_one : forall ext cenv segs c,
  has_ns_bits (clone_flags_of c) = false ->
  (clone_pending_b c = true -> claimed_at ext segs c = false) ->
  wait4_intercept_b c = false ->
  (clone_pending_b c = true ->
   forall hq en st', cenv (clone_flags_of c) (cfg_model c) init_nsctx empty_nsstate hq en st') ->
  ext_flat_at ext cenv segs (one_proc c).
Proof.
  intros ext cenv segs c Hns Hcp Hwt Hce e Hl.
  apply look_one_proc_inv in Hl. subst e. rewrite one_proc_view.
  split; [reflexivity | split; [exact Hns | split; [exact Hcp | split]]].
  - intros Hw. rewrite Hwt in Hw. discriminate Hw.
  - exact Hce.
Qed.

(** For any extension: the projection, claimed calls included, when a
    pending clone makes no namespace, is left to the core, and may fail as
    the core's own clone does. *)
Theorem pstep_x_single_next : forall ext cenv segs cfg c evs P',
  has_ns_bits (clone_flags_of c) = false ->
  (clone_pending_b c = true -> claimed_at ext segs c = false) ->
  (forall c', sstep_cfg segs cfg c evs (SNext c') -> clone_success_b c c' = false) ->
  wait4_intercept_b c = false ->
  (clone_pending_b c = true ->
   forall hq en st', cenv (clone_flags_of c) (cfg_model c) init_nsctx empty_nsstate hq en st') ->
  (pstep_x_cfg ext cenv segs cfg (one_proc c) evs (PNext P')
   <-> exists c', P' = one_proc c' /\ sstep_cfg segs cfg c evs (SNext c')).
Proof.
  intros ext cenv segs cfg c evs P' Hns Hcp Hcs Hwt Hce.
  pose proof (ext_flat_one ext cenv segs c Hns Hcp Hwt Hce) as Hflat.
  apply iff_trans with (B := pstep_cfg segs cfg (one_proc c) evs (PNext P')).
  2: apply pstep_single_next; assumption.
  unfold pstep_x_cfg, pstep_cfg.
  split; intros [p Hp]; exists p;
    [ apply (proj1 (pstep_x_at_flat_iff ext cenv segs cfg p (one_proc c) evs (PNext P') Hflat))
    | apply (proj2 (pstep_x_at_flat_iff ext cenv segs cfg p (one_proc c) evs (PNext P') Hflat)) ];
    exact Hp.
Qed.

Theorem pstep_x_single_err : forall ext cenv segs cfg c evs,
  has_ns_bits (clone_flags_of c) = false ->
  (clone_pending_b c = true -> claimed_at ext segs c = false) ->
  wait4_intercept_b c = false ->
  (clone_pending_b c = true ->
   forall hq en st', cenv (clone_flags_of c) (cfg_model c) init_nsctx empty_nsstate hq en st') ->
  (pstep_x_cfg ext cenv segs cfg (one_proc c) evs PError
   <-> sstep_cfg segs cfg c evs SError).
Proof.
  intros ext cenv segs cfg c evs Hns Hcp Hwt Hce.
  pose proof (ext_flat_one ext cenv segs c Hns Hcp Hwt Hce) as Hflat.
  apply iff_trans with (B := pstep_cfg segs cfg (one_proc c) evs PError).
  2: apply pstep_single_err; assumption.
  unfold pstep_x_cfg, pstep_cfg.
  split; intros [p Hp]; exists p;
    [ apply (proj1 (pstep_x_at_flat_iff ext cenv segs cfg p (one_proc c) evs PError Hflat))
    | apply (proj2 (pstep_x_at_flat_iff ext cenv segs cfg p (one_proc c) evs PError Hflat)) ];
    exact Hp.
Qed.

(** At an instruction nothing is pending, so nothing is claimed and no
    clone makes a namespace: the extended relation is the released step. *)
Lemma no_ns_bits_instr : forall c, at_instruction c -> has_ns_bits (clone_flags_of c) = false.
Proof. intros c H. unfold at_instruction, clone_flags_of in *. rewrite H. reflexivity. Qed.

Lemma clone_pending_instr : forall c, at_instruction c -> clone_pending_b c = false.
Proof. intros c H. unfold at_instruction, clone_pending_b in *. rewrite H. reflexivity. Qed.

Theorem pstep_x_instr_single_next : forall ext cenv segs cfg c evs P',
  at_instruction c ->
  (pstep_x_cfg ext cenv segs cfg (one_proc c) evs (PNext P')
   <-> exists c', P' = one_proc c' /\ sstep_cfg segs cfg c evs (SNext c')).
Proof.
  intros ext cenv segs cfg c evs P' H. apply pstep_x_single_next.
  - apply no_ns_bits_instr. exact H.
  - intros Hp. rewrite (clone_pending_instr c H) in Hp. discriminate Hp.
  - intros c' _. apply clone_success_b_instr. exact H.
  - apply wait4_intercept_b_instr. exact H.
  - intros Hp. rewrite (clone_pending_instr c H) in Hp. discriminate Hp.
Qed.

Theorem pstep_x_instr_single_err : forall ext cenv segs cfg c evs,
  at_instruction c ->
  (pstep_x_cfg ext cenv segs cfg (one_proc c) evs PError <-> sstep_cfg segs cfg c evs SError).
Proof.
  intros ext cenv segs cfg c evs H. apply pstep_x_single_err.
  - apply no_ns_bits_instr. exact H.
  - intros Hp. rewrite (clone_pending_instr c H) in Hp. discriminate Hp.
  - apply wait4_intercept_b_instr. exact H.
  - intros Hp. rewrite (clone_pending_instr c H) in Hp. discriminate Hp.
Qed.

(* ---------------------------------------------- who took the step *)

(** The process a step is indexed by is present and took it. *)
Lemma pstep_x_at_look : forall ext cenv segs cfg p P evs r,
  pstep_x_at ext cenv segs cfg p P evs r -> exists e, look P p = Some e /\ pe_pid e = p.
Proof.
  intros ext cenv segs cfg p P evs r H.
  destruct H; eexists; (split; [eassumption | reflexivity]).
Qed.

Lemma pstep_x_at_one_pid : forall ext cenv segs cfg p c evs r,
  pstep_x_at ext cenv segs cfg p (one_proc c) evs r -> p = one_pid.
Proof.
  intros ext cenv segs cfg p c evs r H.
  destruct (pstep_x_at_look _ _ _ _ _ _ _ _ H) as (e & Hl & <-).
  apply look_one_proc_inv in Hl. subst e. reflexivity.
Qed.

(** In a one-process system, a step of [one_pid] is any step of the system. *)
Lemma pstep_x_at_one : forall ext cenv segs cfg c evs r,
  pstep_x_at ext cenv segs cfg one_pid (one_proc c) evs r
  <-> pstep_x_cfg ext cenv segs cfg (one_proc c) evs r.
Proof.
  intros ext cenv segs cfg c evs r. split.
  - intros H. exists one_pid. exact H.
  - intros [p Hp]. rewrite <- (pstep_x_at_one_pid _ _ _ _ _ _ _ _ Hp). exact Hp.
Qed.
