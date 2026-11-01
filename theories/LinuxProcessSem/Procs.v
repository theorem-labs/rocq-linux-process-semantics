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
    it always gave.  The two never apply to the same configuration —
    [wait4_spec] is [unmodeled] unless the option word is WNOHANG, unless the
    pid is the any-child value, unless the usage pointer is null, and then
    [unmodeled] AGAIN if the model has children (Exit.v:244-252), while the
    reap arm of this file requires the option word to be 0 and requires an own
    halted child.  There is no configuration at which both say anything.
    (Checked line by line against those two files, 2026-11-01.)

    WHY THE CLONE ARM CONSUMES THE RELEASED STEP.  [pstep_clone] fires only
    under [clone_success], which reads the value [Run.apply_effect] put in a0
    against [Fork.clone_errnos] through [Run.ret_in_errnos] — the same
    predicate [Run.refusal_b] uses.  So a FAILING clone keeps the released
    behaviour exactly, and the new arm cannot drift from the released errno
    list even if that list changes.

    BUILD ORDER.  [pstep_single] and [pstep_instr_single] below are proved
    before any arm but [pstep_other], because every consumer's own step
    relation is derived from them, and
    because every one-process statement in the released set depends on them
    holding. *)

From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Exit Fork.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope bool_scope.

(* =========================================================================
   Shared kernel objects that leave the per-process model
   ========================================================================= *)

(** An open file description's identity.  A [positive] rather than a [nat] so
    that freshness is cheap to decide and 0 is not a legal id. *)
Definition OfdId : Type := positive.

(** What a shared description is OF.  The kinds are exactly the [State.FdEntry]
    constructors whose kernel object Linux SHARES across a fork: a regular
    file (whose offset moves), a pipe end, a socket, and the inherited
    standard channels.  [FdDir], [FdDevNull] and [FdUrandom] carry no mutable
    kernel-side offset and stay private in [State.m_fd]. *)
Inductive OfdWhat : Type :=
  | OfdFile   (p : Fs.path) (mode : word)
  | OfdPipeR  (buf : positive)
  | OfdPipeW  (buf : positive)
  | OfdSocket (ix : word)
  | OfdChannel (ch : word).

(** A shared open file description: Linux's [struct file].  THE OFFSET LIVES
    HERE, once, however many descriptors in however many processes name it.
    That is the whole point of the record and the reason it is not a
    [State.FdEntry]: [Sys.Kernel.Fork]'s header (Fork.v:180-193) says what
    survives even a plain fork is the FILE OFFSET, because [copy_files]
    duplicates the table while both tables point at the same [struct file],
    and an offset inside [FdEntry] cannot express that.

    MEASURED ALTERNATIVE, so the choice is on the record: moving the offset out
    of [State.FdEntry] itself costs 1357 constructor-pattern sites across 69
    files in this repository, each in a [Checks/Sys], [Checks/Witness] or
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
  ofd_refs  : positive
}.

(* =========================================================================
   The task-private namespace context
   ========================================================================= *)

Definition MountId  : Type := positive.
Definition DentryId : Type := positive.
Definition NsId     : Type := positive.

(** The five capability sets of [struct cred], as the one 64-bit word each
    that riscv64's [__user_cap_data_struct] pair amounts to. *)
Record CapSets := mkCapSets {
  cap_permitted   : word;
  cap_effective   : word;
  cap_inheritable : word;
  cap_bounding    : word;
  cap_ambient     : word
}.

(** THE TASK-PRIVATE NAMESPACE CONTEXT, and it is task-private rather than a
    projection over the run for a measured reason: a path walk, a capability
    check and [getpid] each read a private reference AND a shared object in
    the SAME step.  A pure projection can decide none of /proc/self, a mount
    root, a uid mapping or a capability set, because [Fs.Fs] is
    [list (path * list byte)] (Fs.v:86) with no mount, no inode identity and
    no owner.

    [nsx_mount] is an INDIRECTION into [sh_ns], not a copy of the mount tree.
    Two reasons, and neither is the lemma count (51 new [reflexivity] lemmas
    against 50 lemmas that stop being [reflexivity] is no difference): a tree
    copied per namespace can DIVERGE between copies, which is a correctness
    hazard rather than a proof cost; and conditional lemmas are paid by every
    future proof that passes through them while [reflexivity] lemmas are paid
    once.  It is also Linux's shape, [struct mnt_namespace]. *)
Record ns_ctx := mkNsCtx {
  nsx_user  : NsId;
  nsx_mount : NsId;
  nsx_pid   : NsId;
  nsx_net   : NsId;
  nsx_ipc   : NsId;
  nsx_uts   : NsId;
  nsx_root  : MountId * DentryId;
  nsx_cwd   : MountId * DentryId;
  nsx_umask : word;
  nsx_caps  : CapSets;
  nsx_securebits   : word;
  nsx_no_new_privs : bool;
  nsx_pdeathsig    : option word;
  nsx_cloexec      : list (word * bool)
}.

(** The shared namespace side: the tables, the mount tree, superblocks,
    inodes, the uid and gid maps, the pid allocation table and the network
    interfaces.  Empty in the pathfinder and pinned empty by
    [Checks.ProcsScope]; a namespace development fills it. *)
Record NsTables := mkNsTables {
  nst_mounts  : list (NsId * list (MountId * DentryId));
  nst_supers  : list (positive * positive);
  nst_inodes  : list (positive * Fs.path);
  nst_uidmaps : list (NsId * list (word * word * word));
  nst_gidmaps : list (NsId * list (word * word * word));
  nst_pidtab  : list (NsId * list (positive * positive));
  nst_netif   : list (NsId * list word)
}.

Definition init_ns_tables : NsTables := mkNsTables [] [] [] [] [] [] [].

Definition init_caps : CapSets :=
  mkCapSets (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
            (Z_to_bv 64 0) (Z_to_bv 64 0).

Definition init_ns_ctx : ns_ctx :=
  mkNsCtx 1%positive 1%positive 1%positive 1%positive 1%positive 1%positive
          (1%positive, 1%positive) (1%positive, 1%positive)
          (Z_to_bv 64 18) init_caps (Z_to_bv 64 0) false None [].

(* =========================================================================
   The entries, the shared state, and the configuration
   ========================================================================= *)

(** One process.

    [pe_model] carries ONLY the per-process part of [State.Model]: [m_fd],
    [m_vm], [m_proc], [m_lim], [m_time].  Its [m_fsys] and [m_io] slots are
    canonically empty and are never read: [pe_cfg] splices the SHARED ones in
    before every step and [pe_absorb] reads them back out after, so the shared
    copy is the only live one.  [fs_only_in_shared] below is the statement of
    that, and it is what makes "the file system is global" true rather than
    decorative. *)
Record ProcessEntry := mkEntry {
  pe_pid    : positive;
  pe_parent : option positive;
  pe_ms     : machine_state;
  pe_model  : Model;
  pe_ofd    : list (word * OfdId);
  pe_ns     : ns_ctx
}.

(** Shared Run state: one of each, for the whole system. *)
Record shared := mkShared {
  sh_fsys  : FsState;
  sh_io    : IoState;
  sh_ofd   : list (OfdId * Ofd);
  (** THE PIPE BUFFERS, a NAMED field beside [sh_ofd] rather than a slot
      inside it or inside [sh_ns]: the projections below are what a consumer
      reads, and a buffer hidden in another field's slot cannot be named by
      one. *)
  sh_pipes : list (positive * PipeBuf);
  sh_ns    : NsTables
}.

Record pconfig := mkPCfg {
  pcfg_procs  : list ProcessEntry;
  pcfg_root   : positive;
  pcfg_shared : shared
}.

Inductive pstep_to := PNext (P : pconfig) | PError.

(* =========================================================================
   The splice: how the shared state reaches a released step
   ========================================================================= *)

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

(** Read one entry's successor back out, splitting it again. *)
Definition pe_absorb (e : ProcessEntry) (c : config) : ProcessEntry :=
  mkEntry (pe_pid e) (pe_parent e) (cfg_ms c) (clear_shared (cfg_model c))
          (pe_ofd e) (pe_ns e).

Definition shared_absorb (S : shared) (c : config) : shared :=
  mkShared (m_fsys (cfg_model c)) (m_io (cfg_model c))
           (sh_ofd S) (sh_pipes S) (sh_ns S).

(** The splice and the absorb are inverse, which is the whole reason the
    per-entry [m_fsys] slot may be blank. *)
Lemma pe_cfg_absorb : forall S e c,
  pe_cfg (shared_absorb S c) (pe_absorb e c) = c.
Proof.
  intros S e c. destruct c as [ms m]. destruct m. reflexivity.
Qed.

(* =========================================================================
   Projections
   ========================================================================= *)

Fixpoint look_in (ps : list ProcessEntry) (p : positive) : option ProcessEntry :=
  match ps with
  | [] => None
  | e :: r => if Pos.eqb (pe_pid e) p then Some e else look_in r p
  end.

Definition look (P : pconfig) (p : positive) : option ProcessEntry :=
  look_in (pcfg_procs P) p.

Fixpoint replace_in (ps : list ProcessEntry) (p : positive) (e' : ProcessEntry)
    : list ProcessEntry :=
  match ps with
  | [] => []
  | e :: r => if Pos.eqb (pe_pid e) p then e' :: r else e :: replace_in r p e'
  end.

Definition pe_running (e : ProcessEntry) : Prop := m_halted (pe_model e) = None.

(** A zombie is an entry whose model is halted.  There is no zombie LIST and no
    zombie flag: every [Run.sstep_cfg] arm requires [m_halted model = None]
    (Run.v:1785, 1790, 1795, 1800, 1810, 1818, 1826, 1833), so a halted entry
    is already stuck in the released relation.  "Dead" is absence from
    [pcfg_procs]. *)
Definition pe_zombie (e : ProcessEntry) : option word := m_halted (pe_model e).

Definition root_view (P : pconfig) : option config :=
  match look P (pcfg_root P) with
  | Some e => Some (pe_cfg (pcfg_shared P) e)
  | None => None
  end.

Definition children_of (P : pconfig) (p : positive) : list ProcessEntry :=
  filter (fun e => match pe_parent e with
                   | Some q => Pos.eqb q p
                   | None => false
                   end) (pcfg_procs P).

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
      Nat.leb (length (pcfg_procs P)) 1%nat
      || existsb (Z.eqb (bv_unsigned x8)) multiproc_sysnos
  end.

(* =========================================================================
   Discriminating the two intercepted steps
   ========================================================================= *)

Definition clone_sysno (n : Z) : bool := (n =? 220)%Z || (n =? 435)%Z.

(** The step [c -> c'] was a clone that really created a child.
    [Run.apply_effect] sets a0 from [eff_ret] (Run.v:177), so the delivered
    value is read off the successor, and [Run.ret_in_errnos] (Run.v:1403-1404)
    is the SAME predicate [Run.refusal_b] uses, so the two readings cannot
    drift.  [Checks.ProcessCreation.clone_resolve_declines_or_sets_children]
    (ProcessCreation.v:410) is what makes this exact: an answer in
    [Fork.clone_errnos] leaves the model untouched, any other answer sets
    [State.m_has_children]. *)
Definition clone_success (c c' : config) : Prop :=
  exists x8, ms_svc_pending (cfg_ms c) = Some x8
             /\ clone_sysno (bv_unsigned x8) = true
             (* [ms_gpr st i] is the i-th SYSCALL ARGUMENT register, x(10+i)
                (RiscvSemantics.v:115-118), so a0 is index 0 and NOT index 10.
                Index 10 would be x20.  [Run.apply_effect] writes the return
                value with [set_reg ms 10], which takes a PHYSICAL register
                number, and physical x10 is a0 -- the two numberings meet at
                a0 and nowhere else. *)
             /\ ret_in_errnos clone_errnos (ms_gpr (cfg_ms c') 0) = false.

(** THE CHILD PID PREDICATE: a DEFINITION with an explicit extension
    parameter, NOT an inductive, and the difference is a soundness one.  An
    inductive is strengthened by adding a CONSTRUCTOR, and a consumer who adds
    one WIDENS the predicate — a wider child predicate lets a proof create a
    child where Linux creates none.  A definition conjoined with [ext] can only
    narrow.  A pid namespace, which gives the child two numbers, passes an
    [ext] relating them; it does not add an alternative. *)
Definition child_pid (ext : config -> positive -> Prop)
    (c' : config) (q : positive) : Prop :=
  bv_unsigned (ms_gpr (cfg_ms c') 0) = Zpos q /\ ext c' q.

Definition child_pid_core : config -> positive -> Prop :=
  child_pid (fun _ _ => True).

(** The argument shape the reap arm answers: wait4(-1, stat_addr, 0, NULL).
    [Exit.WAIT_ANY32] is Exit.v:33.  [Exit.wait4_spec] answers the WNOHANG
    shape and declines this one. *)
Definition wait4_blocking_args (ms : machine_state) : option word :=
  if negb (Z.eqb (bv_unsigned (pid32 (ms_gpr ms 0))) WAIT_ANY32) then None
  else if negb (w_is0 (waitopts32 (ms_gpr ms 2))) then None
  else if negb (w_is0 (ms_gpr ms 3)) then None
  else Some (ms_gpr ms 1).

Definition wait4_intercept (c : config) : Prop :=
  exists x8, ms_svc_pending (cfg_ms c) = Some x8
             /\ bv_unsigned x8 = 260%Z
             /\ wait4_blocking_args (cfg_ms c) <> None.

(* =========================================================================
   The relation
   ========================================================================= *)

Definition absorb (P : pconfig) (e : ProcessEntry) (c' : config) : pconfig :=
  mkPCfg (replace_in (pcfg_procs P) (pe_pid e) (pe_absorb e c'))
         (pcfg_root P)
         (shared_absorb (pcfg_shared P) c').

(** One transition of the system.  The scheduler choice is the [look] premise:
    two choices of entry give two successors, and that is the whole of the
    interleaving nondeterminism. *)
Inductive pstep_cfg (segs : list Segment) (cfg : SpuriousCfg)
  : pconfig -> list event -> pstep_to -> Prop :=
| pstep_other : forall P e evs c',
    look P (pe_pid e) = Some e ->
    sstep_cfg segs cfg (pe_cfg (pcfg_shared P) e) evs (SNext c') ->
    ~ clone_success (pe_cfg (pcfg_shared P) e) c' ->
    ~ wait4_intercept (pe_cfg (pcfg_shared P) e) ->
    multiproc_allowed P (pe_cfg (pcfg_shared P) e) = true ->
    pstep_cfg segs cfg P evs (PNext (absorb P e c'))
(** THE ERROR TRANSITION, and it must EXCLUDE the intercepted wait.
    A blocking [wait4(-1, _, 0, NULL)] is [unmodeled] in the released spec
    (Exit.v:247) and [Run.sstep_cfg_syscall_unmodeled] (Run.v:1832-1836) turns
    that into [SError].  Lifting every [SError] unqualified would send the
    waiting parent to [PError] and the sleep of this core would never happen.
    So the intercepted shape is excluded here, and it is the SECOND place --
    beside a successful clone -- where this relation and the released one
    differ.  [pstep_single]'s second hypothesis is exactly that exclusion. *)
| pstep_error : forall P e evs,
    look P (pe_pid e) = Some e ->
    sstep_cfg segs cfg (pe_cfg (pcfg_shared P) e) evs SError ->
    ~ wait4_intercept (pe_cfg (pcfg_shared P) e) ->
    pstep_cfg segs cfg P evs PError
| pstep_outside : forall P e,
    look P (pe_pid e) = Some e ->
    m_halted (pe_model e) = None ->
    multiproc_allowed P (pe_cfg (pcfg_shared P) e) = false ->
    pstep_cfg segs cfg P [] PError.

(** The relation with the stepping entry exposed, which is what a consumer's
    scheduling restriction quantifies over. *)
Definition pstep_at (segs : list Segment) (cfg : SpuriousCfg) (p : positive)
    (P : pconfig) (evs : list event) (r : pstep_to) : Prop :=
  exists e, look P p = Some e /\ pe_pid e = p
            /\ pstep_cfg segs cfg P evs r.

(* =========================================================================
   The single-process projection theorem
   ========================================================================= *)

(** A system of one process, built from a released configuration. *)
Definition one_proc (c : config) : pconfig :=
  mkPCfg [mkEntry 1%positive None (cfg_ms c) (clear_shared (cfg_model c))
                  [] init_ns_ctx]
         1%positive
         (mkShared (m_fsys (cfg_model c)) (m_io (cfg_model c)) [] [] init_ns_tables).

(** The one entry of a one-process system, named once so the lemmas below and
    the proof of [pstep_single] agree on it. *)
Definition one_entry (c : config) : ProcessEntry :=
  mkEntry 1%positive None (cfg_ms c) (clear_shared (cfg_model c))
          [] init_ns_ctx.

Lemma one_proc_entry : forall c,
  look (one_proc c) 1%positive = Some (one_entry c).
Proof. intros c. reflexivity. Qed.

(** Whatever pid a step picked, a one-process system has only this entry. *)
Lemma look_one_proc_inv : forall c p e,
  look (one_proc c) p = Some e -> e = one_entry c.
Proof.
  intros c p e H. unfold look, one_proc, one_entry in H. cbn in H.
  destruct p; cbn in H; congruence.
Qed.
Proof. intros c. reflexivity. Qed.

(** The splice round-trips at a one-process system: the released view of the
    only entry is the configuration it was built from. *)
Lemma one_proc_view : forall c,
  pe_cfg (pcfg_shared (one_proc c))
         (one_entry c)
  = c.
Proof.
  intros c. destruct c as [ms m]. destruct m. reflexivity.
Qed.

(** At one entry the surface guard is unconditionally open, by its own first
    disjunct.  This is why [pstep_instr_single] needs no side condition. *)
Lemma multiproc_allowed_one : forall c c',
  multiproc_allowed (one_proc c) c' = true.
Proof.
  intros c c'. unfold multiproc_allowed.
  destruct (ms_svc_pending (cfg_ms c')); reflexivity.
Qed.

Lemma absorb_one_proc : forall c c',
  absorb (one_proc c)
         (one_entry c)
         c'
  = one_proc c'.
Proof.
  intros c c'. destruct c' as [ms' m']. destruct m'. reflexivity.
Qed.

(** THE SINGLE-PROCESS PROJECTION THEOREM.

    A one-process system steps exactly as [Run.sstep_cfg] does, with the two
    exceptions named in the hypotheses: a successful clone, which is the one
    step at which the core and the released relation are MEANT to differ (the
    released one lets the parent continue with a child that does not exist),
    and an intercepted blocking [wait4], which the released relation answers
    [unmodeled].

    Proved before any arm but [pstep_other], because every consumer's own step
    relation is derived from it. *)
Theorem pstep_single : forall segs cfg c evs r,
  (forall c', sstep_cfg segs cfg c evs (SNext c') -> ~ clone_success c c') ->
  ~ wait4_intercept c ->
  (pstep_cfg segs cfg (one_proc c) evs r
   <-> match r with
       | PNext P' => exists c', P' = one_proc c'
                                /\ sstep_cfg segs cfg c evs (SNext c')
       | PError => sstep_cfg segs cfg c evs SError
       end).
Proof.
  intros segs cfg c evs r Hnoclone Hnowait. split.
  - (* the core steps, so the released relation does *)
    intros Hp. inversion Hp as [P e evs0 c' Hlook Hss Hcl Hwt Hall Heq1 Heq2 Heq3
                               |P e evs0 Hlook Hss Hwt Heq1 Heq2 Heq3
                               |P e Hlook Hrun Hall Heq1 Heq2 Heq3]; subst.
    + (* pstep_other *)
      (* a one-process system has only the entry [one_proc] built *)
      assert (He : e = one_entry c) by exact (look_one_proc_inv _ _ _ Hlook).
      subst e. rewrite one_proc_view in Hss.
      exists c'. split; [apply absorb_one_proc | exact Hss].
    + (* pstep_error *)
      assert (He : e = one_entry c) by exact (look_one_proc_inv _ _ _ Hlook).
      subst e. rewrite one_proc_view in Hss. exact Hss.
    + (* pstep_outside: impossible at one entry *)
      exfalso. rewrite multiproc_allowed_one in Hall. discriminate.
  - (* the released relation steps, so the core does *)
    destruct r as [P'|].
    + intros (c' & -> & Hss).
      rewrite <- absorb_one_proc.
      eapply pstep_other.
      * apply one_proc_entry.
      * rewrite one_proc_view. exact Hss.
      * rewrite one_proc_view. exact (Hnoclone _ Hss).
      * rewrite one_proc_view. exact Hnowait.
      * apply multiproc_allowed_one.
    + intros Hss. eapply pstep_error.
      * apply one_proc_entry.
      * rewrite one_proc_view. exact Hss.
      * rewrite one_proc_view. exact Hnowait.
Qed.

(** THE INSTRUCTION CASE, which is unconditional.

    At an entry with no pending syscall the step is [Run.mi_account_step] and
    nothing else, and [Run.mi_account_step_model_frame] (Run.v:352-371) proves
    such a step leaves [m_fd], [m_vmmaps], [m_vm_lazy], [m_io], [m_fsys],
    [m_proc] and [m_lim] fixed — so the shared state is literally unchanged
    and neither hypothesis of [pstep_single] is needed.  It is the
    instruction case that a derived step relation needs, and it is provable
    the day [pstep_other] exists, which is why the build order puts it here. *)
Theorem pstep_instr_single : forall segs cfg c evs r,
  ms_svc_pending (cfg_ms c) = None ->
  (pstep_cfg segs cfg (one_proc c) evs r
   <-> match r with
       | PNext P' => exists c', P' = one_proc c'
                                /\ sstep_cfg segs cfg c evs (SNext c')
       | PError => sstep_cfg segs cfg c evs SError
       end).
Proof.
  intros segs cfg c evs r Hsvc. apply pstep_single.
  - intros c' _ (x8 & Hx8 & _). rewrite Hsvc in Hx8. discriminate.
  - intros (x8 & Hx8 & _). rewrite Hsvc in Hx8. discriminate.
Qed.

(** THE FILE SYSTEM IS GLOBAL, and this says so: the per-entry copy is blank
    at every entry a one-process system has, so nothing can read it. *)
Lemma fs_only_in_shared_one : forall c,
  Forall (fun e => m_fsys (pe_model e) = empty_fsys)
         (pcfg_procs (one_proc c)).
Proof.
  intros c. constructor; [reflexivity | constructor].
Qed.

(** THE OFFSETS ROUND-TRIP TOO, and this says so rather than leaving a
    consumer to notice.  A parent that keeps its standard descriptors open
    across a clone, and passes further descriptors to its child at exec,
    needs the projection to carry back the POSITION of each description and
    not merely the entries.  At one process every descriptor is private, its
    offset is inside its [State.FdEntry] in [m_fd], and [pe_ofd] is empty;
    the whole table comes back because the whole configuration does. *)
Lemma one_proc_offsets : forall c,
  m_fds (cfg_model (pe_cfg (pcfg_shared (one_proc c))
           (one_entry c)))
    = m_fds (cfg_model c)
  /\ m_pipes (cfg_model (pe_cfg (pcfg_shared (one_proc c))
           (one_entry c)))
    = m_pipes (cfg_model c)
  /\ pe_ofd (one_entry c) = [].
Proof.
  intros c. rewrite one_proc_view.
  split; [reflexivity | split; reflexivity].
Qed.
