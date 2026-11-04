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
(** [Ns.Clone.clone_ns_exact], the namespace tables' own answer to a clone,
    which the forced-only filter of [px_clone_fail] reads
    ([clone_table_kept]).  Required, not imported: no name of it is
    needed here but that one. *)
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Clone.
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

(** WHAT THE CORE KNOWS ABOUT A PROCESS THAT ITS MODEL DOES NOT SAY, kept
    beside the table rather than in [ProcessEntry]: an entry's fields are
    what statements about the reap name, and this is the core's own
    bookkeeping.

    [pm_ns_stale]: the namespace bits (of [CLONE_NEWUSER], [CLONE_NEWNET],
    [CLONE_NEWPID]) the process was created under, through its own clone or
    an ancestor's, that its namespace context ([pe_nsctx]) does NOT
    reflect.  Under [Ns.Ext.no_ext] a clone with namespace bits leaves the
    child the parent's context and the parent's model copy, which is not
    the child's Linux view: in a new user namespace with no [uid_map] the
    id calls answer the overflow id 65534 and the capability sets are
    full; in a new network namespace no connection from the environment
    can arrive.  The exact behaviour is the namespace extension's
    ([Ns.Ext.ext_clone] builds the child's context); until an extension
    reflects a namespace, [peer_refused_b] stops the core answering the calls
    that namespace changes.  An absent entry reads as no bit
    ([meta_look]).

    [pm_sid]: the session id the process inherited at its clone, when the
    core knows it, ALWAYS IN THE HOST'S PID NUMBERING: if the parent had
    led a session by then ([setsid]), the parent's pid, which is its table
    key for an entry that is not the root and its pinned tid for the root;
    else what the parent inherited.  [None] for the root, whose session the
    launching environment chose.  A setsid answered by the namespace layer
    in a new pid namespace sets [m_setsid_succeeded] and never writes a
    namespace pid into [m_tid], so the key, not [m_tid], is the session id
    of such a leader; translating it into a reader's pid namespace is the
    job of a getsid arm of that layer.  Read by getsid ([answer_ok_b]). *)
Record ProcMeta := mkMeta {
  pm_ns_stale : Z;
  pm_sid      : option word
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
  sh_ns    : NsState;
  sh_meta  : list (Pid * ProcMeta)
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
           (sh_ofd S) (sh_pipes S) (sh_ns S) (sh_meta S).

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
    otherwise be answered against a private copy.  The list is three lists.

    CORE-ANSWERED ([multiproc_core_sysnos]): exit, exit_group, clone, wait4
    and clone3.  Each acts on another process (the orphaning [absorb] does,
    the child, the reap), and the arms below answer it.

    PRIVATE, CLASS (A) ([multiproc_private_sysnos]).  THE CLASS RULE: the
    released spec, run on the caller's spliced view ([pe_cfg]), reads and
    writes only the caller's registers, its memory, and the per-entry parts
    of its model ([m_fd], [m_vm], [m_proc], [m_lim]); it leaves [m_fsys],
    [m_io] and [m_time] as it found them; and no answer it gives depends on
    another process.  So the step changes no other entry's view, and the
    only write it makes to another entry's record is the orphaning [absorb]
    does when the call kills the caller (kill, tkill, tgkill,
    rt_sigprocmask), as
    at exit.  [Checks.ProcsPrivateFrame] proves this for every number below.
    Every descriptor kind a live peer can hold a copy of ([FdChannel],
    [FdDir], [FdDevNull], [FdUrandom], [FdOpaque]) is one
    [Fork.clone_no_shared_file_b] lets through a clone because no modeled
    arm reads state the copy shares, and every file, socket or pipe
    descriptor was made after the last clone, so pipes and sockets are
    private here.  The one descriptor made BEFORE a clone that a peer
    can share is an inherited file ([State.OInherited]), and its offset
    is live in exactly one entry of the configuration: a clone of either
    word leaves the caller [OInherited None], which holds no offset, and
    the child the live entry ([Fork.forfeit_inherited]), and no modeled
    call copies an opaque descriptor within one table
    ([File.dup_modeled_entry]).  So no peer's call moves the offset a
    call here reads.  setns (268) reads only the kind of the caller's
    descriptor (an O_PATH file, a namespace model descriptor, or any
    other), which no process changes, and answers an errno that changes
    nothing.  Two class-(A) calls are admitted with a gate as well.
    flock (32) grants a lock when no descriptor of the CALLER names the
    file, and no lock state exists, so it is refused while another entry
    has a descriptor on the same path ([peer_refused_b]).  prctl (167)
    with PR_SET_PDEATHSIG asks Linux to signal the caller when its parent
    exits, and the exit arm does not send that signal; so a step that
    would halt an entry while one of its running children holds a nonzero
    parent-death signal is refused ([step_refused_b]), and the signal is
    never lost.

    SHARED, WRITTEN BACK, CLASS (B) ([multiproc_shared_sysnos]): 46 48 56
    62 63 64 65 66 67 68 78 79 202 242 439.  They read or write [m_fsys] or
    [m_io], which [pe_cfg] splices and [shared_absorb] writes back.  The
    write-back is half the argument; the other half is that every OTHER
    entry's private state stays consistent with the new shared state.  What
    a peer holds that names [m_fsys] is a file descriptor ([FdFile p off]
    and its three siblings: a path and an offset of its own, opened after
    the last clone, so its own open file description as in Linux) and a
    stat pin (fstat's, which holds no size or time).  An inherited file
    ([State.OInherited]) names no path of [m_fsys]: it holds its bytes and
    its offset in the entry, it was opened before the clone, and its offset
    is live in exactly one entry of the configuration (class (A) above), so
    a [read] through it moves an offset no peer holds.  The descriptors
    and pins stay valid
    because no (B) call removes a path from [m_fsys]: the writers insert or
    replace ([Fs.fs_set]), and removal is unlinkat's, which is (C).  A
    truncation (openat's O_TRUNC, ftruncate) under a peer's offset past the
    new end is end of file for the peer's read: [Fs.file_read] delivers no
    byte at or past the end and the arm returns 0, as Linux does.  A peer
    holds nothing that names [m_io]: stdin, the random stream and the
    connection queue live there alone, so one consumption is seen by all,
    as one shared open file description is in Linux.  AN EXISTING
    APPROXIMATION, not a multi-process one: accept and accept4 answer from
    one global connection queue whichever listening socket the caller
    holds, as they already do for one process holding two listeners; the
    frame lemmas prove the queue is consumed once, not that a connection
    is routed to the listener it was meant for.  An eventfd made
    before a clone IS a per-process copy ([FdOpaque (OEventFd _)], one
    counter per table where Linux has one), and every (B) arm declines it,
    so none answers from the copy; [Checks.ProcsSharedFrame] proves all of
    this, the decline included, so an arm that one day answers an eventfd
    counter fails that Check until the counter is moved into [shared].

    SYNCED ([multiproc_synced_sysnos]): 101 nanosleep, 113 clock_gettime,
    160 uname and 80 fstat.  Each reads per-entry state that stands for one
    value Linux shares: CLOCK_MONOTONIC ([State.timest_clock]), the UTS name
    of the namespace ([procst_utsname], pinned at its first read; nothing
    modeled changes it after), and a file's [struct stat]
    ([procst_statpins], pinned at the first fstat of a path; per inode in
    Linux).  None of them can move into the spliced state:
    [MustExitP.view_frame_absorb] fixes the view at [m_fsys] and [m_io].
    So the core keeps the copies agreeing where they are read: an entry at
    one of these calls whose copy is behind another entry's (a lower clock,
    no UTS pin where a peer has one, no stat pin for the descriptor's path
    where a peer has one) first takes a silent step, [pstep_sync], that
    brings its copy up from the table ([sync_result]); only then does the
    released step answer ([sync_pending_b] gates [pstep_other]).  Every
    clock reading starts at or after every reading any process has made,
    which is the monotonicity Linux gives across processes, and a UTS name
    or a stat pin is the one the first reader in any process saw.

    GATED ([multiproc_gated_sysnos]): 35 unlinkat and 261 prlimit64.
    unlinkat checks only the CALLER's descriptors for one naming the path
    it removes; a step at 35 that removes a path another entry's file
    descriptor or stat pin names is refused ([step_refused_b], read off
    the step's result as [clone_success_b] is).  Otherwise that entry's
    descriptor would name a removed file, or a re-created one Linux keeps
    apart by inode.  RLIMIT_CORE is
    inherited at fork and independent after it, so a process's pin may not
    be taken from a peer's; an entry whose pin is still absent cannot know
    the inherited value, so its call is refused ([peer_refused_b], an
    explicit error).  A pinned entry answers from its own copy, which is
    right per process.  The exact version, a table of which entries still
    share an unread fork-time value, is not needed until a target calls
    prlimit64 from both sides of a clone.

    PIDS ([multiproc_pid_sysnos]): 96 set_tid_address, 172 getpid, 178
    gettid, 157 setsid, 156 getsid, 173 getppid.  The released specs pin
    the tid by a free choice and answer getsid and getppid by a fresh one;
    with a peer the answer is fixed by the table.  A non-root entry's pid
    is its key, the value its parent's clone returned; the root's is its
    tid, pinned by its own first call.  So [answer_ok_b] keeps only the
    released answers that agree: a non-root entry pins its key; the root
    pins a value no other entry's key holds; getppid answers the parent's
    pid (an orphan, whose parent exited, keeps the released choice: Linux
    reparents it to a reaper the model does not name); getsid answers the
    session the entry inherited at its clone ([pm_sid]) until its own
    setsid, and the released choice when no ancestor led one.  A child of
    the root asking getppid while the root's tid is unpinned first takes
    a silent step, [pstep_pin_root], that pins it.  What cannot be
    answered is refused ([peer_refused_b]): a pid call in a new pid
    namespace the entry's context does not reflect, any pid call while
    the root's tid equals another entry's key (a clone below the root
    chose it), and a tid pin that disagrees with the key.

    Every modeled number is in one of these lists ([multiproc_sysnos] is
    [Specs.modeled_sysnos], [Checks.ProcsPrivateFrame.multiproc_partition]);
    a number outside them takes [pstep_outside]. *)
Definition multiproc_core_sysnos : list Z := [93; 94; 220; 260; 435]%Z.

Definition multiproc_clock_sysnos : list Z := [101; 113]%Z.

Definition multiproc_synced_sysnos : list Z := [80; 101; 113; 160]%Z.

Definition multiproc_gated_sysnos : list Z := [35; 261]%Z.

Definition multiproc_pid_sysnos : list Z := [96; 156; 157; 172; 173; 178]%Z.

(** The numbers that pin the caller's tid. *)
Definition multiproc_tid_sysnos : list Z := [96; 157; 172; 178]%Z.

(** The numbers the core answers through arms of its own beyond the core
    list: the synced, the gated and the pid ones. *)
Definition multiproc_owned_sysnos : list Z :=
  multiproc_synced_sysnos ++ multiproc_gated_sysnos ++ multiproc_pid_sysnos.

Definition multiproc_private_sysnos : list Z :=
  [ 17;  19;  20;  21;  22;  23;  24;  25;  29;  32;  57;  59;  61;  72;
    73;  74;  82;  83;  85;  90;  91;  98;  99; 114; 119; 123; 124; 129; 130;
   131; 132; 134; 135; 144; 146; 147; 148; 149; 150; 158; 159; 167; 169; 174;
   175; 176; 177; 198; 199; 200; 201; 203; 204; 205; 206; 207; 208; 209;
   210; 211; 212; 214; 215; 216; 222; 226; 233; 268; 278; 436]%Z.

Definition multiproc_shared_sysnos : list Z :=
  [46; 48; 56; 62; 63; 64; 65; 66; 67; 68; 78; 79; 202; 242; 439]%Z.

Definition multiproc_sysnos : list Z :=
  (multiproc_core_sysnos ++ multiproc_owned_sysnos)
    ++ multiproc_private_sysnos ++ multiproc_shared_sysnos.

Definition multiproc_allowed (P : pconfig) (c : config) : bool :=
  match ms_svc_pending (cfg_ms c) with
  | None => true
  | Some x8 =>
      Nat.leb (List.length (pcfg_procs P)) 1%nat
      || List.existsb (Z.eqb (bv_unsigned x8)) multiproc_sysnos
  end.

(** The guard without the class-(A) and class-(B) numbers: no call
    pending, one entry, or a number the core answers through arms of its
    own (the core list and the owned list). *)
Definition multiproc_base (P : pconfig) (c : config) : bool :=
  match ms_svc_pending (cfg_ms c) with
  | None => true
  | Some x8 =>
      Nat.leb (List.length (pcfg_procs P)) 1%nat
      || List.existsb (Z.eqb (bv_unsigned x8))
           (multiproc_core_sysnos ++ multiproc_owned_sysnos)
  end.

(** A class-(A) number is pending. *)
Definition multiproc_private (c : config) : bool :=
  match ms_svc_pending (cfg_ms c) with
  | None => false
  | Some x8 => List.existsb (Z.eqb (bv_unsigned x8)) multiproc_private_sysnos
  end.

(** A class-(B) number is pending. *)
Definition multiproc_shared (c : config) : bool :=
  match ms_svc_pending (cfg_ms c) with
  | None => false
  | Some x8 => List.existsb (Z.eqb (bv_unsigned x8)) multiproc_shared_sysnos
  end.

(** A number the classes admit beyond the core's own is pending. *)
Definition multiproc_classed (c : config) : bool :=
  multiproc_private c || multiproc_shared c.

Lemma multiproc_allowed_split : forall P c,
  multiproc_allowed P c = multiproc_base P c || multiproc_classed c.
Proof.
  intros P c.
  unfold multiproc_allowed, multiproc_base, multiproc_classed, multiproc_private,
    multiproc_shared, multiproc_sysnos.
  destruct (ms_svc_pending (cfg_ms c)); [|reflexivity].
  rewrite (List.existsb_app _ (multiproc_core_sysnos ++ multiproc_owned_sysnos)),
    (List.existsb_app _ multiproc_private_sysnos).
  apply orb_assoc.
Qed.

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
    opaque descriptor ([FdOpaque]) stays per-process too: a namespace
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
  | FdSeqpacket _ _ _ => None
    (* unreachable: the clone gate declines while an end is open
       ([Kernel.Fork.clone_no_shared_file_b]) *)
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
                     (sh_pipes S) (sh_ns S) (sh_meta S),
            (fd, i))
  end.

(* =========================================================================
   The child a successful clone creates
   ========================================================================= *)

(** The child's machine state: the parent's successor with a0 = 0, and the
    stack pointer the call gives the child.  [set_reg] takes a PHYSICAL
    register number; a0 is x10 and sp is x2.

    WHICH CALL MOVES THE CHILD'S STACK, and the reason the argument is not
    read blindly.  Linux's [copy_thread] (arch/riscv/kernel/process.c)
    seats [usp] in the child's sp only when it is non-zero; otherwise the
    child keeps the parent's.
    - [clone] (220): [usp] is argument 1, [newsp].  Legacy [clone] accepts
      an arbitrary one and it changes the CHILD's stack pointer
      (Fork.v:753-764); zero, which musl's [fork] passes, keeps the
      parent's.
    - [clone3] (435): argument 1 is the SIZE of [struct clone_args], 88
      at the one modeled size, not a stack.  [usp] is the struct's
      [stack] field, which the released spec requires to be zero
      (Fork.v:957), so the child keeps the parent's.
    Reading argument 1 for both gave every [clone3] child sp = 88.
    [clone_child_sp] is the stack a successful call seats, [None] for the
    parent's. *)
Definition clone_child_sp (c : config) : option word :=
  match ms_svc_pending (cfg_ms c) with
  | Some x8 =>
      if Z.eqb (bv_unsigned x8) 220%Z then
        if w_is0 (ms_gpr (cfg_ms c) 1) then None else Some (ms_gpr (cfg_ms c) 1)
      else None
  | None => None
  end.

Definition child_ms (c c' : config) : machine_state :=
  let base := set_reg (cfg_ms c') 10 (Z_to_bv 64 0) in
  match clone_child_sp c with
  | None => base
  | Some sp => set_reg base 2 sp
  end.

(** The child's process record: the parent's, with the NINE fields that
    are the CHILD's own cleared, and every other field copied.

    - [procst_tid] is [None]: the child's differs on Linux, and clone
      admission itself reads it (Fork.v:679-681), so declining [getpid]
      does not make an inherited one unobservable.
    - [procst_setsid_succeeded] is false.  The flag means exactly "this
      process's [setsid] has succeeded, so it leads its session"
      ([Sys.Kernel.Sys.setsid_spec]: [signal->leader], which only
      [ksys_setsid] sets and nothing clears).  Leadership does not
      inherit: [copy_signal] (kernel/fork.c) sets the new thread group's
      [sig->leader = 0], and the child's new pid is in its parent's
      process group, so it leads no group either and its own [setsid]
      succeeds.  Copying the parent's flag answered that call -EPERM, an
      answer Linux does not give.
    - [procst_children] is false: the child has none, and copying the
      parent's pre-clone record is not enough, because on a SECOND clone
      the parent's is already set.
    - [procst_sigabrt_pending] and [procst_sigpipe_pending] are false: a
      new thread group starts with no pending signal ([copy_process],
      kernel/fork.c).
    - [procst_pdeath_signal] is 0: [copy_process] clears it.
    - [procst_child_pids] is []: [copy_process] starts [p->children]
      empty (kernel/fork.c).
    - [procst_reparent_unseen] is false: [copy_process] clears the
      child's [pdeath_signal], and its parent is alive at the clone.
    - [procst_reparent_moved] is false: the child's parent pid is its
      parent's key, given below, so it has not moved.

    The four launch facts ([procst_channel_reader], [procst_sigpipe_default],
    [procst_sigpipe_terminal], [procst_selfkill_terminal]) are copied, and so are the no-new-privs bit
    ([copy_process] sets it in
    the child when the parent has it) and the dumpable mode ([mm_init]
    keeps the parent's MMF_DUMPABLE bits; under CLONE_VM the mm is the
    parent's own).  The child's parent pid is its parent's pid [ppid], the
    parent's key in the process table, which the core always knows:
    [copy_process] sets [p->real_parent = current] (kernel/fork.c), and
    [getppid] answers that task's tgid.  It is not the parent's PINNED tid:
    a child cloned before its parent's first [getpid] would otherwise start
    at 0.  The inheritable capability set copies with the credentials.
    Kernel citations, read at v6.18.44, identical at v6.18.46. *)
Definition child_proc (ppid : Pid) (ps : ProcState) : ProcState :=
  mkProcState (procst_halted ps) None (procst_creds ps)
              false (procst_sigmask ps)
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
              (procst_sigpipe_terminal ps)
              (Z_to_bv 64 0)
              [] (procst_no_new_privs ps) (procst_dumpable ps)
              ppid
              (procst_cap_inheritable ps)
              false false
              (procst_selfkill_terminal ps) (procst_cgroup_bpf_setsockopt ps).

Definition with_proc (ps : ProcState) (m : Model) : Model :=
  mkModelOf (m_fd m) (m_vm m) (m_io m) (m_fsys m) ps (m_lim m) (m_time m).

Definition child_entry (e : ProcessEntry) (c c' : config) (q : Pid)
    : ProcessEntry :=
  mkEntry q (Some (pe_pid e)) (child_ms c c')
          (clear_shared (with_proc (child_proc (pe_pid e) (m_proc (pe_model e)))
                                   (pe_model e)))
          (pe_ofd e) (pe_nsctx e).

(** The flag word of a pending clone: argument 0 of [clone] (220);
    [SIGCHLD] for [clone3] (435), the word of the one image it resolves.

    KNOWN GAP until the namespace extension takes the decoded argument
    record ([Fork.CloneIn]) in place of this word.  Closing it takes two
    answers of the extension, not one.  The first is [CnErr EINVAL]
    where [Fork.clone_arg_checks] fires on a [Fork.CiArgs] record.  It
    does not reach every call the core now answers: a [clone3] struct
    whose own tests refuse it ([Fork.CdErr]) and a [clone3] whose struct
    range [access_ok] refuses (-EFAULT) have no record at all
    ([clone_in_of] gives [Fork.CiNoArgs]), so no rule over a record can
    run for them.  The second answer covers those: for a caller in the
    NAMESPACE world whose [clone_in_of] is [Fork.CiNoArgs] while the
    released step answers, [CnUnmodeled].  For a caller in the released
    world the extension keeps [Ns.Ext.released_clone], which has no
    [CnUnmodeled] (Ns/Ext.v) and which [NsProcs.ns_flat_iff] rests on;
    there these calls keep today's released answer.  (A struct whose own
    tests pass and whose record the argument checks refuse is not in
    this class: [clone_in_of] gives its record, and the first answer
    reaches it.)  The released step now answers -EINVAL for a word the
    argument checks refuse (and, for [clone3], a struct its own tests
    refuse: [Fork.clone3_einval_b]), while the extension still sees this
    word, so:
    - a [clone3] struct [Fork.clone3_einval_b] refuses reaches the
      extension as [SIGCHLD].  For a namespace-world caller under [Ns.Spec.ns_ext]
      whose [clone_ns_exact] is [CnOk] there, the -EINVAL has no step
      under the clone environment [Ns.Clone.clone_tables_failures]
      (before, the call was the error step), and under
      [Ext.any_clone_failure] it is a failure step whose state may be
      [Ns.Clone]'s cursor advance, a state Linux does not reach, since
      these checks come before [alloc_pid]; where [clone_ns_exact] is
      [CnUnmodeled] it is still the error step;
    - under [Ext.no_ext], whose clone is [Ns.Ext.released_clone], a
      refused [clone] (220) word with a namespace bit (for example
      CLONE_NEWNS or CLONE_NEWUSER with CLONE_FS) has no step under
      [Ns.Clone.clone_tables_failures], for which [clone_ns_exact] is
      [CnUnmodeled] (before, the call was the error step).  Under
      [Ns.Spec.ns_ext] such a word keeps the error step
      ([px_clone_unmodeled]): every refused word holds a bit outside
      [Ns.Clone]'s mask.
    - under [Ext.no_ext] and [Ns.Clone.clone_tables_failures], a
      namespace-world caller's refused [clone] or [clone3], with or
      without a namespace bit, has no step either: [clone_ns_exact] is
      not [CnErr EINVAL] for its word, and [Ns.Ext.released_clone] never
      gives [CnUnmodeled].
    Each is a missing or an extra outcome of a call the model declined
    before, never a changed answer to a call it answered. *)
Definition clone_flags_of (c : config) : Z :=
  match ms_svc_pending (cfg_ms c) with
  | Some x8 => if Z.eqb (bv_unsigned x8) 220 then bv_unsigned (ms_gpr (cfg_ms c) 0) else SIGCHLD
  | None => 0%Z
  end.

(** THE DECODED ARGUMENTS of a pending clone, as the namespace extension
    is to receive them ([Fork.CloneIn]).
    - [clone] (220): the record of its registers
      ([Fork.clone_args_of_clone]); none for an a0 with a bit above 31.
    - [clone3] (435): the record of its struct ([Fork.clone3_pre]), read
      as the released step reads it ([Fork.clone3_spec]: the size test,
      then [State.copy_bytes_map] over the pre-syscall memory, which
      [Run.sys_input] gives as [ms_read_byte] whatever the segments,
      [clone_in_of_input]), and only for a record whose call
      [Fork.clone3_spec] answers: the fork image, which it answers off
      the raw struct ([Fork.clone3_fork_args_b]), or a record the
      argument checks refuse.  A struct its own tests refuse or
      decline, a size or a copy it declines or refuses, and a record it
      declines give none.
    - Any other call, and no pending call: none.
    No rule of the core reads it yet. *)
Definition clone_in_of (c : config) : CloneIn :=
  let ms := cfg_ms c in
  match ms_svc_pending ms with
  | Some x8 =>
      if Z.eqb (bv_unsigned x8) 220 then
        match clone_args_of_clone (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2)
                (ms_gpr ms 3) (ms_gpr ms 4) with
        | Some r => CiArgs r
        | None => CiNoArgs
        end
      else if Z.eqb (bv_unsigned x8) 435 then
        if negb (bv_eqb (ms_gpr ms 1) (Z_to_bv 64 CLONE_ARGS_SIZE)) then CiNoArgs
        else
          match copy_bytes_map (ms_read_byte ms) (ms_gpr ms 0) CLONE_ARGS_SIZE with
          | Some bs =>
              match clone3_pre bs with
              | CdArgs r =>
                  if clone3_fork_args_b bs || clone_arg_checks r then CiArgs r
                  else CiNoArgs
              | _ => CiNoArgs
              end
          | None => CiNoArgs
          end
      else CiNoArgs
  | None => CiNoArgs
  end.

(** [clone_in_of] reads the call's arguments and memory as the released
    step's input carries them, for any segments. *)
Lemma clone_in_of_input : forall segs c x8,
  ms_svc_pending (cfg_ms c) = Some x8 ->
  clone_in_of c =
  (let i := sys_input segs (cfg_ms c) x8 in
   if Z.eqb (bv_unsigned x8) 220 then
     match clone_args_of_clone (in_arg i 0) (in_arg i 1) (in_arg i 2)
             (in_arg i 3) (in_arg i 4) with
     | Some r => CiArgs r
     | None => CiNoArgs
     end
   else if Z.eqb (bv_unsigned x8) 435 then
     if negb (bv_eqb (in_arg i 1) (Z_to_bv 64 CLONE_ARGS_SIZE)) then CiNoArgs
     else
       match copy_bytes_map (in_mem i) (in_arg i 0) CLONE_ARGS_SIZE with
       | Some bs =>
           match clone3_pre bs with
           | CdArgs r =>
               if clone3_fork_args_b bs || clone_arg_checks r then CiArgs r
               else CiNoArgs
           | _ => CiNoArgs
           end
       | None => CiNoArgs
       end
   else CiNoArgs).
Proof.
  intros segs c x8 H. unfold clone_in_of. cbv zeta. rewrite H. reflexivity.
Qed.

(** NO RECORD FOR A STRUCT [clone3]'S OWN TESTS REFUSE OR DECLINE.  Where
    the copied struct gives [Fork.CdErr] or [Fork.CdDecline], a pending
    [clone3] has no record, whatever the released step answers for it.
    The [Fork.CdErr] half is the second answer the namespace extension
    owes a NAMESPACE-WORLD caller: at [Fork.CLONE_ARGS_SIZE] the core
    answers -EINVAL ([Fork.clone3_einval_b]) while the call's
    [Fork.CloneIn] is [Fork.CiNoArgs], as for the exit signal of 65 in
    [Checks.Cases.Kernel.Fork.clone3_einval_words]; at any other size
    the core declines ([Checks.ProcessCreation.clone3_other_size_unmodeled]),
    and the lemma holds there too.  The [Fork.CdDecline] half owes
    nothing: the core declines there, as
    [Checks.Cases.Kernel.Fork.clone3_newtime_declines] shows for the
    CLONE_NEWTIME image. *)
Lemma clone_in_of_no_record : forall c bs x8,
  ms_svc_pending (cfg_ms c) = Some x8 ->
  bv_unsigned x8 = 435%Z ->
  copy_bytes_map (ms_read_byte (cfg_ms c)) (ms_gpr (cfg_ms c) 0) CLONE_ARGS_SIZE = Some bs ->
  (forall r, clone3_pre bs <> CdArgs r) ->
  clone_in_of c = CiNoArgs.
Proof.
  intros c bs x8 Hp H435 Hcopy Hno. unfold clone_in_of. cbv zeta. rewrite Hp.
  cbv iota. rewrite H435.
  replace (Z.eqb 435%Z 220%Z) with false by reflexivity.
  replace (Z.eqb 435%Z 435%Z) with true by reflexivity.
  cbv iota.
  destruct (negb (bv_eqb (ms_gpr (cfg_ms c) 1) (Z_to_bv 64 CLONE_ARGS_SIZE)));
    [reflexivity|].
  rewrite Hcopy.
  destruct (clone3_pre bs) as [| |r] eqn:Hpre; [reflexivity|reflexivity|].
  exfalso. apply (Hno r). congruence.
Qed.

(** THE RECORD AND THE WORD THE CORE PASSES TODAY ([clone_flags_of]).  The
    record keeps flags and exit signal apart ([Fork.clone_args_split]), so
    the word [Z.lor flags exit_signal] gives both back.  For [clone] that
    word is [clone_flags_of]'s.  For [clone3], [clone_flags_of] is
    [SIGCHLD] whatever the struct holds, and the record's word equals it
    exactly when the record is a plain fork's: no flag, exit signal
    [SIGCHLD]. *)
Theorem clone_in_of_flags : forall c r,
  clone_in_of c = CiArgs r ->
  clone_args_split r
  /\ exists x8, ms_svc_pending (cfg_ms c) = Some x8
     /\ ((bv_unsigned x8 = 220%Z
          /\ Z.lor (cla_flags r) (cla_exit_signal r) = clone_flags_of c)
         \/ (bv_unsigned x8 = 435%Z /\ clone_flags_of c = SIGCHLD
             /\ (Z.lor (cla_flags r) (cla_exit_signal r) = clone_flags_of c
                 <-> cla_flags r = 0%Z /\ cla_exit_signal r = SIGCHLD))).
Proof.
  intros c r H. unfold clone_in_of in H. cbv zeta in H. unfold clone_flags_of.
  destruct (ms_svc_pending (cfg_ms c)) as [x8|] eqn:Hp; cbv iota in H |- *;
    [|discriminate H].
  destruct (Z.eqb (bv_unsigned x8) 220) eqn:H220; cbv iota in H |- *.
  - destruct (clone_args_of_clone (ms_gpr (cfg_ms c) 0) (ms_gpr (cfg_ms c) 1)
                (ms_gpr (cfg_ms c) 2) (ms_gpr (cfg_ms c) 3) (ms_gpr (cfg_ms c) 4))
      as [r0|] eqn:Hr; cbv iota in H; [|discriminate H].
    injection H as <-.
    split; [exact (clone_args_of_clone_split _ _ _ _ _ _ Hr)|].
    exists x8. split; [reflexivity|]. left.
    split; [apply Z.eqb_eq; exact H220|].
    exact (clone_args_of_clone_word _ _ _ _ _ _ Hr).
  - destruct (Z.eqb (bv_unsigned x8) 435) eqn:H435; cbv iota in H; [|discriminate H].
    destruct (negb (bv_eqb (ms_gpr (cfg_ms c) 1) (Z_to_bv 64 CLONE_ARGS_SIZE)));
      cbv iota in H; [discriminate H|].
    destruct (copy_bytes_map (ms_read_byte (cfg_ms c)) (ms_gpr (cfg_ms c) 0) CLONE_ARGS_SIZE)
      as [bs|]; cbv iota in H; [|discriminate H].
    destruct (clone3_pre bs) as [| |r0] eqn:Hp3; cbv iota in H; try discriminate H.
    destruct (clone3_fork_args_b bs || clone_arg_checks r0); cbv iota in H;
      [|discriminate H].
    injection H as <-.
    pose proof (clone3_pre_split _ _ Hp3) as Hs.
    split; [exact Hs|].
    exists x8. split; [reflexivity|]. right.
    split; [apply Z.eqb_eq; exact H435|].
    split; [reflexivity|].
    exact (clone_args_word_sigchld r0 Hs).
Qed.

(** THE NAMESPACE PREMISE CARRIES OVER.  Where the word the core passes
    today has no namespace bit ([Ns.Ext.has_ns_bits], over
    [Ns.Ext.clone_ns_bits]), a record [clone_in_of] gives has none
    either, or the argument checks refuse it.  The second case is
    [clone3]'s only: its word today is [SIGCHLD] whatever the struct
    holds, and several refusing rows need a namespace bit (CLONE_NEWNS
    or CLONE_NEWUSER with CLONE_FS, CLONE_THREAD with CLONE_NEWUSER or
    CLONE_NEWPID).  A refused record makes no namespace. *)
Theorem clone_in_of_ns_bits : forall c r,
  has_ns_bits (clone_flags_of c) = false ->
  clone_in_of c = CiArgs r ->
  Z.land (cla_flags r) clone_ns_bits = 0%Z \/ clone_arg_checks r = true.
Proof.
  intros c r Hns H.
  destruct (clone_arg_checks r) eqn:Hc; [right; reflexivity|left].
  unfold clone_in_of in H. cbv zeta in H. unfold clone_flags_of in Hns.
  destruct (ms_svc_pending (cfg_ms c)) as [x8|] eqn:Hp; cbv iota in H, Hns;
    [|discriminate H].
  destruct (Z.eqb (bv_unsigned x8) 220) eqn:H220; cbv iota in H, Hns.
  - destruct (clone_args_of_clone (ms_gpr (cfg_ms c) 0) (ms_gpr (cfg_ms c) 1)
                (ms_gpr (cfg_ms c) 2) (ms_gpr (cfg_ms c) 3) (ms_gpr (cfg_ms c) 4))
      as [r0|] eqn:Hr; cbv iota in H; [|discriminate H].
    injection H as <-.
    unfold has_ns_bits in Hns. apply negb_false_iff in Hns. apply Z.eqb_eq in Hns.
    unfold clone_args_of_clone in Hr.
    destruct (bv_unsigned (ms_gpr (cfg_ms c) 0) <? 2 ^ 32)%Z; [|discriminate Hr].
    injection Hr as <-. cbn [cla_flags].
    now rewrite <- Z.land_assoc,
      (Z.land_comm (Z.land CLONE_LEGACY_FLAGS (Z.lnot CSIGNAL)) clone_ns_bits),
      Z.land_assoc, Hns, Z.land_0_l.
  - destruct (Z.eqb (bv_unsigned x8) 435) eqn:H435; cbv iota in H; [|discriminate H].
    destruct (negb (bv_eqb (ms_gpr (cfg_ms c) 1) (Z_to_bv 64 CLONE_ARGS_SIZE)));
      cbv iota in H; [discriminate H|].
    destruct (copy_bytes_map (ms_read_byte (cfg_ms c)) (ms_gpr (cfg_ms c) 0) CLONE_ARGS_SIZE)
      as [bs|]; cbv iota in H; [|discriminate H].
    destruct (clone3_pre bs) as [| |r0] eqn:Hp3; cbv iota in H; try discriminate H.
    destruct (clone3_fork_args_b bs || clone_arg_checks r0) eqn:Hor; cbv iota in H;
      [|discriminate H].
    injection H as <-.
    apply orb_true_iff in Hor as [Ha|Hc0]; [|rewrite Hc0 in Hc; discriminate Hc].
    rewrite (clone3_pre_flags bs r0 Hp3).
    unfold clone3_fork_args_b, w_is0 in Ha.
    repeat (apply andb_true_iff in Ha as [Ha ?]).
    apply bv_eqb_eq in Ha. rewrite Ha. vm_compute. reflexivity.
Qed.

(** The metadata of [p]; an absent pid reads as no stale namespace. *)
Fixpoint meta_look (ms : list (Pid * ProcMeta)) (p : Pid) : ProcMeta :=
  match ms with
  | [] => mkMeta 0 None
  | (k, m) :: r => if bv_eqb k p then m else meta_look r p
  end.

(** Record [m] for [p], in front of anything recorded for it before (a pid
    a reap freed and a later clone reuses). *)
Definition with_meta (S : shared) (p : Pid) (m : ProcMeta) : shared :=
  mkShared (sh_fsys S) (sh_io S) (sh_ofd S) (sh_pipes S) (sh_ns S)
           ((p, m) :: sh_meta S).

(** The child's stale namespaces: its parent's, and each namespace the
    clone's flag word asks for that the child's context does not reflect
    (its id there is still the parent's). *)
Definition ns_stale_child (stale flags : Z) (pctx cctx : NsCtx) : Z :=
  Z.lor stale
    (Z.lor (if Pos.eqb (cx_user cctx) (cx_user pctx) then Z.land flags CLONE_NEWUSER else 0)
      (Z.lor (if Pos.eqb (cx_net cctx) (cx_net pctx) then Z.land flags CLONE_NEWNET else 0)
             (if Pos.eqb (cx_pidns cctx) (cx_pidns pctx) then Z.land flags CLONE_NEWPID else 0))).

Definition child_meta (P : pconfig) (e : ProcessEntry) (cctx : NsCtx) : ProcMeta :=
  let pm := meta_look (sh_meta (pcfg_shared P)) (pe_pid e) in
  mkMeta (ns_stale_child (pm_ns_stale pm)
            (clone_flags_of (pe_cfg (pcfg_shared P) e)) (pe_nsctx e) cctx)
         (if m_setsid_succeeded (pe_model e)
          then (if bv_eqb (pe_pid e) (pcfg_root P) then m_tid (pe_model e) else Some (pe_pid e))
          else pm_sid pm).

(** The configuration a successful clone steps to.  Under no extension the
    child's context is the parent's, so every namespace its flag word asks
    for is recorded stale. *)
Definition clone_result (P : pconfig) (e : ProcessEntry) (c' : config)
    (q : Pid) : pconfig :=
  mkPCfg (replace_in (pcfg_procs P) (pe_pid e) (pe_absorb e c')
            ++ [(q, child_entry e (pe_cfg (pcfg_shared P) e) c' q)])
         (pcfg_root P)
         (with_meta (shared_absorb (pcfg_shared P) c') q (child_meta P e (pe_nsctx e))).

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

(** THE ORPHANING AT EXIT.  When a process ends, Linux reparents its
    children at once ([exit_notify] -> [forget_original_parent],
    kernel/exit.c), to a subreaper or to init, neither of which is a
    process of this table.  So when an entry stops running, every OTHER
    entry that names it as parent gets [pe_parent = None]: no process of
    the table can reap it any more, which is the nearest this model has to
    init adopting it.  Without this a reap drops a zombie whose children
    still name its pid, and a later clone that REUSES the pid would make a
    stranger their parent -- R clones A, A clones G, A exits, R reaps A, R
    clones B with A's old pid, G exits, and B's [wait4] would reap G where
    Linux answers B -ECHILD.

    WHY [m_halted] IS THE ONE TEST.  An entry stops running only through a
    released step that leaves its model halted: every [Run.sstep_cfg] arm
    requires a running model, and the two that end one, [sstep_cfg_exit]
    and [sstep_cfg_killed], both leave [m_halted] set -- a death by signal
    too, because [State.m_killed] reads the halt field through the kill
    flag (State.v:4435-4436), so [m_killed = Some _] implies
    [m_halted = Some _].  Every such step reaches the table through
    [absorb] (or [absorb_x], below, which orphans the same way); the reap
    arms and the clone leave the caller running.

    The exiting entry itself is skipped: it is not its own child in any
    table [pconfig_wf] admits, and skipping it leaves a one-entry table
    unchanged by construction. *)
Definition with_parent (e : ProcessEntry) (par : option Pid) : ProcessEntry :=
  mkEntry (pe_pid e) par (pe_ms e) (pe_model e) (pe_ofd e) (pe_nsctx e).

(** One table slot after [p] exits: a child of [p] other than [p]'s own
    entry loses its parent, and every other slot is unchanged. *)
Definition orphan_one (p : Pid) (kv : Pid * ProcessEntry) : Pid * ProcessEntry :=
  if negb (bv_eqb (fst kv) p)
     && match pe_parent (snd kv) with Some q => bv_eqb q p | None => false end
  then (fst kv, with_parent (snd kv) None)
  else kv.

Definition orphan_children (p : Pid) (ps : list (Pid * ProcessEntry))
    : list (Pid * ProcessEntry) :=
  List.map (orphan_one p) ps.

(** Orphan [p]'s children exactly when the model [p] was left with is over. *)
Definition orphan_at_exit (m : Model) (p : Pid) (ps : list (Pid * ProcessEntry))
    : list (Pid * ProcessEntry) :=
  match m_halted m with
  | Some _ => orphan_children p ps
  | None => ps
  end.

Definition absorb (P : pconfig) (e : ProcessEntry) (c' : config) : pconfig :=
  mkPCfg (orphan_at_exit (cfg_model c') (pe_pid e)
            (replace_in (pcfg_procs P) (pe_pid e) (pe_absorb e c')))
         (pcfg_root P)
         (shared_absorb (pcfg_shared P) c').

(** A one-entry table is unchanged by the orphaning: its only entry is the
    exiting one, which is skipped. *)
Lemma orphan_children_single : forall p e, orphan_children p [(p, e)] = [(p, e)].
Proof.
  intros p e. unfold orphan_children, orphan_one. cbn [List.map fst].
  rewrite bv_eqb_same. reflexivity.
Qed.

(** The orphaning keeps every slot: the table has the same length. *)
Lemma orphan_at_exit_length : forall m p ps,
  List.length (orphan_at_exit m p ps) = List.length ps.
Proof.
  intros m p ps. unfold orphan_at_exit, orphan_children.
  destruct (m_halted m); [|reflexivity].
  induction ps as [|kv r IH]; [reflexivity|].
  cbn [List.map List.length]. rewrite IH. reflexivity.
Qed.

Lemma orphan_at_exit_single : forall m p e, orphan_at_exit m p [(p, e)] = [(p, e)].
Proof.
  intros m p e. unfold orphan_at_exit.
  destruct (m_halted m); [apply orphan_children_single | reflexivity].
Qed.

(** And a running successor orphans nobody. *)
Lemma orphan_at_exit_running : forall m p ps,
  m_halted m = None -> orphan_at_exit m p ps = ps.
Proof. intros m p ps H. unfold orphan_at_exit. rewrite H. reflexivity. Qed.

(* =========================================================================
   The wait4 gate: a caller with a child in the table
   ========================================================================= *)

(** DESIGN NOTE: THE CORE DECIDES EVERY [wait4] OF A CALLER WITH A CHILD.

    [Exit.wait4_spec] is the ONE-PROCESS answer, right only for a caller
    with nothing to reap (Exit.v:234-246).  Here a child is an entry of
    [pcfg_procs], so a caller with one must never reach that spec: whatever
    it answers -- [unmodeled] today, an environment choice of 0 or a pid
    with an invented status once it is given one -- is an answer about
    children it cannot see, while the table holds the real ones and their
    real statuses.  So, for a caller with at least one child in the table
    ([wait4_owned_b]), every call numbered 260 is answered by an arm of
    this core:

    - wait4(-1, &st, 0, NULL), the blocking shape: [pstep_wait_reap],
      unchanged.  A zombie child is reaped; otherwise there is no arm, and
      no arm is how this core says BLOCKED.
    - wait4(-1, &st, WNOHANG, ru), [ru] NULL or writable for a whole
      [struct rusage] ([wait4_rusage_ok_b]): [pstep_wait_nohang_reap]
      reaps a zombie child under the blocking reap's own conditions, and
      with no zombie child [pstep_wait_nohang_zero] returns 0 and changes
      nothing.
    - everything else is [pstep_wait_refuse], an error ([wait4_refused_b]):
      every other argument shape, and a WNOHANG call with a zombie child
      the reap arm cannot take (a killed child, an unwritable [st], a
      copy-out the budget refuses).  A non-blocking call must not be left
      without an arm, because that would model it as blocking; the error
      is fail-closed, and the status word of a killed child, once it is
      modeled, narrows it into an answer.

    [pstep_other] and [pstep_error] are behind [wait4_owned_b = false], so
    the released spec answers a [wait4] only for a caller with NO child in
    the table, exactly as before this gate.

    THE NEXT STEP, deliberately not taken here: a [procst_child_pids]
    field of [State.ProcState], appended to by the clone arm, removed from
    by the reap arms, with an invariant lemma that it lists exactly the
    caller's children in [pcfg_procs].  That invariant also settles the one
    disagreement this gate cannot see: on a hand-built configuration the
    model's own [State.m_has_children] bit and the table can disagree
    (a table child under a clear bit), and the released spec reads the
    bit while this gate reads the table.

    [struct rusage] is accounting this model does not carry, so a reap
    into a non-NULL [ru] writes an ENVIRONMENT-CHOSEN record of
    [RUSAGE_BYTES] bytes, as [pe_status]'s [dumped] bit is chosen. *)

(** The caller has a child in the table. *)
Definition has_child_b (P : pconfig) (p : Pid) : bool :=
  match children_of P p with
  | [] => false
  | _ :: _ => true
  end.

(** THE GATE: a pending 260 from a caller with a child in the table.  It
    REQUIRES the pending call for the reason [wait4_intercept_b] does. *)
Definition wait4_owned_b (P : pconfig) (e : ProcessEntry) : bool :=
  match ms_svc_pending (pe_ms e) with
  | None => false
  | Some x8 => Z.eqb (bv_unsigned x8) 260%Z && has_child_b P (pe_pid e)
  end.

(** The WNOHANG shape: wait4(-1, stat_addr, WNOHANG, ru), giving
    [(stat_addr, ru)].  The words are read as [Exit.wait4_spec]'s
    dispatcher reads them, through [pid32] and [waitopts32]. *)
Definition wait4_nohang_args (ms : machine_state) : option (word * word) :=
  if negb (Z.eqb (bv_unsigned (pid32 (ms_gpr ms 0))) WAIT_ANY32) then None
  else if negb (Z.eqb (bv_unsigned (waitopts32 (ms_gpr ms 2))) WNOHANG) then None
  else Some (ms_gpr ms 1, ms_gpr ms 3).

(** [sizeof(struct rusage)] on a 64-bit kernel: two [struct timeval] of
    16 bytes and fourteen [long]s (include/uapi/linux/resource.h). *)
Definition RUSAGE_BYTES : Z := 144.

(** The writability test the reap arm uses for its copy-out, as a boolean. *)
Definition user_writable_b (segs : list Segment) (ms : machine_state) (x8 : word)
    (a : word) (n : Z) : bool :=
  match read_bytes_map (in_wmem (sys_input segs ms x8)) a (Z_to_bv 64 n) with
  | Some _ => true
  | None => false
  end.

Definition wait4_rusage_ok_b (segs : list Segment) (ms : machine_state) (x8 : word)
    (ru : word) : bool :=
  w_is0 ru || user_writable_b segs ms x8 ru RUSAGE_BYTES.

(** The WNOHANG shape the core answers, at the entry's pending call. *)
Definition wait4_nohang_shape_b (segs : list Segment) (e : ProcessEntry) : bool :=
  match ms_svc_pending (pe_ms e), wait4_nohang_args (pe_ms e) with
  | Some x8, Some (_, ru) => wait4_rusage_ok_b segs (pe_ms e) x8 ru
  | _, _ => false
  end.

Definition pe_zombie_b (e : ProcessEntry) : bool :=
  match pe_zombie e with
  | Some _ => true
  | None => false
  end.

(** The child at key [q] is one the reap arms can take from [p]: present,
    [p]'s child, not [p] itself, halted, and not killed. *)
Definition wait4_reapable_at (P : pconfig) (p q : Pid) : bool :=
  match look P q with
  | Some ez =>
      match pe_parent ez with Some r => bv_eqb r p | None => false end
      && negb (bv_eqb q p)
      && match m_halted (pe_model ez), m_killed (pe_model ez) with
         | Some _, None => true
         | _, _ => false
         end
  | None => false
  end.

(** The writes of a WNOHANG reap: the status word, then the usage record
    when [ru] is not NULL -- [kernel_wait4]'s [put_user] and then the
    [copy_to_user] in [SYSCALL_DEFINE4(wait4, ...)], in that order. *)
Definition wait4_nohang_writes (stat_addr status ru : word) (ru_bytes : list byte)
    : list (word * list byte) :=
  (stat_addr, Z_to_le_bytes 4 (bv_unsigned status))
    :: (if w_is0 ru then [] else [(ru, ru_bytes)]).

(** The user ranges those writes name.  They depend on the addresses and
    lengths only, so the refusal below can test the copy-out without
    choosing the child, its status or the usage bytes. *)
Definition wait4_nohang_accesses (stat_addr ru : word) : list (word * nat) :=
  (stat_addr, 4%nat)
    :: (if w_is0 ru then [] else [(ru, Z.to_nat RUSAGE_BYTES)]).

(** The WNOHANG reap arm can fire: the status word is writable, some key
    holds a reapable child, and the copy-out materializes. *)
Definition wait4_nohang_reap_ok_b (segs : list Segment) (P : pconfig)
    (e : ProcessEntry) : bool :=
  match ms_svc_pending (pe_ms e), wait4_nohang_args (pe_ms e) with
  | Some x8, Some (sa, ru) =>
      user_writable_b segs (pe_ms e) x8 sa 4%Z
      && List.existsb (fun kv => wait4_reapable_at P (pe_pid e) (fst kv)) (pcfg_procs P)
      && match materialize_model_accesses (cfg_model (pe_cfg (pcfg_shared P) e))
                 (wait4_nohang_accesses sa ru) with
         | Some _ => true
         | None => false
         end
  | _, _ => false
  end.

(** THE FAIL-CLOSED CONDITION: a call the gate owns that no answering arm
    takes.  Not the blocking shape, and either not the WNOHANG shape the
    core answers, or that shape with a zombie child the reap cannot take. *)
Definition wait4_refused_b (segs : list Segment) (P : pconfig) (e : ProcessEntry)
    : bool :=
  wait4_owned_b P e
  && negb (wait4_intercept_b (pe_cfg (pcfg_shared P) e))
  && (negb (wait4_nohang_shape_b segs e)
      || (List.existsb pe_zombie_b (children_of P (pe_pid e))
          && negb (wait4_nohang_reap_ok_b segs P e))).

(** What WNOHANG with nothing to reap leaves: a0 = 0, the pc past the
    call, and nothing else. *)
Definition wait4_zero_result (P : pconfig) (e : ProcessEntry) : pconfig :=
  absorb P e
    (mkCfg (advance_past_svc (apply_effect (pe_ms e) (mkEffect (Z_to_bv 64 0) [] [])))
           (cfg_model (pe_cfg (pcfg_shared P) e))).

(** THE NAMESPACE GATE.  The class-(A)/(B) calls whose answer a namespace
    changes, refused for an entry whose context does not reflect that
    namespace ([pm_ns_stale]).  A new user namespace: the id readers and
    setters, capget and capset, getgroups and setgroups (Linux answers the
    overflow ids and full capabilities until a [uid_map] is written).  A new
    network namespace: the socket calls (no connection from the
    environment reaches it).  A new pid namespace changes only class-(C)
    calls, none of which this core answers.  The gate holds under an
    extension too, claimed or not: a bit is stale only when the extension's
    clone left the child's context for that namespace the parent's
    ([child_meta] compares them), so the extension does not model that
    namespace for the entry either; with the gate the same on both
    relations, the four agreement iffs keep their statements. *)
Definition ns_userns_sysnos : list Z :=
  [90; 91; 144; 146; 147; 148; 149; 150; 158; 159; 174; 175; 176; 177]%Z.

Definition ns_netns_sysnos : list Z :=
  [198; 199; 200; 201; 202; 203; 204; 205; 206; 207; 208; 209; 210; 211; 212; 242]%Z.

(** The path a descriptor names in the file image: the four file kinds. *)
Definition fd_named_path (ent : FdEntry) : option Fs.path :=
  match ent with
  | FdFile p _ | FdFileW p _ | FdFileA p _ | FdFileRW p _ => Some p
  | _ => None
  end.

(** Some descriptor of [f] names [p]. *)
Definition entry_fd_names (f : ProcessEntry) (p : Fs.path) : bool :=
  List.existsb (fun kv => match fd_named_path (snd kv) with
                          | Some q => Fs.path_eqb q p
                          | None => false
                          end) (m_fds (pe_model f)).

(** [ok] holds of some entry of the table other than [e]. *)
Definition other_entry_b (P : pconfig) (e : ProcessEntry)
    (ok : ProcessEntry -> bool) : bool :=
  List.existsb (fun kv => negb (bv_eqb (fst kv) (pe_pid e)) && ok (snd kv))
    (pcfg_procs P).

(** flock's descriptor (argument 0) names a file another entry has open. *)
Definition flock_conflict_b (P : pconfig) (e : ProcessEntry) : bool :=
  match fd_lookup (m_fds (pe_model e)) (fd32 (ms_gpr (pe_ms e) 0)) with
  | Some ent =>
      match fd_named_path ent with
      | Some p => other_entry_b P e (fun f => entry_fd_names f p)
      | None => false
      end
  | None => false
  end.

(** THE PIDS.  [f] is the root entry. *)
Definition is_root_b (P : pconfig) (f : ProcessEntry) : bool :=
  bv_eqb (pe_pid f) (pcfg_root P).

(** [t] is the key, so the pid, of an entry that is not the root. *)
Definition key_taken_b (P : pconfig) (t : word) : bool :=
  List.existsb (fun kv => negb (bv_eqb (fst kv) (pcfg_root P)) && bv_eqb (fst kv) t)
    (pcfg_procs P).

(** The root's pinned tid, its pid. *)
Definition root_tid (P : pconfig) : option word :=
  match look P (pcfg_root P) with
  | Some r => m_tid (pe_model r)
  | None => None
  end.

(** Two entries would answer one pid: the root's tid is another entry's
    key (a clone below the root chose it). *)
Definition pid_collision_b (P : pconfig) : bool :=
  match root_tid P with Some t => key_taken_b P t | None => false end.

(** A non-root entry's pinned tid is not its key. *)
Definition tid_conflict_b (P : pconfig) (e : ProcessEntry) : bool :=
  match m_tid (pe_model e) with
  | Some t => negb (is_root_b P e) && negb (bv_eqb t (pe_pid e))
  | None => false
  end.

(** THE REFUSAL GATE: the namespace gate above (a pid call in a new pid
    namespace among it); the prlimit64 gate (261 while a peer lives and
    the caller's RLIMIT_CORE is unpinned); the flock gate (32 while
    another entry has a descriptor on the same file); the pid gate (a pid
    call while two entries would answer one pid, or while the caller's
    tid is not its key).  See the notes above the guard. *)
Definition peer_refused_b (P : pconfig) (e : ProcessEntry) : bool :=
  let stale := pm_ns_stale (meta_look (sh_meta (pcfg_shared P)) (pe_pid e)) in
  match ms_svc_pending (pe_ms e) with
  | None => false
  | Some x8 =>
      (negb (Z.eqb (Z.land stale CLONE_NEWUSER) 0)
       && List.existsb (Z.eqb (bv_unsigned x8)) ns_userns_sysnos)
      || (negb (Z.eqb (Z.land stale CLONE_NEWNET) 0)
          && List.existsb (Z.eqb (bv_unsigned x8)) ns_netns_sysnos)
      || (Nat.ltb 1 (List.length (pcfg_procs P))
          && match m_rlimit_core (pe_model e) with None => true | Some _ => false end
          && Z.eqb (bv_unsigned x8) 261)
      || (Nat.ltb 1 (List.length (pcfg_procs P))
          && Z.eqb (bv_unsigned x8) 32 && flock_conflict_b P e)
      || (negb (Z.eqb (Z.land stale CLONE_NEWPID) 0)
          && List.existsb (Z.eqb (bv_unsigned x8)) multiproc_pid_sysnos)
      || (Nat.ltb 1 (List.length (pcfg_procs P))
          && (pid_collision_b P || tid_conflict_b P e)
          && List.existsb (Z.eqb (bv_unsigned x8)) multiproc_pid_sysnos)
  end.

(** THE PID FILTER, read off the released step's result [c']: of the
    released answers, only the ones the table fixes (see the PIDS note
    above the guard).  A filter, not a refusal: a released answer that
    disagrees is no step, and one that agrees always exists (a key is a
    pid [Fork.clone_pid_ok_b] admitted, so the tid choice can take it).
    At one entry every answer passes ([answer_ok_one]). *)
Definition answer_ok_b (P : pconfig) (e : ProcessEntry) (c' : config) : bool :=
  match ms_svc_pending (pe_ms e) with
  | None => true
  | Some x8 =>
      if List.existsb (Z.eqb (bv_unsigned x8)) multiproc_tid_sysnos then
        match m_tid (pe_model e), m_tid (cfg_model c') with
        | None, Some t =>
            if is_root_b P e then negb (key_taken_b P t) else bv_eqb t (pe_pid e)
        | _, _ => true
        end
      else if Z.eqb (bv_unsigned x8) 173 then
        if is_root_b P e then true
        else match pe_parent e with
             | Some par =>
                 if bv_eqb par (pcfg_root P)
                 then match root_tid P with
                      | Some t => bv_eqb (ms_gpr (cfg_ms c') 0) t
                      | None => false
                      end
                 else bv_eqb (ms_gpr (cfg_ms c') 0) par
             | None => true
             end
      else if Z.eqb (bv_unsigned x8) 156 then
        if m_setsid_succeeded (pe_model e) then true
        else match pm_sid (meta_look (sh_meta (pcfg_shared P)) (pe_pid e)) with
             | Some s => bv_eqb (ms_gpr (cfg_ms c') 0) s
             | None => true
             end
      else true
  end.

(** A child of the root at getppid while the root's tid is unpinned:
    [pstep_pin_root] pins it first. *)
Definition root_pin_pending_b (P : pconfig) (e : ProcessEntry) : bool :=
  match ms_svc_pending (pe_ms e) with
  | Some x8 =>
      Z.eqb (bv_unsigned x8) 173 && negb (is_root_b P e)
      && match pe_parent e with
         | Some par => bv_eqb par (pcfg_root P)
         | None => false
         end
      && match look P (pcfg_root P) with
         | Some r => match m_tid (pe_model r) with None => true | Some _ => false end
         | None => false
         end
  | None => false
  end.

(** The table with the root's tid pinned to [t]. *)
Definition pin_root (P : pconfig) (r : ProcessEntry) (t : word) : pconfig :=
  mkPCfg (replace_in (pcfg_procs P) (pcfg_root P)
            (mkEntry (pe_pid r) (pe_parent r) (pe_ms r) (with_tid t (pe_model r))
                     (pe_ofd r) (pe_nsctx r)))
         (pcfg_root P) (pcfg_shared P).

(** [p] was a path of [old] and is not one of [new]. *)
Definition removed_b (old new : Fs.Fs) (p : Fs.path) : bool :=
  match fs_lookup old p, fs_lookup new p with
  | Some _, None => true
  | _, _ => false
  end.

(** A descriptor or a stat pin of [f] names a path the step removed. *)
Definition entry_names_removed (old new : Fs.Fs) (f : ProcessEntry) : bool :=
  List.existsb (fun kv => match fd_named_path (snd kv) with
                          | Some p => removed_b old new p
                          | None => false
                          end) (m_fds (pe_model f))
  || List.existsb (fun kv => removed_b old new (fst kv)) (m_statpins (pe_model f)).

(** A running child of [e] holds a nonzero parent-death signal. *)
Definition pdeath_child_b (P : pconfig) (e : ProcessEntry) : bool :=
  List.existsb (fun kv =>
      match pe_parent (snd kv) with Some q => bv_eqb q (pe_pid e) | None => false end
      && match m_halted (pe_model (snd kv)) with None => true | Some _ => false end
      && negb (Z.eqb (bv_unsigned (m_pdeath_signal (pe_model (snd kv)))) 0))
    (pcfg_procs P).

(** THE STEP GATE, read off the released step's result [c'] (as
    [clone_success_b] is), and open only while a peer lives.
    - A step that halts [e] while a running child of it holds a nonzero
      parent-death signal: Linux would signal the child, and the exit arm
      does not.  Refused, so the signal is never silently lost.  A clone
      (220, 435) is not read: its step is the clone arms', and a clone
      does not end its caller.
    - A step at unlinkat (35) that removes a path another entry's file
      descriptor or stat pin names.
    See the class-(A) and GATED notes above the guard. *)
Definition step_refused_b (P : pconfig) (e : ProcessEntry) (c' : config) : bool :=
  Nat.ltb 1 (List.length (pcfg_procs P))
  && match ms_svc_pending (pe_ms e) with
     | Some x8 =>
         (negb (clone_sysno (bv_unsigned x8))
          && match m_halted (cfg_model c') with
             | Some _ => pdeath_child_b P e
             | None => false
             end)
         || (Z.eqb (bv_unsigned x8) 35
             && other_entry_b P e
                  (entry_names_removed (fsst_image (sh_fsys (pcfg_shared P)))
                                       (m_fs (cfg_model c'))))
     | None =>
         match m_halted (cfg_model c') with
         | Some _ => pdeath_child_b P e
         | None => false
         end
     end.

(** THE SYNC.  The largest CLOCK_MONOTONIC copy in the table, as an
    unsigned count of nanoseconds; every copy is a word, so it is one. *)
Definition clock_max (ps : list (Pid * ProcessEntry)) : Z :=
  List.fold_right (fun kv acc => Z.max (bv_unsigned (m_clock (pe_model (snd kv)))) acc)
    0%Z ps.

(** The first UTS name pinned in the table, and the first stat pin for a
    path.  All entries that hold one hold the same: a pin is copied at
    clone and by [pstep_sync], and is written by the released spec only
    where none was. *)
Fixpoint uts_any (ps : list (Pid * ProcessEntry)) : option (list byte) :=
  match ps with
  | [] => None
  | (_, f) :: r =>
      match m_utsname (pe_model f) with
      | Some u => Some u
      | None => uts_any r
      end
  end.

Fixpoint pin_any (ps : list (Pid * ProcessEntry)) (p : Fs.path) : option (list byte) :=
  match ps with
  | [] => None
  | (_, f) :: r =>
      match statpin_lookup (m_statpins (pe_model f)) p with
      | Some b => Some b
      | None => pin_any r p
      end
  end.

(** The path an fstat of argument 0 pins, as [Fs.Stat.fstat_spec] keys it:
    a file's path, or the device's. *)
Definition fstat_path (e : ProcessEntry) : option Fs.path :=
  match fd_lookup (m_fds (pe_model e)) (fd32 (ms_gpr (pe_ms e) 0)) with
  | Some (FdFile p _) | Some (FdFileW p _) | Some (FdFileA p _)
  | Some (FdFileRW p _) => Some p
  | Some (FdDevNull _ _) => Some devnull_path
  | Some FdUrandom => Some urandom_path
  | _ => None
  end.

(** The entry has no UTS pin and another has one. *)
Definition uts_lag_b (P : pconfig) (e : ProcessEntry) : bool :=
  match m_utsname (pe_model e) with
  | Some _ => false
  | None => match uts_any (pcfg_procs P) with Some _ => true | None => false end
  end.

(** The entry has no stat pin for its descriptor's path and another has. *)
Definition pin_lag_b (P : pconfig) (e : ProcessEntry) : bool :=
  match fstat_path e with
  | None => false
  | Some p =>
      match statpin_lookup (m_statpins (pe_model e)) p with
      | Some _ => false
      | None => match pin_any (pcfg_procs P) p with Some _ => true | None => false end
      end
  end.

(** A synced call is pending and the copy it reads is behind the table's:
    a lower clock (101, 113), no UTS pin where another entry has one (160),
    no stat pin for the descriptor's path where another entry has one (80).
    At one entry nothing is behind, so this is false. *)
Definition sync_pending_b (P : pconfig) (e : ProcessEntry) : bool :=
  match ms_svc_pending (pe_ms e) with
  | None => false
  | Some x8 =>
      (List.existsb (Z.eqb (bv_unsigned x8)) multiproc_clock_sysnos
       && (bv_unsigned (m_clock (pe_model e)) <? clock_max (pcfg_procs P))%Z)
      || (Z.eqb (bv_unsigned x8) 160 && uts_lag_b P e)
      || (Z.eqb (bv_unsigned x8) 80 && pin_lag_b P e)
  end.

Definition uts_fill (ps : list (Pid * ProcessEntry)) (m : Model) : Model :=
  match m_utsname m with
  | Some _ => m
  | None => match uts_any ps with Some u => with_utsname u m | None => m end
  end.

Definition pin_fill (ps : list (Pid * ProcessEntry)) (e : ProcessEntry) (m : Model)
    : Model :=
  match fstat_path e with
  | None => m
  | Some p =>
      match statpin_lookup (m_statpins m) p with
      | Some _ => m
      | None => match pin_any ps p with Some b => with_statpin p b m | None => m end
      end
  end.

(** The entry with its copies brought up from the table: the clock raised
    to the maximum, the UTS name and the descriptor's stat pin taken from
    another entry where it has none.  Nothing else changes: not its
    machine state (the call stays pending), not its other model state. *)
Definition sync_entry (P : pconfig) (e : ProcessEntry) : ProcessEntry :=
  mkEntry (pe_pid e) (pe_parent e) (pe_ms e)
    (with_clock (Z_to_bv 64 (clock_max (pcfg_procs P)))
       (uts_fill (pcfg_procs P) (pin_fill (pcfg_procs P) e (pe_model e))))
    (pe_ofd e) (pe_nsctx e).

Definition sync_result (P : pconfig) (e : ProcessEntry) : pconfig :=
  mkPCfg (replace_in (pcfg_procs P) (pe_pid e) (sync_entry P e))
         (pcfg_root P) (pcfg_shared P).

(** The sync changes no halt state. *)
Lemma sync_entry_halted : forall P e,
  m_halted (pe_model (sync_entry P e)) = m_halted (pe_model e).
Proof.
  intros P e. unfold sync_entry, uts_fill, pin_fill. cbn [pe_model].
  destruct (fstat_path e) as [p|]; [destruct (statpin_lookup _ p); [|destruct (pin_any _ p)]|];
    destruct (m_utsname _); try destruct (uts_any _); reflexivity.
Qed.

(** THE REAPER'S LIST: the reaped pid leaves [State.procst_child_pids], as
    [release_task] unlinks the child from [p->children] (kernel/exit.c,
    read at v6.18.44; identical at v6.18.46).  The core's reap arms are
    the reap; the released [wait4] never runs for a caller with a child in
    the table ([wait4_owned_b]), so its own removal does not reach them.
    [Checks.ProcsChildPids] proves the list is then exactly the keys of
    the caller's children in the table. *)
Definition reap_model (q : Pid) (m : Model) : Model :=
  with_child_pids (List.filter (fun x => negb (bv_eqb x q)) (m_child_pids m)) m.

(** What a reap leaves: the caller past the call with the effect applied
    and the child's pid off its list, and the child [q] gone.
    [pstep_wait_reap]'s conclusion is this term written out, and is left
    written out because [Examples/forkwait] matches on it. *)
Definition wait4_reap_result (P : pconfig) (e : ProcessEntry) (q : Pid)
    (eff : SyscallEffect) (model'' : Model) : pconfig :=
  mkPCfg
    (drop_in
       (replace_in (pcfg_procs P) (pe_pid e)
          (mkEntry (pe_pid e) (pe_parent e)
             (advance_past_svc (apply_effect (pe_ms e) eff))
             (clear_shared (reap_model q model'')) (pe_ofd e) (pe_nsctx e)))
       q)
    (pcfg_root P)
    (shared_absorb (pcfg_shared P) (mkCfg (pe_ms e) model'')).

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
    (* THE GATE: the released step never answers a [wait4] of a caller
       with a child in the table; see the design note above. *)
    wait4_owned_b P e = false ->
    (* THE NAMESPACE GATE: never the released answer of a call a namespace
       the entry's context does not reflect would change. *)
    peer_refused_b P e = false ->
    (* THE SYNC GATE: a synced call never reads a clock copy that is behind
       another entry's; [pstep_sync] raises it first. *)
    sync_pending_b P e = false ->
    (* THE STEP GATE: never a halt that would lose a child's parent-death
       signal, never an unlinkat that removes a path a peer names. *)
    step_refused_b P e c' = false ->
    (* THE PID FILTER: only the released pid answers the table fixes. *)
    answer_ok_b P e c' = true ->
    pstep_at segs cfg (pe_pid e) P evs (PNext (absorb P e c'))
(** THE ERROR TRANSITION, and it must EXCLUDE the intercepted wait.
    A blocking [wait4(-1, _, 0, NULL)] is [unmodeled] in the released spec
    (Exit.v:247) and [Run.sstep_cfg_syscall_unmodeled] (Run.v:1832-1836) turns
    that into [SError].  Lifting every [SError] unqualified would send the
    waiting parent to [PError] and the sleep of this core would never happen.
    So the intercepted shape is excluded here, and it is the SECOND place --
    beside a successful clone -- where this relation and the released one
    differ.  [pstep_single]'s second hypothesis is exactly that exclusion.
    The error transition is ALSO behind [wait4_owned_b = false], as
    [pstep_other] is: a [wait4] of a caller with a child in the table is
    answered or refused by the gate's own arms, never by a released
    [SError].  At one entry the gate is closed ([wait4_owned_one]), so the
    single-process theorems need no new hypothesis. *)
(** THE CLONE ARM.  The parent's half is the RELEASED step, unedited: flag
    word, errno list, pid envelope, [State.with_child] and the
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
       reaches no statement: [pinit_config] gives [pconfig_wf]
       ([pconfig_wf_one_proc]) and every producing arm keeps it
       ([Checks.ProcsWellFormed.pstep_at_preserves_wf]), so the excluded
       case is unreachable from any start state a statement quantifies
       over.  (Found by trying to prove that the entry count decides which
       arm fired, 2026-11-01.) *)
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
                         (clear_shared (reap_model q model'')) (pe_ofd e) (pe_nsctx e)))
                   q)
                (pcfg_root P)
                (shared_absorb (pcfg_shared P) (mkCfg (pe_ms e) model''))))
| pstep_error : forall P e evs,
    look P (pe_pid e) = Some e ->
    sstep_cfg segs cfg (pe_cfg (pcfg_shared P) e) evs SError ->
    wait4_intercept_b (pe_cfg (pcfg_shared P) e) = false ->
    wait4_owned_b P e = false ->
    pstep_at segs cfg (pe_pid e) P evs PError
| pstep_outside : forall P e,
    look P (pe_pid e) = Some e ->
    m_halted (pe_model e) = None ->
    multiproc_allowed P (pe_cfg (pcfg_shared P) e) = false ->
    pstep_at segs cfg (pe_pid e) P [] PError
(** THE WNOHANG REAP: [pstep_wait_reap]'s conditions on the child and the
    copy-out, at wait4(-1, &st, WNOHANG, ru).  When [ru] is not NULL it
    must be writable for a whole [struct rusage], and the record written
    there is the environment's choice ([ru_bytes]): the model carries no
    accounting. *)
| pstep_wait_nohang_reap : forall P e q ez x8 stat_addr ru ru_bytes status eff
                             model'' dumped,
    look P (pe_pid e) = Some e ->
    m_halted (pe_model e) = None ->
    ms_svc_pending (pe_ms e) = Some x8 ->
    wait4_owned_b P e = true ->
    wait4_nohang_args (pe_ms e) = Some (stat_addr, ru) ->
    wait4_rusage_ok_b segs (pe_ms e) x8 ru = true ->
    look P q = Some ez ->
    q <> pe_pid e ->
    pe_parent ez = Some (pe_pid e) ->
    m_killed (pe_model ez) = None ->
    pe_status dumped ez = Some status ->
    read_bytes_map (in_wmem (sys_input segs (pe_ms e) x8)) stat_addr
      (Z_to_bv 64 4) <> None ->
    List.length ru_bytes = Z.to_nat RUSAGE_BYTES ->
    eff = mkEffect q (wait4_nohang_writes stat_addr status ru ru_bytes) [] ->
    materialize_model_accesses (cfg_model (pe_cfg (pcfg_shared P) e))
      (syscall_effect_accesses eff) = Some model'' ->
    pstep_at segs cfg (pe_pid e) P [] (PNext (wait4_reap_result P e q eff model''))
(** WNOHANG WITH NO ZOMBIE CHILD: 0, and nothing changes but a0 and the
    pc.  A child exists ([wait4_owned_b]) and has nothing to report, which
    is exactly when [__do_wait] clears [notask_error] to 0. *)
| pstep_wait_nohang_zero : forall P e x8 stat_addr ru,
    look P (pe_pid e) = Some e ->
    m_halted (pe_model e) = None ->
    ms_svc_pending (pe_ms e) = Some x8 ->
    wait4_owned_b P e = true ->
    wait4_nohang_args (pe_ms e) = Some (stat_addr, ru) ->
    wait4_rusage_ok_b segs (pe_ms e) x8 ru = true ->
    List.existsb pe_zombie_b (children_of P (pe_pid e)) = false ->
    pstep_at segs cfg (pe_pid e) P [] (PNext (wait4_zero_result P e))
(** EVERY OTHER [wait4] OF A CALLER WITH A CHILD: an error, fail-closed,
    and never the released step ([wait4_refused_b]). *)
| pstep_wait_refuse : forall P e,
    look P (pe_pid e) = Some e ->
    m_halted (pe_model e) = None ->
    wait4_refused_b segs P e = true ->
    pstep_at segs cfg (pe_pid e) P [] PError
(** A CALL THE NAMESPACE GATE REFUSES: an error, fail-closed, so the entry
    is not modelled as blocked. *)
| pstep_peer_refuse : forall P e,
    look P (pe_pid e) = Some e ->
    m_halted (pe_model e) = None ->
    peer_refused_b P e = true ->
    pstep_at segs cfg (pe_pid e) P [] PError
(** THE SYNC: an entry about to read a clock copy that is behind another
    entry's raises it to the table's maximum, silently, and stays at the
    call. *)
| pstep_sync : forall P e,
    look P (pe_pid e) = Some e ->
    m_halted (pe_model e) = None ->
    sync_pending_b P e = true ->
    pstep_at segs cfg (pe_pid e) P [] (PNext (sync_result P e))
(** A STEP THE STEP GATE REFUSES: everything [pstep_other] asks but the
    step gate, which is open.  An error, fail-closed. *)
| pstep_step_refuse : forall P e evs c',
    look P (pe_pid e) = Some e ->
    sstep_cfg segs cfg (pe_cfg (pcfg_shared P) e) evs (SNext c') ->
    clone_success_b (pe_cfg (pcfg_shared P) e) c' = false ->
    wait4_intercept_b (pe_cfg (pcfg_shared P) e) = false ->
    multiproc_allowed P (pe_cfg (pcfg_shared P) e) = true ->
    wait4_owned_b P e = false ->
    peer_refused_b P e = false ->
    sync_pending_b P e = false ->
    step_refused_b P e c' = true ->
    answer_ok_b P e c' = true ->
    pstep_at segs cfg (pe_pid e) P [] PError
(** THE ROOT PIN: a child of the root at getppid while the root's tid is
    unpinned pins it, silently, to a pid no other entry's key holds, in the
    range the released tid choice draws from ([Fork.set_tid_address_spec]),
    and stays at its call. *)
| pstep_pin_root : forall P e r t,
    look P (pe_pid e) = Some e ->
    m_halted (pe_model e) = None ->
    root_pin_pending_b P e = true ->
    look P (pcfg_root P) = Some r ->
    (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z ->
    key_taken_b P t = false ->
    pstep_at segs cfg (pe_pid e) P [] (PNext (pin_root P r t)).

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
                   empty_nsstate []).

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

(** At one entry the [wait4] gate is closed: the only entry has no parent,
    so nobody has a child in the table, and every [wait4] of a one-process
    system is the released step's, as it was before the gate. *)
Lemma has_child_one : forall c p, has_child_b (one_proc c) p = false.
Proof. intros c p. reflexivity. Qed.

Lemma wait4_owned_one : forall c e, wait4_owned_b (one_proc c) e = false.
Proof.
  intros c e. unfold wait4_owned_b.
  destruct (ms_svc_pending (pe_ms e)); [|reflexivity].
  rewrite has_child_one. apply andb_false_r.
Qed.

Lemma wait4_refused_one : forall segs c e, wait4_refused_b segs (one_proc c) e = false.
Proof. intros segs c e. unfold wait4_refused_b. rewrite wait4_owned_one. reflexivity. Qed.

(** At one entry the namespace gate is closed: a one-process system records
    no metadata, so nothing is stale. *)
Lemma peer_refused_one : forall c e, peer_refused_b (one_proc c) e = false.
Proof.
  intros c e. unfold peer_refused_b. cbn [one_proc pcfg_shared sh_meta meta_look pm_ns_stale].
  destruct (ms_svc_pending (pe_ms e)); reflexivity.
Qed.

(** At one entry the sync gate is closed: the only clock copy is the
    table's maximum. *)
Lemma clock_max_single : forall k e,
  clock_max [(k, e)] = bv_unsigned (m_clock (pe_model e)).
Proof.
  intros k e. unfold clock_max. cbn [List.fold_right snd].
  apply Z.max_l. pose proof (bv_unsigned_in_range _ (m_clock (pe_model e))). lia.
Qed.

Lemma sync_pending_one : forall c, sync_pending_b (one_proc c) (one_entry c) = false.
Proof.
  intros c. unfold sync_pending_b, uts_lag_b, pin_lag_b.
  cbn [one_proc pcfg_procs uts_any pin_any snd].
  destruct (ms_svc_pending (pe_ms (one_entry c))); [|reflexivity].
  rewrite clock_max_single, Z.ltb_irrefl, andb_false_r.
  destruct (m_utsname (pe_model (one_entry c)));
    (destruct (fstat_path (one_entry c)) as [p|];
     [destruct (statpin_lookup (m_statpins (pe_model (one_entry c))) p)|]);
    rewrite ?andb_false_r; reflexivity.
Qed.

(** At one entry the step gate is closed: it needs a peer. *)
Lemma step_refused_one : forall c e c', step_refused_b (one_proc c) e c' = false.
Proof. intros c e c'. reflexivity. Qed.

(** At one entry every released pid answer passes the filter: the entry is
    the root, no other key exists, and nothing is inherited. *)
Lemma answer_ok_one : forall c c', answer_ok_b (one_proc c) (one_entry c) c' = true.
Proof.
  intros c c'.
  assert (Hk : forall t, key_taken_b (one_proc c) t = false).
  { intros t. unfold key_taken_b. cbn [one_proc pcfg_procs pcfg_root List.existsb fst].
    rewrite bv_eqb_same. reflexivity. }
  unfold answer_ok_b, is_root_b. cbn [one_proc pcfg_root one_entry pe_pid].
  rewrite bv_eqb_same.
  destruct (ms_svc_pending _) as [x8|]; [|reflexivity].
  destruct (List.existsb _ multiproc_tid_sysnos).
  - destruct (m_tid _), (m_tid (cfg_model c')); rewrite ?Hk; reflexivity.
  - destruct (Z.eqb _ 173); [reflexivity|].
    destruct (Z.eqb _ 156); [|reflexivity].
    destruct (m_setsid_succeeded _); reflexivity.
Qed.

(** At one entry no root pin is pending: the entry is the root. *)
Lemma root_pin_one : forall c, root_pin_pending_b (one_proc c) (one_entry c) = false.
Proof.
  intros c. unfold root_pin_pending_b, is_root_b.
  cbn [one_proc pcfg_root one_entry pe_pid].
  destruct (ms_svc_pending _); [|reflexivity].
  rewrite bv_eqb_same. cbn [negb]. rewrite andb_false_r. reflexivity.
Qed.

Lemma absorb_one_proc : forall c c',
  absorb (one_proc c) (one_entry c) c' = one_proc c'.
Proof.
  intros c c'. unfold absorb.
  replace (replace_in (pcfg_procs (one_proc c)) (pe_pid (one_entry c))
             (pe_absorb (one_entry c) c'))
    with [(one_pid, pe_absorb (one_entry c) c')]
    by (cbn; rewrite bv_eqb_same; reflexivity).
  change (pe_pid (one_entry c)) with one_pid.
  rewrite orphan_at_exit_single.
  unfold one_proc, one_entry. destruct c' as [ms' m']. destruct m'. reflexivity.
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
    try rewrite one_proc_view in *.
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
  - (* pstep_wait_nohang_reap: the gate is closed at one entry *)
    exfalso.
    match goal with
    | [ Hw : wait4_owned_b _ _ = true |- _ ] =>
        rewrite wait4_owned_one in Hw; discriminate
    end.
  - (* pstep_wait_nohang_zero: likewise *)
    exfalso.
    match goal with
    | [ Hw : wait4_owned_b _ _ = true |- _ ] =>
        rewrite wait4_owned_one in Hw; discriminate
    end.
  - (* pstep_sync: the gate is closed at one entry *)
    exfalso.
    match goal with
    | [ Hw : sync_pending_b _ _ = true |- _ ] =>
        rewrite sync_pending_one in Hw; discriminate
    end.
  - (* pstep_pin_root: the only entry is the root *)
    exfalso.
    match goal with
    | [ Hw : root_pin_pending_b _ _ = true |- _ ] =>
        rewrite root_pin_one in Hw; discriminate
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
  - apply wait4_owned_one.
  - apply peer_refused_one.
  - apply sync_pending_one.
  - apply step_refused_one.
  - apply answer_ok_one.
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
  - exfalso.
    match goal with
    | [ Hrf : wait4_refused_b _ (one_proc c) _ = true |- _ ] =>
        rewrite wait4_refused_one in Hrf; discriminate
    end.
  - exfalso.
    match goal with
    | [ Hrf : peer_refused_b (one_proc c) _ = true |- _ ] =>
        rewrite peer_refused_one in Hrf; discriminate
    end.
  - exfalso.
    match goal with
    | [ Hrf : step_refused_b (one_proc c) _ _ = true |- _ ] =>
        rewrite step_refused_one in Hrf; discriminate
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
  - apply wait4_owned_one.
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

(** The structural invariant every arm preserves
    ([Checks.ProcsWellFormed.pstep_at_preserves_wf]).  Stated once, because
    several results silently assume parts of it:

    1. the key of the table is the entry's own pid;
    2. the root is present and parentless;
    3. every parent link resolves, to an entry other than the child;
    4. NO KEY IS REPEATED.  [look], [replace_in] and [drop_in] act on the
       FIRST entry with a key, so a repeated key would leave a shadowed
       entry that no arm sees and every arm keeps;
    5. every parent is RUNNING.  This is what makes a reap's drop safe: an
       entry stops running only at its exit, where [absorb] orphans its
       children ([orphan_at_exit]), so a zombie is nobody's parent and
       dropping it leaves no link dangling.

    A parentless entry is the root or an ORPHAN, whose parent exited:
    clause 2 names the root, and nothing reads "parentless" as "root"
    ([root_view] and [MustExitP.lineage_pick] read [pcfg_root]). *)
Definition pconfig_wf (P : pconfig) : Prop :=
  (forall kv, List.In kv (pcfg_procs P) -> fst kv = pe_pid (snd kv))
  /\ (exists e, look P (pcfg_root P) = Some e /\ pe_parent e = None)
  /\ (forall kv q, List.In kv (pcfg_procs P) -> pe_parent (snd kv) = Some q ->
        q <> fst kv /\ exists f, look P q = Some f)
  /\ List.NoDup (List.map fst (pcfg_procs P))
  /\ (forall kv q f, List.In kv (pcfg_procs P) -> pe_parent (snd kv) = Some q ->
        look P q = Some f -> m_halted (pe_model f) = None).

Lemma pconfig_wf_one_proc : forall c, pconfig_wf (one_proc c).
Proof.
  intros c. unfold pconfig_wf. split; [|split; [|split; [|split]]].
  - intros kv Hkv. cbn in Hkv. destruct Hkv as [<-|[]]. reflexivity.
  - exists (one_entry c). split; [apply one_proc_entry | reflexivity].
  - intros kv q Hkv Hq. cbn in Hkv. destruct Hkv as [<-|[]]. discriminate Hq.
  - cbn. constructor; [intros []|constructor].
  - intros kv q f Hkv Hq. cbn in Hkv. destruct Hkv as [<-|[]]. discriminate Hq.
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

(** A step to a successor is one of the seven producing arms: the released
    step, the clone, the three [wait4] arms (the blocking reap, and the
    two WNOHANG arms of the gate, both behind [wait4_owned_b]), the
    clock sync, and the root pin. *)
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
      \/ (wait4_intercept_b (pe_cfg (pcfg_shared P) e) = true /\ evs = [])
      \/ (wait4_owned_b P e = true /\ evs = [])
      \/ (sync_pending_b P e = true /\ evs = [] /\ P' = sync_result P e)
      \/ (root_pin_pending_b P e = true /\ evs = []
          /\ exists r t, look P (pcfg_root P) = Some r /\ P' = pin_root P r t) ).
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
    right; right; left. split; [assumption | reflexivity].
  - (* pstep_wait_nohang_reap *)
    eexists. split; [eassumption | split; [reflexivity|]].
    right; right; right; left. split; [assumption | reflexivity].
  - (* pstep_wait_nohang_zero *)
    eexists. split; [eassumption | split; [reflexivity|]].
    right; right; right; left. split; [assumption | reflexivity].
  - (* pstep_sync *)
    eexists. split; [eassumption | split; [reflexivity|]].
    right; right; right; right; left. split; [assumption | split; reflexivity].
  - (* pstep_pin_root *)
    eexists. split; [eassumption | split; [reflexivity|]].
    right; right; right; right; right. split; [assumption | split; [reflexivity|]].
    do 2 eexists. split; [eassumption | reflexivity].
Qed.

(** A step to the error transition is one of the four refusing arms: a
    released [SError], the surface guard, the [wait4] gate's refusal, the
    namespace gate's, or the step gate's. *)
Lemma pstep_error_cases : forall segs cfg p P evs,
  pstep_at segs cfg p P evs PError ->
  exists e,
    look P p = Some e /\ pe_pid e = p /\
    ( (sstep_cfg segs cfg (pe_cfg (pcfg_shared P) e) evs SError
       /\ wait4_intercept_b (pe_cfg (pcfg_shared P) e) = false)
      \/ (multiproc_allowed P (pe_cfg (pcfg_shared P) e) = false /\ evs = [])
      \/ (wait4_refused_b segs P e = true /\ evs = [])
      \/ (peer_refused_b P e = true /\ evs = [])
      \/ ((exists evs0 c', sstep_cfg segs cfg (pe_cfg (pcfg_shared P) e) evs0 (SNext c')
                         /\ wait4_intercept_b (pe_cfg (pcfg_shared P) e) = false
                         /\ step_refused_b P e c' = true)
          /\ evs = []) ).
Proof.
  intros segs cfg p P evs Hp.
  inversion Hp; subst.
  - eexists. split; [eassumption | split; [reflexivity|]].
    left. split; assumption.
  - eexists. split; [eassumption | split; [reflexivity|]].
    right; left. split; [assumption | reflexivity].
  - eexists. split; [eassumption | split; [reflexivity|]].
    right; right; left. split; [assumption | reflexivity].
  - eexists. split; [eassumption | split; [reflexivity|]].
    right; right; right; left. split; [assumption | reflexivity].
  - eexists. split; [eassumption | split; [reflexivity|]].
    right; right; right; right. split; [|reflexivity].
    do 2 eexists. split; [eassumption | split; assumption].
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

(* -------------------------------------------------- facts about the wait4 gate *)

(** The gate needs a pending 260, so a pending call with any other number,
    or no pending call, keeps it closed. *)
Lemma wait4_owned_not_260 : forall P e x8,
  ms_svc_pending (pe_ms e) = Some x8 -> bv_unsigned x8 <> 260%Z ->
  wait4_owned_b P e = false.
Proof.
  intros P e x8 Hs Hn. unfold wait4_owned_b. rewrite Hs.
  apply andb_false_intro1. apply Z.eqb_neq. exact Hn.
Qed.

Lemma wait4_owned_instr : forall P e,
  ms_svc_pending (pe_ms e) = None -> wait4_owned_b P e = false.
Proof. intros P e Hs. unfold wait4_owned_b. rewrite Hs. reflexivity. Qed.

Lemma wait4_owned_260 : forall P e,
  wait4_owned_b P e = true ->
  exists x8, ms_svc_pending (pe_ms e) = Some x8 /\ bv_unsigned x8 = 260%Z.
Proof.
  intros P e H. unfold wait4_owned_b in H.
  destruct (ms_svc_pending (pe_ms e)) as [x8|]; [|discriminate H].
  apply andb_true_iff in H as [H _]. apply Z.eqb_eq in H.
  exists x8. split; [reflexivity | exact H].
Qed.

(** 260 is on the multi-process surface, so the surface guard is open
    wherever the gate is. *)
Lemma wait4_owned_allowed : forall P e,
  wait4_owned_b P e = true -> multiproc_allowed P (pe_cfg (pcfg_shared P) e) = true.
Proof.
  intros P e H. destruct (wait4_owned_260 P e H) as (x8 & Hs & H260).
  unfold multiproc_allowed. cbn [cfg_ms pe_cfg]. rewrite Hs, H260.
  destruct (Nat.leb _ _); reflexivity.
Qed.

(** The refusal gate is closed at an instruction, and at any number
    outside its lists. *)
Lemma peer_refused_instr : forall P e,
  ms_svc_pending (pe_ms e) = None -> peer_refused_b P e = false.
Proof. intros P e Hs. unfold peer_refused_b. rewrite Hs. reflexivity. Qed.

Lemma peer_refused_of_sysno : forall P e x8,
  ms_svc_pending (pe_ms e) = Some x8 ->
  List.existsb (Z.eqb (bv_unsigned x8))
    (ns_userns_sysnos ++ ns_netns_sysnos ++ [32; 261]%Z ++ multiproc_pid_sysnos) = false ->
  peer_refused_b P e = false.
Proof.
  intros P e x8 Hs H. unfold peer_refused_b. rewrite Hs.
  rewrite !List.existsb_app in H. apply orb_false_iff in H as [Hu H].
  apply orb_false_iff in H as [Hn H]. apply orb_false_iff in H as [Hg Hp].
  cbn [List.existsb] in Hg. apply orb_false_iff in Hg as [H32 Hg].
  apply orb_false_iff in Hg as [H261 _].
  rewrite Hu, Hn, H32, H261, Hp, !andb_false_r. reflexivity.
Qed.

(** No entry of the table is a child of [e]: the parent-death part of the
    step gate is closed. *)
Lemma pdeath_child_none : forall P e,
  (forall kv, List.In kv (pcfg_procs P) -> pe_parent (snd kv) <> Some (pe_pid e)) ->
  pdeath_child_b P e = false.
Proof.
  intros P e H. unfold pdeath_child_b.
  apply Bool.not_true_iff_false. intros Hx.
  apply List.existsb_exists in Hx as (kv & Hin & Hkv).
  apply andb_true_iff in Hkv as [Hkv _]. apply andb_true_iff in Hkv as [Hkv _].
  destruct (pe_parent (snd kv)) as [q|] eqn:Hp; [|discriminate Hkv].
  apply bv_eqb_true_eq in Hkv. subst q. exact (H kv Hin Hp).
Qed.

(** The step gate is closed at a number other than unlinkat whose step
    does not halt [e], or halts it with no running child holding a
    parent-death signal. *)
Lemma step_refused_of : forall P e c',
  (forall x8, ms_svc_pending (pe_ms e) = Some x8 -> bv_unsigned x8 <> 35%Z) ->
  (m_halted (cfg_model c') = None \/ pdeath_child_b P e = false) ->
  step_refused_b P e c' = false.
Proof.
  intros P e c' H35 Hd. unfold step_refused_b.
  destruct (Nat.ltb 1 _); [cbn [andb]|reflexivity].
  assert (Hpd : match m_halted (cfg_model c') with
                | Some _ => pdeath_child_b P e | None => false end = false)
    by (destruct Hd as [Hn | Hn]; [rewrite Hn; reflexivity
                                   | destruct (m_halted _); [exact Hn | reflexivity]]).
  destruct (ms_svc_pending (pe_ms e)) as [x8|] eqn:Hs; [|exact Hpd].
  rewrite Hpd, andb_false_r. cbn [orb].
  specialize (H35 x8 eq_refl). apply Z.eqb_neq in H35. rewrite H35. reflexivity.
Qed.

(** The sync gate is closed at an instruction, and at any number outside
    the synced list. *)
Lemma sync_instr : forall P e,
  ms_svc_pending (pe_ms e) = None -> sync_pending_b P e = false.
Proof. intros P e Hs. unfold sync_pending_b. rewrite Hs. reflexivity. Qed.

(** The root pin is closed at an instruction and at any number but 173;
    the pid filter passes every step at an instruction and at any number
    outside the pid list. *)
Lemma root_pin_of_sysno : forall P e,
  (forall x8, ms_svc_pending (pe_ms e) = Some x8 -> bv_unsigned x8 <> 173%Z) ->
  root_pin_pending_b P e = false.
Proof.
  intros P e H. unfold root_pin_pending_b.
  destruct (ms_svc_pending (pe_ms e)) as [x8|]; [|reflexivity].
  specialize (H x8 eq_refl). apply Z.eqb_neq in H. rewrite H. reflexivity.
Qed.

Lemma answer_ok_of_sysno : forall P e c',
  (forall x8, ms_svc_pending (pe_ms e) = Some x8 ->
     List.existsb (Z.eqb (bv_unsigned x8)) multiproc_pid_sysnos = false) ->
  answer_ok_b P e c' = true.
Proof.
  intros P e c' H. unfold answer_ok_b.
  destruct (ms_svc_pending (pe_ms e)) as [x8|]; [|reflexivity].
  specialize (H x8 eq_refl). cbn [multiproc_pid_sysnos List.existsb] in H.
  repeat (apply orb_false_iff in H as [?E H]).
  cbn [multiproc_tid_sysnos List.existsb].
  repeat match goal with E : Z.eqb _ _ = false |- _ => rewrite E; clear E end.
  reflexivity.
Qed.

Lemma sync_of_sysno : forall P e x8,
  ms_svc_pending (pe_ms e) = Some x8 ->
  List.existsb (Z.eqb (bv_unsigned x8)) multiproc_synced_sysnos = false ->
  sync_pending_b P e = false.
Proof.
  intros P e x8 Hs H. unfold sync_pending_b. rewrite Hs.
  cbn [multiproc_synced_sysnos List.existsb] in H.
  apply orb_false_iff in H as [H80 H].
  apply orb_false_iff in H as [H101 H].
  apply orb_false_iff in H as [H113 H].
  apply orb_false_iff in H as [H160 _].
  cbn [multiproc_clock_sysnos List.existsb].
  rewrite H80, H101, H113, H160. reflexivity.
Qed.

(** The sync fires only at a synced number. *)
Lemma sync_pending_sysno : forall P e,
  sync_pending_b P e = true ->
  exists x8, ms_svc_pending (pe_ms e) = Some x8
    /\ List.existsb (Z.eqb (bv_unsigned x8)) multiproc_synced_sysnos = true.
Proof.
  intros P e H.
  destruct (ms_svc_pending (pe_ms e)) as [x8|] eqn:Hs;
    [|unfold sync_pending_b in H; rewrite Hs in H; discriminate H].
  exists x8. split; [reflexivity|].
  destruct (List.existsb (Z.eqb (bv_unsigned x8)) multiproc_synced_sysnos) eqn:Hin;
    [reflexivity|].
  rewrite (sync_of_sysno P e x8 Hs Hin) in H. discriminate H.
Qed.

(** A [wait4] is never synced. *)
Lemma wait4_owned_not_sync : forall P e,
  wait4_owned_b P e = true -> sync_pending_b P e = false.
Proof.
  intros P e H. destruct (wait4_owned_260 P e H) as (x8 & Hs & H260).
  apply (sync_of_sysno P e x8 Hs). rewrite H260. reflexivity.
Qed.

(** A [wait4] is never namespace-gated. *)
Lemma wait4_owned_not_ns : forall P e,
  wait4_owned_b P e = true -> peer_refused_b P e = false.
Proof.
  intros P e H. destruct (wait4_owned_260 P e H) as (x8 & Hs & H260).
  apply (peer_refused_of_sysno P e x8 Hs). rewrite H260. reflexivity.
Qed.

(** ... and it is open without the class numbers: 260 is core-answered. *)
Lemma wait4_owned_base : forall P e,
  wait4_owned_b P e = true -> multiproc_base P (pe_cfg (pcfg_shared P) e) = true.
Proof.
  intros P e H. destruct (wait4_owned_260 P e H) as (x8 & Hs & H260).
  unfold multiproc_base. cbn [cfg_ms pe_cfg]. rewrite Hs, H260.
  destruct (Nat.leb _ _); reflexivity.
Qed.

(** The blocking shape and the WNOHANG shape are disjoint: the option word
    is 0 in one and [WNOHANG] in the other. *)
Lemma wait4_blocking_not_nohang : forall ms a,
  wait4_blocking_args ms = Some a -> wait4_nohang_args ms = None.
Proof.
  intros ms a. unfold wait4_blocking_args, wait4_nohang_args.
  destruct (negb (Z.eqb (bv_unsigned (pid32 (ms_gpr ms 0))) WAIT_ANY32));
    [intros H; discriminate H|].
  destruct (w_is0 (waitopts32 (ms_gpr ms 2))) eqn:Hw; cbn [negb];
    [|intros H; discriminate H].
  intros _. unfold w_is0 in Hw. apply bv_eqb_true_eq in Hw. rewrite Hw. reflexivity.
Qed.

(** The refusal is behind the gate, and never at the blocking shape. *)
Lemma wait4_refused_not_owned : forall segs P e,
  wait4_owned_b P e = false -> wait4_refused_b segs P e = false.
Proof. intros segs P e H. unfold wait4_refused_b. rewrite H. reflexivity. Qed.

Lemma wait4_refused_intercept : forall segs P e,
  wait4_intercept_b (pe_cfg (pcfg_shared P) e) = true -> wait4_refused_b segs P e = false.
Proof.
  intros segs P e H. unfold wait4_refused_b. rewrite H.
  cbn [negb]. rewrite andb_false_r. reflexivity.
Qed.

(* =========================================================================
   A step extension: answers the released step does not give, inside the core
   ========================================================================= *)

(** [pstep_x_at ext cenv] is [pstep_at] with an extension
    ([Ns.Ext.ExtSpec]): a pending call the extension CLAIMS is answered by
    [ext_spec] on the SPLICED model ([pe_cfg], never [pe_model], whose file
    system and I/O are blank), the entry's namespace context and the shared
    namespace state, filtered by [ext_refusal] on the whole [EOk] outcome
    as the released step is by [Run.spurious_refusal_cfg] on the effect
    (an [EUnmodeled] outcome and a step that ends the process get no
    filter, as in the released step); the context and state it returns are
    written into [pe_nsctx] and [sh_ns].  An unclaimed call is the released
    step, unchanged.  A clone is the released clone, and [ext_clone] says
    what it does to the namespace model: the child's context and the next
    state, the state after a failure, or no answer.  A claimed call while
    other entries are live is admitted when the core's guard WITHOUT the
    class-(A) and class-(B) numbers ([multiproc_base]) admits it, or
    [ext_multiproc] does, or it is a class number at a flat view; see
    [multiproc_ok].

    [cenv] ([Ns.Ext.CloneEnv]) names the clone failures a run admits.  It
    is an explicit argument so that a statement shows it:
    [Ns.Ext.any_clone_failure] admits every failure
    ([pstep_x_at_any_clone_failure]: it is the largest), and a narrower one
    is an environment premise of the statement that names it.

    The text of [pstep_at] is unchanged (its meaning changed with the
    parent-side extensions, through [clone_success_b], [child_proc] and
    [fd_shared_view]); [pstep_at_no_ext_iff] is the two relations'
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
    ~ ext_refusal ext cfg (sys_input segs ms x8) model ctx st (EOk eff model' ctx' st' evs) ->
    m_halted model' = None ->
    materialize_model_accesses model' (syscall_effect_accesses eff) = Some model'' ->
    xsstep ext segs cfg ctx st (mkCfg ms model) evs
      (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model'')) ctx' st'
| xs_materialization_fault : forall ms model x8 eff model' ctx' st' evs,
    m_halted model = None ->
    ms_svc_pending ms = Some x8 ->
    ext_claims ext (sys_input segs ms x8) = true ->
    ext_spec ext (sys_input segs ms x8) model ctx st (EOk eff model' ctx' st' evs) ->
    ~ ext_refusal ext cfg (sys_input segs ms x8) model ctx st (EOk eff model' ctx' st' evs) ->
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
  mkShared (sh_fsys S) (sh_io S) (sh_ofd S) (sh_pipes S) st (sh_meta S).

Definition with_nsctx (e : ProcessEntry) (ctx : NsCtx) : ProcessEntry :=
  mkEntry (pe_pid e) (pe_parent e) (pe_ms e) (pe_model e) (pe_ofd e) ctx.

(** It orphans at exit exactly as [absorb] does: a claimed call that ends
    the process ([xs_exit], [xs_killed]) leaves its model halted too. *)
Definition absorb_x (P : pconfig) (e : ProcessEntry) (c' : config) (ctx' : NsCtx)
    (st' : NsState) : pconfig :=
  mkPCfg (orphan_at_exit (cfg_model c') (pe_pid e)
            (replace_in (pcfg_procs P) (pe_pid e) (with_nsctx (pe_absorb e c') ctx')))
         (pcfg_root P)
         (with_sh_ns (shared_absorb (pcfg_shared P) c') st').

Definition clone_result_x (P : pconfig) (e : ProcessEntry) (c' : config) (q : Pid)
    (child : NsCtx) (st' : NsState) : pconfig :=
  mkPCfg (replace_in (pcfg_procs P) (pe_pid e) (pe_absorb e c')
            ++ [(q, with_nsctx (child_entry e (pe_cfg (pcfg_shared P) e) c' q) child)])
         (pcfg_root P)
         (with_sh_ns (with_meta (shared_absorb (pcfg_shared P) c') q (child_meta P e child)) st').

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


(** THE GUARD UNDER AN EXTENSION.  An unclaimed call is the released step,
    so the core's guard ([multiproc_allowed]) decides it.  A claimed call is
    answered by [ext_spec], not by the released spec, and classes (A) and
    (B) are properties of the released spec; so their numbers admit a
    claimed call only at a FLAT view.  That case is derived, not assumed:
    [Ns.Ext.ext_coherent] makes a claimed flat call's outcome the
    [Ns.Ext.released] one, an [EOk] whose context and namespace state are
    the ones it was given and whose effect and model are the released
    spec's, so the extension writes nothing to [sh_ns] and the class
    argument applies as it stands.  Elsewhere a claimed call with a live
    peer needs [multiproc_base] or [ext_multiproc]. *)
Definition multiproc_ok (ext : ExtSpec) (segs : list Segment) (P : pconfig)
    (e : ProcessEntry) : bool :=
  let c := pe_cfg (pcfg_shared P) e in
  match pending_input segs c with
  | Some i =>
      if ext_claims ext i
      then multiproc_base P c
           || (flat_view (pe_nsctx e) (sh_ns (pcfg_shared P)) && multiproc_classed c)
           || ext_multiproc ext i (cfg_model c) (pe_nsctx e) (sh_ns (pcfg_shared P))
      else multiproc_allowed P c
  | None => multiproc_allowed P c
  end.

(** Where the core's guard without the class numbers is open, so is the
    guard under any extension. *)
Lemma multiproc_ok_base : forall ext segs P e,
  multiproc_base P (pe_cfg (pcfg_shared P) e) = true ->
  multiproc_ok ext segs P e = true.
Proof.
  intros ext segs P e H. unfold multiproc_ok. cbv zeta.
  destruct (pending_input segs (pe_cfg (pcfg_shared P) e)) as [i|].
  - destruct (ext_claims ext i).
    + rewrite H. reflexivity.
    + rewrite multiproc_allowed_split, H. reflexivity.
  - rewrite multiproc_allowed_split, H. reflexivity.
Qed.

(** THE FORCED-ONLY FILTER OF A FAILED CLONE.  The released step filters
    a clone's outcome with [Run.spurious_refusal_cfg]: it removes an
    outcome when its errno is in the clone's refusal list
    ([Fork.clone_errnos]), the clone's family is forced-only in the run's
    configuration, and the released spec admits a non-refusal at the same
    input.  That filter cannot see the namespace state, so once an errno
    the namespace tables decide is in the refusal list (a closed pid
    namespace's ENOMEM, which the tables do not answer yet) it can remove
    an answer the tables force, and then [px_clone_fail] has no step to
    match the extension's answer.  Today no [CnErr] errno of
    [clone_ns_exact] (EPERM, EINVAL, ENOSPC) is in [Fork.clone_errnos], and
    where [clone_ns_exact] is [CnUnmodeled], [Ns.Spec.ns_ext]'s clone admits
    no failure; so under [ns_ext] the premise of [px_clone_fail] is the
    released step for every failure [ns_ext] admits
    ([NsProcs.ns_clone_fail_step_released], over
    [NsProcs.clone_ns_exact_errno]).

    So for a caller in the namespace world, under an extension other than
    [no_ext], the failure is the released step with the clone's family
    allowed to fail, and the filter removes an outcome with errno [e] only
    when all of these hold: (1) [e] is in the refusal list and its family
    is forced-only; (2) [e] is not the errno of [clone_ns_exact]'s [CnErr]
    for this call; (3) the released spec admits a non-refusal at the same
    input; and [clone_ns_exact] is not [CnUnmodeled].  (1) and (3) are
    [Run.spurious_refusal_cfg]'s conjuncts.  So an outcome is kept when the
    released filter keeps it, or when the tables decide it
    ([clone_table_kept]): [clone_fail_step] is that disjunction.  The
    refusal list stays [Fork.clone_errnos].

    The namespace world under an extension other than [no_ext] is the
    first conjunct of [clone_table_kept]: the extension's clone admits no
    success at this call.  [no_ext]'s clone ([released_clone]) admits one
    at every call, and so does every extension's for a caller in the
    released world whose word has no namespace bit
    ([Ns.Ext.ext_clone_coherent]); there the filter is the released one,
    unchanged ([clone_fail_step_unchanged]).  [Ns.Spec.ns_ext]'s clone
    admits no success whenever [clone_ns_exact] is [CnErr] or
    [CnUnmodeled], so for it the conjunct adds nothing to (2) and the last
    condition ([NsProcs.ns_clone_table_kept]).  A test of the extension's
    identity would not do: [ExtSpec] has no decidable equality, and
    [pstep_x_at_agree_iff] holds for every extension whose clone is
    [released_clone] at the caller, in the namespace world too.

    So the condition is decided per extension.  It equals the design's
    wording under [ns_ext] ([NsProcs.ns_clone_table_kept]) and today's
    filter under [no_ext] ([clone_fail_step_unchanged]), and those are the
    only extensions today.  A future [ExtSpec] must re-prove that equality
    for itself, or state how it differs. *)
Definition clone_table_kept (ext : ExtSpec) (f : Z) (m : Model) (ctx : NsCtx)
    (st : NsState) (hq en : Z) : Prop :=
  (forall child ret st', ~ ext_clone ext f m ctx st hq (CnOk child ret st'))
  /\ ((exists st', Ns.Clone.clone_ns_exact f m ctx st hq = CnErr en st')
      \/ Ns.Clone.clone_ns_exact f m ctx st hq = CnUnmodeled).

(** The released step of a failed clone, under the filter above.  The
    step is the pending clone's own syscall step, and [sstep_cfg]'s filter
    reads only the pending call's family, so [may_fail_cfg] there is the
    run's configuration with the clone's family allowed to fail. *)
Definition clone_fail_step (ext : ExtSpec) (segs : list Segment) (cfg : SpuriousCfg)
    (c : config) (ctx : NsCtx) (st : NsState) (hq en : Z) (evs : list event)
    (c' : config) : Prop :=
  sstep_cfg segs cfg c evs (SNext c')
  \/ (sstep_cfg segs may_fail_cfg c evs (SNext c')
      /\ clone_table_kept ext (clone_flags_of c) (cfg_model c) ctx st hq en).

(** Where the extension's clone admits a success, the filter is the
    released one. *)
Lemma clone_fail_step_success_iff : forall ext segs cfg c ctx st hq en evs c',
  (exists child ret st',
     ext_clone ext (clone_flags_of c) (cfg_model c) ctx st hq (CnOk child ret st')) ->
  (clone_fail_step ext segs cfg c ctx st hq en evs c' <-> sstep_cfg segs cfg c evs (SNext c')).
Proof.
  intros ext segs cfg c ctx st hq en evs c' (child & ret & st' & Hok). split.
  - intros [Hs | (_ & Hno & _)]; [exact Hs|].
    exfalso. exact (Hno child ret st' Hok).
  - intros Hs. left. exact Hs.
Qed.

(** ... so it is wherever the extension's clone is the released clone. *)
Lemma clone_fail_step_released_clone : forall ext segs cfg c ctx st hq en evs c',
  (forall o, ext_clone ext (clone_flags_of c) (cfg_model c) ctx st hq o
             <-> released_clone ctx st o) ->
  (clone_fail_step ext segs cfg c ctx st hq en evs c' <-> sstep_cfg segs cfg c evs (SNext c')).
Proof.
  intros ext segs cfg c ctx st hq en evs c' Hrc. apply clone_fail_step_success_iff.
  exists ctx, None, st. apply (proj2 (Hrc _)). unfold released_clone. left. reflexivity.
Qed.

(** NO PUBLISHED ANSWER CHANGES: under [no_ext], and for a caller in the
    released world whose word has no namespace bit, the premise of
    [px_clone_fail] is the released step under the run's configuration, as
    it was before the filter above. *)
Theorem clone_fail_step_unchanged : forall ext segs cfg c ctx st hq en evs c',
  ext = no_ext \/ (flat_view ctx st = true /\ has_ns_bits (clone_flags_of c) = false) ->
  (clone_fail_step ext segs cfg c ctx st hq en evs c' <-> sstep_cfg segs cfg c evs (SNext c')).
Proof.
  intros ext segs cfg c ctx st hq en evs c' H. apply clone_fail_step_released_clone.
  intros o. destruct H as [-> | (Hf & Hb)].
  - apply no_ext_clone.
  - apply ext_clone_coherent; assumption.
Qed.

Lemma bvmap_get_set_eq {n A} (k k' : bv n) (x : A) mp :
  k = k' -> bvmap_get k' (bvmap_set k x mp) = Some x.
Proof. intros ->. apply LinuxProcessSemantics.Riscv.Prelude.bvmap_get_set_same. Qed.

(** a0 after a syscall step holds the effect's return value. *)
Lemma a0_after_effect : forall ms eff,
  ms_gpr (advance_past_svc (apply_effect ms eff)) 0 = eff_ret eff.
Proof.
  intros ms eff. unfold ms_gpr, advance_past_svc, apply_effect, set_reg, reg_get. simpl.
  erewrite bvmap_get_set_eq by (apply bv_eq; reflexivity). reflexivity.
Qed.

(** THE FILTER, OUTCOME BY OUTCOME, for one syscall outcome [eff] of a
    pending clone and an errno [en]; [px_clone_fail] ties the two (a0
    after the step holds [errno_ret en]), and the cases pass
    [SpuriousCfg.errno_eff en].  [clone_kept]: the released filter
    keeps it ([Run.spurious_refusal_cfg]), or the namespace tables decide
    it ([clone_table_kept]); such an outcome is a step of
    [clone_fail_step] ([clone_fail_step_kept]).  [clone_removed]: the
    released filter removes it and the tables do not decide it; such an
    outcome is not a step ([clone_fail_step_removed]).  The two exclude
    each other ([clone_kept_not_removed]); that one of them holds is the
    excluded middle on [Run.spurious_refusal_cfg] and [clone_table_kept],
    which are not decidable in general, so each case states the one it
    proves. *)
Definition clone_kept (ext : ExtSpec) (cfg : SpuriousCfg) (i : SyscallInput) (m : Model)
    (f : Z) (ctx : NsCtx) (st : NsState) (hq en : Z) (eff : SyscallEffect) : Prop :=
  ~ spurious_refusal_cfg cfg i m eff \/ clone_table_kept ext f m ctx st hq en.

Definition clone_removed (ext : ExtSpec) (cfg : SpuriousCfg) (i : SyscallInput) (m : Model)
    (f : Z) (ctx : NsCtx) (st : NsState) (hq en : Z) (eff : SyscallEffect) : Prop :=
  spurious_refusal_cfg cfg i m eff /\ ~ clone_table_kept ext f m ctx st hq en.

Lemma clone_kept_not_removed : forall ext cfg i m f ctx st hq en eff,
  clone_kept ext cfg i m f ctx st hq en eff -> ~ clone_removed ext cfg i m f ctx st hq en eff.
Proof.
  intros ext cfg i m f ctx st hq en eff [Hn | Hk] (Hs & Hnk); [exact (Hn Hs) | exact (Hnk Hk)].
Qed.

Lemma clone_fail_step_kept : forall ext segs cfg ms model x8 eff model' model'' evs
                                    ctx st hq en,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  m_halted model' = None ->
  materialize_model_accesses model' (syscall_effect_accesses eff) = Some model'' ->
  clone_kept ext cfg (sys_input segs ms x8) model (clone_flags_of (mkCfg ms model))
    ctx st hq en eff ->
  clone_fail_step ext segs cfg (mkCfg ms model) ctx st hq en evs
    (mkCfg (advance_past_svc (apply_effect ms eff)) model'').
Proof.
  intros ext segs cfg ms model x8 eff model' model'' evs ctx st hq en
    Hh Hx8 Hsp Hh' Hmat [Hn | Hk].
  - left. eapply sstep_cfg_syscall; eassumption.
  - right. split; [|exact Hk].
    eapply sstep_cfg_syscall; try eassumption. apply spurious_refusal_may_fail.
Qed.

Lemma clone_fail_step_removed : forall ext segs cfg ms model x8 eff evs model''
                                       ctx st hq en,
  ms_svc_pending ms = Some x8 ->
  clone_removed ext cfg (sys_input segs ms x8) model (clone_flags_of (mkCfg ms model))
    ctx st hq en eff ->
  ~ clone_fail_step ext segs cfg (mkCfg ms model) ctx st hq en evs
      (mkCfg (advance_past_svc (apply_effect ms eff)) model'').
Proof.
  intros ext segs cfg ms model x8 eff evs model'' ctx st hq en Hx8 (Hsp & Hnk) Hstep.
  destruct Hstep as [H | (_ & Hk)]; [|exact (Hnk Hk)].
  assert (Hadv : ms_svc_pending (advance_past_svc (apply_effect ms eff)) = None)
    by reflexivity.
  remember (mkCfg ms model) as c0 eqn:Ec.
  remember (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model'')) as r0 eqn:Er.
  destruct H; injection Ec as Ems Emd; subst; try discriminate Er; try congruence;
    pose proof (f_equal (fun r => match r with
                                  | SNext c => ms_svc_pending (cfg_ms c)
                                  | SError => None
                                  end) Er) as Ep;
    pose proof (f_equal (fun r => match r with
                                  | SNext c => Some (ms_gpr (cfg_ms c) 0)
                                  | SError => None
                                  end) Er) as Ea;
    cbn [cfg_ms] in Ep, Ea; try congruence.
  (* the syscall arm: the same return value, so the same filter *)
  rewrite !a0_after_effect in Ea. injection Ea as Hret.
  match goal with
  | Hn : ~ spurious_refusal_cfg _ (sys_input _ _ ?y) _ _ |- _ =>
      assert (Hy : y = x8) by congruence; rewrite Hy in Hn;
      apply Hn; destruct Hsp as (Hoff & Hr & Hex);
      split; [exact Hoff | split; [rewrite Hret; exact Hr | exact Hex]]
  end.
Qed.

(** When every family may fail ([may_fail_cfg]), every outcome is kept. *)
Lemma clone_kept_may_fail : forall ext i m f ctx st hq en eff,
  clone_kept ext may_fail_cfg i m f ctx st hq en eff.
Proof. intros. left. apply spurious_refusal_may_fail. Qed.

(** ... and the step is the released one. *)
Lemma clone_fail_step_may_fail : forall ext segs c ctx st hq en evs c',
  clone_fail_step ext segs may_fail_cfg c ctx st hq en evs c'
  <-> sstep_cfg segs may_fail_cfg c evs (SNext c').
Proof.
  intros. split; [intros [H | (H & _)]; exact H | intros H; left; exact H].
Qed.

(** An answer that is not a refusal is always kept. *)
Lemma clone_kept_not_refusal : forall ext cfg i m f ctx st hq en eff,
  refusal_b i m (eff_ret eff) = false -> clone_kept ext cfg i m f ctx st hq en eff.
Proof. intros ext cfg i m f ctx st hq en eff Hr. left. exact (spurious_refusal_not_refusal _ _ _ _ Hr). Qed.

(** Under [no_ext], and for a caller in the released world whose word
    has no namespace bit, the extension's clone admits a success, so the
    tables keep nothing and both decisions are the released filter's. *)
Lemma clone_success_unchanged : forall ext f m ctx st hq,
  ext = no_ext \/ (flat_view ctx st = true /\ has_ns_bits f = false) ->
  ext_clone ext f m ctx st hq (CnOk ctx None st).
Proof.
  intros ext f m ctx st hq H.
  destruct H as [-> | (Hf & Hb)];
    [apply (proj2 (no_ext_clone _ _ _ _ _ _)) | apply (proj2 (ext_clone_coherent ext _ _ _ _ _ _ Hf Hb))];
    unfold released_clone; left; reflexivity.
Qed.

Lemma clone_kept_unchanged : forall ext cfg i m f ctx st hq en eff,
  ext = no_ext \/ (flat_view ctx st = true /\ has_ns_bits f = false) ->
  (clone_kept ext cfg i m f ctx st hq en eff <-> ~ spurious_refusal_cfg cfg i m eff).
Proof.
  intros ext cfg i m f ctx st hq en eff H. split; [|intros Hn; left; exact Hn].
  intros [Hn | (Hno & _)]; [exact Hn|].
  exfalso. exact (Hno ctx None st (clone_success_unchanged ext f m ctx st hq H)).
Qed.

Lemma clone_removed_unchanged : forall ext cfg i m f ctx st hq en eff,
  ext = no_ext \/ (flat_view ctx st = true /\ has_ns_bits f = false) ->
  (clone_removed ext cfg i m f ctx st hq en eff <-> spurious_refusal_cfg cfg i m eff).
Proof.
  intros ext cfg i m f ctx st hq en eff H. split; [intros (Hs & _); exact Hs|].
  intros Hs. split; [exact Hs|]. intros (Hno & _).
  exact (Hno ctx None st (clone_success_unchanged ext f m ctx st hq H)).
Qed.

(** ONE TRANSITION OF THE SYSTEM UNDER AN EXTENSION, indexed by the pid
    that steps, as [pstep_at] is.

    THE [wait4] GATE HOLDS HERE TOO, CLAIMED OR NOT.  [px_other] and
    [px_error] are behind [wait4_owned_b = false], so neither the released
    step nor the extension answers a [wait4] of a caller with a child in
    the table, and the three gate arms below carry no claim premise.  They
    could not: [ext_agrees] promises an unclaimed call only for the
    blocking shape, so a claim premise on the WNOHANG arms would break
    [pstep_x_at_agree_iff].  [px_wait_reap] keeps its claim premise as it
    was; a claimed blocking call therefore still has no arm. *)
Inductive pstep_x_at (ext : ExtSpec) (cenv : CloneEnv) (segs : list Segment) (cfg : SpuriousCfg)
  : Pid -> pconfig -> list event -> pstep_to -> Prop :=
| px_other : forall P e evs c' ctx' st',
    look P (pe_pid e) = Some e ->
    xsstep ext segs cfg (pe_nsctx e) (sh_ns (pcfg_shared P))
      (pe_cfg (pcfg_shared P) e) evs (SNext c') ctx' st' ->
    clone_pending_b (pe_cfg (pcfg_shared P) e) = false ->
    wait4_intercept_b (pe_cfg (pcfg_shared P) e) = false ->
    wait4_owned_b P e = false ->
    peer_refused_b P e = false ->
    sync_pending_b P e = false ->
    step_refused_b P e c' = false ->
    answer_ok_b P e c' = true ->
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
    says the failure leaves.  Its errno comes from the released step under
    the clone's forced-only filter ([clone_fail_step]): under a forced-only
    configuration a refusal the released filter
    ([Run.spurious_refusal_cfg]) drops is no step here either, unless the
    namespace tables decide it ([clone_table_kept]); and the run's clone
    environment [cenv] must admit the failure. *)
| px_clone_fail : forall P e evs c' en hq st',
    look P (pe_pid e) = Some e ->
    claimed_at ext segs (pe_cfg (pcfg_shared P) e) = false ->
    clone_fail_step ext segs cfg (pe_cfg (pcfg_shared P) e) (pe_nsctx e)
      (sh_ns (pcfg_shared P)) hq en evs c' ->
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
                         (clear_shared (reap_model q model'')) (pe_ofd e) (pe_nsctx e)))
                   q)
                (pcfg_root P)
                (shared_absorb (pcfg_shared P) (mkCfg (pe_ms e) model''))))
| px_error : forall P e evs ctx' st',
    look P (pe_pid e) = Some e ->
    xsstep ext segs cfg (pe_nsctx e) (sh_ns (pcfg_shared P))
      (pe_cfg (pcfg_shared P) e) evs SError ctx' st' ->
    wait4_intercept_b (pe_cfg (pcfg_shared P) e) = false ->
    wait4_owned_b P e = false ->
    pstep_x_at ext cenv segs cfg (pe_pid e) P evs PError
| px_outside : forall P e,
    look P (pe_pid e) = Some e ->
    m_halted (pe_model e) = None ->
    multiproc_ok ext segs P e = false ->
    pstep_x_at ext cenv segs cfg (pe_pid e) P [] PError
| px_wait_nohang_reap : forall P e q ez x8 stat_addr ru ru_bytes status eff
                          model'' dumped,
    look P (pe_pid e) = Some e ->
    m_halted (pe_model e) = None ->
    ms_svc_pending (pe_ms e) = Some x8 ->
    wait4_owned_b P e = true ->
    wait4_nohang_args (pe_ms e) = Some (stat_addr, ru) ->
    wait4_rusage_ok_b segs (pe_ms e) x8 ru = true ->
    look P q = Some ez ->
    q <> pe_pid e ->
    pe_parent ez = Some (pe_pid e) ->
    m_killed (pe_model ez) = None ->
    pe_status dumped ez = Some status ->
    read_bytes_map (in_wmem (sys_input segs (pe_ms e) x8)) stat_addr
      (Z_to_bv 64 4) <> None ->
    List.length ru_bytes = Z.to_nat RUSAGE_BYTES ->
    eff = mkEffect q (wait4_nohang_writes stat_addr status ru ru_bytes) [] ->
    materialize_model_accesses (cfg_model (pe_cfg (pcfg_shared P) e))
      (syscall_effect_accesses eff) = Some model'' ->
    pstep_x_at ext cenv segs cfg (pe_pid e) P [] (PNext (wait4_reap_result P e q eff model''))
| px_wait_nohang_zero : forall P e x8 stat_addr ru,
    look P (pe_pid e) = Some e ->
    m_halted (pe_model e) = None ->
    ms_svc_pending (pe_ms e) = Some x8 ->
    wait4_owned_b P e = true ->
    wait4_nohang_args (pe_ms e) = Some (stat_addr, ru) ->
    wait4_rusage_ok_b segs (pe_ms e) x8 ru = true ->
    List.existsb pe_zombie_b (children_of P (pe_pid e)) = false ->
    pstep_x_at ext cenv segs cfg (pe_pid e) P [] (PNext (wait4_zero_result P e))
| px_wait_refuse : forall P e,
    look P (pe_pid e) = Some e ->
    m_halted (pe_model e) = None ->
    wait4_refused_b segs P e = true ->
    pstep_x_at ext cenv segs cfg (pe_pid e) P [] PError
| px_peer_refuse : forall P e,
    look P (pe_pid e) = Some e ->
    m_halted (pe_model e) = None ->
    peer_refused_b P e = true ->
    pstep_x_at ext cenv segs cfg (pe_pid e) P [] PError
| px_sync : forall P e,
    look P (pe_pid e) = Some e ->
    m_halted (pe_model e) = None ->
    sync_pending_b P e = true ->
    pstep_x_at ext cenv segs cfg (pe_pid e) P [] (PNext (sync_result P e))
| px_step_refuse : forall P e evs c' ctx' st',
    look P (pe_pid e) = Some e ->
    xsstep ext segs cfg (pe_nsctx e) (sh_ns (pcfg_shared P))
      (pe_cfg (pcfg_shared P) e) evs (SNext c') ctx' st' ->
    clone_pending_b (pe_cfg (pcfg_shared P) e) = false ->
    wait4_intercept_b (pe_cfg (pcfg_shared P) e) = false ->
    wait4_owned_b P e = false ->
    peer_refused_b P e = false ->
    sync_pending_b P e = false ->
    multiproc_ok ext segs P e = true ->
    step_refused_b P e c' = true ->
    answer_ok_b P e c' = true ->
    pstep_x_at ext cenv segs cfg (pe_pid e) P [] PError
| px_pin_root : forall P e r t,
    look P (pe_pid e) = Some e ->
    m_halted (pe_model e) = None ->
    root_pin_pending_b P e = true ->
    look P (pcfg_root P) = Some r ->
    (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z ->
    key_taken_b P t = false ->
    pstep_x_at ext cenv segs cfg (pe_pid e) P [] (PNext (pin_root P r t)).

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
              | eapply px_clone_claimed | eapply px_wait_reap | eapply px_error | eapply px_outside
              | eapply px_wait_nohang_reap | eapply px_wait_nohang_zero | eapply px_wait_refuse
              | eapply px_peer_refuse | eapply px_sync | eapply px_step_refuse
              | eapply px_pin_root];
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
    cbv beta iota in H |- *; [rewrite H|]; reflexivity.
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

(** A pending clone is not a [wait4], so the gate is closed at it. *)
Lemma clone_pending_not_owned : forall P e,
  clone_pending_b (pe_cfg (pcfg_shared P) e) = true -> wait4_owned_b P e = false.
Proof.
  intros P e H. unfold clone_pending_b in H. cbn [cfg_ms pe_cfg] in H.
  destruct (ms_svc_pending (pe_ms e)) as [x8|] eqn:Hs; [|discriminate H].
  apply (wait4_owned_not_260 P e x8 Hs). unfold clone_sysno in H.
  apply orb_true_iff in H as [H|H]; apply Z.eqb_eq in H; rewrite H; discriminate.
Qed.

(** ... and no clone number is namespace-gated. *)
Lemma clone_pending_not_ns : forall P e,
  clone_pending_b (pe_cfg (pcfg_shared P) e) = true -> peer_refused_b P e = false.
Proof.
  intros P e H. unfold clone_pending_b in H. cbn [cfg_ms pe_cfg] in H.
  destruct (ms_svc_pending (pe_ms e)) as [x8|] eqn:Hs; [|discriminate H].
  apply (peer_refused_of_sysno P e x8 Hs). unfold clone_sysno in H.
  apply orb_true_iff in H as [H|H]; apply Z.eqb_eq in H; rewrite H; reflexivity.
Qed.

(** ... nor filtered by the pid filter. *)
Lemma clone_pending_answer_ok : forall P e c',
  clone_pending_b (pe_cfg (pcfg_shared P) e) = true -> answer_ok_b P e c' = true.
Proof.
  intros P e c' H. unfold clone_pending_b in H. cbn [cfg_ms pe_cfg] in H.
  unfold answer_ok_b.
  destruct (ms_svc_pending (pe_ms e)) as [x8|]; [|reflexivity].
  unfold clone_sysno in H.
  apply orb_true_iff in H as [H|H]; apply Z.eqb_eq in H; rewrite H; reflexivity.
Qed.

(** ... nor read by the step gate. *)
Lemma clone_pending_not_step : forall P e c',
  clone_pending_b (pe_cfg (pcfg_shared P) e) = true -> step_refused_b P e c' = false.
Proof.
  intros P e c' H. unfold clone_pending_b in H. cbn [cfg_ms pe_cfg] in H.
  unfold step_refused_b.
  destruct (ms_svc_pending (pe_ms e)) as [x8|]; [|discriminate H].
  rewrite H. cbn [negb andb orb].
  unfold clone_sysno in H.
  apply orb_true_iff in H as [H|H]; apply Z.eqb_eq in H; rewrite H;
    rewrite andb_false_r; reflexivity.
Qed.

(** ... nor synced. *)
Lemma clone_pending_not_sync : forall P e,
  clone_pending_b (pe_cfg (pcfg_shared P) e) = true -> sync_pending_b P e = false.
Proof.
  intros P e H. unfold clone_pending_b in H. cbn [cfg_ms pe_cfg] in H.
  destruct (ms_svc_pending (pe_ms e)) as [x8|] eqn:Hs; [|discriminate H].
  apply (sync_of_sysno P e x8 Hs). unfold clone_sysno in H.
  apply orb_true_iff in H as [H|H]; apply Z.eqb_eq in H; rewrite H; reflexivity.
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
    as the released step filters their effects
    ([Ext.ext_refusal_released]), and the namespace context and state do
    not change. *)
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
      intros Hc. apply Hrf.
      exact (proj2 (ext_refusal_released ext cfg _ _ _ _ eff _ _ _ _ Hf Hcl) Hc).
    + apply (proj1 (ext_coherent ext _ _ _ _ Hf Hcl _)) in Hsp.
      destruct Hsp as (_ & _ & Hsp).
      split; [|split; reflexivity].
      apply sstep_cfg_syscall_materialization_fault
        with (x8 := x8) (eff := eff) (model' := model') (evs := evs0); try assumption.
      intros Hc. apply Hrf.
      exact (proj2 (ext_refusal_released ext cfg _ _ _ _ eff _ _ _ _ Hf Hcl) Hc).
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
      | ms model fn n eff model' model'' evs0 Hh Hx8 Hm Hfn Hn Hsp Hne Hh' Hmat
      | ms model fn n eff model' evs0 Hh Hx8 Hm Hfn Hn Hsp Hne Hh' Hmat
      | ms model fn Hh Hx8 Hm Hfn Hu
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
      * intros Hc. apply Hrf.
        exact (proj1 (ext_refusal_released ext cfg _ _ _ _ eff _ _ _ _ Hf Hcl) Hc).
    + apply xs_materialization_fault
        with (x8 := x8) (eff := eff) (model' := model') (ctx' := ctx) (st' := st) (evs := evs0);
        try assumption.
      * apply (proj2 (ext_coherent ext _ _ _ _ Hf Hcl _)).
        exact (conj eq_refl (conj eq_refl Hsp)).
      * intros Hc. apply Hrf.
        exact (proj1 (ext_refusal_released ext cfg _ _ _ _ eff _ _ _ _ Hf Hcl) Hc).
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
    [|reflexivity].
  destruct (ext_claims ext i); [|reflexivity].
  rewrite (ext_multiproc_coherent ext i _ _ _ Hf), Hf, orb_false_r, andb_true_l.
  symmetry. apply multiproc_allowed_split.
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
      [ Q e ev c' ctx' st' Hl Hx Hcp Hwt Hwo Hns Hsy Hst Han Hmp
      | Q e ev c' q child ret st' Hl Hcl Hs Hsucc Hq Hfree Hma Hec
      | Q e ev c' en hq st' Hl Hcl Hs Hcp Hsucc Hret Hma Hec Hnr
      | Q e ev c' hq Hl Hcl Hs Hcp Hma Hec
      | Q e Hl Hh Hcp Hcl
      | Q e q ez x8 stat_addr status eff model'' dumped
          Hl Hcl Hh Hx8 Hwt Hargs Hq Hne Hpar Hk Hst Hrd Heff Hmat
      | Q e ev ctx' st' Hl Hx Hwt Hwo
      | Q e Hl Hh Hmp
      | Q e q ez x8 stat_addr ru ru_bytes status eff model'' dumped
          Hl Hh Hx8 Hwo Hna Hru Hq Hne Hpar Hk Hst Hrd Hlen Heff Hmat
      | Q e x8 stat_addr ru Hl Hh Hx8 Hwo Hna Hru Hz
      | Q e Hl Hh Hrf
      | Q e Hl Hh Hns
      | Q e Hl Hh Hsy
      | Q e ev c' ctx' st' Hl Hx Hcp Hwt Hwo Hns Hsy Hmp Hst Han
      | Q e r t Hl Hh Hpin Hlr Ht Hkt ]; intros Hag;
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
      apply (proj1 (clone_fail_step_released_clone ext segs cfg _ _ _ hq en ev c' (Hcln hq)))
        in Hs.
      apply (proj1 (Hcln _ _)) in Hec.
      destruct Hec as [Heq | (en' & _ & Heq)]; [discriminate Heq|].
      injection Heq as _ ->. rewrite absorb_x_same.
      apply pstep_other; try assumption.
      * apply clone_pending_not_wait4. exact Hcp.
      * apply clone_pending_not_owned. exact Hcp.
      * apply clone_pending_not_ns. exact Hcp.
      * apply clone_pending_not_sync. exact Hcp.
      * apply clone_pending_not_step. exact Hcp.
      * apply clone_pending_answer_ok. exact Hcp.
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
    + (* px_wait_nohang_reap: the gate's own arm, on both sides *)
      eapply pstep_wait_nohang_reap; eassumption.
    + (* px_wait_nohang_zero *)
      eapply pstep_wait_nohang_zero; eassumption.
    + (* px_wait_refuse *)
      apply pstep_wait_refuse; assumption.
    + (* px_peer_refuse: the gate's own arm, on both sides *)
      apply pstep_peer_refuse; assumption.
    + (* px_sync: the gate's own arm, on both sides *)
      apply pstep_sync; assumption.
    + (* px_step_refuse: the gate's own arm, on both sides *)
      apply (proj1 (Hxs _ _ _ _ _)) in Hx. destruct Hx as (Hs & -> & ->).
      apply pstep_step_refuse with (evs := ev) (c' := c'); try assumption.
      * apply clone_pending_success. exact Hcp.
      * rewrite <- Hmpe. exact Hmp.
    + (* px_pin_root: the core's own arm, on both sides *)
      eapply pstep_pin_root; eassumption.
  - intros H. revert Hag. destruct H as
      [ Q e ev c' Hl Hs Hsucc Hwt Hma Hwo Hns Hsy Hst Han
      | Q e ev c' q Hl Hs Hsucc Hq Hfree Hma
      | Q e q ez x8 stat_addr status eff model'' dumped
          Hl Hh Hx8 Hwt Hargs Hq Hne Hpar Hk Hst Hrd Heff Hmat
      | Q e ev Hl Hs Hwt Hwo
      | Q e Hl Hh Hma
      | Q e q ez x8 stat_addr ru ru_bytes status eff model'' dumped
          Hl Hh Hx8 Hwo Hna Hru Hq Hne Hpar Hk Hst Hrd Hlen Heff Hmat
      | Q e x8 stat_addr ru Hl Hh Hx8 Hwo Hna Hru Hz
      | Q e Hl Hh Hrf
      | Q e Hl Hh Hns
      | Q e Hl Hh Hsy
      | Q e ev c' Hl Hs Hsucc Hwt Hma Hwo Hns Hsy Hst Han
      | Q e r t Hl Hh Hpin Hlr Ht Hkt ]; intros Hag;
      destruct (Hag e Hl) as (Hxs & Hclp & Hwtp & Hmpe & Hcln & Hnrf).
    + (* pstep_other *)
      destruct (clone_pending_b (pe_cfg (pcfg_shared Q) e)) eqn:Hp.
      * destruct (clone_fail_errno _ _ Hp Hsucc) as (en & Hen & Hret).
        rewrite <- absorb_x_same.
        apply px_clone_fail with (en := en) (hq := 0%Z); try assumption.
        -- exact (Hclp eq_refl).
        -- left. exact Hs.
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
    + (* pstep_wait_nohang_reap *)
      eapply px_wait_nohang_reap; eassumption.
    + (* pstep_wait_nohang_zero *)
      eapply px_wait_nohang_zero; eassumption.
    + (* pstep_wait_refuse *)
      apply px_wait_refuse; assumption.
    + (* pstep_peer_refuse *)
      apply px_peer_refuse; assumption.
    + (* pstep_sync *)
      apply px_sync; assumption.
    + (* pstep_step_refuse *)
      destruct (clone_pending_b (pe_cfg (pcfg_shared Q) e)) eqn:Hp.
      * rewrite (clone_pending_not_step _ _ c' Hp) in Hst. discriminate Hst.
      * apply px_step_refuse with (evs := ev) (c' := c')
          (ctx' := pe_nsctx e) (st' := sh_ns (pcfg_shared Q)); try assumption.
        -- apply (proj2 (Hxs _ _ _ _ _)). split; [exact Hs | split; reflexivity].
        -- rewrite Hmpe. exact Hma.
    + (* pstep_pin_root *)
      eapply px_pin_root; eassumption.
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
