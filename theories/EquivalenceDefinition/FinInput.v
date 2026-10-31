(** * EquivalenceDefinition.FinInput — finite process inputs as a record

    TRUST BOUNDARY: this file is part of the trusted specification.
    Proof files never edit it.  A top-level check whose statement
    quantifies over [FinProcInput] — the classifier shapes do, and the
    weighted-measure layer is a function out of it — depends on the
    definitions here remaining fixed, exactly as the baseline check
    depends on [Equivalence].

    ** This is NOT a validity claim about standard input

    [Run.valid_input] constrains argv, envp, the initial file system,
    the image's keys, the launching credentials, the soft descriptor
    limit, the blocked-signal mask, the hart's AT_HWCAP word and the
    random device's declared stream ([Run.valid_argv], [Run.valid_envp],
    [Fs.valid_fs], [Fs.fs_keys_relative], [Run.valid_creds],
    [Run.valid_nofile], [Run.valid_sigmask], [Run.valid_hwcap],
    [Run.valid_urandom]) — and
    deliberately none for the standard-input stream.  The argument for
    that is made twice in theories/LinuxProcessSem/Run.v, at the
    [Run.valid_input] declaration and in the section banner above it: the
    stream's elements are bytes by TYPING, so there is nothing left for a
    predicate to say, and any colist of bytes, finite or infinite, is an
    input a real process could be handed.  A never-ending pipe is not an
    invalid input; it is an input.

    That argument stands, untouched.  Nothing here adds a clause to
    [Run.valid_input]; [valid_fin_input] below is literally
    [Run.valid_input] of the corresponding [State.ProcInput], and it says
    exactly as little about stdin as its parent does
    ([valid_fin_input_stdin_irrelevant], and
    [valid_input_stdin_irrelevant] for the underlying fact).  A stream
    being infinite is therefore not a defect, and this file does not
    treat it as one.

    THE RANDOM DEVICE IS THE EXCEPTION THAT PROVES IT.
    [Run.valid_urandom] does ask that
    the declared /dev/urandom stream never end, and that is not a
    restriction of the same kind: a pipe that ends is a real pipe, and a
    /dev/urandom that ends is no device at all, so the clause excludes a
    declaration Linux cannot produce rather than one it can.  What it
    costs this file is that a record's [fin_urandom] denotes its bytes
    followed by [State.default_urandom] rather than stopping
    ([stream_of_list_then]); see [finite_input].  Standard input is
    still padded by nothing and still ends where its list ends.

    Finiteness is instead the HYPOTHESIS OF A DIFFERENT THEOREM SHAPE.
    [Equivalence.strong_universal_T] and
    [Equivalence.strong_universal_error_free_T] quantify over every valid
    input and must keep the infinite ones — a target that diverges on an
    endless pipe exactly when the source does is part of what those
    statements assert.  A classifier obligation is the other kind: it
    says a binary EXITS ([MustExit.must_exit_with]) with a verdict on
    each input, and a program that must read to end-of-input before it
    can answer cannot terminate on a stream that never ends.  Restricting
    the quantifier is the honest response.  Restricting the MODEL — a
    [Run.valid_input] that rejected infinite STANDARD-INPUT streams —
    would be a lie about Linux, and would silently weaken every existing
    equivalence statement in the tree.  So the restriction lives in the consuming
    statement, where a reader can see it, and the two shapes coexist.

    ** Why a record, and not just the predicate

    Both are here.  [finite_input] is the predicate on [State.ProcInput],
    [FinProcInput] is the record, and [finite_input_iff_image] says they
    carve out the same inputs — so this is a representation choice, not a
    second restriction.

    The record earns its place because a WEIGHT FUNCTION MUST COMPUTE.
    The measure layer asks a task author for a total function from inputs
    to rationals, which the consuming checker then evaluates; the natural
    ones are structural recursions over the input bytes (a length, a
    per-byte product, a decreasing weight per read).  A
    [State.InputStream] admits no such function.  It is coinductive, so a
    [Fixpoint] over it is rejected — every consumer in the tree pays for
    this already: [State.stream_take] threads a [nat] fuel argument it
    does not otherwise need, and [Common.DrainAlg.stream_firstn] is
    written the same way for the same reason.

    Carrying the predicate alongside the stream — a [State.ProcInput]
    together with a proof of [finite_input] — does not rescue the
    situation either.  [finite_stream] is a [Prop], so its derivations
    are erased and cannot be eliminated into [Type]: there is no way to
    recurse on the proof to produce a rational.  Putting it in [Type]
    would make the "input" a stream plus a particular derivation, and two
    derivations of the same stream's finiteness would then be two
    different inputs.  A [list byte] has none of these problems: it is
    inductive, it recurses, and it is a canonical representation.

    The record buys that for STANDARD INPUT, which is what the weights
    the measure layer motivates are computed from, and not for the
    network: [fin_net] is a [State.NetQueue] carried across unchanged and
    still coinductive.  The reason is exactness, and it is argued at the
    record below — restricting the network would make "every valid
    [FinProcInput]" a narrower quantifier than "every finite valid
    input", which is the one property this record must not lose.

    ** The embedding is exact

    [to_proc_input] is injective on every field but the random one
    ([to_proc_input_inj], whose hypothesis says so, and
    [to_proc_input_not_inj], which exhibits the collision), everything
    in its image is finite ([finite_input_to_proc_input]), and
    everything finite is in its image ([finite_input_surjection]).  So
    "for every finite valid input" and "for every valid [FinProcInput]"
    are the same quantifier, and a reader checking a classifier statement against that
    informal phrase need not reason about the record at all;
    [valid_finite_input_surjection] is that sentence stated with the
    validity premise carried across, which is the form those statements
    are actually quantified in.
    [stream_take_of_list] pins the other half of the correspondence — the
    bytes in [fin_stdin] are exactly the bytes the process reads, in
    order, followed by end-of-file, for a read of any sufficiently large
    buffer — so the record is not merely isomorphic to something, it
    denotes the input it looks like.

    ** The core, and what the measure layer charges for

    [FinCore] and [fin_core] project out the four finite fields and
    forget the launch environment ([fin_uid], [fin_gid], [fin_groups],
    [fin_net], [fin_nofile], [fin_sigmask], [fin_hwcap]).  This is not a
    convenience projection: it is the index [Measure.weight_bound_T]
    counts by, and the reason is that the seven forgotten fields are
    invisible to a classifier that ignores them while two of them range
    over infinitely many valid values.
    [fin_core_env_eq] pins that the core forgets the launch environment
    and NOTHING else — the lemma to re-check when a field next joins
    [State.ProcInput] — and [fin_core_fibre_infinite] pins that the
    fibre over a core is an infinite family of equally VALID records,
    which is the half of [Measure]'s unprovability argument that can be
    mechanized.  The argument itself is in [Measure]'s header, where the
    obligation it justifies lives.

    ** Non-vacuity

    Finiteness can fail: [all_zeros_not_finite] refutes it on a concrete
    infinite stream, so [finite_stream] is not a predicate everything
    satisfies, and [finite_stream_bites] states both directions together.
    Validity does not imply it either ([valid_input_not_finite]), which
    is the mechanical form of this header's first section: the finite
    restriction is a real restriction, taken on purpose, and not a
    consequence of anything [Run] already demands. *)

From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   Finite streams
   ========================================================================= *)

(** The input stream that delivers exactly the bytes of [l] and then ends.
    Structural recursion on the LIST, which is inductive — the result
    being coinductive is no obstacle, and no [CoFixpoint] is needed
    because the stream this builds is always finite.

    [stream_take_of_list] below is the statement that this is the right
    function: reading [length l] bytes off it yields [l] itself and
    leaves [State.IEof]. *)
Fixpoint stream_of_list (l : list byte) : InputStream :=
  match l with
  | [] => IEof
  | b :: l' => ICons b (stream_of_list l')
  end.

(** THE SAME LIST, FOLLOWED BY A TAIL THAT GOES ON, which is what the
    RANDOM declaration has to denote and what the standard-input one
    must not.

    [Run.valid_urandom] asks that a launch's declared random stream
    never end, because a /dev/urandom that runs out is not a device.  A
    [FinProcInput]'s [fin_urandom] is a LIST — it has to be, or the
    weight functions this record exists for could not recurse on it —
    so a finite record cannot denote an endless stream by itself.  It
    denotes one by PADDING: the declared bytes, and then
    [State.default_urandom] forever.

    WITHOUT THIS, [valid_fin_input] WOULD BE UNSATISFIABLE and every
    classifier statement quantified over it VACUOUSLY TRUE, which is the
    exact failure this file's header is written against.  Padding is the
    smallest repair: it changes no [fin_urandom] a task can write, it
    keeps the record inductive, and it leaves
    [valid_fin_input_urandom_irrelevant] true, since every list pads to
    an endless stream.

    STANDARD INPUT IS NOT PADDED and must not be.  A pipe that ends is a
    real pipe and [finite_input] is about exactly that; padding stdin
    would make a classifier task unable to express the end of input at
    all. *)
Fixpoint stream_of_list_then (l : list byte) (s : InputStream) : InputStream :=
  match l with
  | [] => s
  | b :: l' => ICons b (stream_of_list_then l' s)
  end.

Lemma stream_of_list_then_infinite : forall l s,
  State.stream_infinite s -> State.stream_infinite (stream_of_list_then l s).
Proof.
  induction l as [|b l IH]; intros s Hs; cbn [stream_of_list_then].
  - exact Hs.
  - apply State.stream_infinite_cons. now apply IH.
Qed.

(** The stream ends after finitely many bytes.

    INDUCTIVE, and that is the whole content: a [State.InputStream] is
    coinductive, so an infinite stream is a perfectly good inhabitant of
    the type and nothing about the type distinguishes it.  An inductive
    predicate cannot be built for one — every derivation is finite, and
    each [finite_stream_cons] strips one [State.ICons], so a derivation
    is a proof that [State.IEof] is reached in a bounded number of steps.
    [all_zeros_not_finite] is that reasoning carried out on a witness.

    This is the same argument [Run.all_traces_error]'s header makes for
    ITS inductive shape, and the same one [MustExit.must_exit_at]
    inherits: inductive is how termination is expressed when the object
    being talked about is coinductive. *)
Inductive finite_stream : InputStream -> Prop :=
| finite_stream_eof : finite_stream IEof
| finite_stream_cons : forall b s, finite_stream s -> finite_stream (ICons b s).

(** The decomposition ("frob") lemma for [State.InputStream]: a stream is
    equal to its own one-level case analysis.  Trivial by [destruct] —
    the point is not the proof but what it enables.  A [CoFixpoint]
    constant does not reduce on its own; it reduces only as the scrutinee
    of a [match].  Rewriting with this lemma is what puts the constant in
    that position, so a stream defined corecursively can be unfolded one
    constructor at a time.  [all_zeros_unfold] is the use. *)
Lemma stream_decompose : forall s,
  s = match s with
      | IEof => IEof
      | ICons b r => ICons b r
      end.
Proof. destruct s; reflexivity. Qed.

(** Every list builds a finite stream. *)
Lemma finite_stream_stream_of_list : forall l, finite_stream (stream_of_list l).
Proof.
  induction l as [| b l IH]; cbn [stream_of_list].
  - apply finite_stream_eof.
  - apply finite_stream_cons, IH.
Qed.

(** ... and conversely every finite stream comes from one, so
    [stream_of_list] is onto the finite streams.  Induction on the
    DERIVATION: the base case names the empty list and the step case
    conses the byte the constructor stripped.  No appeal to
    [stream_decompose] is needed on this side, because [stream_of_list]
    recurses on the list and so reduces at every constructor of it. *)
Lemma finite_stream_of_list : forall s,
  finite_stream s -> exists l, s = stream_of_list l.
Proof.
  intros s Hfin.
  induction Hfin as [| b s Hfin IH].
  - exists []. reflexivity.
  - destruct IH as [l Hl].
    exists (b :: l). cbn [stream_of_list]. rewrite Hl. reflexivity.
Qed.

(** [stream_of_list] is injective: distinct byte lists are distinct
    inputs.  Needed for [to_proc_input_inj] on the STANDARD-INPUT field,
    and with it for the claim that the record is a faithful
    representation of that field rather than a quotient — a weight
    function on [FinProcInput] that gives two [fin_stdin] lists
    different weights is not thereby inconsistent.  The random field has
    no such lemma any more, because it has no such property: see
    [to_proc_input_not_inj]. *)
Lemma stream_of_list_inj : forall l1 l2,
  stream_of_list l1 = stream_of_list l2 -> l1 = l2.
Proof.
  induction l1 as [| b1 l1 IH]; intros [| b2 l2] H; cbn [stream_of_list] in H.
  - reflexivity.
  - discriminate.
  - discriminate.
  - injection H as Hb Hs.
    rewrite Hb, (IH l2 Hs). reflexivity.
Qed.

(** The bytes of [l] are exactly what a process reads from
    [stream_of_list l]: any read whose buffer is big enough hands back
    [l] itself, and what remains is end-of-input.  This is the soundness
    side of the representation — without it, [fin_stdin] would be a list
    the record carries around with no stated relation to the input the
    run consumes.  ([State.stream_take] is the only way bytes leave a
    stream; [Sys.Fs.ReadWrite.read_spec] chooses how many a given read
    delivers but not which.)

    Stated for an arbitrary [k] at or above [length l], not just for
    [length l] itself, because that is the shape a real read has: a
    program calls read with a BUFFER SIZE it picked — 4096, say — and
    does not know how many bytes are left.  The exact-length case is
    [stream_take_of_list_exact] below.  Nothing is being hidden by the
    bound: for [k] BELOW [length l] the result is the honest [k]-byte
    prefix with the rest of the stream still to come, which is a short
    read and is exactly what the model should say. *)
Lemma stream_take_of_list : forall l k,
  (length l <= k)%nat -> stream_take (stream_of_list l) k = (l, IEof).
Proof.
  intros l k. revert l.
  induction k as [| k IH]; intros [| b l] Hle;
    cbn [stream_of_list length stream_take] in *.
  - reflexivity.
  - exfalso. inversion Hle.
  - reflexivity.
  - rewrite IH by (apply le_S_n; exact Hle). reflexivity.
Qed.

(** The exact-length case, which is the one to quote when the reader is
    thinking of the whole input rather than of one read. *)
Lemma stream_take_of_list_exact : forall l,
  stream_take (stream_of_list l) (length l) = (l, IEof).
Proof. intros l. apply stream_take_of_list, Nat.le_refl. Qed.

(* =========================================================================
   An infinite stream, and the refutation
   ========================================================================= *)

(** A concrete infinite input: zero bytes forever, never ending.  This is
    a real Linux input — /dev/zero on standard input — not a pathology
    invented to break a definition, which is what makes the refutation
    below worth having. *)
CoFixpoint all_zeros : InputStream := ICons (Z_to_bv 8 0) all_zeros.

(** One level of [all_zeros], via [stream_decompose]. *)
Lemma all_zeros_unfold : all_zeros = ICons (Z_to_bv 8 0) all_zeros.
Proof. exact (stream_decompose all_zeros). Qed.

(** No finite stream is [all_zeros].  Induction on the finiteness
    derivation, unfolding [all_zeros] one constructor at each case: the
    base case is [State.IEof] against a [State.ICons], and the step case
    peels one byte off both sides and lands on the induction hypothesis.
    The derivation is finite and each step consumes one byte, so it runs
    out; [all_zeros] does not. *)
Lemma finite_stream_neq_all_zeros : forall s, finite_stream s -> s <> all_zeros.
Proof.
  intros s Hfin.
  induction Hfin as [| b s Hfin IH]; intros Heq;
    rewrite all_zeros_unfold in Heq.
  - discriminate.
  - injection Heq as _ Hs. exact (IH Hs).
Qed.

(** [finite_stream] BITES: there is a stream it refutes. *)
Lemma all_zeros_not_finite : ~ finite_stream all_zeros.
Proof.
  intros H. exact (finite_stream_neq_all_zeros _ H eq_refl).
Qed.

(** Both directions in one statement: [finite_stream] is neither empty
    nor universal. *)
Lemma finite_stream_bites :
  finite_stream (stream_of_list [Z_to_bv 8 0]) /\ ~ finite_stream all_zeros.
Proof.
  split; [apply finite_stream_stream_of_list | apply all_zeros_not_finite].
Qed.

(* =========================================================================
   Finite process inputs
   ========================================================================= *)

(** A [State.ProcInput] A FINITE RECORD CAN DENOTE.  The other fields
    the record recurses over are already inductive — two byte-string
    lists and two [Fs.Fs] tables — so the two clauses here are the whole
    of what "finite input" adds.

    THE TWO CLAUSES ARE NOT THE SAME SHAPE.
    Standard input must END: a pipe that closes is a real pipe, a
    classifier task has to be able to express one, and [fin_stdin]
    denotes exactly the bytes it lists.  The RANDOM stream must NOT end,
    because [Run.valid_urandom] asks that it never does, so a record's
    [fin_urandom] denotes its bytes FOLLOWED BY
    [State.default_urandom] ([stream_of_list_then], in [to_proc_input]).
    What "finite" means for that field is therefore not that the stream
    ends but that the record's list determines it — a declared prefix
    and then the default — which is [padded_urandom].

    IF BOTH CLAUSES SAID "ENDS", [Run.valid_input] AND [finite_input]
    WOULD BE CONTRADICTORY and every classifier statement quantified
    over both would be VACUOUSLY TRUE.  That is the failure this file's
    header is written against, and it is why the second clause has a
    different shape.  [valid_and_finite_inhabited] and
    [valid_fin_input_inhabited] below are that sentence as a pair of
    lemmas rather than as a claim: a witness both predicates accept, so
    the quantifier a classifier obligation ranges over is not empty.

    Read through the projections rather than by matching on the
    record, following the convention [State.ProcInput]'s own header sets
    out: a projection reduces whatever the record is, so this predicate
    is transparent for a variable input as well as for a literal one. *)
Definition padded_urandom (s : InputStream) : Prop :=
  exists l, s = stream_of_list_then l State.default_urandom.

Definition finite_input (inp : ProcInput) : Prop :=
  finite_stream (in_stdin inp) /\ padded_urandom (in_urandom inp).

(** A process input with the standard-input stream and the random
    device's stream each replaced by the list of bytes it delivers.
    Field-for-field [State.ProcInput] — SAME NAMES IN THE SAME ORDER,
    including the two ENVIRONMENT fields [State.in_urandom] and
    [State.in_tmp] at the end — with [fin_stdin] and [fin_urandom] the
    two that differ in TYPE: inductive where the original is
    coinductive, which is the reason this record exists (see the header:
    a weight function has to recurse on something).

    [fin_image_fs] is the IMAGE, not the file system the run starts
    with.  It feeds [State.in_image_fs], and the run's initial file
    system is the seeded [State.in_fs] of the result — the image with
    [fin_tmp] laid into it under absolute keys
    ([State.fs_seed_tmp]).  The two are equal exactly when [fin_tmp] is
    empty.  The field is named for its counterpart
    [State.in_image_fs], so that a weight function reading it cannot
    mistake the image for the run's file system.

    [fin_net] is carried ACROSS UNCHANGED, still a [State.NetQueue] and
    still coinductive, and that is deliberate.  What this record has to
    preserve above everything else is that "every finite valid input" and
    "every valid [FinProcInput]" are the SAME quantifier
    ([finite_input_iff_image], [valid_finite_input_surjection]) — a
    classifier obligation quantified over the record would otherwise
    silently ask about fewer inputs than it appears to.  Dropping the
    network, or representing it by a finite prefix, would break
    surjectivity: an input whose environment offers endlessly many
    connections is a perfectly good input, and [Run.valid_input] does not
    exclude it.  So the exactness is kept and the finiteness is not
    claimed for this field.

    The consequence, stated plainly rather than left to be discovered: a
    weight function may read [fin_argv], [fin_envp], [fin_image_fs] and
    [fin_stdin] — the four that make up [fin_core] below — and may read
    NONE of [fin_uid], [fin_gid], [fin_groups], [fin_net], [fin_nofile],
    [fin_sigmask], [fin_hwcap].  All seven are ruled out, not just the
    coinductive one: [Measure.DISTRIBUTION]'s
    [w_core_blind] requires the weight to agree on records with equal
    cores, which is what makes the per-core charge in
    [Measure.weight_bound_T] well defined, and a weight peeking at
    [fin_uid] breaks it exactly as one peeking at [fin_net] does.
    [fin_net] carries a second and independent limitation on top of
    that — being coinductive, it could not be RECURSED over even if the
    measure charged per record, and a weight that wanted to would need a
    finiteness theory for [State.NetQueue] first.  Every weight the
    measure layer's header motivates is over the input bytes (a length,
    a per-byte product, a decreasing weight per read), so none of them
    wants any of the seven.

    The name AND the position of each field mirror its counterpart, so
    that a reader can put the two records side by side and a positional
    literal over one reads across to the other; [to_proc_input] is the
    only conversion, and it goes one way.  It builds through
    [State.mkProcInput_full] rather than the thirteen-place
    [State.mkProcInput], since it supplies both environment fields. *)
Record FinProcInput := mkFinProcInput {
  fin_argv  : list (list byte);
  fin_envp  : list (list byte);
  fin_image_fs    : Fs.Fs;
  fin_stdin : list byte;
  fin_uid   : word;
  fin_gid   : word;
  fin_groups : list word;
  fin_net   : NetQueue;
  fin_nofile : word;
  fin_sigmask : word;
  fin_hwcap : word;
  fin_abort_terminal : bool
    (* the task's abort-path declaration, mirroring
       [State.in_abort_terminal].  IT IS A FIELD RATHER THAN A PIN for
       the reason [fin_sigmask] is: a classifier statement must range
       over exactly the inputs an equivalence statement would, minus the
       infinite ones, and a bool is not one of the infinite ones.
       Pinning it here would put the abort stance out of reach of every
       classifier shape while leaving it in reach of the equivalence
       shapes, which is exactly the silent divergence between the two
       quantifiers this record exists to prevent *);
  fin_va_size : VaSize
    (* the task's address-space declaration, mirroring
       [State.in_va_size], a field rather than a pin for the same reason
       as [fin_abort_terminal]: a three-valued declaration is not one of
       the infinite fields, and pinning it here would put the size out
       of reach of every classifier shape while leaving it in reach of
       the equivalence shapes *);
  fin_urandom : list byte
    (* the random device's declared bytes, mirroring [State.in_urandom]:
       a list where the original is a colist, for the reason
       [fin_stdin] is.  It is NOT part of [fin_core] — see there *);
  fin_tmp   : Fs.Fs
    (* the run's declared private /tmp, mirroring [State.in_tmp].  It
       is already inductive -- a [Fs.Fs] is a list -- so unlike
       [fin_stdin] and [fin_urandom] it adds no clause to
       [finite_input].  It is NOT part of [fin_core] -- see there *)
}.

(** The process input a [FinProcInput] denotes.  Built with
    [State.ProcInput]'s constructor and reading the finite record by its
    projections; every statement about the result goes back through
    [State.ProcInput]'s projections, which reduce. *)
Definition to_proc_input (f : FinProcInput) : ProcInput :=
  mkProcInput_full (fin_argv f) (fin_envp f) (fin_image_fs f)
              (stream_of_list (fin_stdin f))
              (fin_uid f) (fin_gid f) (fin_groups f) (fin_net f)
              (fin_nofile f) (fin_sigmask f) (fin_hwcap f)
              (fin_abort_terminal f) (fin_va_size f)
              (stream_of_list_then (fin_urandom f) State.default_urandom)
              (fin_tmp f).

(** Validity of a finite input is validity of the input it denotes —
    [Run.valid_input] and nothing else.  Deliberately not a new
    predicate: a classifier statement that quantifies over valid
    [FinProcInput]s must range over exactly the inputs an equivalence
    statement would, minus the infinite ones, and the way to guarantee
    that is to reuse the definition rather than restate it.  In
    particular, [valid_fin_input] constrains [fin_argv], [fin_envp],
    [fin_image_fs], the two ids in [fin_uid] / [fin_gid], [fin_nofile] (via
    [Run.valid_nofile]) and [fin_sigmask] (via [Run.valid_sigmask]),
    and says nothing whatever about
    [fin_stdin] ([valid_fin_input_stdin_irrelevant]), [fin_urandom]
    ([valid_fin_input_urandom_irrelevant]), [fin_groups] or
    [fin_net].

    [fin_sigmask] CARRIES A REAL VALUE rather than being pinned to 0,
    and the reason is the rule this record is built on: a classifier
    statement must range over exactly the inputs an equivalence
    statement would, minus the infinite ones.  A blocked mask is one
    64-bit word, so it is not one of the infinite ones — pinning it
    would silently narrow every theorem stated over this record to
    launches that block nothing, which is not a launch [ProcInput] is
    restricted to. *)
Definition valid_fin_input (f : FinProcInput) : Prop := valid_input (to_proc_input f).

(** The abort-path twin, for the reason this file exists: the classifier
    quantifier and the equivalence quantifier must range over the same
    inputs.  [Run.valid_input_abort] is [Run.valid_input] with the task's
    declaration pinned the other way, so this is [valid_fin_input] with
    it pinned the other way, and a classifier obligation stated under it
    speaks about the same runs an equivalence obligation under
    [Run.valid_input_abort] does. *)
Definition valid_fin_input_abort (f : FinProcInput) : Prop :=
  valid_input_abort (to_proc_input f).

(** NO TWIN FOR THE OTHER DECLARATIONS, and the reason is that they do
    not move this file's quantifier.  The address-space predicates
    ([Run.valid_input_sv39], [Run.valid_input_sv57],
    [Run.valid_input_va_any]) and the capability ones
    ([Run.valid_input_hwcap_rv64gc], [Run.valid_input_hwcap_rv64gcv])
    are [Run.valid_input] with one field's clause moved, and every
    statement in the measure and classifier layers that this record
    serves is issued under [Run.valid_input] or [Run.valid_input_abort].
    A twin here would be a definition nothing quantifies over.  The day a
    classifier obligation is stated under one of them, its twin is
    written the way [valid_fin_input_abort] is. *)

(* =========================================================================
   The CORE: the input proper, with the launch environment forgotten
   ========================================================================= *)

(** [FinProcInput]'s four finite fields — argv, envp, the file system
    and standard input — and nothing else.  Exactly the fields a weight
    function may recurse over (see the record above), and exactly the
    fields the measure layer charges for.

    THE SEVEN FIELDS LEFT OUT ARE A HOLE, not a convenience.  A
    classifier whose behavior does not depend on the launch environment
    gives the same verdict to two records differing only in [fin_uid],
    [fin_gid], [fin_groups], [fin_net], [fin_nofile], [fin_sigmask] or
    [fin_hwcap] — and that is a claim about the PROGRAM, which nothing
    here mechanizes.  It also takes more than "issues no credential or
    network syscall": TWO of the seven are published on the initial
    stack, [fin_uid] as AT_UID and AT_EUID and [fin_hwcap] as AT_HWCAP
    ([StackLayout.auxv_entries]), so a program can read the launching
    user, and the hart's extension mask, without a syscall.  The other
    five reach a program only through syscalls — [fin_nofile] through
    exactly one, [Sys.Fs.File.dup3_spec], which compares [newfd]
    against it, and [fin_sigmask] through
    [Kernel.Signal.rt_sigprocmask_spec], which copies the entry mask
    back out through [oset].

    One rejected input is therefore really a FAMILY of rejected records,
    and two of those fields make the family INFINITE:
    [Run.valid_input] constrains neither [in_groups] (a [list word] of
    any length — bounded where [Kernel.Groups.getgroups_spec] reads it,
    not here) nor [in_net] (every [State.NetQueue] is a network some
    environment could present).  [fin_core_fibre_infinite] mechanizes
    that: over any core sits an injective [nat]-indexed family.

    Charging once per FAMILY is what [Measure.weight_bound_T] does.
    Charging once per record would not merely be generous, it would make
    the bound UNPROVABLE wherever the reject set is inhabited at all —
    the infinite family is duplicate-free, so its partial sums pass every
    candidate bound.  [Measure]'s header sets that argument out in full.

    A [Record] rather than a tuple so the projections have names a
    citation can point at, and so equality of cores is decided
    field-by-field by [injection] the way equality of the parent record
    is. *)
Record FinCore := mkFinCore {
  core_argv  : list (list byte);
  core_envp  : list (list byte);
  core_fs    : Fs.Fs;
  core_stdin : list byte
}.

Definition fin_core (f : FinProcInput) : FinCore :=
  mkFinCore (fin_argv f) (fin_envp f) (fin_image_fs f) (fin_stdin f).

(** The core forgets the LAUNCH ENVIRONMENT and nothing else: the core
    together with the seven environment fields determines the record.
    This is what makes "the input proper, quotiented by the launch
    environment" an accurate description of [fin_core] rather than a
    hopeful one, and it is the statement to re-check if a future field
    joins [State.ProcInput] — a new field lands on one side of this line
    or the other, and this lemma stops failing to decide which.

    [fin_sigmask] is the field that arrived and had to be decided.  It
    lands on the ENVIRONMENT side, with the ids and the network, because
    the blocked mask a process starts with is inherited across execve
    (fs/exec.c never names [blocked]; [begin_new_exec]'s
    [flush_signal_handlers] resets dispositions only — Linux v6.18.46,
    commit 1f99e9ab748f) and so is a property of the launch rather than
    of the input the program is asked to process.

    [fin_hwcap] is the second such field, and it lands on the same side
    for the same kind of reason: the AT_HWCAP word is a property of the
    HART the process is launched on, not of the bytes it is asked to
    process.  See [State.ProcInput]'s [in_hwcap] and [Run.valid_hwcap].

    [fin_urandom] is the third, and it lands on the ENVIRONMENT side
    too — a decision worth stating, because the field looks like
    [fin_stdin]'s twin and is not treated as one.  The random device's
    bytes are a fact about the launch (which generator state the kernel
    was in), not the input the program is asked to process, and no
    weight the measure layer's header motivates reads them.  What the
    placement DECIDES is which side of the per-core charge a record
    lands on: with [fin_urandom] outside the core, two records that
    differ only in the device's bytes are one charge in
    [Measure.weight_bound_T], so a classifier whose verdict depends on
    those bytes pays for the whole core once any record over it is
    rejected.  That is conservative — the bound over-approximates the
    rejected mass, never under-approximates it — and it is the reading
    under which nothing in the measure library, which is written over
    [mkFinCore argv envp fs stdin], moves.  Widening the core is a
    separate change, if a weight over the device's bytes is ever wanted.

    [fin_tmp] is the fourth, and lands on the ENVIRONMENT side for the
    same reason and with the same consequence: what the run's private
    /tmp already contains at launch is a fact about the launch, not the
    input the program is asked to process, and the measure library —
    written over [mkFinCore argv envp fs stdin] — is untouched by it.
    Two records that differ only in the declared /tmp are one charge in
    [Measure.weight_bound_T], which over-approximates the rejected mass
    rather than under-approximating it. *)
Lemma fin_core_env_eq : forall f g,
  fin_core f = fin_core g ->
  fin_tmp f = fin_tmp g ->
  fin_urandom f = fin_urandom g ->
  fin_uid f = fin_uid g -> fin_gid f = fin_gid g ->
  fin_groups f = fin_groups g -> fin_net f = fin_net g ->
  fin_nofile f = fin_nofile g ->
  fin_sigmask f = fin_sigmask g ->
  fin_hwcap f = fin_hwcap g ->
  fin_abort_terminal f = fin_abort_terminal g ->
  fin_va_size f = fin_va_size g ->
  f = g.
Proof.
  intros [a1 e1 fs1 s1 u1 g1 gs1 n1 nf1 sm1 hc1 ab1 va1 r1 tm1]
         [a2 e2 fs2 s2 u2 g2 gs2 n2 nf2 sm2 hc2 ab2 va2 r2 tm2]
    Hcore Htm Hr Hu Hg Hgs Hn Hnf Hsm Hhc Hab Hva.
  unfold fin_core in Hcore.
  cbn [fin_argv fin_envp fin_image_fs fin_tmp fin_stdin fin_urandom fin_uid fin_gid fin_groups fin_net
       fin_nofile fin_sigmask fin_hwcap fin_abort_terminal fin_va_size]
    in Hcore, Htm, Hr, Hu, Hg, Hgs, Hn, Hnf, Hsm, Hhc, Hab, Hva.
  injection Hcore as Ha He Hfs Hs.
  subst. reflexivity.
Qed.

(** The fibre over any core is INFINITE: an injective family indexed by
    [nat], every member sharing the given record's core.  This is the
    unprovability argument of [Measure]'s header, mechanized — combined
    with a classifier whose verdict ignores the launch environment, it
    turns one rejected input into arbitrarily long duplicate-free lists
    of rejected records.

    The VALIDITY conjunct is what makes the family usable against
    [Classifier.rejects], which is [valid_fin_input] conjoined with
    non-acceptance: a family of distinct records would say nothing if
    its members were not inputs the obligation quantifies over.  It
    holds by conversion — [Run.valid_input] reads argv, envp, the file
    system, the two ids and the descriptor limit, none of which this
    family varies — so the
    proof is [exact H], and that is the sharpest form: a step would mean
    [Run.valid_input] had grown a clause about the supplementary groups.

    Witnessed by varying [fin_groups] alone, which needs no reasoning
    about [State.NetQueue]: the supplementary group list is an ordinary
    [list word] that [Run.valid_input] does not constrain, so
    lengthening it walks the fibre and the lengths tell the members
    apart.  [fin_net] opens the same hole a second time and is quotiented
    away for the same reason; it is not needed here, since one infinite
    fibre is all the argument requires.

    What remains in prose, and cannot be mechanized here, is the other
    half: that a classifier's verdict is constant along the fibre.  That
    is a claim about a program, argued at the record above. *)
Lemma fin_core_fibre_infinite : forall f,
  exists h : nat -> FinProcInput,
    (forall n, fin_core (h n) = fin_core f)
    /\ (forall m n, h m = h n -> m = n)
    /\ (valid_fin_input f -> forall n, valid_fin_input (h n)).
Proof.
  intros f.
  exists (fun n => mkFinProcInput (fin_argv f) (fin_envp f) (fin_image_fs f)
                     (fin_stdin f) (fin_uid f) (fin_gid f)
                     (repeat (Z_to_bv 64 0) n) (fin_net f) (fin_nofile f) (fin_sigmask f)
                     (fin_hwcap f)
                     (fin_abort_terminal f) (fin_va_size f)
                     (fin_urandom f) (fin_tmp f)).
  split; [| split].
  - intros n. reflexivity.
  - intros m n Heq.
    apply (f_equal fin_groups) in Heq. cbn [fin_groups] in Heq.
    apply (f_equal (@length word)) in Heq.
    rewrite !repeat_length in Heq. exact Heq.
  - intros H n. exact H.
Qed.

(* =========================================================================
   The embedding
   ========================================================================= *)

(** Everything in the image is finite. *)
Lemma finite_input_to_proc_input : forall f, finite_input (to_proc_input f).
Proof.
  intros f. unfold finite_input, to_proc_input. cbn [in_stdin in_urandom].
  split; [apply finite_stream_stream_of_list|].
  exists (fin_urandom f). reflexivity.
Qed.

(** [to_proc_input] is injective ON EVERY FIELD BUT THE RANDOM ONE,
    which is what the extra hypothesis says.  Every field but two
    transfers verbatim; [fin_stdin] is [stream_of_list_inj].  So a
    statement quantified over [FinProcInput] does not accidentally
    quantify over the same input twice under different names, and the
    record really is a faithful index for the inputs it denotes — which
    is what makes [fin_core_env_eq] and the surjection say what they
    appear to.

    THE RANDOM FIELD IS NOT A FAITHFUL INDEX, and the hypothesis
    is where that is admitted rather than hidden.  [fin_urandom] denotes
    its bytes FOLLOWED BY [State.default_urandom], and padding cannot be
    injective: a list that is a prefix of the padding denotes the same
    stream as the shorter list that stops before it.
    [to_proc_input_not_inj] below is that collision on the smallest
    pair, so the loss is pinned rather than described.

    WHAT WOULD RESTORE IT is an APERIODIC padding: the collision is
    exactly "the padding has a period", so a [State.default_urandom]
    with no period would make every list recoverable.  That is a real
    little proof (a stream whose gaps grow without bound has no period)
    and it belongs with the measure layer, because that is
    where the cost lands — see the note below on [Measure.weight_bound_T].

    It is NOT what decides duplication for the measure layer: that bound
    is over lists no two of whose entries share a [fin_core]
    ([Measure.weight_bound_T]), so duplication there is judged on the
    core and two records this lemma calls distinct may still be one
    charge. *)
Lemma to_proc_input_inj : forall f g,
  to_proc_input f = to_proc_input g ->
  fin_urandom f = fin_urandom g ->
  f = g.
Proof.
  intros [a1 e1 fs1 s1 u1 g1 gs1 n1 nf1 sm1 hc1 ab1 va1 r1 tm1]
         [a2 e2 fs2 s2 u2 g2 gs2 n2 nf2 sm2 hc2 ab2 va2 r2 tm2] H Hr.
  cbn [fin_urandom] in Hr.
  unfold to_proc_input in H.
  cbn [fin_argv fin_envp fin_image_fs fin_tmp fin_stdin fin_urandom fin_uid fin_gid fin_groups fin_net
       fin_nofile fin_sigmask]
    in H.
  (* the constructor's order, with the two ENVIRONMENT fields last:
     argv, envp, image, stdin, the ids, the queue, the limits, the
     declarations, then [in_urandom] and [in_tmp] *)
  injection H as Ha He Hfs Hs Hu Hg Hgs Hn Hnf Hsm Hhc Hab Hva _ Htm.
  apply stream_of_list_inj in Hs.
  subst. reflexivity.
Qed.

(** THE COLLISION, on the smallest pair: the empty declaration and the
    one-byte declaration whose byte is the padding's first byte denote
    the SAME input.  Stated so that a reader who quotes the lemma above
    meets its hypothesis's reason rather than taking it on trust. *)
Lemma to_proc_input_not_inj :
  exists f g, f <> g /\ to_proc_input f = to_proc_input g.
Proof.
  pose (base := mkFinProcInput [] [] []
                  [] (Z_to_bv 64 0) (Z_to_bv 64 0) [] net_silent
                  (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) false Sv48 [] []).
  exists base.
  exists (mkFinProcInput [] [] []
            [] (Z_to_bv 64 0) (Z_to_bv 64 0) [] net_silent
            (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) false Sv48
            [Z_to_bv 8 0] []).
  split.
  - intro Hc. apply (f_equal fin_urandom) in Hc.
    unfold base in Hc. cbn [fin_urandom] in Hc. discriminate Hc.
  - unfold to_proc_input, base.
    cbn [fin_argv fin_envp fin_image_fs fin_stdin fin_urandom fin_uid
         fin_gid fin_groups fin_net fin_nofile fin_sigmask fin_hwcap
         fin_abort_terminal fin_va_size fin_tmp stream_of_list_then].
    unfold State.default_urandom. now rewrite <- State.stream_const_unfold.
Qed.

(** ... and everything finite is IN the image.  Together with
    [finite_input_to_proc_input] this is what makes the record a
    representation of the finite inputs rather than a restriction to some
    of them. *)
Lemma finite_input_surjection : forall inp,
  finite_input inp -> exists f, inp = to_proc_input f.
Proof.
  (* [State.ProcInput]'s constructor order, the two ENVIRONMENT fields
     last: argv, envp, image, stdin, ids, queue, limits, declarations,
     then [in_urandom] and [in_tmp] *)
  intros [a e fs s u g gs n nf sm hc ab va r tm] Hfin.
  unfold finite_input in Hfin. cbn [in_stdin in_urandom] in Hfin.
  destruct Hfin as [Hfin [lr Hlr]].
  destruct (finite_stream_of_list _ Hfin) as [l Hl].
  exists (mkFinProcInput a e fs l u g gs n nf sm hc ab va lr tm).
  unfold to_proc_input.
  cbn [fin_argv fin_envp fin_image_fs fin_tmp fin_stdin fin_urandom fin_uid fin_gid fin_groups fin_net
       fin_nofile fin_sigmask fin_hwcap fin_abort_terminal fin_va_size].
  rewrite Hl, Hlr. reflexivity.
Qed.

(** The two readings of "finite input", stated as one equivalence.  This
    is the lemma to quote when checking a classifier statement against
    the informal claim it is supposed to make: quantifying over
    [FinProcInput] and quantifying over [State.ProcInput]s satisfying
    [finite_input] pick out the same inputs. *)
Lemma finite_input_iff_image : forall inp,
  finite_input inp <-> exists f, inp = to_proc_input f.
Proof.
  intros inp. split.
  - apply finite_input_surjection.
  - intros [f Hf]. rewrite Hf. apply finite_input_to_proc_input.
Qed.

(** The surjection with VALIDITY carried across, which is the form a
    classifier statement actually needs.  Those statements quantify over
    valid [FinProcInput]s, so the claim to check them against is "for
    every valid finite [State.ProcInput]" — and reading one off the other
    means transporting [Run.valid_input] through the equation
    [finite_input_surjection] produces.  That transport is one rewrite,
    but it is one rewrite at every site that wants it, and each of those
    sites is a place a reader has to re-convince themselves the two
    quantifiers agree.  Doing it once, here, is what makes this file's
    promise — that a reader auditing a classifier statement need not
    reason about the record — true at the point of use rather than in
    principle. *)
Lemma valid_finite_input_surjection : forall inp,
  valid_input inp -> finite_input inp ->
  exists f, valid_fin_input f /\ inp = to_proc_input f.
Proof.
  intros inp Hvalid Hfin.
  destruct (finite_input_surjection inp Hfin) as [f Hf].
  exists f. split; [| exact Hf].
  unfold valid_fin_input. rewrite <- Hf. exact Hvalid.
Qed.

(* =========================================================================
   Finiteness is not validity
   ========================================================================= *)

(** [Run.valid_input] does not look at standard input: replacing the
    stream with an arbitrary one preserves validity.  Both sides reduce
    to the same conjuncts — the two credential clauses, the
    descriptor-limit clause, the signal-mask clause and the AT_HWCAP
    clause included, since [Run.valid_creds] reads [in_uid] and
    [in_gid], [Run.valid_nofile] reads [in_nofile], [Run.valid_sigmask]
    reads [in_sigmask] and [Run.valid_hwcap] reads [in_hwcap], all
    carried across unchanged — so this holds by conversion, which is the sharpest
    way to say it, since a proof that needed a step would mean a clause
    had appeared.  Read it as a regression test on [Run.valid_input]'s
    shape as much as a lemma. *)
Lemma valid_input_stdin_irrelevant : forall inp s,
  valid_input inp ->
  valid_input (mkProcInput_full (in_argv inp) (in_envp inp) (in_image_fs inp) s
                 (in_uid inp) (in_gid inp) (in_groups inp) (in_net inp)
                 (in_nofile inp) (in_sigmask inp) (in_hwcap inp) (in_abort_terminal inp) (in_va_size inp)
                 (in_urandom inp) (in_tmp inp)).
Proof. intros inp s H. exact H. Qed.

(** THE RANDOM DEVICE'S STREAM IS NOT LIKE STANDARD INPUT.
    [Run.valid_urandom] asks that the declared
    stream never end, because [Sys.Fs.ReadWrite.read_urandom] declines
    when it runs out and that decline is reachable from a whole-program
    theorem.  So the honest statement is not "any stream" but "any
    ENDLESS stream", and it takes a step: the swap preserves the
    other conjuncts by conversion and carries the last one from the
    hypothesis.  Read the step itself as the regression test — if the
    [conj] chain below stops matching, another clause has appeared. *)
Lemma valid_input_urandom_endless_irrelevant : forall inp r,
  valid_input inp ->
  State.stream_infinite r ->
  valid_input (mkProcInput_full (in_argv inp) (in_envp inp) (in_image_fs inp)
                 (in_stdin inp)
                 (in_uid inp) (in_gid inp) (in_groups inp) (in_net inp)
                 (in_nofile inp) (in_sigmask inp) (in_hwcap inp) (in_abort_terminal inp) (in_va_size inp)
                 r (in_tmp inp)).
Proof.
  intros inp r H Hr.
  (* [valid_input] has twelve conjuncts: keep the first eleven and
     replace the last ([valid_urandom]) with [Hr]. *)
  destruct H as (a & b & c & d & e & f & g & h & i & j & k & _).
  exact (conj a (conj b (conj c (conj d (conj e (conj f (conj g (conj h (conj i (conj j (conj k Hr))))))))))).
Qed.

(** The same for [valid_fin_input]: the byte list in [fin_stdin] is
    unconstrained.  A classifier task therefore cannot smuggle a
    restriction on the inputs it is asked about into the validity
    premise; the only restriction is finiteness, and it is visible in the
    quantifier. *)
Lemma valid_fin_input_stdin_irrelevant : forall f l,
  valid_fin_input f ->
  valid_fin_input (mkFinProcInput (fin_argv f) (fin_envp f) (fin_image_fs f)
                     l
                     (fin_uid f) (fin_gid f) (fin_groups f) (fin_net f)
                     (fin_nofile f) (fin_sigmask f) (fin_hwcap f) (fin_abort_terminal f) (fin_va_size f)
                     (fin_urandom f) (fin_tmp f)).
Proof. intros f l H. exact H. Qed.

(** And the byte list in [fin_urandom] is unconstrained too — even
    under [Run.valid_urandom], and that is what the padding in
    [to_proc_input] buys.  The clause is on the DENOTED stream, every
    list denotes an endless one, so no list is excluded and a classifier
    task can still write whatever prefix it means.  It takes a step
    rather than holding by conversion, because the last conjunct is
    about a different stream on each side. *)
(** The declared /tmp is not constrained EITHER, which takes one more
    word to say than stdin's and the device's do, because
    [Run.valid_input]'s [Fs.valid_fs] clause reads the SEEDED image
    ([State.in_fs]) and the seeding reads [in_tmp].  What is true is
    this: given an image in the
    canonical form, EVERY declared /tmp yields a valid input.  No table
    a launch could present is excluded, which is
    [State.fs_seed_tmp_valid]. *)
Lemma valid_input_tmp_arbitrary : forall inp t,
  Fs.valid_fs (in_image_fs inp) ->
  valid_input inp ->
  valid_input (mkProcInput_full (in_argv inp) (in_envp inp) (in_image_fs inp)
                 (in_stdin inp)
                 (in_uid inp) (in_gid inp) (in_groups inp) (in_net inp)
                 (in_nofile inp) (in_sigmask inp) (in_hwcap inp)
                 (in_abort_terminal inp) (in_va_size inp) (in_urandom inp) t).
Proof.
  intros inp t Him H. unfold valid_input in H |- *.
  destruct H as (Ha & He & _ & Hrest).
  refine (conj Ha (conj He (conj _ Hrest))).
  unfold in_fs. cbn [in_image_fs in_tmp].
  apply fs_seed_tmp_valid. exact Him.
Qed.

Lemma valid_fin_input_urandom_irrelevant : forall f l,
  valid_fin_input f ->
  valid_fin_input (mkFinProcInput (fin_argv f) (fin_envp f) (fin_image_fs f)
                     (fin_stdin f)
                     (fin_uid f) (fin_gid f) (fin_groups f) (fin_net f)
                     (fin_nofile f) (fin_sigmask f) (fin_hwcap f) (fin_abort_terminal f) (fin_va_size f)
                     l (fin_tmp f)).
Proof.
  intros f l H.
  (* Twelve conjuncts: keep the first eleven and prove the last
     ([valid_urandom]) from the padding. *)
  destruct H as (a & b & c & d & e & g & h & i & j & k & n & _).
  exact (conj a (conj b (conj c (conj d (conj e (conj g (conj h (conj i (conj j (conj k (conj n
    (stream_of_list_then_infinite l State.default_urandom
       State.default_urandom_infinite)))))))))))).
Qed.

(* -------------------------------------------------------------------------
   Neither quantifier is empty
   ------------------------------------------------------------------------- *)

(** THE WITNESS THE TWO PINS BELOW EXHIBIT: one empty argument, no
    environment, an empty image and an empty /tmp, the launching ids at
    zero, the quiet network, the default descriptor limit, an empty
    blocked mask, the V-less capability word, the abort declaration off,
    Sv48, and an empty random declaration — which denotes
    [State.default_urandom], the endless stream, because
    [to_proc_input] pads.

    It is written here rather than borrowed from
    theories/LinuxProcessSem/Checks/Cases/Prelude.v because that file is
    DOWNSTREAM of this one: a claim about this file's quantifiers cannot
    rest on a fixture this file cannot see. *)
Definition inhabited_fin_input : FinProcInput :=
  mkFinProcInput [[]] [] [] [] (Z_to_bv 64 0) (Z_to_bv 64 0) [] net_silent
                 default_nofile (Z_to_bv 64 0) StackLayout.hwcap_rv64gc
                 false Sv48 [] [].

(** THE FINITE-RECORD QUANTIFIER IS NOT EMPTY, which is the one the
    classifier and gated-size shapes are written over. *)
Lemma valid_fin_input_inhabited : exists f, valid_fin_input f.
Proof.
  exists inhabited_fin_input.
  unfold valid_fin_input, to_proc_input, inhabited_fin_input,
         valid_input, valid_argv, valid_envp.
  cbn [fin_argv fin_envp fin_image_fs fin_stdin fin_uid fin_gid fin_groups
       fin_net fin_nofile fin_sigmask fin_hwcap fin_abort_terminal
       fin_va_size fin_urandom fin_tmp
       in_argv in_envp in_fs in_nofile in_sigmask in_hwcap
       in_abort_terminal in_va_size in_urandom].
  repeat split; cbn;
    try (unfold valid_nofile; apply Z.leb_le; vm_compute; reflexivity);
    try (unfold valid_sigmask; apply bv_eq; vm_compute; reflexivity);
    try (unfold valid_hwcap; left; reflexivity);
    try lia; try reflexivity;
    repeat first [ apply Forall_nil | apply Forall_cons | split
                 | cbn; lia | reflexivity | intros [] ].
  all: try (unfold valid_urandom; cbn [in_urandom];
            exact State.default_urandom_infinite).
Qed.

(** ...and so THE TWO CLAUSES ARE SATISFIABLE TOGETHER, which is what
    this file's header and [finite_input]'s own note claim.  Read it as
    the regression test on the padding: if [finite_input]'s random
    clause ever went back to saying "it ends", [Run.valid_urandom] would
    contradict it, this statement would be FALSE, and every classifier
    obligation quantified over both would have gone vacuously true
    instead of failing anywhere. *)
Lemma valid_and_finite_inhabited : exists inp, valid_input inp /\ finite_input inp.
Proof.
  destruct valid_fin_input_inhabited as (f & Hf).
  exists (to_proc_input f).
  split; [exact Hf | apply finite_input_to_proc_input].
Qed.

(** Validity does not imply finiteness, and the gap is not marginal: from
    ANY valid input, swapping in [all_zeros] gives another valid input
    that [finite_input] refutes.  So the finite restriction really does
    discard inputs the equivalence shapes cover, which is the price of
    the classifier shapes and is stated here rather than left implicit.

    Stated from a hypothesis rather than on a concrete input, because
    exhibiting a valid input from nothing means building an argv, an
    envp and a file system that satisfy [Run.valid_argv],
    [Run.valid_envp] and [Fs.valid_fs] — example-side work, in the spirit
    of the fixtures in theories/LinuxProcessSem/Checks/Cases/Prelude.v,
    and not needed to make this point. *)
Lemma valid_input_not_finite : forall inp,
  valid_input inp ->
  valid_input (mkProcInput_full (in_argv inp) (in_envp inp) (in_image_fs inp)
                 all_zeros
                 (in_uid inp) (in_gid inp) (in_groups inp) (in_net inp)
                 (in_nofile inp) (in_sigmask inp) (in_hwcap inp) (in_abort_terminal inp) (in_va_size inp)
                 (in_urandom inp) (in_tmp inp))
  /\ ~ finite_input (mkProcInput_full (in_argv inp) (in_envp inp) (in_image_fs inp)
                      all_zeros
                      (in_uid inp) (in_gid inp) (in_groups inp) (in_net inp)
                      (in_nofile inp) (in_sigmask inp) (in_hwcap inp) (in_abort_terminal inp) (in_va_size inp)
                      (in_urandom inp) (in_tmp inp)).
Proof.
  intros inp H. split.
  - apply valid_input_stdin_irrelevant, H.
  - unfold finite_input. cbn [in_stdin in_urandom]. intros [Hz _].
    exact (all_zeros_not_finite Hz).
Qed.
