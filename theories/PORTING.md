# Porting from plain `N` to stdpp-bitvector + the effect-tree ISA model

This development was ported (July 2026) from

- **mit-plv/riscv-coq** (`coq-riscv` opam package) to the effect-tree
  RV64GC semantics now maintained in this repository (`theories/Riscv/`,
  namespace `LinuxProcessSemantics.Riscv`), and
- **plain `N`** for bytes/machine words to **`rocq-stdpp-bitvector`**
  (`byte = bv 8`, `word = bv 64`, `reg = bv 5`).

The port was developed as a parallel tree (`theories/Bv/`) mirroring the original layout file-for-file, then
collapsed over the old tree — every file kept its relative path, so the
pre-/post-port history of each module lines up in git.  The only
import-level change beyond the namespace collapse:

```
From riscv.Spec Require Import Decode ...  →  From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
```

## Dependencies

- `opam install rocq-stdpp-bitvector` (tested with 1.13.0).
- `coq-riscv` / `coq-coqutil` are no longer needed.

## The two global conversion rules

1. **Quantities become bitvectors.**  Register values, addresses, syscall
   args/returns, fds, channel ids, sizes, offsets, exit codes, brk values,
   vm intervals: `word = bv 64`.  Memory/file/event/argv bytes:
   `byte = bv 8`.  Register indices: `reg = bv 5`.
2. **Unbounded arithmetic goes to `Z` over `bv_unsigned`.**  Everywhere the
   old model relied on `N` arithmetic *not wrapping* — page rounding,
   interval overlap/disjointness, allocation-ceiling bounds, segment range
   checks, length bounds — compute in `Z` on `bv_unsigned x` and compare
   with `Z.ltb/Z.leb/Z.eqb`.  Only values that land back in registers or
   memory are re-wrapped with `Z_to_bv`.  (Naively replacing `N.+` with
   `bv` `+` would silently change semantics at the 2^64 boundary — e.g.
   `page_round_up` of a length near 2^64 must *fail* the ceiling check,
   not wrap to a small number.)

Address *iteration* (`addr + 1` walking a buffer) does use wrapping `bv`
addition — a buffer straddling the top of the address space is not
something a real process can produce, and the old code's behavior there
was equally unreachable.

## Mechanical translation table

| old (`N`) | new (bv) |
|---|---|
| `N`, `Local Open Scope N_scope` | `word`/`byte`/`Z` as appropriate, `Open Scope bv_scope` |
| numeric literal `42` (word value) | `Z_to_bv 64 42` (or bare `42` where the type is inferred and `bv_scope` is open; prefer `Z_to_bv` in definitions, literals are fine inside proofs/examples) |
| `a =? b` (words) | `bv_eqb a b` |
| `a <? b` (unsigned) | `bv_ltu a b`, or `Z.ltb (bv_unsigned a) (bv_unsigned b)` when the sum/bound side can exceed 2^64 |
| `a <=? b` | `bv_leu a b` / `Z.leb (bv_unsigned a) (bv_unsigned b)` |
| `a + b` (no-wrap bookkeeping) | `(bv_unsigned a + bv_unsigned b)%Z` inside checks; `a + b` (bv add) for stored values known in range |
| `two_pow_64 - e` (negatives in two's complement) | `Z_to_bv 64 (-e)` (`State.errno_ret`) |
| `N.land v 0xFF`, shift-based byte splits | `bv_extract 0 8 v`, `bv_extract 8 8 v`, … (`BvBase.word_le8`, `word_to_le_bytes`) |
| little-endian byte assembly (`b0 + 256*b1 + …`) | `BvBase.le2/le4/le8` (`bv_concat`; first arg = high bits), `le_bytes_to_word` |
| `N.of_nat (length l)` (as a word) | `BvBase.len_word l` |
| `N.to_nat n` (fuel/index from a word) | `BvBase.word_to_nat` |
| `Forall (fun b => b < 256) bs` | delete — enforced by `bv 8` |
| register index `17 : N` | `17 : reg` (bv 5 numeral; fine under `bv_scope`) |
| `nth k args 0` | `nth k args (Z_to_bv 64 0)` |

Notation gotchas (stdpp is now imported everywhere via the Riscv
prelude):

- The `Sys` monad notations in `Monad.v` had to move: `x <- c ;; k` and
  `c ;; k` now sit at level 100 (matching stdpp's `;;`), with `k` at
  level 200.  Existing spec code parses unchanged.
- `From Stdlib Require Import String` shadows `List.length` — qualify as
  `List.length` after importing `String` (RiscvSemantics.v).
- stdpp's `mret`/`mbind`/`≫=` and `λ` notations are available; `Sem.v`
  uses them.

## Architecture changes in `RiscvSemantics.v`

The ISA wrapper was rewritten (not line-ported) against the new model.

**Effect-tree semantics.**  `Sem.v` is a kraken-style first-order effect tree
(github.com/AeneasVerif/kraken): core state (registers as a `bvmap`,
FP registers, pc, fcsr, LR/SC reservation) is threaded concretely
through `exec : word → instr → core → eff`, and only memory accesses
and the environment boundary are tree nodes (`EDone`/`EIllegal`/
`EEcall`/`EEbreak`/`EFpu`/`ELoad`/`EStore`; load/store widths in bits
with `bv n` payloads).  `RiscvSemantics.v` interprets the tree with a
short structural `Fixpoint` (`interp_eff` + `ov_read_bytes`:
overlay-then-segments loads that fail on unmapped, stores checked by
`range_avoids_ro_segs`); the boundary nodes all map to illegal (ecall
is intercepted pre-decode and never reaches its node).  Consequences
for this model, absorbed entirely inside `RiscvSemantics.v` (see its
comments):

- the core's FP regs and fcsr live in `machine_state`
  (`ms_fregs`/`ms_fcsr`) and are threaded through `decode_exec`
  unchanged, so F/D/Zicsr execute like any other instructions;
- `machine_state.ms_regs` is a `bvmap 5 word` — the same
  representation as the core's `c_regs` — so `step` threads the
  register file with no conversion; `getr`/`regupd` are x0-guarded
  `reg_get`/`bvmap_set`, and downstream register hypotheses are
  `reg_get regs r = v` equalities (no functional extensionality
  involved).
- **Fetch is still ROM-only, 4 bytes, with pre-decode ECALL
  interception** (`fetch_word` / `is_ecall`), exactly like the old
  model; we do *not* use `Sem.step` (which fetches through `load_word`,
  i.e. through the writable overlay).
- **Compressed instructions now decode and execute** (`DecodeC.decode_any`
  returns the instruction plus its size 2 or 4; the pc advance uses that
  size).  The old model was RV64IMAF-only.
- **`machine_state` gained `ms_resv : option word`** (LR/SC reservation,
  placed between `ms_svc_pending` and `ms_mem`).  The old model's
  `checkReservation` was constantly `true` (SC always succeeded);
  the new model tracks reservations properly.  Ported code constructing
  `machine_state` records must add the field; syscalls preserve it,
  `Run.init_machine_state` starts it at `None`.
- `MemImageType.v` (and every generated `SourceMemImage.v` /
  `TargetMemImage.v` / `.hex`) is **unchanged**: `Segment` stays
  `N`-based snapshot data, and the semantics converts at the boundary
  (`find_segment` compares in `Z`; `hex_byte_at` returns `bv 8`).
  `Run` takes `mi_init_pc : N` straight from the `MemImage` module.

## Trusted-surface diffs to review (deliberate)

- Compressed instructions are in scope (RV64GC minus FP arithmetic).
- LR/SC reservations are modeled; SC can now fail.
- FP data movement (`FLoad`/`FStore`/`Fmv`/`Fsgnj`) is *illegal* in the
  ported model (no FP register file), whereas the old model executed
  F-extension data moves it could never observe (no FP state was
  reachable anyway since every CSR access failed).  `-ns` binaries use
  no FP.
- `valid_argv`/`valid_envp`/`valid_fs` lost their `b < 256` clauses
  (typed away); `brk`'s query choice lost `r < 2^64` (same reason).
- Events carry `byte` payloads and `word` channel ids/exit codes.
- Errnos and open-flag masks are `Z` constants (`EBADF : Z`), bridged
  by `errno_ret : Z → word`; flag arithmetic (`Z.ldiff`) happens on
  `bv_unsigned flags`.

## Porting the remaining files (Checks, Common, Examples)

Status/process for each layer is tracked below as the port progresses.

### Checks

`ExecutableSpecs.v`, `Examples.v`, `Extraction.v` are ported.  Notes:

- Checker conditions mirror the ported Specs.v shapes exactly: word
  equality via `bv_eqb`, length/bound checks as `Z.leb`/`Z.ltb` over
  `bv_unsigned`, zero-against-word tests via `Specs.w_is0`, errnos as
  `Z` through `errno_ret`.  The `bytes_ok` conditions (and
  `bytes_ok_Forall`) are gone — typed away by `bv 8`.  The old
  `r <? two_pow_64` conditions (brk query, set_tid_address) are gone —
  typed away by `word`.  `check_set_tid_address` does carry an explicit
  numeric bound again, but a narrower and unrelated one: the model's
  `PID_MAX_ENVELOPE`, which constrains the tid the environment may
  choose rather than restating the word width.
- `listN_eqb` keeps its name but is byte-list (`bv 8`) equality;
  `listNN_eqb` is equality on `list (word * word)`.
- New arithmetic helpers: `errno_ret_unsigned`, `word_unsigned_range`,
  `page_round_up_Z_nonneg` (the last replaces the free `0 <= n` fact of
  `N` in the mmap ceiling/error-range disjointness argument).
- `Examples.v`: concrete-checker examples cannot always close with
  `vm_compute; reflexivity` — `Z_to_bv`'s `BvWf` obligation is opaque,
  so a computed `bv` and a numeral-notation literal have different
  (proof-irrelevant) proof fields.  `check_eq` descends with `f_equal`
  and compares `bv` leaves via `bv_eq`.
- `Extraction.v`: roots renamed `page_round_up`/`page_round_down` →
  `page_round_up_Z`/`page_round_down_Z`.  `bv` extracts to a plain
  `Big_int_Z.big_int` (singleton record, proof erased).

### Common

ALL of Common is ported: `ExitSim`, `PropExec`, `CatSim`, `CatExec`,
`SeqExec`, `StreamExec`, `StreamSim`, `DrainSim`, `MmapSim`, `AllocSim`,
`AllocSim2`, `FileSim`, `ErrEscape`, `ErrEscape2`, `NumPrint`, and the
full `StepTac` (all nine chain-relation arms, plus a consolidation layer
of shared example helpers/tactics — see below).  Every public
definition/lemma name is preserved, with two audited exceptions:
`MmapSim.sb_chain1_any` is dropped (`Sb` bytes are `word_to_le_bytes 1 v`
by conversion, same rationale as SeqExec's dropped chain lemmas), and a
DrainSim lia-certificate cleanup removed spurious `ec`/`Hec` arguments
from internal `_1k`/`dinv` lemmas (no caller used them).

The statement-shape changes downstream code must know fall in two layers.
The PropExec layer: decode hypotheses via `decode_any` with encoded-width
immediates, dropped `align4`, the `Z_to_bv 64 (…)` canonical value form,
Z-characterized syscall-number tests, no-overflow hypotheses on
stack-read lemmas, store lemmas concluding `word_to_le_bytes` with no
x0 case splits, `ov_rdn` load bridges. Everything above PropExec:
per-module statement shapes — quantified `x8` syscall witnesses,
2-conjunct `block_ok`, `(word * Fs.Fs)` outcomes, Z errnos — plus the
StepTac consolidation and the proof-engineering gotchas, including every
known cause of divergent multi-GB compiles: `vm_compute`/`bveq`/`wlits`
reaching an OPEN bv term, an evar-carrying goal, or a memory-image term.

### Examples — how they were ported

Step 1 (fully scripted at the time; the one-shot porting scripts were
deleted after the integration): generated files.  Memory images
(`SourceMemImage.v` / `TargetMemImage.v` + `.hex`) were copied with only
the namespace lines rewritten (segment data untouched — `MemImageType`
stays `N`-based).  In `<problem>_code.v`, the `SF_*` fetch lemmas kept
their exact text (numerals elaborate at `word`/`bv 32` under
`bv_scope`); each `SD_*` decode lemma
`decode RV64IMAF (Z.of_N w) = <riscv-coq AST>` was rewritten to
`decode_any (Z_to_bv 32 w) = Some (<Instr AST>, <2 or 4>%Z)`,
where the right-hand side was computed by the new decoder itself
(a batch `Compute` run) — the tooling never re-implemented decoding,
and every lemma stays VM-checked.  For a *new* example,
`gen-fd-lemmas` now generates this format directly from the
memory images, and dune runs it on every build — `<problem>_code.v` is no
longer a checked-in file at all.

Two systematic changes this baked in:

- **immediates are encoded-width bitvectors** in the `Instr` AST
  (`Addi 2 2 (-64)` becomes `OpImm ALU_ADD 2 2 4032` — 4032 is the
  unsigned 12-bit encoding of −64; `Lui 21 65536` becomes `Lui 21 16` —
  the raw 20-bit field);
- **`vm_refl` goes through `bool_decide`**: `bv` values carry a
  well-formedness proof whose vm-computed form differs from the
  elaborated literal's, so a raw `vm_cast_no_check (eq_refl rhs)` no
  longer typechecks.  The generated
  `apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (eq_refl true)`
  pattern keeps the lemma statement an equation while the VM-checked
  object is a proof-irrelevant boolean.  Use the same pattern for any
  new VM-checked equation whose sides contain `bv` values.

Step 2: `Proof.v` and `Checker.v` — the import rewrite is the same as
everywhere (`From riscv.Spec ...` → `From LinuxProcessSemantics.Riscv ...`),
and the
statement-shape vocabulary is the two-layer catalogue above.

**Status: ALL examples are ported and their Checkers audited**
(grep_args_ns, cat1024_ns, conditional_bug_ns, brk_rev_ns,
mmap_upper_ns, tail1_ns, headcp_ns, alloc_join_ns, cp_ns,
oob_read_bug_ns, modprint_ns).  Every `Checked.strong_universal` closure is a subset
of {`functional_extensionality_dep`, PrimInt63/PrimString primitives};
most examples don't even pull in funext.  The grep_args_ns port
settled these example-level conventions:

- Section variables: `av ev : list (list byte)`; `rsp : word` with the
  window bounds as Z hypotheses over `bv_unsigned rsp`.  Every
  `x < 2^64` lemma (`rsp_lt64`-style) is *deleted* — typed away.
- sp-relative register invariants are stated in the canonical form
  `regs r = Z_to_bv 64 (bv_unsigned rsp ± k)`; indices/lengths via
  `nat_to_word`; `word_to_nat` replaces `N.to_nat` on counts.
- `align4`/`align4_jalr` hypotheses are gone repo-wide (the ISA model
  has no alignment fault).
- `range_avoids_ro_segs` takes Z args; the per-image `*_avoids_ro`
  lemmas restate their address bound as `0x... <= bv_unsigned a`.
- StepTac's `wlits`/`norm_pc` keep computed pc/value literals in
  numeral form so the generated `SF_*` fetch lemmas apply by
  conversion; `sp_norm`+`u_Z2bv` normalize open sp-relative arithmetic.
- The loop-index word bridges (`word_add_nat` family) and the other
  helpers that recurred across examples now live in `Common/StepTac.v`
  (`bveq`, `vm_refl_bv`, `wlit_closed`/`wlits_closed`,
  `rdn_ext_lit`, `u_norm_ceil`, byte-compare reflection lemmas, …).
  Earlier-ported examples keep local copies that harmlessly shadow the
  imports; new proofs should use the StepTac versions.
- stdpp gotcha: `cbn [skipn]` no longer reduces `skipn 0` — use
  `rewrite skipn_O`.
- `Checker.v` ports verbatim (module plumbing only); audit with
  `Print Assumptions` — the permitted closure is
  `functional_extensionality_dep` + the PrimInt63/PrimString
  primitives from the hex-segment machinery.
