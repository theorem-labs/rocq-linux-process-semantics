# How to complete an example equivalence proof

Ported in part from theorem-labs/linux-process-semantics `r22/namespace-core` at 6ff3d045 (issue #1011).

This guide describes how the completed examples (`modprint_ns`,
`grep_args_ns`, `brk_rev_ns`, `cat1024_ns`, `conditional_bug_ns`,
`mmap_upper_ns`) are proved, so that a new example can follow the same
recipe. Read `README.md` in this directory first for the file layout and
the generation steps (`make source-images target-images`,
`gen-fd-lemmas`), and `../Common/README.md` for the library.

Start from **`modprint_ns`** — at ~1.5k lines it is by far the smallest
complete example, and the only one with no input-dependent control flow
(one behavior, no case split, so `Proof.v` is a single
`cat_omni_strong_equiv_alg`). It shows the whole skeleton with nothing else in
the way. Move to a branching example (`conditional_bug_ns`) once the
skeleton makes sense.

## 1. What must be proved

`EquivalenceDefinition/Equivalence.v` is the whole trust boundary:

- `equiv source target` (Equivalence.v) — either **every source execution
  errors** (`bh_all_errors` — the universal source-error escape), or the
  target's finite trace-prefix set exactly equals the source's **and** the
  target cannot error on any execution (`~ bh_errors target`). A single
  chosen source error path is not an escape if another resolution avoids
  error.
- `modeled source` (Equivalence.v) — the source never reaches a
  configuration the model declines to interpret: an instruction step that is
  `MachineUnmodeled` (undecodable word — unless the ISA defines it illegal,
  like the all-zero parcel, which faults instead — F/D/Zicsr, an ISA
  `EIllegal`/`EFpu` node) or a syscall whose spec yields `Unmodeled` (number outside
  `modeled_sysnos`, unmodeled flags, a buffer the spec will not read). The
  source **may** fault — `MachineFault` (wild jump, unmapped load, store into
  a read-only segment, `ebreak`) is a faithful model of a process that really
  dies, and it still gets the `bh_all_errors` escape. (Stepping onto the
  all-zero parcel the ISA defines illegal is a fault too — SIGILL on real
  hardware, `DecodeC.is_defined_illegal`.) What it may not do is
  run off the edge of the model, which is what would otherwise make the
  escape a statement about this development's incompleteness rather than
  about the binary.
- `strong_universal_T` — the sole obligation: for all `en_source en_target`
  (`Run.ExecEntry`: `en_sp`, `en_brk`, `en_mmap_base`, `en_draw`) and every `inp`
  (`State.ProcInput`: `in_argv`, `in_envp`, `in_fs` — a namespace of folders,
  files by inode, devices and symbolic links — `in_cwd`, `in_stdin`, `in_uid`,
  `in_gid`, `in_groups`, `in_net`, `in_nofile`, `in_sigmask`, `in_hwcap`, and
  the launch fields `State.ProcInput` lists after them)
  satisfying the
  validity hypotheses (`valid_entry` ×2, `valid_input`),
  `modeled (run source_image en_source inp)` **and**
  `equiv (run source_image en_source inp) (run target_image en_target inp)`.
  Each image is a `MemImageType.Image` record — segments, `init_pc`, `phdrs`.
  The two entry records are quantified **independently** (ASLR: `valid_entry`
  lets `en_sp` and `en_brk` roam their windows, and constrains `en_draw` not
  at all — every 128-bit AT_RANDOM draw is one a kernel can make, and so is
  every set of bytes above the entry block up to the page boundary); the input record
  is quantified ONCE and shared, so the two binaries are always compared on
  the same input — including on `in_uid`/`in_gid`, the user and group the
  process was launched as, which the two binaries therefore always agree on.
  Its `in_stdin` field — the standard-input byte stream
  (`State.InputStream`) — carries no validity predicate: its elements are
  `byte`, so every colist of bytes is a real input.

`Proof.v` ends with `Theorem omni_strong_universal : omni_strong_universal_T … .`
— the same obligation in the omni shape of
`EquivalenceDefinition/OmniEquivalence.v`, which is what every `Common/`
combinator now produces — followed by the one-line corollary
`Theorem strong_universal : strong_universal_T … .` through
`OmniEquivalence.strong_universal_iff`. `Checker.v` pins the latter into
`Module Checked <: Equivalence.SPEC Source Target` (and the former into
`OmniChecked <: OmniEquivalence.OMNI_SPEC Source Target`) and runs
`Print Assumptions` on both; only `functional_extensionality_dep` and the
`PrimInt63`/`PrimString`/`PrimArray` primitives may appear.

`cp_ns` and `headcp_ns` are the two exceptions, and `tools/gen_checker.py`'s
`SPEC_ON` list names them. Their `Proof.v` defines the input hypothesis
`operands_inside_model` (the walk of each operand the program opens does not
end at `Fs.ROutside`, the one walk end on which the model declines an open; a
device entry is answered at any key), a witness
`operands_inside_model_witness`, the lemma `operands_inside_model_iff` (the
hypothesis holds exactly when the model answers the open of each operand), and
`Theorem strong_universal_operands_inside :
Equivalence.strong_universal_T_on operands_inside_model … .`. Their
`Checker.v` ascribes `Equivalence.SPEC_ON` under `Module Hyp <:
Equivalence.INPUT_HYP`, prints the hypothesis's text, and runs
`Print Assumptions` on the theorem and on the witness. No comment in such a
`Proof.v` may hold a double quote: `gen_checker.py --check` reads the file
with its comments removed and refuses one whose comments it cannot remove.

## 2. File plan

For problem `foo` (beyond `SourceMemImage.v` and `TargetMemImage.v`, and
the two files dune generates into `_build` rather than the tree —
`foo_code.v` and `Checker.v`; see `theories/Examples/dune`):

| File | Role |
|---|---|
| `foo_defs.v` | The *bridge*: pure spec functions (the mathematical model of the program's output), image probes (`*_init_pc_val`, `*_avoids_ro`, buffer writability), shared step tactics. |
| `foo_source.v` | Symbolic execution of the source binary: one result lemma per input branch. |
| `foo_target.v` | Same for the target binary. |
| `Proof.v` | Glue: case-split the input, apply one `Common` `*_omni_strong_equiv*` lemma per branch, feeding both sides the *same* spec value; derive the legacy `strong_universal` through `OmniEquivalence.strong_universal_iff`. |
| `Checker.v` | Generated — one template stamped with the problem name (`tools/gen_checker.py`). |

Large examples split further to keep recompiles cheap — `oob_read_bug_ns`
splits the target outcomes into `_target_outcomes.v`. Split when a single
file's compile time becomes painful; the split files import the frame/read
infrastructure from the base `_source.v`/`_target.v`. Prefer generalizing the
shared library over splitting: `cat1024_ns` used to carry its own fork of the
stream-loop machinery, and it went away once `Common/StreamSim.v` took the
chunk size as a parameter.

## 3. The defs file: agree on a spec first

Both per-binary proofs must conclude with the **same** `(bufs, code)` (or
outcome set / trace set). Define that value once in `foo_defs.v` as a pure
function of the input, e.g. `grep_bufs pat args`, `mod_bufs argc`,
`rev_buf s`, `out_buf s`, `brkU …`. Everything downstream pattern-matches
on this function, so get it right (and computable) before starting the
stepping proofs.

Also in defs:

- `source_init_pc_val` / `target_init_pc_val` — proved by
  `vm_compute; reflexivity`, rewritten at the top of `Proof.v`.
- read-only-avoidance and writability probes for the buffers the program
  touches (`*_avoids_ro`, per-buffer `wbytes` facts).
- `valid_argv_*` helper lemmas for the input case-split.
- Re-export of the step tactics (below) so all files share them.

## 4. Stepping through a binary

The per-binary files open a `Section` over the whole process input and the
launch (`modprint_ns/modprint_ns_source.v` is the file to copy this from):

```coq
Section SourceProof.

Variable inp : ProcInput.
Local Abbreviation av := (in_argv inp).
Local Abbreviation ev := (in_envp inp).
Local Abbreviation fs0 := (in_fs inp).
Hypothesis Hva : valid_argv av.
Hypothesis Hvl : valid_launch inp.      (* the E2BIG cap on the launch *)

Variable rsp : word.                    (* the quantified stack pointer *)
Variable rbrk : word.                   (* the quantified initial break *)
Variable rmb : word.                    (* the quantified mmap base *)
Variable rrnd : EntryDraw.              (* AT_RANDOM, the stack VMA's end,
                                           the vDSO's leftovers *)
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned rsp)%Z.
Hypothesis Hsp_hi : (bv_unsigned rsp <= sp_window_hi)%Z.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry rsp rbrk rmb rrnd) inp.
Variable vt : list Segment.             (* the vDSO pair of the run *)
```

Seven things about that head:

- **Quantify over the record, not over its fields.** `State.init_model` and
  `Run.init_config` take a `ProcInput`, so a section that mentions either
  needs one. Keeping `av` and `ev` as independent variables would let a lemma
  quantify over an `init_machine_state` built from one argv and an
  `init_model` built from an unrelated one — a configuration `Run.run` cannot
  produce.
- **Abbreviate, don't bind.** The abbreviations leave the rest of the section
  the text it already was: `av` still means `av` in every statement and every
  tactic below. Write `Local Abbreviation`, not `Local Notation` — Rocq 9.2
  rejects `Notation` for a parameterless abbreviation with a deprecation
  error.
- **Declare only the abbreviations the file uses, and never one whose name is
  already a binder there.** `arena_tee_ns` is the live case: it abbreviates
  `av` and `ev` but not `fs0`, because `fs0` is already the bound parameter of
  `src_inv`, `src_LH`, `src_tail`, `tgt_LH` and `tgt_TH`, which range over an
  arbitrary file system. Those lemmas spell `in_fs inp` out instead, and the
  proofs that instantiate them recover the short name with
  `set (fs0 := in_fs inp) in *`.
- **The launch draw gets a variable, and the launch conjunct is its
  hypothesis.** `rrnd` (`StackLayout.EntryDraw`: the AT_RANDOM bytes, the
  stack VMA's end `ed_top`, the vDSO's leftover-naming function) sits next to
  `rsp` because `Run.init_machine_state` takes it there. `Hlau` is the fifth
  conjunct of `Run.valid_entry_va`: it bounds the entry block
  (`StepTac.bsb_bound`, with `Hvl`) and places `rsp` at or below `ed_top`.
  Every lemma below is then proved for every draw the launch admits, which is
  what the theorem asks. Declare it in the target section too, under its own
  name (`arnd`), never sharing the source's: the two are quantified
  independently.
- **`init_machine_state` takes the whole input.** It reads argv, envp, the
  launching uid and the `AT_HWCAP` word out of `inp` (they fill the strings
  and the auxv's `AT_UID`/`AT_EUID` and `AT_HWCAP`), so a section writes
  `(in_uid inp)` and `(in_hwcap inp)` and declares no free binder for them.
- **The run's segment list is the image's followed by the vDSO pair**
  (`Run.run_segments`). State the section's derivations over `segs ++ vt`
  and instantiate `vt` with the pair in `Proof.v`, or prove them over the
  image's own segments and carry them to the run with `Common/RunSegmentsLift.v`
  (`msteps_run`, `to_wexit_run`, `to_wallexit_run`). A fetch over `segs ++ vt`
  is the image's fetch through `fetch_word_app`.
- **`PropExec.mkst` takes an `FPState` instance**: the per-binary file names
  `#[local] Instance` of the state at process entry (`fx0`).

The section then builds the initial memory in layers:
`wmem := wrap_mem inp rmb phdrs (Z_to_bv 64 entry) rsp rrnd`,
plus `fmem`/`emem` layering the `_start`+prologue stores (`environ` slot,
callee-save slots) as nested `wbytes`. For musl sources, a
`mem_ok`-style predicate abstracts the libc scratch window so reads
outside it defer to the layered memory.

Instructions are stepped with the tactics defined in
`grep_args_ns/Proof.v:154-183` (and copied into each `_defs.v`):

- `stepi F D` — one ALU step. `F`/`D` are the generated `SF_<addr>` /
  `SD_<addr>` fetch/decode lemmas from `foo_code.v`.
- `stepiv F D v tac` — ALU step with a pre-normalized written value.
- `stepj F D` — unconditional jump (`step_jal_x0`).
- Branches, loads, stores, calls inline: `step_bltu_ft`, `step_ld`,
  `step_sd_at`, `step_jal_link` (call), `step_jalr_x0` (ret) — from
  `Common/{PropExec,CatExec,SeqExec}`.
- `norm_pc` `vm_compute`s the next-pc literal; `sp_norm` normalizes nested
  `v_addi rsp` offsets; `getr_resolve`/`regupd_resolve` resolve registers.
- Syscalls: `step_ecall` produces the pending-svc record, then the shape
  library attaches the tail — `tw_write_ret` / `tw_exit_coden` (CatSim /
  SeqExec) for write/exit, or the shape-specific record entry points
  (`trd_here_rec`, `tmw_mmap_rec`, `tou_brk_r`, …).

Model a callee (e.g. a `put()` helper) as its own `msteps` lemma
parameterized by the return address, then splice it at each call site
(`SeqExec` pattern).

Name the result lemmas `source_wexit_<branch>` / `target_wexit_<branch>`
(`_lt2`, `_ge2`, `_cap`, `_n`, …); allocation shapes use
`source_outcomes`/`target_outcomes` (brk) or `source_tmw`/`target_tmw`
(mmap); error escapes use `source_err_<branch>` / `source_escape`.

## 5. Choose the Common glue per branch

Every branch of `Proof.v` applies exactly one library lemma:

| Behavior on that branch | Lemma | Witness needed from each side |
|---|---|---|
| writes to fd 1, then exit | `cat_omni_strong_equiv_te` (CatSim.v) | `to_wexit (run_segments …) (init_machine_state …) bufs code`, identical `(bufs, code)`, and a `cat_launch` fact (the reader on fd 1, `Run.valid_input_channel_reader`) |
| exit only, no I/O | `exit_omni_strong_equiv` (ExitSim.v) | `to_exit` with the same code |
| brk allocation (nondet resolution) | `alloc_omni_strong_equiv` (AllocSim.v) | `to_outcomes … U`, identical outcome set `U` |
| one anonymous mmap (fail/succeed) | `mmap_omni_strong_equiv_te` (MmapSim.v) | `tmw … bf cf bs cs`, identical fail/success pairs |
| unbounded read/write stream | `stream_omni_strong_equiv` (StreamSim.v) | per-binary loop-head `to_rd` invariants; trace set is `stream_traces cnt (in_fs inp) (in_stdin inp)` |
| file operations, the result an exit code and the final files | `fout_omni_strong_equiv` (FileSim.v) | `to_fout (run_segments …) (init_machine_state …) model U`, identical outcome set `U` of (exit code, final image) |
| file operations where a copy loop may never stop (an endless source) | `floop_omni_strong_equiv` (FileSimLoop.v) | `to_floop … U`: `to_fout` plus `tfl_loop` leaves (a silent loop region, `fsilent`, shown by anchors `fanchored` / `fsilent_fpath`), identical `U` |
| every source execution deterministically faults | `err_escape_omni_strong_equiv` (ErrEscape.v) | source-only: `msteps` reaching `MachineFault`; target unanalyzed |
| one trace shape per branch, any allocator mix | `shape_omni_strong_equiv` (ShapeAlg.v) | a `realizes` derivation per side for the *same* shape (`SHAPE_ALGEBRA.md`) |

Every `*_omni_strong_equiv*` lemma above discharges **both** conjuncts of
`omni_strong_equiv` — `covered` for the source and the `omni_equiv`
agreement — so `Proof.v` applies one lemma per branch and the `covered`
clause costs nothing there. For the ordinary rows it is the combinator's
own omni run judgment weakened from its `exits_with`/`never_errors`
postcondition to `covered` (`OmniRun.never_errors_covered`); for the escape
row both halves come from one omni judgment,
`ErrEscape.msteps_illegal_exec`, which is where the
`MachineFault`/`MachineUnmodeled` split earns its keep — the escape is only
available for a source that genuinely crashes. Each omni combinator sits
beside its legacy twin (`cat_strong_equiv_te`, `exit_strong_equiv`,
`alloc_strong_equiv`, `mmap_strong_equiv_te`, `stream_strong_equiv`,
`err_escape_strong_equiv`), which is now derived from it through
`OmniEquivalence.strong_equiv_iff`; a `Proof.v` no longer applies the
legacy twins directly.

`FileMixSim.file_mix_equiv_only` is the exception, and its name says so: its
`tfm_unmodeled` leaf *is* an unmodeled syscall, so it supplies `equiv` only and
cannot close `strong_universal_T`. No example uses it — its canonical instance
was `cp_ns` / `headcp_ns` on an over-PATH_MAX `argv[2]`, and `openat_spec` now
answers that with a real `-ENAMETOOLONG`, which makes it an ordinary
`FileSim.to_fout` node. The combinator is retained (AGENTS.md forbids deleting
proofs) but has no call site; if you find yourself needing it, the fix belongs
in the syscall spec, not in a weaker per-binary theorem.

Use the escape row only when the path is deterministic up to the error.
If an earlier syscall has multiple resolutions, every successful successor
must itself satisfy `all_traces_error`; choosing one faulting resolution is
not sufficient.

The `Proof.v` recipe:

```coq
Theorem omni_strong_universal : OmniEquivalence.omni_strong_universal_T … .
Proof.
  intros [sp_source brk_source mb_source rnd_source]
         [sp_target brk_target mb_target rnd_target] inp Hens Hent Hvalid.
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
  destruct Hens as (Hspr & _ & _ & _ & Hlau_source).
  destruct Hent as (Hspa & _ & _ & _ & Hlau_target).
  set (argv := in_argv inp) in *.
  destruct Hspr as (lo & hi & _). destruct Hspa as (alo & ahi & _).
  rewrite source_init_pc_val, target_init_pc_val.
  destruct (le_lt_dec 2 (length argv)) as [Hge|Hlt].
  - (* further sub-splits on byte values / lengths / counts … *)
    …  eapply cat_omni_strong_equiv_te; [ apply source_wexit_ge2 | apply target_wexit_ge2 | … ].
  - eapply cat_omni_strong_equiv_te; [ apply source_wexit_lt2 | … ].
Qed.

Theorem strong_universal : strong_universal_T … .
Proof. apply strong_universal_iff. exact omni_strong_universal. Qed.
```

Take each clause of `valid_input` from its accessor lemma
(`Run.valid_input_argv`, `Run.valid_input_launch`,
`Run.valid_input_channel_reader`, `Run.valid_input_va_size`, …) rather than
from a positional pattern: the predicate has gained conjuncts (the image and
working folder, the urandom stream, the launch cap, the reader on fd 1, the
kernel build), and each insertion moves every later position.
`theories/Examples/README.md` peels it with a guarded `repeat` instead.

Four of its conjuncts say what a launch is allowed to carry: `valid_creds` —
the launching uid and gid are 32-bit and not `(uid_t)-1` — `valid_nofile`,
the soft descriptor limit's ceiling, `valid_sigmask`, which says the launch
blocks neither SIGKILL nor SIGSTOP, and `valid_hwcap`, which admits exactly
the two `AT_HWCAP` masks of `docs/writing-reference-programs.md` §2. A proof
that issues no credential syscall, no `dup3` and no `rt_sigprocmask`, and does
not read `AT_HWCAP`, uses none of them.

A proof that wants ONE of the two masks instead of both issues its statement
under `Run.valid_input_hwcap_rv64gc` or `Run.valid_input_hwcap_rv64gcv`, which
replace the `valid_hwcap` disjunction by an equation. That is a declaration
about the task's kernel, not about the hart, and it is what a reference
program that probes for a vector unit needs; see
`bugs/hwcap-word-is-the-tasks-declaration.md`.

`inp` is introduced whole and the `set` line names the projections the case
split reads — only those; no `Proof.v` sets all of them (`grep_args_ns` sets
just `argv`). Do not `destruct inp` instead.
`Run.run`, `Run.init_config` and `State.init_model` read the record with
projections precisely so they reduce for a variable `inp` — destructing throws
that away, and adding another process input later would then move every intro
pattern in every proof.

Case-split only on properties of the *input* (`argc`, byte tests, length
caps) — never on the machine state; the per-binary lemmas already carry
the branch hypotheses.

## 6. Checker.v and auditing

`Checker.v` is generated from the single template in
`tools/gen_checker.py`, so this shape is written in exactly one place and
example 12 cannot copy-paste it wrong. It:

1. `Module Checked <: Equivalence.SPEC SourceMemImage.Source TargetMemImage.Target`
   with `Definition strong_universal := Proof.strong_universal.`, and
   `Module OmniChecked <: OmniEquivalence.OMNI_SPEC …` with
   `Definition omni_strong_universal := Proof.omni_strong_universal.`
2. `Module SourceWf <: Equivalence.IMAGE_WF SourceMemImage.Source` and the
   `TargetWf` counterpart — the per-image anti-vacuity checks, each a
   `vm_compute` proof of a statement the module type pins.
3. `Print Assumptions` on the checked theorem. The build output is the
   audit: anything beyond `functional_extensionality_dep` +
   `PrimInt63`/`PrimString`/`PrimArray` primitives means an
   `Admitted`/`Axiom` leaked in.

For the examples in its `SPEC_ON` list (`cp_ns`, `headcp_ns`) the generator
stamps a second template instead of item 1: `Module Hyp <:
Equivalence.INPUT_HYP` with the `Proof.v`'s hypothesis and its witness, the
hypothesis's text in a comment, `Module Checked <: Equivalence.SPEC_ON Hyp
SourceMemImage.Source TargetMemImage.Target` of
`Proof.strong_universal_operands_inside`, and `Print Assumptions` on both the
theorem and the witness. `gen_checker.py --check` also reads each such
`Proof.v` and refuses one that does not define the pinned hypothesis text, its
witness or the theorem.

## 7. Performance notes

- All closed-term computation (`init_pc`, fetch/decode checks, pc
  arithmetic) goes through `vm_compute` — never `simpl`/`cbn` on terms
  that mention the memory image, and avoid `nat` for anything sized
  (addresses, lengths, counters are `N`/`Z`).
- The generated `foo_code.v` lemmas are closed with a `vm_refl` cast so
  the kernel checks them with the VM.
- Keep `Global Strategy 200` (from the `_code.v` header) so image
  constants stay opaque to conversion.
- Split big per-binary proofs into separate files (see §2) so iterating
  on `Proof.v` doesn't recompile the stepping proofs.
