# Common tactics: Rocq to Lean

The Lean proof library is a compatibility layer for the Rocq one in
`theories/Common/`. An example's Rocq proof script should copy across almost
line by line, so each Rocq tactic is ported under its own name, with the same
argument order, aiming to leave the same goals in the same shape. This file
records where that holds and where it cannot.

Rocq baseline: `theories/Common/*.v` at
`f44244ad6b8041aa83053d9ca91e090037ed743b`. The commit the Lean files'
headers name, `2cde689f94c086b868999970834b76a25616b94a`, differs from it in
`theories/Common/` only in one constant of `AllocSim.v`
(`brk_aslr_max_val`), which no tactic reads.

Nothing checks this file against the code. Every PR that adds, renames or
changes a tactic in `Common/` owes its row here; a row that says *not ported*
is wrong as soon as the tactic lands.

## Lemmas and definitions

A lemma or definition `x` of the Rocq file `Common/<File>.v` is ported as
`LinuxProcessSemantics.Common.<File>.x`, with the Rocq statement and its
hypotheses in the Rocq order. Rocq's `Z` is Lean's `Int`, `nat` and `N`
are `Nat`, `bv n` is `BitVec n`; the Rocq library functions are spelled as
each Lean file's header says (`Z.land` as `Z_land`, `Z.shiftr a n` as
`Z_shiftl a (-n)`, `firstn` as `List.take`, and the like). The names that
differ, or have no Rocq counterpart, that a copied script runs into:

| Rocq | Lean | Why |
| --- | --- | --- |
| `StepTac.v_add_comm` | `StepTac.v_add_comm` (protected) | Same statement, with word addition on the RHS; protected because `SymExec.v_add_comm` has a different statement. Batch 2 ports every remaining lemma/definition outside `DispatchSmoke`, preserving order and hypotheses; `Z.ltb`/`Z.leb` become `decide`, `forallb` becomes `List.all`. |
| `bv_eq` (stdpp, the iff) | `PropExec.bv_eq_of_unsigned` (the `←` direction) | stdpp's lemma has no Lean twin. Rocq's `reg_neq_tac` uses the `→` direction; its Lean twin decides the equality instead and needs neither. |
| `unfold bv_lts` (to `Z.ltb` on `bv_signed`) | `SymBranch.bv_lts_signed`, `bv_ltu_Z`, `bv_eqb_Z` | Lean's `unfold bv_lts` (and `bv_ltu`, `bv_eqb`) gives `BitVec` operations, not the `Int` comparison Rocq's does; these lemmas state Rocq's form, so a `rewrite` by them stands for the `unfold` (`bv_lts_signed` holds by `rfl`). Lean-only. |
| Rocq `vm_compute` deciding `wseg_ok` on a concrete image | `StoreOk.wseg_ok_backed` (with `wseg_ok_app`, `wseg_cover`) | Lean-only. Use `wseg_ok_backed` with the image's generated `_chars_eq`/`_ascii`/`_hex` theorems (the fixture at the end of `StoreOk.lean` is the template); a direct `decide +kernel` on a page-sized window does not finish. |

## Tactics

Status is **twin** (ported under the Rocq name), **renamed** (ported under
another name, with the reason), or **not ported** (the Rocq name is the planned
Lean name). Lean tactics are global syntax, so the Lean name is unqualified, as
the Rocq one is. A tactic's keyword is not a reserved token: an identifier
spelled the same still parses (`SeqExec`, `SymBranch` and `SymSide` pin this
for their tactics; `PropExec` pins both `step_pipeline` and `split_value_ifs`).

Differences that hold for every row and are not repeated in it:

- Every instruction-step row accepts an `is_ecall` hypothesis after conversion fails; Rocq supplies only `eq_refl`.

- Rocq's `lia` is `omega`. `omega` does linear arithmetic over `Int` and
  `Nat` atoms and does not unfold definitions, so a goal `lia` closes through
  a transparent definition may need it unfolded first.
- `rewrite L by tac` is `focus (rewrite [L]; rotate_left; tac)`, with `tac`
  written once per side condition of `L` (`rotate_left; omega; omega` for
  `StepTac.u_Z2bv`, which has two): Lean's `rewrite` leaves the side
  conditions as goals after the main one, `rotate_left` brings them all to
  the front, and each `tac` closes the first. `rewrite ?L by tac` is a
  `repeat` of that, and stops at the first instance whose side conditions
  `tac` cannot close, as Rocq's does.
- Rocq's `vm_compute; reflexivity` on a closed goal is `decide +kernel`, which
  evaluates in the kernel. StepTac now provides `check_closed_term` (and the
  public Meta guard `checkClosedTerm`): it instantiates metavariables, expands
  local let definitions, and rejects remaining metavariables before free
  variables. `vmEval` and `bveq` use this guard; `vm_closed` remains a direct
  `decide +kernel` alias without this explicit guard.

### `SeqExec.v`

| Rocq | Lean | Status | Difference |
| --- | --- | --- | --- |
| `reg_neq_tac` | `reg_neq_tac` | twin | Rocq turns the equality into one of `Z`s by `bv_eq`, `cbv`s and `discriminate`s; Lean refutes it by `decide` on the five-bit equality. Both close exactly the inequalities of two distinct register literals. |
| `getr_resolve` | `getr_resolve` | twin | — |
| `regupd_resolve` | `regupd_resolve` | twin | — |

### `PropExec.v`

| Rocq | Lean | Status | Difference |
| --- | --- | --- | --- |
| `step_pipeline Hfetch Hecall Hdecode` | `step_pipeline hf he hd` | twin | Rocq unfolds `step` and reduces it by `cbv` on named constants; Lean refines with `PropExec.step_exec`. The goal left is the interpreter goal on the decoded instruction's effect in both, but its printed form differs, so a `change`/`show` copied after it may need rewriting. |
| `split_value_ifs` | `split_value_ifs` | twin | Lean orders the Bool cases false then true (Rocq: true first), so bullets copied after it swap; a Bool `match` is not split (Rocq's `if` is a `match`, so Rocq's tactic splits one); Lean's `repeat'` bounds the repetition. As in Rocq, it searches the goal only, outermost and leftmost first, recognizing `ite (b = true)` and `cond b` without unfolding; it skips literal scrutinees, ones bound inside the goal and non-Bool conditions; and it replaces the scrutinee in the hypotheses too (a compound one through `generalize ... at *`, in the goal alone when that fails). It succeeds unchanged when nothing applies and does not simplify the leaves. |

### `StepTac.v`

| Rocq | Lean | Status | Difference |
| --- | --- | --- | --- |
| `u_norm` | `u_norm` | twin | Same first-instance `repeat rewrite u_Z2bv by omega` behavior; leaves the first goal open and stops when its bounds cannot be proved. `sym_u_norm` remains an alias with the same behavior, owned by SymBranch. |
| `imm_norm` | `imm_norm` | twin | Reads literal BitVec signed/unsigned projections at every width using public `wordLit?` (optional width, default 64), then checks the computed numeral by conversion. Nonliterals remain unchanged. `sym_imm_norm` remains an alias with the same behavior, owned by SymSide. A proof-backed literal whose spelling disagrees with its value makes `imm_norm` fail; Rocq’s repeat-match leaves it unchanged. |
| `chain_step` | `chain_step` | twin | Same constructor order. Lean Meta `apply` with `newGoals := .nonDependentOnly` implements `eapply`. Leaves pending-syscall, step, continuation goals. |
| `step_intro` | `step_intro` | twin | Alias of `chain_step`. |
| `expand_ctx_defs p` | `expandCtxDefs` | renamed | Value-returning Ltac becomes a public `Expr → MetaM Expr` function, transitively expanding local let definitions. No tactic form is needed: Rocq only calls it from the closedness guard. |
| `check_closed_term p` | `check_closed_term p` | twin | Elaborates in the main goal context and instantiates assigned metavariables before expanding local lets; remaining metavariables (including universe metavariables) are rejected before free variables. Unrelated metavariables in the goal do not matter; Lean-side callers use `checkClosedTerm`. |
| `vm_eval t` | `vm_eval t` | twin | The tactic silently validates evaluation and leaves the goal unchanged; Lean-side value callers use `vmEval`, since a leading-keyword term elaborator would reserve the identifier. Default-transparency Meta `whnf` produces Nat/Int/BitVec 64 literals only, checked by the kernel on an equality proof before returning; unlike Rocq, arbitrary normal forms are unsupported. |
| `word_lit p` | `word_lit p` | twin | The tactic silently validates the literal; value callers use `wordLit`. The unsigned value modulo `2^64` becomes an `OfNat` word numeral, definitionally equal in Lean, with a kernel-checked conversion proof. |
| `wlit_replace p` | `wlit_replace p` | twin | Proves the BitVec equation directly by `decide +kernel` and rewrites all occurrences in the first goal, including definitionally equal matches. Leaves hypotheses unchanged and the rewritten goal open. |
| `wlit p` | `wlit p` | twin | Recognizes word `OfNat`, `ofNat`, `ofNatLT`, and `ofFin` literals, as SymSide does. Argument elaboration failures propagate; `wlit_replace` failures roll back and leave the goal unchanged. |
| `wlits` | `wlits` | twin | Backtracking sweep in v_addi/btgt/v_jalr/v_auipc priority order, producing word numerals. Tries every occurrence in an arm before the next arm; skips failed open candidates, restarts after the first success, and stops only when none succeeds, as Rocq `repeat match` does. |
| `wlit_closed p`, `wlits_closed` | `wlit_closed p`, `wlits_closed` | twin | Guard and evaluate with batch 1 Meta functions; rewrite by `bveq` to `Z_to_bv 64 u`, preserving that spelling. The sweep follows actual Rocq `repeat match`: tries v_addi/v_add/v_sub in order and skips failed open candidates. Lean rewriting also matches convertible occurrences. The equality proved is `p = Z_to_bv 64 u`, the reverse of Rocq’s `replace` obligation. |
| `norm_pc_state st` | `norm_pc_state st` | twin | Instantiates metavariables, skips states still containing one, and recognizes syntactic four-argument `PropExec.mkst` only. An argument that does not elaborate fails, as in Rocq; later failures are no-ops. |
| `norm_pc` | `norm_pc` | twin | Matches full Lean names and total arities, including implicit parameters (`DrainSim.to_rd` has state index 8, zero-based). |
| `reduce_bv_eqb_ifs` | `reduce_bv_eqb_ifs` | twin | Both operands must be syntactic BitVec literals (any width, including registers). Conversion replaces only the conditional; recognizes Lean `ite (bv_eqb a b = true)` and Bool `cond`. |
| `step_simpl` | `step_simpl` | twin | `reduce_bv_eqb_ifs`, repeated `rewrite [List.drop_zero]` for Rocq `rewrite ?skipn_O`, then `norm_pc`; the repeat is parenthesized so normalization also runs without a drop-zero redex. Leaves the main goal open. |
| `stepi_search F D`, `stepi F D` | `stepi_search F D`, `stepi F D` | twin | Fetch/decode are terms (parenthesize applications). Search preserves all 41 Rocq alternatives in order; stepi dispatches on the decode shape, preserving divu/remu nonzero goals before the normalized continuation. Full PropExec names; divu/remu use SeqExec. Ecall closure tries `rfl`, then `assumption` for an abstract instruction word. |
| `stepiv F D vv tac`, `stepiwv F D vv tac` | `stepiv F D vv (tac)`, `stepiwv F D vv (tac)` | twin | Parenthesized `tacticSeq` stays in the original argument position. SeqExec `_at` dispatch with addi fallback; stepiwv is addiw-only. Same fetch/ecall/decode/register-guard/value goals, then step_simpl. |
| `stepj F D`, `stepjr F D tv tac` | `stepj F D`, `stepjr F D tv (tac)` | twin | Try x0 before linking, using PropExec/SeqExec lemmas in Rocq order. Indirect target is a term; its parenthesized tactic proves the register equation. Closed targets permit norm_pc. |
| `stepi_at F D val` | `stepi_at F D val` | twin | Addi-only; same register, literal-guard and stack normalization before the ordered closers. `omega` replaces `lia`, `congr 1 <;> omega` replaces `f_equal; lia`, and the final unsigned-equality closer checks closedness before `decide +kernel`. |
| `sp_norm` | `sp_norm` | twin | `imm_norm`, then innermost v_addi rewrites in m80/m64/m48/m32/m16/m1/nneg order with `u_norm; omega` on bounds and `u_norm` after each iteration. Backtracks past nested bases and unprovable bounds to later occurrences, matching Rocq level-zero failure. Rocq `cbn [Z.to_N]` is a no-op: Lean BitVec.ofInt introduces no such wrapper. A proof-backed literal whose spelling disagrees with its value makes `imm_norm` fail; Rocq’s repeat-match leaves it unchanged. |
| `bveq` | `bveq` | twin | Applies `bv_eq_of_unsigned`, then uses `decide +kernel` for closed goals, rejects evars, or tries only `rfl` for open goals with the Rocq OPEN diagnostic. No `timeout 30`: ambient `maxHeartbeats` is the nearest bound, and a failed closed evaluation reports kernel failure rather than a timeout. |
| `stepw_addr`, `stepw_val`, `stepw_addr_hyps` | `stepw_addr`, `stepw_val`, `stepw_addr_hyps` | twin | No arguments. Preserve register/stack normalization and closer order; val beta-reduces without closing the goal, hyps backtracks through matching `Sem.reg_get` equations. Congruence/omega and guarded bveq replace the Rocq closers. A proof-backed literal whose spelling disagrees with its value makes `imm_norm` fail; Rocq’s repeat-match leaves it unchanged. |
| `stepw F D aa vv oktac`, `stepsd F D aexp vexp vtac oktac`, `stepld F D aexp vexp readtac` | `stepw F D aa vv (oktac)`, `stepsd F D aexp vexp (vtac) (oktac)`, `stepld F D aexp vexp (readtac)` | twin | Term addresses/values and parenthesized tactic sequences in the same positions. Store widths follow sd/sw/sh/sb order. sd uses the hypothesis-aware address closer; ld replaces the address before readtac and closes the byte-value equation with bytes_le_to_Z_8. `stepld` proves `ad = aexp`, the reverse of Rocq’s `replace` obligation, and searches for `rdn` anywhere; Rocq requires `rdn … = …` at the goal head. |
| `vm_refl_bv` | `vm_refl_bv` | twin | `decide +kernel` replaces the bool_decide VM cast of eq_refl; also works for general closed decidable goals. Stuck open equations fail. |
| `rdn_ext_lit` | `rdn_ext_lit` | twin | `rdn_ext` arguments are segs/k/m1/m2/a/no-overflow/pointwise. Ordinary Lean rewriting also exposes m2; the Meta wrapper keeps it as a shared evar and restores Rocq order: main, no-overflow, pointwise. Closes the second with `imm_norm; u_norm; omega`, normalizes the third under its introduced point, and restores main then pointwise order with shared replacement-memory evar. The introduced point and bound are named `x` and `Hx` so a script can use them, as Rocq's `fresh "x"`/`fresh "Hx"`; when taken, Lean's fresh name is `x_1` where Rocq's is `x0`. A proof-backed literal whose spelling disagrees with its value makes `imm_norm` fail; Rocq’s repeat-match leaves it unchanged. |
| `smoke enc sh` | `smoke enc sh` | twin | Two terms; introduces fetch, kernel-proves concrete decode, takes stepi and closes the chain. All 40 DispatchSmoke Goals become proved examples; Lean decodes every integer encoding without Rocq tables. Every script retains its original family and proof obligations, including sb through MmapSim.step_sb_at. |

The step-family names are tactic-category syntax only, so all remain legal
identifiers. `F` and `D` are proof terms rather than hypothesis-name syntax.
Non-atomic terms need parentheses. Script arguments are parenthesized Lean
`tacticSeq`, in the same positions as Rocq's `ltac:(...)`; for example:

```lean
-- Rocq: stepiv F D (v_slli (getr regs 10) 1) ltac:(reflexivity).
stepiv hf hd (v_slli (getr regs 10) 1) (rfl)
-- Rocq: stepsd F D a v ltac:(exact V) ltac:(exact OK).
stepsd hf hd a v (exact hv) (exact hok)
```

The chain wrappers preserve pending-syscall, instruction side-goal and
continuation order. User scripts may leave subgoals; those remain before the
continuation, which receives `step_simpl` independently.

### `SymBranch.v`

| Rocq | Lean | Status | Difference |
| --- | --- | --- | --- |
| `sym_br` | `sym_br` | twin | Rocq's `unfold bv_lts, bv_ltu, bv_eqb` is a rewrite by the lemmas in the Lemmas section. Lean's `rewrite` and `omega` are not Rocq's `rewrite` and `lia`, so a goal can close on one side and not the other. |

### `SymSide.v`

| Rocq | Lean | Status | Difference |
| --- | --- | --- | --- |
| `u_norm_deep` | `u_norm_deep` | twin | Skips an instance whose side conditions fail and goes on, as Rocq's does. |
| `u_norm_deep_in H` | `u_norm_deep_in h` | twin | — |
| `vm_closed` | `vm_closed` | twin | `decide +kernel` (see the note above). |
| `sym_close_open` | `sym_close_open` | twin | Calls `sym_f_equal` for Rocq's `f_equal`. |
| `sym_sc` | `sym_sc` | twin | Rocq's `repeat split` is `repeat'` over `intro`s then `And.intro`, `True.intro`, `Iff.intro` or `with_reducible rfl`. |
| `rdn_side` | `rdn_side` | twin | `cbn [length]` is `dsimp only [List.length_cons, List.length_nil]`. |
| stdpp's `f_equal` | `sym_f_equal` | renamed | Rocq's is a library tactic, not a `Common` one. The Lean one omits stdpp's outer `try` and never splits an argument goal. |

### `SymTac.v`

| Rocq | Lean | Status | Difference |
| --- | --- | --- | --- |
| `sym_env_cbn` | `sym_env_cbn` | twin | Rocq's `cbn` on named constants is `simp only` with `Eplus`, arithmetic and list reduction rules, and the corresponding projections. |
| `sym_env_norm` | `sym_env_norm` | twin | — |
| `sym_z_lit k` | `sym_z_lit k` | twin | — |
| `sym_z_norm` | `sym_z_norm` | twin | — |
| `sym_addr_norm` | `sym_addr_norm` | twin | — |
| `sym_lit_norm` | `sym_lit_norm` | twin | — |
| `sym_norm` | `sym_norm` | twin | Calls `sym_u_norm` from `SymBranch.lean` and `sym_imm_norm` from `SymSide.lean` through `sym_addr_norm` where Rocq calls `u_norm` and `imm_norm`. |
| `sym_mem_norm` | `sym_mem_norm` | twin | — |
| `sym_halted` | `sym_halted` | twin | Lean has no `model` autorewrite set; it uses the named `MmapSim` rules instead. |
| `sym_no_lazy` | `sym_no_lazy` | twin | — |
| `chain_mst` | `chain_mst` | twin | Rocq's `eapply` alternatives use `apply` in Lean, in the same order, leaving the machine-step premise before the advanced chain premise. |
| `sym_close` | `sym_close` | twin | Rocq's final `bveq` alternative is `vm_closed` guarded by a closedness check; `sym_close_open` calls `sym_f_equal` for Rocq's `f_equal`. |
| `sym_regs H` | `sym_regs H` | twin | Rocq's `eval vm_compute` and `change` on each closed `sr_get a b` become `convertClosed` with `Lean.Meta.reduce`, with the kernel checking conversion. |
| `sym_reg H R r v tac` | `sym_reg H R r v tac` | twin | Lean names the asserted register equality `this`. |
| `list_len l` | `list_len l` | twin | Lean uses term syntax and fails on a non-literal list. |
| `sym_pc_Z` | `sym_pc_Z` | twin | — |
| `sym_pc_lit` | `sym_pc_lit` | twin | — |
| `sym_sc_auto` | `sym_sc_auto` | twin | Rocq's `repeat split; lia` is `repeat'` over `intro`s then `And.intro`, `True.intro`, `Iff.intro` or `with_reducible rfl`, followed by `omega` on every remaining goal. |
| `sym_pin_auto` | `sym_pin_auto` | twin | — |
| `sym_block segs fuel dirs rds ps pvals rvals R H` | `sym_block segs fuel dirs rds ps pvals rvals R H` | twin | Rocq's `vm_compute` becomes per-instruction kernel-checked fetch and step equations, with direct kernel reduction as a fallback when image certification fails. |
| `sym_block_ex segs ms fuel dirs rds ps pvals rvals R H Hms` | `sym_block_ex segs ms fuel dirs rds ps pvals rvals R H Hms` | twin | Rocq's `vm_compute` becomes per-instruction kernel-checked fetch and step equations, with direct kernel reduction as a fallback when image certification fails. |
| `sym_chain Hms` | `sym_chain Hms` | twin | — |

### `StoreOk.v`

| Rocq | Lean | Status | Difference |
| --- | --- | --- | --- |
| `store_ok_peel` | `store_ok_peel` | twin | `eapply store_ok_mono; [apply X_grows\|]` is `apply store_ok_mono; apply X_grows`. |
| `store_ok_base` | `store_ok_base` | twin | Calls `sym_u_norm` where Rocq calls `u_norm`; the two expand to the same tactic (the `u_norm` row above). `discriminate` on the nonempty grant list is `simp only [List.cons_ne_nil, ...]`. |
| `solve_store_ok` | `solve_store_ok` | twin | — |
| `store_ok_grows` (`eauto with store_ok_db`) | `store_ok_grows` | twin | Rocq's hint database `store_ok_db` is the extensible tactic `store_ok_grows`. An example registers its invariant's `mem_grows` projection with `macro_rules \| `(tactic\| store_ok_grows) => `(tactic\| (apply my_proj; assumption))` (or `local macro_rules` inside a section), where Rocq writes `Hint Resolve my_proj : store_ok_db`. Lean tries the newest rule first and backtracks; the base rule is `assumption`, standing for the context hypotheses `eauto` uses. Unlike `eauto`, it does not search: each rule is one tactic, and a hypothesis is used only when it is the goal itself. |
| `solve_store_ok_inv` | `solve_store_ok_inv` | twin | — |
| `solve_mem_grows` | `solve_mem_grows` | twin | `eapply mem_grows_trans; [ \| apply X_grows ]` is `apply mem_grows_trans; rotate_left; apply X_grows`. Its `solve [ eauto with store_ok_db ]` branch is `solve \| store_ok_grows`. |

### Other files

All not ported: `SymExec.v`'s `sym_val_norm`; `SimInv.v`'s `norm_fd32` and
`fd32_ok`; `MuslStrlen.v`'s `by8 i`; `MuslCall.v`'s `at_fold`, `gres`, `apc`,
`hstepv F D vv tac` and `in_clob`; `WxExec.v`'s
`wx_step_pipeline Hwx Hecall Hdecode`.

## Rocq terms in a copied script

| Rocq | Lean |
| --- | --- |
| `20%nat` | `(20 : Nat)` |
| `0x50` in `Z` | `0x50` (an `Int` where the type says so) |
| `[a; b]` | `[a, b]` |
| `(@nil T)` | `([] : List T)` |
