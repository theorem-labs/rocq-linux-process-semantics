import LinuxProcessSemantics.Common.FileSim.Base
import LinuxProcessSemantics.Common.FileSim.Decode
import LinuxProcessSemantics.Common.FileSim.Algebra
import LinuxProcessSemantics.Common.FileSim.Tree
import LinuxProcessSemantics.Common.FileSim.Glue
import LinuxProcessSemantics.Common.FileSim.Open
import LinuxProcessSemantics.Common.FileSim.ReadWrite
import LinuxProcessSemantics.Common.ExitSim
import LinuxProcessSemantics.Common.CatExec
import LinuxProcessSemantics.Common.CatSim
import LinuxProcessSemantics.Common.ErrEscape
import LinuxProcessSemantics.Examples.headcp_ns.headcp_ns_defs
import LinuxProcessSemantics.Examples.headcp_ns.headcp_ns_source
import LinuxProcessSemantics.Examples.headcp_ns.headcp_ns_target

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! # headcp-ns: equivalence proof, top-level glue

PROOF-SIDE, not trusted spec. Mirrors `theories/Examples/headcp_ns/Proof.v`:
the input case split joins the per-binary file outcomes with
`fout_omni_strong_equiv`, and the `argc < 3` usage path with
`cat_omni_strong_equiv_te`. The legacy theorem follows through
`strong_universal_iff`.
-/

namespace LinuxProcessSemantics.Examples.headcp_ns.Proof

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.Common.FileSim
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
open LinuxProcessSemantics.Examples.headcp_ns.SourceMemImage
open LinuxProcessSemantics.Examples.headcp_ns.TargetMemImage
open LinuxProcessSemantics.Examples.headcp_ns.headcp_ns_code
open LinuxProcessSemantics.Examples.headcp_ns.headcp_ns_defs
open LinuxProcessSemantics.Examples.headcp_ns.headcp_ns_source
open LinuxProcessSemantics.Examples.headcp_ns.headcp_ns_target

theorem omni_strong_universal :
    omni_strong_universal_T
      (Image.mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (Image.mkImage Target.loaded_segments Target.init_pc Target.phdrs) := by
  intro es et inp Hens Hent Hvalid
  cases es with
  | mkEntry sp_source brk_source mb_source rnd_source =>
  cases et with
  | mkEntry sp_target brk_target mb_target rnd_target =>
  have Hsv48 := valid_input_va_size inp Hvalid
  obtain ⟨⟨Hr_lo, Hr_hi, _⟩, _⟩ := (valid_entry_sv48 _ _ _ Hsv48).1 Hens
  obtain ⟨⟨Ha_lo, Ha_hi, _⟩, _⟩ := (valid_entry_sv48 _ _ _ Hsv48).1 Hent
  obtain ⟨Hva, Hve, _⟩ := Hvalid
  by_cases Hge3 : 3 ≤ inp.in_argv.length
  · by_cases Hsrc_big : 4096 ≤ (inp.in_argv.getD 1 []).length
    · apply fout_omni_strong_equiv
      · exact source_src_toolong inp Hva Hve sp_source rnd_source Hr_lo Hr_hi
          brk_source mb_source Hge3 Hsrc_big
      · exact target_src_toolong inp Hva Hve sp_target rnd_target Ha_lo Ha_hi
          brk_target mb_target Hge3 Hsrc_big
    · have Hs45 : (inp.in_argv.getD 1 []).length ≤ 4095 := by omega
      cases Hsdot : path_eqb (inp.in_argv.getD 1 []) dot_path with
      | true =>
        by_cases Hdst_big : 4096 ≤ (inp.in_argv.getD 2 []).length
        · apply fout_omni_strong_equiv
          · exact source_src_dot_dst_toolong inp Hva Hve sp_source rnd_source Hr_lo Hr_hi
              brk_source mb_source Hge3 Hdst_big Hsdot
          · exact target_src_dot_dst_toolong inp Hva Hve sp_target rnd_target Ha_lo Ha_hi
              brk_target mb_target Hge3 Hdst_big Hsdot
        · have Hd45 : (inp.in_argv.getD 2 []).length ≤ 4095 := by omega
          cases Hde : path_eqb (inp.in_argv.getD 2 []) [] with
          | true =>
            apply fout_omni_strong_equiv
            · exact source_src_dot_dstempty inp Hva Hve sp_source rnd_source Hr_lo Hr_hi
                brk_source mb_source Hge3 Hd45 Hsdot Hde
            · exact target_src_dot_dstempty inp Hva Hve sp_target rnd_target Ha_lo Ha_hi
                brk_target mb_target Hge3 Hd45 Hsdot Hde
          | false =>
            cases Hddot : path_eqb (inp.in_argv.getD 2 []) dot_path with
            | true =>
              apply fout_omni_strong_equiv
              · exact source_src_dot_dstdot inp Hva Hve sp_source rnd_source Hr_lo Hr_hi
                  brk_source mb_source Hge3 Hd45 Hsdot Hddot
              · exact target_src_dot_dstdot inp Hva Hve sp_target rnd_target Ha_lo Ha_hi
                  brk_target mb_target Hge3 Hd45 Hsdot Hddot
            | false =>
              have Hdplain := valid_argv_str_plain inp.in_argv 1 Hva (by omega) Hddot
              apply fout_omni_strong_equiv
              · exact source_src_dot inp Hva Hve sp_source rnd_source Hr_lo Hr_hi
                  brk_source mb_source Hge3 Hd45 Hsdot Hde Hdplain
              · exact target_src_dot inp Hva Hve sp_target rnd_target Ha_lo Ha_hi
                  brk_target mb_target Hge3 Hd45 Hsdot Hde Hdplain
      | false =>
        cases Hse : path_eqb (inp.in_argv.getD 1 []) [] with
        | true =>
          apply fout_omni_strong_equiv
          · exact source_src_empty inp Hva Hve sp_source rnd_source Hr_lo Hr_hi
              brk_source mb_source Hge3 Hs45 Hse
          · exact target_src_empty inp Hva Hve sp_target rnd_target Ha_lo Ha_hi
              brk_target mb_target Hge3 Hs45 Hse
        | false =>
          have Hsplain := valid_argv_str_plain inp.in_argv 0 Hva (by omega) Hsdot
          cases Hsrc_lk : fs_lookup inp.in_fs (inp.in_argv.getD 1 []) with
          | some d0 =>
            by_cases Hdst_big : 4096 ≤ (inp.in_argv.getD 2 []).length
            · apply fout_omni_strong_equiv
              · exact source_present_dst_toolong inp Hva Hve sp_source rnd_source Hr_lo Hr_hi
                  brk_source mb_source Hge3 Hsplain d0 Hs45 Hdst_big Hse Hsrc_lk
              · exact target_present_dst_toolong inp Hva Hve sp_target rnd_target Ha_lo Ha_hi
                  brk_target mb_target Hge3 Hsplain d0 Hs45 Hdst_big Hse Hsrc_lk
            · have Hd45 : (inp.in_argv.getD 2 []).length ≤ 4095 := by omega
              cases Hddot : path_eqb (inp.in_argv.getD 2 []) dot_path with
              | true =>
                apply fout_omni_strong_equiv
                · exact source_dst_dot inp Hva Hve sp_source rnd_source Hr_lo Hr_hi
                    brk_source mb_source Hge3 Hsplain d0 Hs45 Hd45 Hse Hddot Hsrc_lk
                · exact target_dst_dot inp Hva Hve sp_target rnd_target Ha_lo Ha_hi
                    brk_target mb_target Hge3 Hsplain d0 Hs45 Hd45 Hse Hddot Hsrc_lk
              | false =>
                cases Hde : path_eqb (inp.in_argv.getD 2 []) [] with
                | true =>
                  apply fout_omni_strong_equiv
                  · exact source_present_dst_empty inp Hva Hve sp_source rnd_source Hr_lo Hr_hi
                      brk_source mb_source Hge3 Hsplain d0 Hs45 Hd45 Hse Hde Hsrc_lk
                  · exact target_present_dst_empty inp Hva Hve sp_target rnd_target Ha_lo Ha_hi
                      brk_target mb_target Hge3 Hsplain d0 Hs45 Hd45 Hse Hde Hsrc_lk
                | false =>
                  have Hdplain := valid_argv_str_plain inp.in_argv 1 Hva (by omega) Hddot
                  apply fout_omni_strong_equiv
                  · exact source_present inp Hva Hve sp_source rnd_source Hr_lo Hr_hi
                      brk_source mb_source Hge3 Hsplain Hdplain d0 Hs45 Hd45 Hse Hde Hsrc_lk
                  · exact target_present inp Hva Hve sp_target rnd_target Ha_lo Ha_hi
                      brk_target mb_target Hge3 Hsplain Hdplain d0 Hs45 Hd45 Hse Hde Hsrc_lk
          | none =>
            apply fout_omni_strong_equiv
            · exact source_absent inp Hva Hve sp_source rnd_source Hr_lo Hr_hi
                brk_source mb_source Hge3 Hsplain Hs45 Hsrc_lk
            · exact target_absent inp Hva Hve sp_target rnd_target Ha_lo Ha_hi
                brk_target mb_target Hge3 Hsplain Hs45 Hsrc_lk
  · have Hlt3 : inp.in_argv.length < 3 := by omega
    apply cat_omni_strong_equiv_te
    · exact source_wexit_lt3 inp Hva Hve sp_source rnd_source Hr_lo Hr_hi Hlt3
    · exact target_wexit_lt3 inp Hva Hve sp_target rnd_target Ha_lo Ha_hi Hlt3
    · intro b Hb
      exact (List.not_mem_nil Hb).elim

/-- The legacy statement, through the compat `iff`, as pinned by the checker. -/
theorem strong_universal :
    strong_universal_T
      (Image.mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (Image.mkImage Target.loaded_segments Target.init_pc Target.phdrs) :=
  (strong_universal_iff _ _).2 omni_strong_universal

end LinuxProcessSemantics.Examples.headcp_ns.Proof
