import LinuxProcessSemantics.Examples.cp_ns.cp_ns_source
import LinuxProcessSemantics.Examples.cp_ns.cp_ns_target
import LinuxProcessSemantics.Common.FileSim.Glue

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! Top-level glue for `theories/Examples/cp_ns/Proof.v`. The entry draws
are independent. The huge-content case uses trace equivalence and absence
of errors rather than termination; coverage remains part of the conclusion. -/

namespace LinuxProcessSemantics.Examples.cp_ns.Proof

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.OmniRun
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.FileSim
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
open LinuxProcessSemantics.Examples.cp_ns.SourceMemImage
open LinuxProcessSemantics.Examples.cp_ns.TargetMemImage
open LinuxProcessSemantics.Examples.cp_ns.cp_ns_code
open LinuxProcessSemantics.Examples.cp_ns.cp_ns_defs
open LinuxProcessSemantics.Examples.cp_ns.cp_ns_source
open LinuxProcessSemantics.Examples.cp_ns.cp_ns_target

theorem omni_strong_universal : omni_strong_universal_T Source.image Target.image := by
  intro es et inp hs ht hi
  cases es with
  | mkEntry sp_source brk_source mb_source rnd_source =>
  cases et with
  | mkEntry sp_target brk_target mb_target rnd_target =>
  have hsv48 := valid_input_va_size inp hi
  have hs' := (valid_entry_sv48 _ _ _ hsv48).1 hs
  have ht' := (valid_entry_sv48 _ _ _ hsv48).1 ht
  have Hva := hi.1
  have Hve := hi.2.1
  have Hr_lo := hs'.1.1
  have Hr_hi := hs'.1.2.1
  have Ha_lo := ht'.1.1
  have Ha_hi := ht'.1.2.1
  by_cases Hge3 : 3 ≤ inp.in_argv.length
  · by_cases Hsrc_big : 4096 ≤ (inp.in_argv.getD 1 []).length
    · apply fout_omni_strong_equiv
      · exact source_src_toolong inp Hva Hve sp_source rnd_source Hr_lo Hr_hi
          brk_source mb_source Hge3 Hsrc_big
      · exact target_src_toolong inp Hva Hve sp_target rnd_target Ha_lo Ha_hi
          brk_target mb_target Hge3 Hsrc_big
    · have Hs45 : (inp.in_argv.getD 1 []).length ≤ 4095 := by omega
      by_cases Hse : path_eqb (inp.in_argv.getD 1 []) [] = true
      · apply fout_omni_strong_equiv
        · exact source_src_empty inp Hva Hve sp_source rnd_source Hr_lo Hr_hi
            brk_source mb_source Hge3 Hs45 Hse
        · exact target_src_empty inp Hva Hve sp_target rnd_target Ha_lo Ha_hi
            brk_target mb_target Hge3 Hs45 Hse
      · have Hse : path_eqb (inp.in_argv.getD 1 []) [] = false := by simpa using Hse
        by_cases Hsdot : path_eqb (inp.in_argv.getD 1 []) dot_path = true
        · by_cases Hdst_big : 4096 ≤ (inp.in_argv.getD 2 []).length
          · apply fout_omni_strong_equiv
            · exact source_src_dot_dst_toolong inp Hva Hve sp_source rnd_source
                Hr_lo Hr_hi brk_source mb_source Hge3 Hsdot Hdst_big
            · exact target_src_dot_dst_toolong inp Hva Hve sp_target rnd_target
                Ha_lo Ha_hi brk_target mb_target Hge3 Hsdot Hdst_big
          · have Hd45 : (inp.in_argv.getD 2 []).length ≤ 4095 := by omega
            by_cases Hde : path_eqb (inp.in_argv.getD 2 []) [] = true
            · apply fout_omni_strong_equiv
              · exact source_src_dot_dstempty inp Hva Hve sp_source rnd_source
                  Hr_lo Hr_hi brk_source mb_source Hge3 Hsdot Hde
              · exact target_src_dot_dstempty inp Hva Hve sp_target rnd_target
                  Ha_lo Ha_hi brk_target mb_target Hge3 Hd45 Hsdot Hde
            · have Hde : path_eqb (inp.in_argv.getD 2 []) [] = false := by simpa using Hde
              by_cases Hddot : path_eqb (inp.in_argv.getD 2 []) dot_path = true
              · apply fout_omni_strong_equiv
                · exact source_src_dot_dstdot inp Hva Hve sp_source rnd_source
                    Hr_lo Hr_hi brk_source mb_source Hge3 Hsdot Hddot
                · exact target_src_dot_dstdot inp Hva Hve sp_target rnd_target
                    Ha_lo Ha_hi brk_target mb_target Hge3 Hd45 Hsdot Hddot
              · have Hddot := valid_argv_str_plain inp.in_argv 1 Hva (by omega)
                  (by simpa using Hddot)
                apply fout_omni_strong_equiv
                · exact source_src_dot_normal inp Hva Hve sp_source rnd_source
                    Hr_lo Hr_hi brk_source mb_source Hge3 Hsdot Hd45 Hde Hddot
                · exact target_src_dot_normal inp Hva Hve sp_target rnd_target
                    Ha_lo Ha_hi brk_target mb_target Hge3 Hd45 Hsdot Hde Hddot
        · have Hsdot := valid_argv_str_plain inp.in_argv 0 Hva (by omega)
            (by simpa using Hsdot)
          cases Hsrc_lk : fs_lookup inp.in_fs (inp.in_argv.getD 1 []) with
          | none =>
            apply fout_omni_strong_equiv
            · exact source_absent inp Hva Hve sp_source rnd_source Hr_lo Hr_hi
                brk_source mb_source Hge3 Hsdot Hs45 Hsrc_lk
            · exact target_absent inp Hva Hve sp_target rnd_target Ha_lo Ha_hi
                brk_target mb_target Hge3 Hsdot Hs45 Hsrc_lk
          | some d0 =>
            by_cases Hdst_big : 4096 ≤ (inp.in_argv.getD 2 []).length
            · apply fout_omni_strong_equiv
              · exact source_present_dst_toolong inp Hva Hve sp_source rnd_source
                  Hr_lo Hr_hi brk_source mb_source Hge3 Hsdot d0 Hs45 Hdst_big Hse Hsrc_lk
              · exact target_present_dst_toolong inp Hva Hve sp_target rnd_target
                  Ha_lo Ha_hi brk_target mb_target Hge3 Hsdot d0 Hs45 Hdst_big Hse Hsrc_lk
            · have Hd45 : (inp.in_argv.getD 2 []).length ≤ 4095 := by omega
              by_cases Hde : path_eqb (inp.in_argv.getD 2 []) [] = true
              · apply fout_omni_strong_equiv
                · exact source_present_dst_empty inp Hva Hve sp_source rnd_source
                    Hr_lo Hr_hi brk_source mb_source Hge3 Hsdot d0 Hs45 Hd45 Hse Hde Hsrc_lk
                · exact target_present_dst_empty inp Hva Hve sp_target rnd_target
                    Ha_lo Ha_hi brk_target mb_target Hge3 Hsdot d0 Hs45 Hd45 Hse Hde Hsrc_lk
              · have Hde : path_eqb (inp.in_argv.getD 2 []) [] = false := by simpa using Hde
                by_cases Hddot : path_eqb (inp.in_argv.getD 2 []) dot_path = true
                · apply fout_omni_strong_equiv
                  · exact source_present_dst_dot inp Hva Hve sp_source rnd_source
                      Hr_lo Hr_hi brk_source mb_source Hge3 Hsdot d0 Hs45 Hd45 Hse Hddot Hsrc_lk
                  · exact target_present_dst_dot inp Hva Hve sp_target rnd_target
                      Ha_lo Ha_hi brk_target mb_target Hge3 Hsdot d0 Hs45 Hd45 Hse Hddot Hsrc_lk
                · have Hddot := valid_argv_str_plain inp.in_argv 1 Hva (by omega)
                    (by simpa using Hddot)
                  by_cases Hrep : ((cp_read_data inp.in_fs (inp.in_argv.getD 1 [])
                      (inp.in_argv.getD 2 [])).length : Int) < 2^64
                  · apply fout_omni_strong_equiv
                    · exact source_present inp Hva Hve sp_source rnd_source Hr_lo Hr_hi
                        brk_source mb_source Hge3 Hsdot Hddot d0 Hs45 Hd45 Hse Hde Hsrc_lk Hrep
                    · exact target_present inp Hva Hve sp_target rnd_target Ha_lo Ha_hi
                        brk_target mb_target Hge3 Hsdot Hddot d0 Hs45 Hd45 Hse Hde Hsrc_lk Hrep
                  · have Hbig : (2^64 : Int) ≤ ((cp_read_data inp.in_fs
                        (inp.in_argv.getD 1 []) (inp.in_argv.getD 2 [])).length : Int) := by omega
                    have Hneq := cp_read_data_big_neq inp.in_fs (inp.in_argv.getD 1 [])
                      (inp.in_argv.getD 2 []) Hbig
                    have Hbig0 : (2^64 : Int) ≤ (d0.length : Int) := by
                      rw [cp_read_data_neq _ _ _ d0 Hneq Hsrc_lk] at Hbig
                      exact Hbig
                    constructor
                    · apply (covered_iff _ _).1
                      apply no_error_no_unmodeled
                      exact source_huge_no_error inp Hva Hve sp_source rnd_source
                        Hr_lo Hr_hi brk_source mb_source Hge3 Hsdot Hddot d0
                        Hs45 Hd45 Hneq Hsrc_lk Hbig0 Hse Hde
                    · apply Or.inr
                      constructor
                      · apply (trace_equiv_iff_omni _ _ _ _ _ _ _).1
                        intro tr
                        exact (source_huge_obs inp Hva Hve sp_source rnd_source Hr_lo Hr_hi
                          brk_source mb_source Hge3 Hsdot Hddot d0 Hs45 Hd45 Hneq
                          Hsrc_lk Hbig0 Hse Hde tr).trans
                          (target_huge_obs inp Hva Hve sp_target rnd_target Ha_lo Ha_hi
                            brk_target mb_target Hge3 Hsdot Hddot d0 Hs45 Hd45 Hneq
                            Hsrc_lk Hbig0 Hse Hde tr).symm
                      · apply (bh_errors_iff _ _ _ _).1
                        exact target_huge_no_error inp Hva Hve sp_target rnd_target Ha_lo Ha_hi
                          brk_target mb_target Hge3 Hsdot Hddot d0 Hs45 Hd45 Hneq
                          Hsrc_lk Hbig0 Hse Hde
  · apply cat_omni_strong_equiv_te
      source_segs SourceMemImage_init_pc SourceMemImage_phdrs
      sp_source brk_source mb_source rnd_source
      target_segs TargetMemImage_init_pc TargetMemImage_phdrs
      sp_target brk_target mb_target rnd_target
      [] (Z_to_bv 64 2) inp
    · exact source_wexit_lt3 inp Hva Hve sp_source rnd_source Hr_lo Hr_hi (by omega)
    · exact target_wexit_lt3 inp Hva Hve sp_target rnd_target Ha_lo Ha_hi (by omega)
    · intro b hb
      exact False.elim (List.not_mem_nil hb)

theorem strong_universal : strong_universal_T Source.image Target.image :=
  (strong_universal_iff Source.image Target.image).2 omni_strong_universal

theorem specification : SPEC Source.image Target.image := ⟨strong_universal⟩
theorem omni_specification : OMNI_SPEC Source.image Target.image := ⟨omni_strong_universal⟩

end LinuxProcessSemantics.Examples.cp_ns.Proof
