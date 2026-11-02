(** * Tests: the extracted checker's input boundary refuses out-of-type values

    These are the tests for [Checks.CheckedInput].  Each one feeds the
    boundary an integer that the Rocq type it would have to inhabit does
    not hold, and shows the answer is [CheckedRefused] — the boundary's
    third answer, which is NOT a verdict — rather than [CheckedAnswer _].
    Beside each refusal is the in-range control that shows the same call
    IS judged when the value is one a machine could produce, so the tests
    cannot pass by refusing everything.

    THE WITNESS.  [witness_effect_2_64] is the effect of record [seq 1] of
    theorem-labs/linux-process-semantics at ff0313ba4f,
    testing/syscall-check/traces/set_tid/022.jsonl, case
    [reject --mutate set_tid_address#2:ret=2^64]: a [set_tid_address]
    (riscv64 syscall 96) whose observed return value is
    18446744073709551616.  The extracted checker gave that record the
    verdict [reject]; a0 is 64 bits wide
    (arch/riscv/include/asm/syscall.h, [syscall_set_return_value], Linux
    v6.18.46, commit 1f99e9ab748f), so no kernel produced it and no
    theorem of this tree covers that verdict.  [witness_effect_ok] is the
    same record's unmutated return, 624. *)

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import CheckedInput.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* The primitive                                                       *)
(* ------------------------------------------------------------------ *)

Example word_2_64_refused : word_of_Z 18446744073709551616 = None.
Proof. vm_compute. reflexivity. Qed.

Example word_max64_accepted :
  option_map bv_unsigned (word_of_Z 18446744073709551615)
  = Some 18446744073709551615.
Proof. vm_compute. reflexivity. Qed.

Example word_negative_refused : word_of_Z (-1) = None.
Proof. vm_compute. reflexivity. Qed.

Example byte_256_refused : byte_of_Z 256 = None.
Proof. vm_compute. reflexivity. Qed.

Example byte_255_accepted :
  option_map bv_unsigned (byte_of_Z 255) = Some 255.
Proof. vm_compute. reflexivity. Qed.

Example byte_negative_refused : byte_of_Z (-1) = None.
Proof. vm_compute. reflexivity. Qed.

Example bv32_refused : bv32_of_Z 4294967296 = None.
Proof. vm_compute. reflexivity. Qed.

Example bv16_refused : bv16_of_Z 65536 = None.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The witness: a return value no 64-bit word holds                    *)
(* ------------------------------------------------------------------ *)

(** set_tid_address(2) as the trace records it: syscall 96, one pointer
    argument, no captured memory and no writable range (the call reads
    and writes nothing). *)
Definition witness_input : RawInput :=
  mkRawInput 96 [274877906944; 0; 0; 0; 0; 0] [] (wmem_ranges []).

Definition witness_effect_2_64 : RawEffect :=
  mkRawEffect 18446744073709551616 [] [] [] [] [].

Definition witness_effect_ok : RawEffect :=
  mkRawEffect 624 [] [] [] [] [].

(** The defect, closed: the boundary refuses, for every model. *)
Example witness_is_refused : forall m,
  check_syscall_for_run_checked witness_input witness_effect_2_64 m
  = CheckedRefused.
Proof. intro m. vm_compute. reflexivity. Qed.

(** And it is refused BEFORE the checker runs: the effect has no
    in-type reading at all. *)
Example witness_effect_has_no_reading :
  effect_of_raw witness_effect_2_64 = None.
Proof. vm_compute. reflexivity. Qed.

(** The control: the same call with the return value the kernel really
    gave is judged, not refused. *)
Example witness_in_range_is_judged : forall m,
  exists a, check_syscall_for_run_checked witness_input witness_effect_ok m
            = CheckedAnswer a.
Proof.
  intro m. unfold check_syscall_for_run_checked.
  destruct (input_of_raw witness_input) as [i|] eqn:Hi;
    [|vm_compute in Hi; discriminate Hi].
  destruct (effect_of_raw witness_effect_ok) as [e|] eqn:He;
    [|vm_compute in He; discriminate He].
  eexists. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* One test per place an out-of-type value can enter a syscall         *)
(* ------------------------------------------------------------------ *)

(* word: the syscall number *)
Example sysno_out_of_range_refused : forall m,
  check_syscall_for_run_checked
    (mkRawInput 18446744073709551616 [] [] (wmem_ranges [])) witness_effect_ok m
  = CheckedRefused.
Proof. intro m. vm_compute. reflexivity. Qed.

(* word: a register argument *)
Example arg_out_of_range_refused : forall m,
  check_syscall_for_run_checked
    (mkRawInput 96 [0; 18446744073709551616] [] (wmem_ranges []))
    witness_effect_ok m
  = CheckedRefused.
Proof. intro m. vm_compute. reflexivity. Qed.

(* word: the address of a captured readable run *)
Example mem_address_out_of_range_refused : forall m,
  check_syscall_for_run_checked
    (mkRawInput 96 [] [(18446744073709551616, [1])] (wmem_ranges []))
    witness_effect_ok m
  = CheckedRefused.
Proof. intro m. vm_compute. reflexivity. Qed.

(* byte: a captured readable byte *)
Example mem_byte_out_of_range_refused : forall m,
  check_syscall_for_run_checked
    (mkRawInput 96 [] [(4096, [0; 256])] (wmem_ranges []))
    witness_effect_ok m
  = CheckedRefused.
Proof. intro m. vm_compute. reflexivity. Qed.

(* The writable view is a PREDICATE, so it has nothing to refuse: its
   result is a [bool] and the address it is asked about is one the
   boundary built.  What is tested instead is that the view it builds
   answers where the reader says it may, and nowhere else. *)
Example wmem_view_follows_the_predicate :
  wmem_view (wmem_ranges [(4096, 16)]) (Z_to_bv 64%N 4100) <> None
  /\ wmem_view (wmem_ranges [(4096, 16)]) (Z_to_bv 64%N 4112) = None.
Proof.
  split.
  - vm_compute. discriminate.
  - vm_compute. reflexivity.
Qed.

(* The readable view, beside it.  [mem_view] builds its map ONCE, outside
   the lambda, so a lookup costs the width of the address and not the
   captured bytes; this is what the lifted form must still ANSWER.  Two
   runs overlap here on purpose: the EARLIER run wins at 4096, which is
   the one thing a lift that re-ordered the build would get wrong, and
   the abstract
   [CheckedInput.mem_view_is_get_of_mem_of_runs] cannot see because it
   compares the two forms rather than computing either. *)
Example mem_view_answers_where_the_runs_say :
  match runs_of_Z [(4096, [7; 8]); (4096, [9])] with
  | Some runs =>
      option_map bv_unsigned (mem_view runs (Z_to_bv 64%N 4096)) = Some 7
      /\ option_map bv_unsigned (mem_view runs (Z_to_bv 64%N 4097)) = Some 8
      /\ option_map bv_unsigned (mem_view runs (Z_to_bv 64%N 4098)) = None
  | None => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* byte: a byte the kernel is said to have written *)
Example write_byte_out_of_range_refused : forall m,
  check_syscall_for_run_checked witness_input
    (mkRawEffect 0 [(4096, [256])] [] [] [] []) m
  = CheckedRefused.
Proof. intro m. vm_compute. reflexivity. Qed.

(* word: a zero-filled range *)
Example zeros_out_of_range_refused : forall m,
  check_syscall_for_run_checked witness_input
    (mkRawEffect 0 [] [(18446744073709551616, 4096)] [] [] []) m
  = CheckedRefused.
Proof. intro m. vm_compute. reflexivity. Qed.

(* word: an unmapped range *)
Example unmaps_out_of_range_refused : forall m,
  check_syscall_for_run_checked witness_input
    (mkRawEffect 0 [] [] [(0, 18446744073709551616)] [] []) m
  = CheckedRefused.
Proof. intro m. vm_compute. reflexivity. Qed.

(* word: a symbolic copy *)
Example copies_out_of_range_refused : forall m,
  check_syscall_for_run_checked witness_input
    (mkRawEffect 0 [] [] [] [(0, 0, 18446744073709551616)] []) m
  = CheckedRefused.
Proof. intro m. vm_compute. reflexivity. Qed.

(* word, and the nat beside it: a copy-in ledger entry *)
Example copyin_address_out_of_range_refused : forall m,
  check_syscall_for_run_checked witness_input
    (mkRawEffect 0 [] [] [] [] [(18446744073709551616, 8)]) m
  = CheckedRefused.
Proof. intro m. vm_compute. reflexivity. Qed.

Example copyin_negative_length_refused : forall m,
  check_syscall_for_run_checked witness_input
    (mkRawEffect 0 [] [] [] [] [(4096, -1)]) m
  = CheckedRefused.
Proof. intro m. vm_compute. reflexivity. Qed.

(* the in-range controls for the effect components *)
Example effect_components_in_range_are_judged : forall m,
  exists a, check_syscall_for_run_checked witness_input
              (mkRawEffect 0 [(4096, [255])] [(4096, 4096)] [(8192, 4096)]
                 [(0, 4096, 8)] [(4096, 8)]) m
            = CheckedAnswer a.
Proof.
  intro m. unfold check_syscall_for_run_checked.
  destruct (input_of_raw witness_input) as [i|] eqn:Hi;
    [|vm_compute in Hi; discriminate Hi].
  destruct (effect_of_raw _) as [e|] eqn:He;
    [|vm_compute in He; discriminate He].
  eexists. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* One test per place an out-of-type value can enter the model's seed  *)
(* ------------------------------------------------------------------ *)

(** [State.default_kernel] in the raw vocabulary: a kernel built
    without transparent huge pages, vDSO image 1, randomizing, the
    256-page [stack_guard_gap], no extra [vm.mmap_rnd_bits],
    CONFIG_RSEQ, no vector unit, and the four cache leaves absent.
    [[97]] is [State.default_execfn], the one-byte relative name "a",
    which [Run.valid_execfn] admits. *)
Definition raw_leaf_absent : RawCacheLeaf := mkRawCacheLeaf false 0 0 0.
Definition raw_cache_absent : RawCacheView :=
  mkRawCacheView raw_leaf_absent raw_leaf_absent raw_leaf_absent
    raw_leaf_absent.
Definition raw_kernel_default : RawKernelBuild :=
  mkRawKernelBuild false 1 true 256 0 true 0 raw_cache_absent.

Definition raw_seed : RawProcInput :=
  mkRawProcInput [] [] [] [] 0 0 [] [] 1024 0 4397 false Sv48 [] []
    raw_kernel_default [97] true true false.

Example seed_is_accepted :
  exists m, init_model_checked [] 4096 4096 4096 0 raw_seed = Some m.
Proof.
  unfold init_model_checked.
  destruct (pairs_of_Z []) eqn:E1; [|vm_compute in E1; discriminate E1].
  destruct (word_of_Z 4096) eqn:E2; [|vm_compute in E2; discriminate E2].
  destruct (proc_input_of_raw raw_seed) eqn:E3;
    [|vm_compute in E3; discriminate E3].
  eexists. reflexivity.
Qed.

(* word: the reserved segments, the break, the mmap base, the stack *)
Example seed_reserved_out_of_range_refused :
  init_model_checked [(18446744073709551616, 4096)] 4096 4096 4096 0 raw_seed
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_brk_out_of_range_refused :
  init_model_checked [] 18446744073709551616 4096 4096 0 raw_seed = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_mmap_base_out_of_range_refused :
  init_model_checked [] 4096 18446744073709551616 4096 0 raw_seed = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_sp_out_of_range_refused :
  init_model_checked [] 4096 4096 18446744073709551616 0 raw_seed = None.
Proof. vm_compute. reflexivity. Qed.

(* word: the credentials and the launch limits *)
Example seed_uid_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] [] [] 18446744073709551616 0 [] [] 1024 0 4397
       false Sv48 [] [] raw_kernel_default [97] true true false) = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_group_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] [] [] 0 0 [18446744073709551616] [] 1024 0 4397
       false Sv48 [] [] raw_kernel_default [97] true true false) = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_nofile_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] [] [] 0 0 [] [] 18446744073709551616 0 4397
       false Sv48 [] [] raw_kernel_default [97] true true false) = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_sigmask_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] [] [] 0 0 [] [] 1024 18446744073709551616 4397
       false Sv48 [] [] raw_kernel_default [97] true true false) = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_hwcap_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] [] [] 0 0 [] [] 1024 0 18446744073709551616
       false Sv48 [] [] raw_kernel_default [97] true true false) = None.
Proof. vm_compute. reflexivity. Qed.

(* byte: argv, envp, the file system, standard input, the random device *)
Example seed_argv_byte_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [[256]] [] [] [] 0 0 [] [] 1024 0 4397 false Sv48 [] []
       raw_kernel_default [97] true true false)
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_envp_byte_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [[256]] [] [] 0 0 [] [] 1024 0 4397 false Sv48 [] []
       raw_kernel_default [97] true true false)
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_fs_byte_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] [([97], [256])] [] 0 0 [] [] 1024 0 4397
       false Sv48 [] [] raw_kernel_default [97] true true false) = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_stdin_byte_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] [] [256] 0 0 [] [] 1024 0 4397 false Sv48 [] []
       raw_kernel_default [97] true true false)
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_urandom_byte_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] [] [] 0 0 [] [] 1024 0 4397 false Sv48 [256] []
       raw_kernel_default [97] true true false)
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_tmp_byte_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] [] [] 0 0 [] [] 1024 0 4397 false Sv48 []
       [([97], [256])] raw_kernel_default [97] true true false) = None.
Proof. vm_compute. reflexivity. Qed.

(* bv 32 and bv 16: a network peer's address and port *)
Example seed_peer_addr_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] [] [] 0 0 []
       [mkRawPeer 4294967296 80 [] RneFin] 1024 0 4397 false Sv48 [] []
       raw_kernel_default [97] true true false)
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_peer_port_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] [] [] 0 0 []
       [mkRawPeer 0 65536 [] RneFin] 1024 0 4397 false Sv48 [] []
       raw_kernel_default [97] true true false)
  = None.
Proof. vm_compute. reflexivity. Qed.

(* byte: what a peer says *)
Example seed_peer_byte_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] [] [] 0 0 []
       [mkRawPeer 0 80 [256] RneFin] 1024 0 4397 false Sv48 [] []
       raw_kernel_default [97] true true false)
  = None.
Proof. vm_compute. reflexivity. Qed.

(** A machine, rather than the absent default: transparent huge pages,
    vDSO image 3, randomizing, a one-page guard gap, 20 bits of mmap
    randomization, CONFIG_RSEQ, a 128-bit vector unit, and four cache
    leaves the L3 of which ACPI PPTT reported.  [[47; 97]] is the exec
    file name "/a". *)
Definition raw_kernel_live : RawKernelBuild :=
  mkRawKernelBuild true 3 true 1 20 true 4
    (mkRawCacheView (mkRawCacheLeaf false 32768 8 64)
                    (mkRawCacheLeaf false 32768 8 64)
                    (mkRawCacheLeaf false 1048576 8 64)
                    (mkRawCacheLeaf true 33554432 16 64)).

(* the in-range control for the seed's structured fields *)
Definition raw_seed_full : RawProcInput :=
  mkRawProcInput [[112; 0]] [[65; 0]] [([97], [1; 255])] [0; 255] 1000 1000
    [1000] [mkRawPeer 2130706433 80 [255] RneRst] 1024 0 4397 false Sv48
    [7] [([98], [2])] raw_kernel_live [47; 97] true true false.

Example seed_structured_fields_in_range_accepted :
  exists m, init_model_checked [(4096, 4096)] 8192 12288 16384 65536
              raw_seed_full = Some m.
Proof.
  unfold init_model_checked.
  destruct (pairs_of_Z [(4096, 4096)]) eqn:E1; [|vm_compute in E1; discriminate E1].
  destruct (word_of_Z 8192) eqn:E2; [|vm_compute in E2; discriminate E2].
  destruct (word_of_Z 12288) eqn:E3; [|vm_compute in E3; discriminate E3].
  destruct (word_of_Z 16384) eqn:E4; [|vm_compute in E4; discriminate E4].
  destruct (proc_input_of_raw raw_seed_full) eqn:E5;
    [|vm_compute in E5; discriminate E5].
  eexists. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The kernel build and the exec file name: each refusal beside the    *)
(* neighbouring value the boundary still converts                      *)
(* ------------------------------------------------------------------ *)

(** The seed with the kernel build or the exec file name replaced, so
    that each pair below differs in exactly the value under test. *)
Definition seed_with_kernel (k : RawKernelBuild) : RawProcInput :=
  mkRawProcInput [] [] [] [] 0 0 [] [] 1024 0 4397 false Sv48 [] [] k [97]
    true true false.
Definition seed_with_execfn (fn : list Z) : RawProcInput :=
  mkRawProcInput [] [] [] [] 0 0 [] [] 1024 0 4397 false Sv48 [] []
    raw_kernel_default fn true true false.

(* [N]: which vDSO image the build carries *)
Example seed_kernel_vdso_negative_refused :
  init_model_checked [] 4096 4096 4096 0
    (seed_with_kernel
       (mkRawKernelBuild false (-1) true 256 0 true 0 raw_cache_absent))
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_kernel_vdso_zero_converted :
  option_map in_kernel
    (proc_input_of_raw
       (seed_with_kernel
          (mkRawKernelBuild false 0 true 256 0 true 0 raw_cache_absent)))
  = Some (mkKernelBuild false 0%N true 256%N 0%N true 0%N cache_view_absent).
Proof. reflexivity. Qed.

(* [N]: the [stack_guard_gap] boot parameter, in pages *)
Example seed_kernel_guard_negative_refused :
  init_model_checked [] 4096 4096 4096 0
    (seed_with_kernel
       (mkRawKernelBuild false 1 true (-1) 0 true 0 raw_cache_absent))
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_kernel_guard_zero_converted :
  option_map in_kernel
    (proc_input_of_raw
       (seed_with_kernel
          (mkRawKernelBuild false 1 true 0 0 true 0 raw_cache_absent)))
  = Some (mkKernelBuild false 1%N true 0%N 0%N true 0%N cache_view_absent).
Proof. reflexivity. Qed.

(* [N]: vm.mmap_rnd_bits *)
Example seed_kernel_rnd_bits_negative_refused :
  init_model_checked [] 4096 4096 4096 0
    (seed_with_kernel
       (mkRawKernelBuild false 1 true 256 (-1) true 0 raw_cache_absent))
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_kernel_rnd_bits_zero_converted :
  option_map in_kernel
    (proc_input_of_raw
       (seed_with_kernel
          (mkRawKernelBuild false 1 true 256 0 true 0 raw_cache_absent)))
  = Some (mkKernelBuild false 1%N true 256%N 0%N true 0%N cache_view_absent).
Proof. reflexivity. Qed.

(* [N]: the vector unit's VLENB *)
Example seed_kernel_vlenb_negative_refused :
  init_model_checked [] 4096 4096 4096 0
    (seed_with_kernel
       (mkRawKernelBuild false 1 true 256 0 true (-1) raw_cache_absent))
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_kernel_vlenb_four_converted :
  option_map in_kernel
    (proc_input_of_raw
       (seed_with_kernel
          (mkRawKernelBuild false 1 true 256 0 true 4 raw_cache_absent)))
  = Some (mkKernelBuild false 1%N true 256%N 0%N true 4%N cache_view_absent).
Proof. reflexivity. Qed.

(* [N]: one of the twelve numbers of the four cache leaves *)
Example seed_kernel_cache_assoc_negative_refused :
  init_model_checked [] 4096 4096 4096 0
    (seed_with_kernel
       (mkRawKernelBuild false 1 true 256 0 true 0
          (mkRawCacheView raw_leaf_absent raw_leaf_absent
             (mkRawCacheLeaf false 1048576 (-1) 64) raw_leaf_absent)))
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_kernel_cache_assoc_zero_converted :
  option_map in_kernel
    (proc_input_of_raw
       (seed_with_kernel
          (mkRawKernelBuild false 1 true 256 0 true 0
             (mkRawCacheView raw_leaf_absent raw_leaf_absent
                (mkRawCacheLeaf false 1048576 0 64) raw_leaf_absent))))
  = Some (mkKernelBuild false 1%N true 256%N 0%N true 0%N
            (mkCacheView cache_leaf_absent cache_leaf_absent
               (mkCacheLeaf false 1048576%N 0%N 64%N) cache_leaf_absent)).
Proof. reflexivity. Qed.

(* the exec file name: the empty name [getname_flags] refuses with
   -ENOENT, and the one-byte name beside it *)
Example seed_execfn_empty_refused :
  init_model_checked [] 4096 4096 4096 0 (seed_with_execfn []) = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_execfn_one_byte_converted :
  option_map (fun inp => map bv_unsigned (in_execfn inp))
    (proc_input_of_raw (seed_with_execfn [97])) = Some [97].
Proof. reflexivity. Qed.

(* a NUL byte, which [strncpy_from_user] stops at, so no name carries
   one, and the same name with a byte that is not NUL *)
Example seed_execfn_nul_refused :
  init_model_checked [] 4096 4096 4096 0
    (seed_with_execfn [47; 0; 97]) = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_execfn_no_nul_converted :
  option_map (fun inp => map bv_unsigned (in_execfn inp))
    (proc_input_of_raw (seed_with_execfn [47; 1; 97])) = Some [47; 1; 97].
Proof. reflexivity. Qed.

(* byte: a value no [byte] holds, beside the largest one that does *)
Example seed_execfn_byte_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (seed_with_execfn [47; 256]) = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_execfn_byte_255_converted :
  option_map (fun inp => map bv_unsigned (in_execfn inp))
    (proc_input_of_raw (seed_with_execfn [47; 255])) = Some [47; 255].
Proof. reflexivity. Qed.

(* the length bound: PATH_MAX counting the NUL, so 4095 bytes is a
   name [getname_flags] can return and 4096 is not *)
Example seed_execfn_4096_bytes_refused :
  init_model_checked [] 4096 4096 4096 0
    (seed_with_execfn (repeat 97 4096%nat)) = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_execfn_4095_bytes_converted :
  option_map (fun inp => Z.of_nat (length (in_execfn inp)))
    (proc_input_of_raw (seed_with_execfn (repeat 97 4095%nat)))
  = Some 4095.
Proof. vm_compute. reflexivity. Qed.

(** AND THE ONE NAME THE BOUNDARY REFUSES THAT THE MODEL ADMITS: the
    descriptor form "/dev/fd/3/" and a 4088-byte relative name is 4098
    bytes, which [Run.valid_execfn]'s third disjunct admits and
    [Run.valid_path_name] does not.  It is refused, and the refusal is
    the third answer rather than a verdict; [CheckedInput]'s
    [execfn_of_Z] says why that is the safe direction.  Beside it the
    same shape at 4095 bytes, which the boundary converts. *)
Example seed_execfn_long_dev_fd_refused :
  init_model_checked [] 4096 4096 4096 0
    (seed_with_execfn
       ([47; 100; 101; 118; 47; 102; 100; 47; 51; 47] ++ repeat 97 4088%nat))
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_execfn_short_dev_fd_converted :
  option_map (fun inp => Z.of_nat (length (in_execfn inp)))
    (proc_input_of_raw
       (seed_with_execfn
          ([47; 100; 101; 118; 47; 102; 100; 47; 51; 47]
           ++ repeat 97 4085%nat)))
  = Some 4095.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The file-system image: the one that describes no file system, and   *)
(* the neighbour the boundary still converts                           *)
(* ------------------------------------------------------------------ *)

(** [revision/linux-only] added [Fs.fs_image_real] to
    [Run.valid_input] over [State.in_image_fs]; the boundary enforces
    it here, and this pair is what says the enforcement is not
    vacuous.  [fs_image_real] is a [bool], so a test that read the
    wrong thing would still type-check and still answer: only an
    image it must refuse beside an image it must convert shows which
    test was written.

    "a" and "a/b": the first key is a regular file and the second
    says the same name is the directory "b" lives under.  No Linux
    file system holds both -- one name in one directory is one inode
    -- and the model would answer a read open with the regular file
    while a write-create answered EISDIR.  It is
    [Checks.Cases.Fs.Open.prefix_key_image] in the raw vocabulary.
    Beside it "a" and "ab", which differ in one byte of the second
    key and name two files. *)
Definition seed_with_image (img : list (list Z * list Z)) : RawProcInput :=
  mkRawProcInput [] [] img [] 0 0 [] [] 1024 0 4397 false Sv48 [] []
    raw_kernel_default [97] true true false.

Definition raw_image_prefix_key : list (list Z * list Z) :=
  [([97], [104]); ([97; 47; 98], [104])].
Definition raw_image_flat_keys : list (list Z * list Z) :=
  [([97], [104]); ([97; 98], [104])].

Example seed_unreal_image_refused :
  init_model_checked [] 4096 4096 4096 0
    (seed_with_image raw_image_prefix_key) = None.
Proof. vm_compute. reflexivity. Qed.

(** And WHICH refusal it is, which is what the published root answers:
    the image is a VALUE -- every byte of it is a [byte], so
    [fs_of_raw] converts it -- and it is no launch. *)
Example seed_unreal_image_is_a_value :
  option_map (fun fs => map (fun pf => map bv_unsigned (fst pf)) fs)
    (fs_of_raw raw_image_prefix_key) = Some [[97]; [97; 47; 98]].
Proof. vm_compute. reflexivity. Qed.

Example seed_unreal_image_is_no_launch :
  image_shape_b raw_image_prefix_key = false.
Proof. vm_compute. reflexivity. Qed.

Example seed_flat_image_is_a_launch :
  image_shape_b raw_image_flat_keys = true.
Proof. vm_compute. reflexivity. Qed.

(** The neighbour, converted, with the seed's [State.in_image_fs] read
    back out: the two keys and their contents, in the model's sorted
    order. *)
Example seed_flat_image_converted :
  option_map
    (fun inp => map (fun pf => (map bv_unsigned (fst pf),
                                map bv_unsigned (snd pf)))
                  (in_image_fs inp))
    (proc_input_of_raw (seed_with_image raw_image_flat_keys))
  = Some [([97], [104]); ([97; 98], [104])].
Proof. vm_compute. reflexivity. Qed.

(** A key that is not canonical is refused by the same clause and
    converted by [fs_of_raw] just as readily: "./a" names the file
    "a", which the flat map would keep as a file of its own. *)
Example seed_noncanonical_image_refused :
  init_model_checked [] 4096 4096 4096 0
    (seed_with_image [([46; 47; 97], [104])]) = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_canonical_image_converted :
  option_map
    (fun inp => map (fun pf => (map bv_unsigned (fst pf),
                                map bv_unsigned (snd pf)))
                  (in_image_fs inp))
    (proc_input_of_raw (seed_with_image [([97], [104])]))
  = Some [([97], [104])].
Proof. vm_compute. reflexivity. Qed.

(** The /tmp declaration beside it, which carries NO reality
    condition in [Run] -- [State.fs_seed_tmp] seeds it into
    [State.in_fs] under absolute keys and no clause constrains the
    declaration -- so the same nesting the image is refused for is
    converted there. *)
Example seed_nested_tmp_converted :
  exists m, init_model_checked [] 4096 4096 4096 0
              (mkRawProcInput [] [] [] [] 0 0 [] [] 1024 0 4397 false Sv48 []
                 [([97], [104]); ([97; 47; 98], [104])]
                 raw_kernel_default [97] true true false) = Some m.
Proof.
  unfold init_model_checked.
  destruct (pairs_of_Z []) eqn:E1; [|vm_compute in E1; discriminate E1].
  destruct (word_of_Z 4096) eqn:E2; [|vm_compute in E2; discriminate E2].
  destruct (proc_input_of_raw _) eqn:E3; [|vm_compute in E3; discriminate E3].
  eexists. reflexivity.
Qed.
