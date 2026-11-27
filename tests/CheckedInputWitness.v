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
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
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
    CONFIG_RSEQ, no vector unit, the four cache leaves absent, a
    224-byte [struct sk_buff], and the [net.core] buffer sysctls at
    their defaults ([wmem_default] and [rmem_default] 212992,
    [wmem_max] and [rmem_max] 4194304).
    [[97]] is [State.default_execfn], the one-byte relative name "a",
    which [Run.valid_execfn] admits. *)
Definition raw_leaf_absent : RawCacheLeaf := mkRawCacheLeaf false 0 0 0.
Definition raw_cache_absent : RawCacheView :=
  mkRawCacheView raw_leaf_absent raw_leaf_absent raw_leaf_absent
    raw_leaf_absent.
Definition raw_kernel_default : RawKernelBuild :=
  mkRawKernelBuild false 1 true 256 0 true 0 raw_cache_absent
    224 212992 212992 4194304 4194304.

(** The standard root at the default working directory, in the raw
    vocabulary: "/", "/dev", the two devices, "/tmp" and "/work".  A
    launch needs it: [Run.valid_image] asks for the five standard
    entries and for the working directory to be a folder of the
    image. *)
Definition raw_work : list Z := [47; 119; 111; 114; 107].
Definition raw_std_image : list (list Z * RawEntry) :=
  [([47], RawDir); ([47; 100; 101; 118], RawDir);
   ([47; 100; 101; 118; 47; 110; 117; 108; 108], RawDevNull);
   ([47; 100; 101; 118; 47; 117; 114; 97; 110; 100; 111; 109], RawDevUrandom);
   ([47; 116; 109; 112], RawDir); (raw_work, RawDir)].

Definition raw_seed : RawProcInput :=
  mkRawProcInput [] [] raw_std_image raw_work [] 0 0 [] [] 1024 0 4397 false Sv48 []
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
    (mkRawProcInput [] [] raw_std_image raw_work [] 18446744073709551616 0 [] [] 1024 0 4397
       false Sv48 [] raw_kernel_default [97] true true false) = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_group_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] raw_std_image raw_work [] 0 0 [18446744073709551616] [] 1024 0 4397
       false Sv48 [] raw_kernel_default [97] true true false) = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_nofile_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] raw_std_image raw_work [] 0 0 [] [] 18446744073709551616 0 4397
       false Sv48 [] raw_kernel_default [97] true true false) = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_sigmask_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] raw_std_image raw_work [] 0 0 [] [] 1024 18446744073709551616 4397
       false Sv48 [] raw_kernel_default [97] true true false) = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_hwcap_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] raw_std_image raw_work [] 0 0 [] [] 1024 0 18446744073709551616
       false Sv48 [] raw_kernel_default [97] true true false) = None.
Proof. vm_compute. reflexivity. Qed.

(* byte: argv, envp, the file system, standard input, the random device *)
Example seed_argv_byte_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [[256]] [] raw_std_image raw_work [] 0 0 [] [] 1024 0 4397 false Sv48 []
       raw_kernel_default [97] true true false)
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_envp_byte_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [[256]] raw_std_image raw_work [] 0 0 [] [] 1024 0 4397 false Sv48 []
       raw_kernel_default [97] true true false)
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_fs_byte_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] (raw_std_image ++ [(raw_work ++ [47; 97], RawFile [256])])
       raw_work [] 0 0 [] [] 1024 0 4397
       false Sv48 [] raw_kernel_default [97] true true false) = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_stdin_byte_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] raw_std_image raw_work [256] 0 0 [] [] 1024 0 4397 false Sv48 []
       raw_kernel_default [97] true true false)
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_urandom_byte_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] raw_std_image raw_work [] 0 0 [] [] 1024 0 4397 false Sv48 [256]
       raw_kernel_default [97] true true false)
  = None.
Proof. vm_compute. reflexivity. Qed.

(** A byte out of range in a file under /tmp, which is a folder of the
    image like any other. *)
Example seed_tmp_byte_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] []
       (raw_std_image ++ [([47; 116; 109; 112; 47; 97], RawFile [256])])
       raw_work [] 0 0 [] [] 1024 0 4397 false Sv48 []
       raw_kernel_default [97] true true false) = None.
Proof. vm_compute. reflexivity. Qed.

(* bv 32 and bv 16: a network peer's address and port *)
Example seed_peer_addr_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] raw_std_image raw_work [] 0 0 []
       [mkRawPeer 4294967296 80 [] RneFin] 1024 0 4397 false Sv48 []
       raw_kernel_default [97] true true false)
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_peer_port_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] raw_std_image raw_work [] 0 0 []
       [mkRawPeer 0 65536 [] RneFin] 1024 0 4397 false Sv48 []
       raw_kernel_default [97] true true false)
  = None.
Proof. vm_compute. reflexivity. Qed.

(* byte: what a peer says *)
Example seed_peer_byte_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] raw_std_image raw_work [] 0 0 []
       [mkRawPeer 0 80 [256] RneFin] 1024 0 4397 false Sv48 []
       raw_kernel_default [97] true true false)
  = None.
Proof. vm_compute. reflexivity. Qed.

(** A machine, rather than the absent default: transparent huge pages,
    vDSO image 3, randomizing, a one-page guard gap, 20 bits of mmap
    randomization, CONFIG_RSEQ, a 128-bit vector unit, four cache
    leaves the L3 of which ACPI PPTT reported, a 256-byte
    [struct sk_buff], and buffer sysctls that are not the defaults.
    [[47; 97]] is the exec file name "/a". *)
Definition raw_kernel_live : RawKernelBuild :=
  mkRawKernelBuild true 3 true 1 20 true 4
    (mkRawCacheView (mkRawCacheLeaf false 32768 8 64)
                    (mkRawCacheLeaf false 32768 8 64)
                    (mkRawCacheLeaf false 1048576 8 64)
                    (mkRawCacheLeaf true 33554432 16 64))
    256 425984 425984 8388608 8388608.

(* the in-range control for the seed's structured fields *)
Definition raw_seed_full : RawProcInput :=
  mkRawProcInput [[112; 0]] [[65; 0]]
    (raw_std_image ++ [(raw_work ++ [47; 97], RawFile [1; 255]);
                       ([47; 116; 109; 112; 47; 98], RawFile [2])])
    raw_work [0; 255] 1000 1000
    [1000] [mkRawPeer 2130706433 80 [255] RneRst] 1024 0 4397 false Sv48
    [7] raw_kernel_live [47; 97] true true false.

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
  mkRawProcInput [] [] raw_std_image raw_work [] 0 0 [] [] 1024 0 4397 false Sv48 [] k [97]
    true true false.
Definition seed_with_execfn (fn : list Z) : RawProcInput :=
  mkRawProcInput [] [] raw_std_image raw_work [] 0 0 [] [] 1024 0 4397 false Sv48 []
    raw_kernel_default fn true true false.

(* [N]: which vDSO image the build carries *)
Example seed_kernel_vdso_negative_refused :
  init_model_checked [] 4096 4096 4096 0
    (seed_with_kernel
       (mkRawKernelBuild false (-1) true 256 0 true 0 raw_cache_absent
          224 212992 212992 4194304 4194304))
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_kernel_vdso_zero_converted :
  option_map in_kernel
    (proc_input_of_raw
       (seed_with_kernel
          (mkRawKernelBuild false 0 true 256 0 true 0 raw_cache_absent
             224 212992 212992 4194304 4194304)))
  = Some (mkKernelBuild false 0%N true 256%N 0%N true 0%N cache_view_absent
            224%N 212992%N 212992%N 4194304%N 4194304%N).
Proof. reflexivity. Qed.

(* [N]: the [stack_guard_gap] boot parameter, in pages *)
Example seed_kernel_guard_negative_refused :
  init_model_checked [] 4096 4096 4096 0
    (seed_with_kernel
       (mkRawKernelBuild false 1 true (-1) 0 true 0 raw_cache_absent
          224 212992 212992 4194304 4194304))
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_kernel_guard_zero_converted :
  option_map in_kernel
    (proc_input_of_raw
       (seed_with_kernel
          (mkRawKernelBuild false 1 true 0 0 true 0 raw_cache_absent
             224 212992 212992 4194304 4194304)))
  = Some (mkKernelBuild false 1%N true 0%N 0%N true 0%N cache_view_absent
            224%N 212992%N 212992%N 4194304%N 4194304%N).
Proof. reflexivity. Qed.

(* [N]: vm.mmap_rnd_bits *)
Example seed_kernel_rnd_bits_negative_refused :
  init_model_checked [] 4096 4096 4096 0
    (seed_with_kernel
       (mkRawKernelBuild false 1 true 256 (-1) true 0 raw_cache_absent
          224 212992 212992 4194304 4194304))
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_kernel_rnd_bits_zero_converted :
  option_map in_kernel
    (proc_input_of_raw
       (seed_with_kernel
          (mkRawKernelBuild false 1 true 256 0 true 0 raw_cache_absent
             224 212992 212992 4194304 4194304)))
  = Some (mkKernelBuild false 1%N true 256%N 0%N true 0%N cache_view_absent
            224%N 212992%N 212992%N 4194304%N 4194304%N).
Proof. reflexivity. Qed.

(* [N]: the vector unit's VLENB *)
Example seed_kernel_vlenb_negative_refused :
  init_model_checked [] 4096 4096 4096 0
    (seed_with_kernel
       (mkRawKernelBuild false 1 true 256 0 true (-1) raw_cache_absent
          224 212992 212992 4194304 4194304))
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_kernel_vlenb_four_converted :
  option_map in_kernel
    (proc_input_of_raw
       (seed_with_kernel
          (mkRawKernelBuild false 1 true 256 0 true 4 raw_cache_absent
             224 212992 212992 4194304 4194304)))
  = Some (mkKernelBuild false 1%N true 256%N 0%N true 4%N cache_view_absent
            224%N 212992%N 212992%N 4194304%N 4194304%N).
Proof. reflexivity. Qed.

(* [N]: one of the twelve numbers of the four cache leaves *)
Example seed_kernel_cache_assoc_negative_refused :
  init_model_checked [] 4096 4096 4096 0
    (seed_with_kernel
       (mkRawKernelBuild false 1 true 256 0 true 0
          (mkRawCacheView raw_leaf_absent raw_leaf_absent
             (mkRawCacheLeaf false 1048576 (-1) 64) raw_leaf_absent)
          224 212992 212992 4194304 4194304))
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_kernel_cache_assoc_zero_converted :
  option_map in_kernel
    (proc_input_of_raw
       (seed_with_kernel
          (mkRawKernelBuild false 1 true 256 0 true 0
             (mkRawCacheView raw_leaf_absent raw_leaf_absent
                (mkRawCacheLeaf false 1048576 0 64) raw_leaf_absent)
             224 212992 212992 4194304 4194304)))
  = Some (mkKernelBuild false 1%N true 256%N 0%N true 0%N
            (mkCacheView cache_leaf_absent cache_leaf_absent
               (mkCacheLeaf false 1048576%N 0%N 64%N) cache_leaf_absent)
            224%N 212992%N 212992%N 4194304%N 4194304%N).
Proof. reflexivity. Qed.

(* [N]: [sizeof(struct sk_buff)], in bytes *)
Example seed_kernel_skb_head_negative_refused :
  init_model_checked [] 4096 4096 4096 0
    (seed_with_kernel
       (mkRawKernelBuild false 1 true 256 0 true 0 raw_cache_absent
          (-1) 212992 212992 4194304 4194304))
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_kernel_skb_head_zero_converted :
  option_map in_kernel
    (proc_input_of_raw
       (seed_with_kernel
          (mkRawKernelBuild false 1 true 256 0 true 0 raw_cache_absent
             0 212992 212992 4194304 4194304)))
  = Some (mkKernelBuild false 1%N true 256%N 0%N true 0%N cache_view_absent
            0%N 212992%N 212992%N 4194304%N 4194304%N).
Proof. reflexivity. Qed.

(* [N]: net.core.wmem_default *)
Example seed_kernel_wmem_default_negative_refused :
  init_model_checked [] 4096 4096 4096 0
    (seed_with_kernel
       (mkRawKernelBuild false 1 true 256 0 true 0 raw_cache_absent
          224 (-1) 212992 4194304 4194304))
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_kernel_wmem_default_zero_converted :
  option_map in_kernel
    (proc_input_of_raw
       (seed_with_kernel
          (mkRawKernelBuild false 1 true 256 0 true 0 raw_cache_absent
             224 0 212992 4194304 4194304)))
  = Some (mkKernelBuild false 1%N true 256%N 0%N true 0%N cache_view_absent
            224%N 0%N 212992%N 4194304%N 4194304%N).
Proof. reflexivity. Qed.

(* [N]: net.core.rmem_default *)
Example seed_kernel_rmem_default_negative_refused :
  init_model_checked [] 4096 4096 4096 0
    (seed_with_kernel
       (mkRawKernelBuild false 1 true 256 0 true 0 raw_cache_absent
          224 212992 (-1) 4194304 4194304))
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_kernel_rmem_default_zero_converted :
  option_map in_kernel
    (proc_input_of_raw
       (seed_with_kernel
          (mkRawKernelBuild false 1 true 256 0 true 0 raw_cache_absent
             224 212992 0 4194304 4194304)))
  = Some (mkKernelBuild false 1%N true 256%N 0%N true 0%N cache_view_absent
            224%N 212992%N 0%N 4194304%N 4194304%N).
Proof. reflexivity. Qed.

(* [N]: net.core.wmem_max *)
Example seed_kernel_wmem_max_negative_refused :
  init_model_checked [] 4096 4096 4096 0
    (seed_with_kernel
       (mkRawKernelBuild false 1 true 256 0 true 0 raw_cache_absent
          224 212992 212992 (-1) 4194304))
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_kernel_wmem_max_zero_converted :
  option_map in_kernel
    (proc_input_of_raw
       (seed_with_kernel
          (mkRawKernelBuild false 1 true 256 0 true 0 raw_cache_absent
             224 212992 212992 0 4194304)))
  = Some (mkKernelBuild false 1%N true 256%N 0%N true 0%N cache_view_absent
            224%N 212992%N 212992%N 0%N 4194304%N).
Proof. reflexivity. Qed.

(* [N]: net.core.rmem_max *)
Example seed_kernel_rmem_max_negative_refused :
  init_model_checked [] 4096 4096 4096 0
    (seed_with_kernel
       (mkRawKernelBuild false 1 true 256 0 true 0 raw_cache_absent
          224 212992 212992 4194304 (-1)))
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_kernel_rmem_max_zero_converted :
  option_map in_kernel
    (proc_input_of_raw
       (seed_with_kernel
          (mkRawKernelBuild false 1 true 256 0 true 0 raw_cache_absent
             224 212992 212992 4194304 0)))
  = Some (mkKernelBuild false 1%N true 256%N 0%N true 0%N cache_view_absent
            224%N 212992%N 212992%N 4194304%N 0%N).
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

(** [Run.valid_image] is the launch condition over [State.in_image_fs]
    and [State.in_cwd]; the boundary enforces it here, and these pairs
    are what say the enforcement is not vacuous.  [valid_imageb] is a
    [bool], so a test that read the wrong thing would still type-check
    and still answer: only an image it must refuse beside an image it
    must convert shows which test was written.

    "/work/a" and "/work/a/b": the first key is a regular file and the
    second says the same name is the folder "b" lives under.  No Linux
    file system holds both -- one name in one directory is one inode --
    and [Fs.wf_fs] refuses an entry whose parent is not a directory.
    Beside it "/work/a" and "/work/ab", which differ in one byte of the
    second key and name two files. *)
Definition seed_with_image (img : list (list Z * RawEntry)) : RawProcInput :=
  mkRawProcInput [] [] img raw_work [] 0 0 [] [] 1024 0 4397 false Sv48 []
    raw_kernel_default [97] true true false.

Definition raw_work_a : list Z := raw_work ++ [47; 97].
Definition raw_image_prefix_key : list (list Z * RawEntry) :=
  raw_std_image ++ [(raw_work_a, RawFile [104]); (raw_work_a ++ [47; 98], RawFile [104])].
Definition raw_image_two_files : list (list Z * RawEntry) :=
  raw_std_image ++ [(raw_work_a, RawFile [104]); (raw_work_a ++ [98], RawFile [104])].

Example seed_unreal_image_refused :
  init_model_checked [] 4096 4096 4096 0
    (seed_with_image raw_image_prefix_key) = None.
Proof. vm_compute. reflexivity. Qed.

(** And WHICH refusal it is, which is what the published root answers:
    the image is a VALUE -- every byte of it is a [byte], so
    [fs_of_raw] converts it -- and it is no launch. *)
Example seed_unreal_image_is_a_value :
  option_map (fun fs => map (fun pf => map bv_unsigned (fst pf)) (Fs.fs_tree fs))
    (fs_of_raw [(raw_work_a, RawFile [104]); (raw_work_a ++ [47; 98], RawFile [104])])
  = Some [raw_work_a; raw_work_a ++ [47; 98]].
Proof. vm_compute. reflexivity. Qed.

Example seed_unreal_image_is_no_launch :
  image_shape_b raw_image_prefix_key raw_work = false.
Proof. vm_compute. reflexivity. Qed.

Example seed_two_files_image_is_a_launch :
  image_shape_b raw_image_two_files raw_work = true.
Proof. vm_compute. reflexivity. Qed.

(** The neighbour, converted, with the two files of the seed's
    [State.in_image_fs] read back out through the inode each name holds,
    and its eight names. *)
Definition file_bytes (fs : Fs.Fs) (k : list Z) : option (list Z) :=
  match bytes_of_Z k with
  | Some k' =>
      match Fs.fs_lookup fs k' with
      | Some (Fs.EFile i) => Some (map bv_unsigned (Fs.fs_ino_data fs i))
      | _ => None
      end
  | None => None
  end.

Example seed_two_files_image_converted :
  option_map
    (fun inp => (file_bytes (in_image_fs inp) raw_work_a,
                 file_bytes (in_image_fs inp) (raw_work_a ++ [98]),
                 length (Fs.fs_tree (in_image_fs inp))))
    (proc_input_of_raw (seed_with_image raw_image_two_files))
  = Some (Some [104], Some [104], 8%nat).
Proof. vm_compute. reflexivity. Qed.

(** A key that is not canonical is refused by the same clause and
    converted by [fs_of_raw] just as readily: "/work/./a" names the
    file "/work/a". *)
Example seed_noncanonical_image_refused :
  init_model_checked [] 4096 4096 4096 0
    (seed_with_image (raw_std_image ++ [(raw_work ++ [47; 46; 47; 97], RawFile [104])]))
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_canonical_image_converted :
  option_map (fun inp => file_bytes (in_image_fs inp) raw_work_a)
    (proc_input_of_raw (seed_with_image (raw_std_image ++ [(raw_work_a, RawFile [104])])))
  = Some (Some [104]).
Proof. vm_compute. reflexivity. Qed.

(** /tmp is a folder of the image like any other, so the same nesting
    under it is refused too. *)
Example seed_nested_tmp_refused :
  init_model_checked [] 4096 4096 4096 0
    (seed_with_image
       (raw_std_image ++ [([47; 116; 109; 112; 47; 97], RawFile [104]);
                          ([47; 116; 109; 112; 47; 97; 47; 98], RawFile [104])]))
  = None.
Proof. vm_compute. reflexivity. Qed.

(** The working directory must be a folder of the image: the seed with
    "/work" dropped is no launch, and so is one whose working directory
    names the file "/work/a". *)
Example seed_missing_cwd_is_no_launch :
  image_shape_b (removelast raw_std_image) raw_work = false.
Proof. vm_compute. reflexivity. Qed.

Example seed_cwd_on_a_file_is_no_launch :
  image_shape_b (raw_std_image ++ [(raw_work_a, RawFile [104])]) raw_work_a = false.
Proof. vm_compute. reflexivity. Qed.

(** ...and it must lie outside /proc and /sys
    ([Run.outside_proc_sysb]): with the folders /proc, /sys and
    /sys/kernel in the image, the working directory /work is a launch,
    and /proc and /sys/kernel are not. *)
Definition raw_proc : list Z := [47; 112; 114; 111; 99].
Definition raw_sys_kernel : list Z := [47; 115; 121; 115; 47; 107; 101; 114; 110; 101; 108].
Definition raw_proc_sys_image : list (list Z * RawEntry) :=
  raw_std_image ++ [(raw_proc, RawDir); ([47; 115; 121; 115], RawDir);
                    (raw_sys_kernel, RawDir)].

Example seed_work_beside_proc_and_sys_is_a_launch :
  image_shape_b raw_proc_sys_image raw_work = true.
Proof. vm_compute. reflexivity. Qed.

Example seed_proc_cwd_is_no_launch :
  image_shape_b raw_proc_sys_image raw_proc = false.
Proof. vm_compute. reflexivity. Qed.

Example seed_sys_kernel_cwd_is_no_launch :
  image_shape_b raw_proc_sys_image raw_sys_kernel = false.
Proof. vm_compute. reflexivity. Qed.

(** The standard root is part of the launch: without /dev/null the
    image is no launch. *)
Example seed_without_devnull_is_no_launch :
  image_shape_b (List.filter (fun ke => match snd ke with RawDevNull => false | _ => true end)
                   raw_std_image) raw_work = false.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Symbolic links and second names of one file                         *)
(* ------------------------------------------------------------------ *)

(** "/work/b" is a second name of "/work/a", and "/work/l" a symbolic
    link whose body is "a".  The second name sits at the head of the
    list, which [fs_of_raw] applies last, so its target is already a
    file when it is read.  Converted: both names hold ONE inode, whose
    link count is the two names the tree shows, and the link holds its
    body. *)
Definition raw_work_b : list Z := raw_work ++ [47; 98].
Definition raw_work_l : list Z := raw_work ++ [47; 108].
Definition raw_image_links : list (list Z * RawEntry) :=
  [(raw_work_b, RawName raw_work_a)]
  ++ raw_std_image ++ [(raw_work_a, RawFile [104]); (raw_work_l, RawLink [97])].

Definition entry_at (fs : Fs.Fs) (k : list Z) : option Fs.Entry :=
  match bytes_of_Z k with Some k' => Fs.fs_lookup fs k' | None => None end.

Definition ino_at (fs : Fs.Fs) (k : list Z) : option (Fs.ino * nat) :=
  match entry_at fs k with
  | Some (Fs.EFile i) => Some (i, Fs.fs_ino_nlink fs i)
  | _ => None
  end.

Definition link_at (fs : Fs.Fs) (k : list Z) : option (list Z) :=
  match entry_at fs k with
  | Some (Fs.ELink b) => Some (map bv_unsigned b)
  | _ => None
  end.

Example seed_links_image_is_a_launch :
  image_shape_b raw_image_links raw_work = true.
Proof. vm_compute. reflexivity. Qed.

Example seed_links_image_converted :
  option_map
    (fun inp => (ino_at (in_image_fs inp) raw_work_a,
                 ino_at (in_image_fs inp) raw_work_b,
                 file_bytes (in_image_fs inp) raw_work_b,
                 link_at (in_image_fs inp) raw_work_l))
    (proc_input_of_raw (seed_with_image raw_image_links))
  = Some (Some (1%Z, 2%nat), Some (1%Z, 2%nat), Some [104], Some [97]).
Proof. vm_compute. reflexivity. Qed.

(** Two [RawFile]s with the same bytes are two files: each is its own
    inode with one link.  This is the control that shows the shared
    inode above comes from [RawName] and not from equal contents. *)
Example seed_two_files_are_two_inodes :
  option_map
    (fun inp => (ino_at (in_image_fs inp) raw_work_a,
                 ino_at (in_image_fs inp) raw_work_b))
    (proc_input_of_raw
       (seed_with_image
          (raw_std_image ++ [(raw_work_a, RawFile [104]); (raw_work_b, RawFile [104])])))
  = Some (Some (2%Z, 1%nat), Some (1%Z, 1%nat)).
Proof. vm_compute. reflexivity. Qed.

(** A second name whose target is not a regular file is not a value:
    of a directory ("/work"), of a link ("/work/l"), of a missing key
    ("/work/z"), and of a target the list makes only AFTER the name is
    applied (the name at the tail is applied first, when nothing is at
    "/work/a" yet). *)
Example seed_second_name_of_a_folder_refused :
  fs_of_raw ([(raw_work_b, RawName raw_work)] ++ raw_std_image) = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_second_name_of_a_link_refused :
  fs_of_raw ([(raw_work_b, RawName raw_work_l)] ++ raw_std_image
             ++ [(raw_work_l, RawLink [97])]) = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_second_name_of_nothing_refused :
  fs_of_raw ([(raw_work_b, RawName (raw_work ++ [47; 122]))] ++ raw_std_image) = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_second_name_before_its_target_refused :
  fs_of_raw (raw_std_image ++ [(raw_work_a, RawFile [104]); (raw_work_b, RawName raw_work_a)])
  = None.
Proof. vm_compute. reflexivity. Qed.

(** A byte out of range in a link's body or in a second name's target
    is a value question like any other byte of the image. *)
Example seed_link_body_byte_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (seed_with_image (raw_std_image ++ [(raw_work_l, RawLink [256])])) = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_second_name_byte_out_of_range_refused :
  fs_of_raw ([(raw_work_b, RawName (raw_work ++ [47; 256]))] ++ raw_std_image
             ++ [(raw_work_a, RawFile [104])]) = None.
Proof. vm_compute. reflexivity. Qed.

(** A link whose body is empty, or names nothing, is still a launch:
    no clause limits a body ([Fs.wf_fs]). *)
Example seed_dangling_link_is_a_launch :
  image_shape_b (raw_std_image ++ [(raw_work_l, RawLink []);
                                   (raw_work ++ [47; 109], RawLink [122])]) raw_work = true.
Proof. vm_compute. reflexivity. Qed.
