(* The same tests as tests/CheckedInputWitness.v, against the EXTRACTED
   checker rather than the Rocq term.

   WHY BOTH.  The defect this boundary closes is a defect of EXTRACTION:
   a [bv n] is a record whose well-formedness proof is a [Prop], so the
   extracted word is zarith's integer and holds no range.  A Rocq test
   shows the boundary refuses; only a test on the generated OCaml shows
   that the refusal survived extraction.  This also makes the build
   compile theories/LinuxProcessSem/Checks/Extraction.v, which nothing
   else does.

   THE WITNESS: theorem-labs/linux-process-semantics at ff0313ba4f,
   testing/syscall-check/traces/set_tid/022.jsonl, record [seq 1], case
   [reject --mutate set_tid_address#2:ret=2^64] — a set_tid_address
   (riscv64 syscall 96) whose observed return is 18446744073709551616,
   which the extracted checker gave the verdict [reject]. *)

module M = Syscall_model

let z = Big_int_Z.big_int_of_string
let failures = ref 0

let check name ok =
  if ok then Printf.printf "ok   %s\n" name
  else begin incr failures; Printf.printf "FAIL %s\n" name end

(* ----------------------------------------------------------------- *)
(* the scalar boundary                                                *)
(* ----------------------------------------------------------------- *)

let is_none = function None -> true | Some _ -> false
let is_value v = function
  | Some w -> Big_int_Z.eq_big_int w (z v)
  | None -> false

let () =
  check "word_of_Z refuses 2^64" (is_none (M.word_of_Z (z "18446744073709551616")));
  check "word_of_Z takes 2^64 - 1"
    (is_value "18446744073709551615" (M.word_of_Z (z "18446744073709551615")));
  check "word_of_Z refuses -1" (is_none (M.word_of_Z (z "-1")));
  check "byte_of_Z refuses 256" (is_none (M.byte_of_Z (z "256")));
  check "byte_of_Z takes 255" (is_value "255" (M.byte_of_Z (z "255")));
  check "byte_of_Z refuses -1" (is_none (M.byte_of_Z (z "-1")))

(* ----------------------------------------------------------------- *)
(* a model to judge against                                           *)
(* ----------------------------------------------------------------- *)

let seed : M.rawProcInput = {
  M.rpi_argv = []; rpi_envp = []; rpi_image_fs = []; rpi_stdin = [];
  rpi_uid = z "0"; rpi_gid = z "0"; rpi_groups = []; rpi_net = [];
  rpi_nofile = z "1024"; rpi_sigmask = z "0"; rpi_hwcap = z "4397";
  rpi_abort_terminal = false; rpi_va_size = M.Sv48;
  rpi_urandom = []; rpi_tmp = []; rpi_channel_reader = true;
  rpi_sigpipe_default = true }

let model =
  match M.init_model_checked [] (z "4096") (z "4096") (z "4096") (z "0") seed with
  | Some m -> m
  | None -> failwith "the in-range seed was refused"

(* ----------------------------------------------------------------- *)
(* the witness, and one case per place an out-of-type value enters    *)
(* ----------------------------------------------------------------- *)

let input : M.rawInput = {
  M.rin_sysno = z "96"; rin_args = List.map z ["274877906944"; "0"; "0"; "0"; "0"; "0"];
  rin_mem = []; rin_wmem = M.wmem_ranges [] }

let effect_of ret : M.rawEffect = {
  M.reff_ret = z ret; reff_writes = []; reff_zeros = []; reff_unmaps = [];
  reff_copies = []; reff_copyins = [] }

let refused ri re = match M.check_syscall_for_run_checked ri re model with
  | M.CheckedRefused -> true
  | M.CheckedAnswer _ -> false

let () =
  check "the witness 2^64 return is refused, not judged"
    (refused input (effect_of "18446744073709551616"));
  check "the kernel's own return 624 is judged, not refused"
    (not (refused input (effect_of "624")));
  check "a negative return is refused" (refused input (effect_of "-1"));
  check "an out-of-range syscall number is refused"
    (refused { input with M.rin_sysno = z "18446744073709551616" } (effect_of "0"));
  check "an out-of-range argument is refused"
    (refused { input with M.rin_args = [z "18446744073709551616"] } (effect_of "0"));
  check "an out-of-range captured address is refused"
    (refused { input with M.rin_mem = [(z "18446744073709551616", [z "1"])] }
       (effect_of "0"));
  check "a captured byte above 255 is refused"
    (refused { input with M.rin_mem = [(z "4096", [z "0"; z "256"])] } (effect_of "0"));
  (* The writable view is a predicate: a [bool] has no erased invariant,
     so there is nothing there to refuse.  What is checked instead is
     that the view answers where the reader says it may. *)
  check "the writable view follows the reader's predicate"
    (not (refused { input with M.rin_wmem = M.wmem_ranges [(z "4096", z "16")] }
            (effect_of "0")));
  check "a written byte above 255 is refused"
    (refused input { (effect_of "0") with
                     M.reff_writes = [(z "4096", [z "256"])] });
  check "an out-of-range zero-filled range is refused"
    (refused input { (effect_of "0") with
                     M.reff_zeros = [(z "18446744073709551616", z "4096")] });
  check "an out-of-range unmapped range is refused"
    (refused input { (effect_of "0") with
                     M.reff_unmaps = [(z "0", z "18446744073709551616")] });
  check "an out-of-range copy is refused"
    (refused input { (effect_of "0") with
                     M.reff_copies = [((z "0", z "0"), z "18446744073709551616")] });
  check "an out-of-range copy-in address is refused"
    (refused input { (effect_of "0") with
                     M.reff_copyins = [(z "18446744073709551616", z "8")] });
  check "a negative copy-in length is refused"
    (refused input { (effect_of "0") with
                     M.reff_copyins = [(z "4096", z "-1")] });
  check "an in-range effect in every component is judged"
    (not (refused input { M.reff_ret = z "0";
                          reff_writes = [(z "4096", [z "255"])];
                          reff_zeros = [(z "4096", z "4096")];
                          reff_unmaps = [(z "8192", z "4096")];
                          reff_copies = [((z "0", z "4096"), z "8")];
                          reff_copyins = [(z "4096", z "8")] }))

(* ----------------------------------------------------------------- *)
(* the model's seed                                                   *)
(* ----------------------------------------------------------------- *)

let seed_refused ?(reserved = []) ?(brk0 = "4096") ?(mbase = "4096")
    ?(sp = "4096") (s : M.rawProcInput) =
  M.init_model_checked reserved (z brk0) (z mbase) (z sp) (z "0") s = None

let w = "18446744073709551616"

let () =
  check "an out-of-range reserved segment is refused"
    (seed_refused ~reserved:[(z w, z "4096")] seed);
  check "an out-of-range initial break is refused" (seed_refused ~brk0:w seed);
  check "an out-of-range mmap base is refused" (seed_refused ~mbase:w seed);
  check "an out-of-range stack pointer is refused" (seed_refused ~sp:w seed);
  check "an out-of-range uid is refused" (seed_refused { seed with M.rpi_uid = z w });
  check "an out-of-range group is refused"
    (seed_refused { seed with M.rpi_groups = [z w] });
  check "an out-of-range RLIMIT_NOFILE is refused"
    (seed_refused { seed with M.rpi_nofile = z w });
  check "an out-of-range signal mask is refused"
    (seed_refused { seed with M.rpi_sigmask = z w });
  check "an out-of-range AT_HWCAP is refused"
    (seed_refused { seed with M.rpi_hwcap = z w });
  check "an argv byte above 255 is refused"
    (seed_refused { seed with M.rpi_argv = [[z "256"]] });
  check "an envp byte above 255 is refused"
    (seed_refused { seed with M.rpi_envp = [[z "256"]] });
  check "a file-system byte above 255 is refused"
    (seed_refused { seed with M.rpi_image_fs = [([z "97"], [z "256"])] });
  check "a standard-input byte above 255 is refused"
    (seed_refused { seed with M.rpi_stdin = [z "256"] });
  check "a random-device byte above 255 is refused"
    (seed_refused { seed with M.rpi_urandom = [z "256"] });
  check "a /tmp byte above 255 is refused"
    (seed_refused { seed with M.rpi_tmp = [([z "97"], [z "256"])] });
  check "a peer address above 2^32 - 1 is refused"
    (seed_refused { seed with M.rpi_net =
      [{ M.rpe_addr = z "4294967296"; rpe_port = z "80"; rpe_bytes = [];
         rpe_end = M.RneFin }] });
  check "a peer port above 2^16 - 1 is refused"
    (seed_refused { seed with M.rpi_net =
      [{ M.rpe_addr = z "0"; rpe_port = z "65536"; rpe_bytes = [];
         rpe_end = M.RneFin }] });
  check "a peer byte above 255 is refused"
    (seed_refused { seed with M.rpi_net =
      [{ M.rpe_addr = z "0"; rpe_port = z "80"; rpe_bytes = [z "256"];
         rpe_end = M.RneFin }] });
  check "an in-range seed in every structured field is accepted"
    (not (seed_refused ~reserved:[(z "4096", z "4096")] ~brk0:"8192"
            ~mbase:"12288" ~sp:"16384"
            { M.rpi_argv = [[z "112"; z "0"]]; rpi_envp = [[z "65"; z "0"]];
              rpi_image_fs = [([z "97"], [z "1"; z "255"])];
              rpi_stdin = [z "0"; z "255"]; rpi_uid = z "1000";
              rpi_gid = z "1000"; rpi_groups = [z "1000"];
              rpi_net = [{ M.rpe_addr = z "2130706433"; rpe_port = z "80";
                           rpe_bytes = [z "255"]; rpe_end = M.RneRst }];
              rpi_nofile = z "1024"; rpi_sigmask = z "0"; rpi_hwcap = z "4397";
              rpi_abort_terminal = false; rpi_va_size = M.Sv48;
              rpi_urandom = [z "7"]; rpi_tmp = [([z "98"], [z "2"])] }))

let () =
  if !failures = 0 then print_endline "checked-input smoke: all checks passed"
  else begin
    Printf.printf "checked-input smoke: %d check(s) failed\n" !failures;
    exit 1
  end
