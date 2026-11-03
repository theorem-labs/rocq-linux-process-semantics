(* The same tests as tests/CheckedIsaWitness.v, against the EXTRACTED
   ISA model rather than the Rocq term.

   WHY BOTH.  The defect this boundary closes is a defect of EXTRACTION:
   a [bv n] is a record whose well-formedness proof is a [Prop], so the
   extracted bitvector is zarith's integer with no width and no range.
   A Rocq test shows the boundary refuses; only a test on the generated
   OCaml shows that the refusal survived extraction.  This also makes
   the build compile theories/Riscv/Extraction.v, which nothing else
   does. *)

module M = Riscv_model

let z = Big_int_Z.big_int_of_string
let failures = ref 0

let check name ok =
  if ok then Printf.printf "ok   %s\n" name
  else begin incr failures; Printf.printf "FAIL %s\n" name end

let refused : 'a M.checked -> bool = function
  | M.CkRefused -> true
  | M.CkAnswer _ -> false

let answered_none : 'a option M.checked -> bool = function
  | M.CkAnswer None -> true
  | _ -> false

(* ----------------------------------------------------------------- *)
(* the decoders                                                       *)
(* ----------------------------------------------------------------- *)

let () =
  check "decode refuses 2^32" (refused (M.decode_checked (z "4294967296")));
  check "decode refuses -1" (refused (M.decode_checked (z "-1")));
  check "decode takes the nop encoding" (not (refused (M.decode_checked (z "19"))));
  check "decode takes the top 32-bit word"
    (not (refused (M.decode_checked (z "4294967295"))));
  check "decode16 refuses 2^16" (refused (M.decode16_checked (z "65536")));
  check "decode16 takes the top halfword"
    (not (refused (M.decode16_checked (z "65535"))));
  check "expand_c refuses 2^16" (refused (M.expand_c_checked (z "65536")));
  check "expand_c takes a halfword" (not (refused (M.expand_c_checked (z "1"))));
  check "decode_any refuses 2^32" (refused (M.decode_any_checked (z "4294967296")));
  check "decode_any takes the nop encoding"
    (not (refused (M.decode_any_checked (z "19"))));
  (* a word the model does not decode is an ANSWER, not a refusal *)
  check "an undecodable word is answered, not refused"
    (answered_none (M.decode_any_checked (z "4294967295")));
  check "is_defined_illegal refuses 2^32"
    (refused (M.is_defined_illegal_checked (z "4294967296")));
  check "is_defined_illegal takes the zero parcel"
    (M.is_defined_illegal_checked (z "0") = M.CkAnswer true)

(* ----------------------------------------------------------------- *)
(* the core state                                                     *)
(* ----------------------------------------------------------------- *)

let zeros32 = List.init 32 (fun _ -> z "0")

let core0 : M.rawCore =
  { M.rc_regs = zeros32; rc_fregs = zeros32; rc_pc = z "0"; rc_fcsr = z "0";
    rc_resv = None }

let core_refused (c : M.rawCore) = M.core_of_raw c = None
let w = "18446744073709551616"

let () =
  check "the zero core is accepted" (not (core_refused core0));
  check "an out-of-range pc is refused"
    (core_refused { core0 with M.rc_pc = z w });
  check "an out-of-range integer register is refused"
    (core_refused { core0 with M.rc_regs = z w :: List.tl zeros32 });
  check "an out-of-range floating-point register is refused"
    (core_refused { core0 with M.rc_fregs = z w :: List.tl zeros32 });
  check "a negative register is refused"
    (core_refused { core0 with M.rc_regs = z "-1" :: List.tl zeros32 });
  check "an out-of-range fcsr is refused"
    (core_refused { core0 with M.rc_fcsr = z "4294967296" });
  check "an out-of-range reservation is refused"
    (core_refused { core0 with M.rc_resv = Some (z w) });
  check "a live reservation is taken"
    (not (core_refused { core0 with M.rc_resv = Some (z "4096") }));
  check "a thirty-one register file is refused, not padded"
    (core_refused { core0 with M.rc_regs = List.tl zeros32 });
  check "a thirty-three register file is refused"
    (core_refused { core0 with M.rc_regs = z "0" :: zeros32 })

(* ----------------------------------------------------------------- *)
(* running one instruction                                            *)
(* ----------------------------------------------------------------- *)

let () =
  check "exec refuses a wide encoding"
    (refused (M.exec_encoded_checked (z "4294967296") core0));
  check "exec refuses a bad core"
    (refused (M.exec_encoded_checked (z "19")
                { core0 with M.rc_regs = List.tl zeros32 }));
  check "exec runs the nop encoding"
    (not (refused (M.exec_encoded_checked (z "19") core0)));
  check "step refuses a bad core"
    (refused (M.step_checked { core0 with M.rc_pc = z w }))

(* ----------------------------------------------------------------- *)
(* the value that arrives mid-execution                               *)
(* ----------------------------------------------------------------- *)

(* [step] opens with the instruction fetch, so the first thing the
   interpreter is asked for is a 32-bit load. *)
let fed (v : string) : M.load_step =
  match M.step_checked core0 with
  | M.CkRefused -> failwith "the zero core was refused"
  | M.CkAnswer e -> M.eff_feed_load e (z v)

let is_refused = function M.LsRefused -> true | _ -> false
let is_next = function M.LsNext _ -> true | _ -> false

let () =
  check "the fetch refuses an answer no 32-bit word holds"
    (is_refused (fed "4294967296"));
  check "the fetch refuses a negative answer" (is_refused (fed "-1"));
  check "the fetch takes the nop encoding" (is_next (fed "19"));
  check "the pending fetch reports its width and address"
    (match M.step_checked core0 with
     | M.CkAnswer e ->
       (match M.eff_pending_load e with
        | Some (n, a) ->
          Big_int_Z.eq_big_int n (z "32") && Big_int_Z.eq_big_int a (z "0")
        | None -> false)
     | M.CkRefused -> false);
  check "an effect that is not waiting for a load says so, and that is not a refusal"
    (match M.step_checked core0 with
     | M.CkAnswer e ->
       (match M.eff_feed_load e (z "19") with
        | M.LsNext e' -> M.eff_feed_load e' (z "0") = M.LsNotPending
                         && M.eff_pending_load e' = None
        | _ -> false)
     | M.CkRefused -> false)

let () =
  if !failures = 0 then print_endline "checked-isa smoke: all checks passed"
  else begin
    Printf.printf "checked-isa smoke: %d check(s) failed\n" !failures;
    exit 1
  end
