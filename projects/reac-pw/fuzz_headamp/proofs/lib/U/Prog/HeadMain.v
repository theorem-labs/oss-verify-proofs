(** ubsan_halts of reac-pw/fuzz_headamp with LLVMFuzzerTestOneInput's walk closed (UBSan image):
    HeadEnd.ubsan_halts_of_contracts (the six segments, the slot, the builder, the small evts and the leaves memset,
    memcpy, strlen, pod_write_ent discharged) with the checking evt headamp_check_contract discharged by
    headamp_check.headamp_check_holds, whose own leaves memset, strncmp and strcmp are discharged by their walks
    (U/Prog/memset.v, strncmp.v, strcmp.v). The premises left are the contracts of fuzz_headamp's other functions,
    whose walks are written apart: the two parse entries (reac_headamp_prop_parse_result, reac_headamp_prop_parse) and
    the eight checks.
    rule 24: proves no function by itself (kind: segment lemma of LLVMFuzzerTestOneInput's walk: its closure); the
    walk of LLVMFuzzerTestOneInput is closed here. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import reac_headamp_prop_parse_result_c
  reac_headamp_prop_parse_c check_no_overrun_c check_count_c check_cells_valid_c check_object_c check_cells_c
  check_keys_c check_refusal_c check_plain_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require HeadEnd headamp_check memset strncmp strcmp.
From OSSVerify.reac_pw.fuzz_headamp Require Statements.

Theorem ubsan_halts_of_main_callees :
  reac_headamp_prop_parse_result_contract -> reac_headamp_prop_parse_contract ->
  check_no_overrun_contract -> check_count_contract -> check_cells_valid_contract ->
  check_object_contract -> check_cells_contract -> check_keys_contract -> check_refusal_contract ->
  check_plain_contract ->
  Statements.ubsan_halts.
Proof.
  intros PRES PARSE CKNO CKCNT CKCV CKO CKC CKK CKR CKP.
  apply HeadEnd.ubsan_halts_of_contracts; [| exact PARSE | exact CKP].
  exact (headamp_check.headamp_check_holds memset.memset_holds PRES CKNO CKCNT CKCV strncmp.strncmp_holds
           strcmp.strcmp_holds CKO CKC CKK CKR).
Qed.
