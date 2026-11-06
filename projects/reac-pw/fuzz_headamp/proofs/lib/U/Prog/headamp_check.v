(** Segment M03 of reac-pw/fuzz_headamp's LLVMFuzzerTestOneInput (UBSan), [0x14118, 0x147dc): proof of
    headamp_check_contract (U/Prog/LLVMFuzzerTestOneInput_c.v) from the callee contracts, in the order of that
    contract's comment: memset, reac_headamp_prop_parse_result, check_no_overrun, check_count, check_cells_valid,
    strncmp, strcmp, check_object, check_cells, check_keys, check_refusal. The five soft-float contracts of the
    inlined pod_nearest (__extendsftf2, __floatditf, __subtf3, __getf2 / __gttf2, __letf2 / __lttf2) are not premises:
    CJ/RL/I/InstU.v proves them for the UBSan image. The pieces: U/Prog/HeadCheck/Near.v (the inlined nearest),
    Key.v (one pair with the prefix), Expect.v (expect_of), Head.v (the head, the checks and first's size). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import memset_c reac_headamp_prop_parse_result_c
  check_no_overrun_c check_count_c check_cells_valid_c strncmp_c strcmp_c check_object_c check_cells_c check_keys_c
  check_refusal_c LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.I Require InstU.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadCheck Require Import Cut Near Key Expect Head.

Theorem headamp_check_holds :
  memset_contract -> reac_headamp_prop_parse_result_contract ->
  check_no_overrun_contract -> check_count_contract -> check_cells_valid_contract ->
  strncmp_contract -> strcmp_contract ->
  check_object_contract -> check_cells_contract -> check_keys_contract -> check_refusal_contract ->
  headamp_check_contract.
Proof.
  intros MSET PARSE CKNO CKCNT CKCV STRN STRC CKO CKC CKK CKR.
  pose proof (near_holds InstU.N_extendsftf2_contract InstU.N_floatditf_contract InstU.N_subtf3_contract
                InstU.N_getf2_contract InstU.N_letf2_contract) as NEAR.
  exact (Head.head_holds MSET PARSE CKNO CKCNT CKCV (expect_holds MSET STRN (key_holds STRC NEAR)) CKO CKC CKK CKR).
Qed.
