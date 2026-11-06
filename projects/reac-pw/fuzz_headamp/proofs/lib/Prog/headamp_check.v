(** headamp_check_contract (Prog/LLVMFuzzerTestOneInput_c.v: segment M03 of fuzz_headamp's plain
    LLVMFuzzerTestOneInput, [0x14080, 0x14164)) from its callee contracts, by the four pieces of Prog/HeadCheck:
    the walk outside expect_of (Head.v head_holds) with expect_of's piece (Expect.v expect_holds), which takes one
    prefixed pair's piece (Key.v key_holds), which takes the inlined pod_nearest's piece (Near.v near_holds). The
    five soft-float contracts the nearest piece takes (__extendsftf2, __floatditf, __subtf3 with __addtf3, __getf2,
    __lttf2 = __cmptf2, relocated from role's CJ closure) are proved for the plain image by CJ/RL/I/InstP.v, so the
    theorem's premises are the remaining callee contracts in the order of headamp_check_contract's comment. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import memset_c reac_headamp_prop_parse_result_c
  check_no_overrun_c check_count_c check_cells_valid_c strncmp_c strcmp_c check_object_c check_cells_c check_keys_c
  check_refusal_c LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.I Require IImgP InstP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.G Require C_extendsftf2 C_floatditf G_subtf3 G_getf2 G_letf2.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require Import Cut Head Near Key Expect.

(** The inlined pod_nearest's piece, its soft-float callees discharged. *)
Theorem near_closed : near_stmt.
Proof.
  apply near_holds.
  - exact InstP.N_extendsftf2_contract.
  - exact InstP.N_floatditf_contract.
  - exact InstP.N_subtf3_contract.
  - exact InstP.N_getf2_contract.
  - exact InstP.N_letf2_contract.
Qed.

Theorem headamp_check_holds :
  memset_contract -> reac_headamp_prop_parse_result_contract ->
  check_no_overrun_contract -> check_count_contract -> check_cells_valid_contract ->
  strncmp_contract -> strcmp_contract ->
  check_object_contract -> check_cells_contract -> check_keys_contract -> check_refusal_contract ->
  headamp_check_contract.
Proof.
  intros MSET PARSE CKNO CKCNT CKCV STRN STRC CKO CKC CKK CKR.
  apply head_holds; try assumption.
  apply expect_holds; [exact MSET | exact STRN |].
  apply key_holds; [exact STRC |].
  exact near_closed.
Qed.
