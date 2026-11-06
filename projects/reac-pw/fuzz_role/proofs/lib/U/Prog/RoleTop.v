(* ubsan_halts of reac-pw/fuzz_role with no premise: U RoleEnd.ubsan_halts_of_callees, its premises (the four segment
   lemmas of LLVMFuzzerTestOneInput and the contracts of its two callees role_build and role_check) discharged by
   their walks, and the walks' own callee contracts by the leaf proofs: the libc leaves, pod_write_ent, pod_nearest
   with its binary128 value facts (NearSFClose) and its five soft-float callees at the UBSan image (CJ/RL/I/InstU).
   rule 24: proves no function by itself (kind: segment lemma of LLVMFuzzerTestOneInput's walk: the top composition). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require RoleEnd role_build role_check memset memcpy strlen strcmp
  pod_write_ent reac_role_prop_parse pod_nearest check_absent check_role check_malformed reac_role_cfg_changes
  reac_role_cfg_apply_state check_answer reac_role_refuse_code check_code.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog.Seg Require E01 M01 M02 X01.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require NearSFClose.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.I Require InstU.
From OSSVerify.reac_pw.fuzz_role Require Statements.

Theorem ubsan_halts_holds : Statements.ubsan_halts.
Proof.
  apply (RoleEnd.ubsan_halts_of_callees (@E01.seg_E01) (@M01.seg_M01) (@M02.seg_M02) (@X01.seg_X01)).
  - exact (role_build.role_build_holds memset.memset_holds memcpy.memcpy_holds strlen.strlen_holds
             (pod_write_ent.pod_write_ent_holds memcpy.memcpy_holds memset.memset_holds)).
  - exact (role_check.role_check_holds memcpy.memcpy_holds
             (reac_role_prop_parse.reac_role_prop_parse_holds strcmp.strcmp_holds) strcmp.strcmp_holds
             (pod_nearest.pod_nearest_holds NearSFClose.near_sf_facts_ok
                InstU.N_extendsftf2_contract InstU.N_letf2_contract InstU.N_floatditf_contract
                InstU.N_subtf3_contract InstU.N_getf2_contract)
             check_absent.check_absent_holds check_role.check_role_holds check_malformed.check_malformed_holds
             reac_role_cfg_changes.reac_role_cfg_changes_holds reac_role_cfg_apply_state.reac_role_cfg_apply_state_holds
             (check_answer.check_answer_holds strcmp.strcmp_holds) reac_role_refuse_code.reac_role_refuse_code_holds
             (check_code.check_code_holds strcmp.strcmp_holds)).
Qed.
