(** pod_nearest's contract at fuzz_rate's UBSan image (0x14b84) with no premise: [pod_nearest.pod_nearest_holds]
    (U/Prog/pod_nearest.v) with its binary128 value facts closed by NearSFClose.near_sf_facts_ok (the same facts as
    the plain build's) and its five soft-float callees by their proofs at the UBSan sym map (CJ/RL/I/InstU.v). The
    same closing as fuzz_role's U/Prog/RoleTop.v makes inside its ubsan_halts_holds; here it is a theorem of its
    own, for the walks that call pod_nearest. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require pod_nearest_c pod_nearest.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require NearSFClose.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.I Require InstU.

Theorem pod_nearest_ok : OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.pod_nearest_c.pod_nearest_contract.
Proof.
  exact (OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.pod_nearest.pod_nearest_holds
           NearSFClose.near_sf_facts_ok
           InstU.N_extendsftf2_contract InstU.N_letf2_contract InstU.N_floatditf_contract
           InstU.N_subtf3_contract InstU.N_getf2_contract).
Qed.
