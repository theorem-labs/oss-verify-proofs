(** pod_nearest's contract at fuzz_rate's plain image (0x14884) with no premise: [pod_nearest.pod_nearest_holds]
    with its binary128 value facts closed by NearSFClose.near_sf_facts_ok and its five soft-float callees
    (__extendsftf2, __lttf2 = __cmptf2, __floatditf, __subtf3 with __addtf3, __getf2) by their proofs at the plain
    sym map (CJ/RL/I/InstP.v). The same closing as fuzz_role's Prog/RoleTop.v makes inside its plain_halts_holds;
    here it is a theorem of its own, for the walks that call pod_nearest. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require pod_nearest_c pod_nearest NearSFClose.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.I Require InstP.

Theorem pod_nearest_ok : OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog.pod_nearest_c.pod_nearest_contract.
Proof.
  exact (OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog.pod_nearest.pod_nearest_holds
           NearSFClose.near_sf_facts_ok
           InstP.N_extendsftf2_contract InstP.N_letf2_contract InstP.N_floatditf_contract
           InstP.N_subtf3_contract InstP.N_getf2_contract).
Qed.
