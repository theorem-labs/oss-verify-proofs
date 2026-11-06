(** reac-pw/fuzz_segconf, UBSan build: the contracts of the trim, refuse and cross_check walks with their callees discharged by the
    callees' proofs in this tree.
    - trim: trim_holds (U/Prog/trim.v) over strlen_holds (U/Prog/strlen.v).
    - refuse: refuse_holds (U/Prog/refuse.v, the walk) takes rf_snprintf and rf_vsnprintf (U/Prog/refuse_pf_c.v);
      U/Prog/refuse_pf.v proves them from snprintf_contract and vsnprintf_contract, which
      U/Prog/snprintf.v and U/Prog/vsnprintf.v prove of the binary.
    - cross_check: cross_check_holds (U/Prog/cross_check.v) over the closed refuse_contract.
    reac_segconf_parse_holds (U/Prog/reac_segconf_parse.v) also takes reac_segconf_parse_file_contract (family F3's
    walk), so it is not closed here. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require strlen_c strlen trim_c trim refuse_c snprintf_c
  vsnprintf_c refuse refuse_pf snprintf vsnprintf cross_check_c cross_check.

Theorem trim_contract_closed : U.Prog.trim_c.trim_contract.
Proof. exact (U.Prog.trim.trim_holds U.Prog.strlen.strlen_holds). Qed.

Theorem refuse_holds_pf : U.Prog.snprintf_c.snprintf_contract -> U.Prog.vsnprintf_c.vsnprintf_contract ->
  U.Prog.refuse_c.refuse_contract.
Proof. intros HS HV. exact (U.Prog.refuse.refuse_holds (U.Prog.refuse_pf.rf_snprintf_of HS) (U.Prog.refuse_pf.rf_vsnprintf_of HV)). Qed.

Theorem refuse_contract_closed : U.Prog.refuse_c.refuse_contract.
Proof. exact (refuse_holds_pf U.Prog.snprintf.snprintf_holds U.Prog.vsnprintf.vsnprintf_holds). Qed.

Theorem cross_check_contract_closed : U.Prog.cross_check_c.cross_check_contract.
Proof. exact (U.Prog.cross_check.cross_check_holds refuse_contract_closed). Qed.
