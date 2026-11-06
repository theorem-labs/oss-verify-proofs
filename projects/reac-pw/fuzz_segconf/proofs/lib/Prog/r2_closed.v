(** reac-pw/fuzz_segconf, plain build: the contracts of the trim, refuse and cross_check walks with their callees discharged by the
    callees' proofs in this tree.
    - trim: trim_holds (Prog/trim.v) over strlen_holds (Prog/strlen.v).
    - refuse: refuse_holds (Prog/refuse.v, the walk) takes rf_snprintf and rf_vsnprintf (Prog/refuse_pf_c.v);
      Prog/refuse_pf.v proves them from snprintf_contract and vsnprintf_contract, which
      Prog/snprintf.v and Prog/vsnprintf.v prove of the binary.
    - cross_check: cross_check_holds (Prog/cross_check.v) over the closed refuse_contract.
    reac_segconf_parse_holds (Prog/reac_segconf_parse.v) also takes reac_segconf_parse_file_contract (family F3's
    walk), so it is not closed here. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require strlen_c strlen trim_c trim refuse_c snprintf_c
  vsnprintf_c refuse refuse_pf snprintf vsnprintf cross_check_c cross_check.

Theorem trim_contract_closed : Prog.trim_c.trim_contract.
Proof. exact (Prog.trim.trim_holds Prog.strlen.strlen_holds). Qed.

Theorem refuse_holds_pf : Prog.snprintf_c.snprintf_contract -> Prog.vsnprintf_c.vsnprintf_contract ->
  Prog.refuse_c.refuse_contract.
Proof. intros HS HV. exact (Prog.refuse.refuse_holds (Prog.refuse_pf.rf_snprintf_of HS) (Prog.refuse_pf.rf_vsnprintf_of HV)). Qed.

Theorem refuse_contract_closed : Prog.refuse_c.refuse_contract.
Proof. exact (refuse_holds_pf Prog.snprintf.snprintf_holds Prog.vsnprintf.vsnprintf_holds). Qed.

Theorem cross_check_contract_closed : Prog.cross_check_c.cross_check_contract.
Proof. exact (Prog.cross_check.cross_check_holds refuse_contract_closed). Qed.
