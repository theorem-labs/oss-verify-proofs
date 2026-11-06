(* ubsan_halts of reac-pw/fuzz_pin with no premise: PinEnd.ubsan_halts_of_callees, its premise (the contracts of pin's own
   callees of LLVMFuzzerTestOneInput) discharged by their walks, and the walks' own callee contracts by the leaf proofs.
   rule 24: proves no function by itself (kind: segment lemma of LLVMFuzzerTestOneInput's walk: the top composition). *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog Require PinEnd check_known check_row check_label fuzz_catalogue_row reac_box_pin_parse
  strlen bcmp strcspn memset strchrnul reac_box_catalogue strncmp.
From OSSVerify.reac_pw.fuzz_pin Require Statements.

Theorem ubsan_halts_holds : Statements.ubsan_halts.
Proof.
  apply PinEnd.ubsan_halts_of_callees.
  refine (conj check_known.check_known_holds (conj check_row.check_row_holds (conj check_label.check_label_holds
            (conj (fuzz_catalogue_row.fuzz_catalogue_row_holds strlen.strlen_holds bcmp.bcmp_holds)
                  (reac_box_pin_parse.reac_box_pin_parse_holds
                     (strcspn.strcspn_holds memset.memset_holds strchrnul.strchrnul_holds)
                     reac_box_catalogue.reac_box_catalogue_holds strlen.strlen_holds strncmp.strncmp_holds))))).
Qed.
