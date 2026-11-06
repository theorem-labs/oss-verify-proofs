(* ubsan_halts of reac-pw/fuzz_rate with no premise: U/Prog/RateEnd.ubsan_halts_of_callees, its premises (the five
   segment lemmas of LLVMFuzzerTestOneInput and the contracts of its three evts rate_build, rate_check and rate_csv)
   discharged by their walks, and the walks' own callee contracts by the callee proofs: the libc leaves (memset,
   memcpy, strlen, strcmp, bcmp), pod_write_ent, pod_nearest (pod_nearest_ok: its binary128 value facts and its five
   soft-float callees at the UBSan image), snprintf, and rate's own callees. Model: reac-pw/fuzz_role's
   U/Prog/RoleTop.v, for rate's five segments and three evts.
   build_ok, check_ok, csv_ok and the seg_*_ok lemmas are also the UBSan agreement slot's premises
   (U/Prog/SegCF/SlotTopCF.v).
   rule 24: proves no function by itself (kind: segment lemma of LLVMFuzzerTestOneInput's walk: the top composition). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require RateEnd rate_build rate_check rate_csv memset memcpy
  strlen strcmp bcmp pod_write_ent snprintf reac_rate_prop_parse pod_nearest_ok check_absent check_rate check_malformed
  reac_rate_cfg_decide check_decide reac_rate_refuse_code check_code reac_rate_bit reac_rate_is_closed
  reac_rate_best_drivable check_list reac_rate_drivable_csv check_csv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.Seg Require E01 M01 M02 M03 X01.
From OSSVerify.reac_pw.fuzz_rate Require Statements.

(* The builder evt, from the UBSan walk and the _holds theorems of its callees. *)
Lemma build_ok : rate_build_contract.
Proof.
  exact (rate_build.rate_build_holds memset.memset_holds memcpy.memcpy_holds strlen.strlen_holds
           (pod_write_ent.pod_write_ent_holds memcpy.memcpy_holds memset.memset_holds)).
Qed.

(* The checking evt, from the UBSan walk and the _holds theorems of its callees. *)
Lemma check_ok : rate_check_contract.
Proof.
  exact (rate_check.rate_check_holds memcpy.memcpy_holds
           (reac_rate_prop_parse.reac_rate_prop_parse_holds strcmp.strcmp_holds) strcmp.strcmp_holds
           pod_nearest_ok.pod_nearest_ok check_absent.check_absent_holds check_rate.check_rate_holds
           check_malformed.check_malformed_holds reac_rate_cfg_decide.reac_rate_cfg_decide_holds
           check_decide.check_decide_holds reac_rate_refuse_code.reac_rate_refuse_code_holds
           (check_code.check_code_holds strcmp.strcmp_holds) reac_rate_bit.reac_rate_bit_holds
           reac_rate_is_closed.reac_rate_is_closed_holds reac_rate_best_drivable.reac_rate_best_drivable_holds
           check_list.check_list_holds).
Qed.

(* The csv evt, from the UBSan walk and the _holds theorems of its callees. *)
Lemma csv_ok : rate_csv_contract.
Proof.
  exact (rate_csv.rate_csv_holds memset.memset_holds
           (reac_rate_drivable_csv.reac_rate_drivable_csv_holds snprintf.snprintf_holds memcpy.memcpy_holds)
           (check_csv.check_csv_holds bcmp.bcmp_holds)).
Qed.

(* A segment lemma as its file states it once its Section closes (passed with @, so that its implicit FP state
   and run ceiling are not resolved before the binders are introduced): the binders, then the premises (frame
   facts and the contract the segment takes) up to the folded segment statement, each premise found among them. *)
Ltac seg L := red; intros fx rc B APIf LS SH SK ra empty; repeat match goal with |- _ -> _ => intro end;
  unshelve eapply L; eassumption.

Lemma seg_E01_ok : RateEnd.seg_E01_stmt.
Proof. seg @E01.seg_E01. Qed.

Lemma seg_M01_ok : RateEnd.seg_M01_stmt.
Proof. seg @M01.seg_M01. Qed.

Lemma seg_M02_ok : RateEnd.seg_M02_stmt.
Proof. exact M02.seg_M02_stmt_holds. Qed.

Lemma seg_M03_ok : RateEnd.seg_M03_stmt.
Proof. seg @M03.seg_M03. Qed.

Lemma seg_X01_ok : RateEnd.seg_X01_stmt.
Proof. seg @X01.seg_X01. Qed.

Theorem ubsan_halts_holds : Statements.ubsan_halts.
Proof.
  exact (RateEnd.ubsan_halts_of_callees seg_E01_ok seg_M01_ok seg_M02_ok seg_M03_ok seg_X01_ok
           build_ok check_ok csv_ok).
Qed.
