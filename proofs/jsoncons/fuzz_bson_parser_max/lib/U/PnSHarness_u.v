(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core L5CoreKit
     PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgV8 PnLayout PnModel PnStatics PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u PnTopS_u PnSHarnessStmts_u
     PnSHarness1_u PnSHarness2_u PnSHarness3_u PnSHarness4_u PnSHarness5_u PnSHarness6_u PnSHarness7_u PnSHarness8_u PnSHarness9_u PnSHarness10_u PnSHarness11_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNHT.
Import PMS. Import PNH.

Section Glue.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.

Theorem harness_call_ok : PNH.harness_deps L HI -> lib_call_ok (PNTS.TopLay L) SCFG HI PNTS.TopLS.
Proof.
  intros [STR ISS RDR SYS RST PARSE OPD SDT LDT IDT].
  unfold lib_call_ok. intros fx g LB cr sp ptr ra payload R M model K PRE HH Mh Ml Mm K0 KONT.
  unfold lib_cfg in *. cbn [ll_heap ll_entry PNTS.TopLay] in KONT |- *. rewrite (ly_segs L LY) in KONT |- *.
  set (n := Z.of_nat (length payload)).
  assert (Hn : 0 <= n < 2 ^ 26) by (pose proof (lp_len _ _ _ _ _ _ _ _ _ _ _ PRE) as X; unfold n; lia).
  assert (Hcr0 : PMSP.credit_le (PNTS.TOPK, PNTS.TOPB n) cr) by exact (lp_credit _ _ _ _ _ _ _ _ _ _ _ PRE).
  assert (Hgp : getr R (reg 3) = Z_to_bv 64 (pa_gp AD)) by (rewrite <- L5K.rl3; exact (lp_gp _ _ _ _ _ _ _ _ _ _ _ PRE)).
  assert (Htp : getr R (reg 4) = Z_to_bv 64 (pa_tp AD)).
  { rewrite <- L5K.rl4. pose proof (lp_tp _ _ _ _ _ _ _ _ _ _ _ PRE) as X. cbn [ll_heap PNTS.TopLay] in X. rewrite (ly_tp L LY) in X. exact X. }
  assert (Hsp0 : getr R (reg 2) = Z_to_bv 64 sp) by (rewrite <- L5K.rl2; exact (lp_sp _ _ _ _ _ _ _ _ _ _ _ PRE)).
  assert (Hra : L5.ra_ok ra) by exact (lp_ra_ok _ _ _ _ _ _ _ _ _ _ _ PRE).
  apply (PNH1.stage1 L HI LY HIok STR fx g LB cr sp ptr ra payload R M model K PRE HH Mh Ml Mm K0). fold n.
  intros fx1 R1 M1 model1 cr1 s H1.
  apply (PNH2.stage2 L HI LY HIok R M model sp ra n LB cr g Hn Hcr0 Hgp Htp ISS fx1 R1 M1 model1 cr1 s K H1 K0).
  clear fx1 R1 M1 model1 cr1 H1. intros fx2 R2 M2 model2 cr2 s2 sm H2.
  apply (PNH3.stage3 L HI LY HIok R M model sp ra n LB cr g Hn Hcr0 Hgp Htp RDR fx2 R2 M2 model2 cr2 s s2 sm K H2 K0).
  clear fx2 R2 M2 model2 cr2 H2. intros fx3 R3 M3 model3 cr3 qc b H3.
  apply (PNH4.stage4 L HI LY HIok R M model sp ra n LB cr g Hn Hcr0 Hgp Htp SYS fx3 R3 M3 model3 cr3 s s2 sm qc b K H3 K0).
  clear fx3 R3 M3 model3 H3. intros fx4 R4 M4 model4 H4.
  apply (PNH5.stage5 L HI LY HIok R M model sp ra n LB cr g Hn Hcr0 Hgp Htp RST PARSE fx4 R4 M4 model4 cr3 s s2 sm qc b K H4 K0).
  clear fx4 R4 M4 model4 cr3 H4. intros fx5 R5 M5 model5 cr5 p sm5 ax H5.
  apply (PNH6.stage6 L HI LY HIok R M model sp ra n LB cr g Hn Hcr0 Hgp Htp OPD fx5 R5 M5 model5 cr5 s s2 p sm5 ax K H5 K0).
  clear fx5 R5 M5 model5 H5. intros fx6 R6 M6 model6 H6.
  apply (PNH7.stage7 L HI LY HIok R M model sp ra n LB cr g Hn Hcr0 Hgp Htp OPD fx6 R6 M6 model6 cr5 s s2 (PNM.b_src p) (PNM.b_bb p) (PNM.b_nb p) (PNM.b_tb p) sm5 ax K H6 K0).
  clear fx6 R6 M6 model6 H6. intros fx7 R7 M7 model7 H7.
  apply (PNH8.stage8 L HI LY HIok R M model sp ra n LB cr g Hn Hcr0 Hgp Htp OPD fx7 R7 M7 model7 cr5 s s2 (PNM.b_src p) (PNM.b_bb p) (PNM.b_nb p) sm5 ax K H7 K0).
  clear fx7 R7 M7 model7 H7. intros fx8 R8 M8 model8 H8.
  apply (PNH9.stage9 L HI LY HIok R M model sp ra n LB cr g Hn Hcr0 Hgp Htp OPD SDT fx8 R8 M8 model8 cr5 s s2 (PNM.b_src p) (PNM.b_bb p) sm5 ax K H8 K0).
  clear fx8 R8 M8 model8 H8. intros fx9 R9 M9 model9 H9.
  apply (PNH10.stage10 L HI LY HIok R M model sp ra n LB cr g Hn Hcr0 Hgp Htp OPD LDT IDT fx9 R9 M9 model9 cr5 s s2 sm5 ax K H9 K0).
  clear fx9 R9 M9 model9 H9. intros fx10 R10 M10 model10 H10.
  apply (PNH11.stage11 L HI LY HIok R M model sp ra n LB cr g Hn Hcr0 Hgp Htp Hsp0 Hra payload eq_refl OPD fx10 R10 M10 model10 cr5 s ax K H10 K0).
  clear fx10 R10 M10 model10 H10. intros fx11 g11 R11 M11 model11 cr11 POST HH11 MB11.
  exact (KONT fx11 g11 R11 M11 model11 cr11 POST HH11 MB11).
Qed.

(* [comment removed for export] *)
Theorem harness_iface_ok : PNH.harness_deps L HI -> lib_iface_ok (PNTS.TopLay L) SCFG HI PNTS.TopLS.
Proof. intros D. apply (PNTS.top_iface_ok SCFG L HI LY). exact (harness_call_ok D). Qed.

End Glue.
End PNHT.
