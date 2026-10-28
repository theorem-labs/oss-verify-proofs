(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF Spec BigintSpec HeapIface LibIface L5Defs.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Bridge Require Import HeapInst0_u HeapClosed_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0DrvLibL_u Bs0DrvG_u Bs0DrvMain_u Bs0HeapBridge_u
     Bs0PmLayout_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PnStatics PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u PnTopS_u PnSHarness_u PnSHarnessStmts_u PnSExitCells_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require PropExec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition cfg0 : SpuriousCfg := mkSpuriousCfg false true true true true true.
#[export] Instance ScfgP_cfg0 : ScfgP := {| SCFG := cfg0 |}.
Lemma sc_alloc_cfg0 : sc_alloc (@SCFG ScfgP_cfg0) = false.
Proof. reflexivity. Qed.

Section FPX_1.
#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma drv_lib_layout_top0 : forall sp, valid_sp sp ->
  Bs0DrvLibL_u.drv_lib_layout (PNTS.TopLay (HeapInst0_u.L0 (bv_unsigned sp))) (HeapInst0_u.L0 (bv_unsigned sp)).
Proof.
  intros sp Hsp. constructor; try reflexivity; try (cbn; lia).
  - intros iv Hin. unfold PNTS.TopLay, PNST.pn_foot, pm_foot, PNL.pn_d128_foot in Hin. cbn in Hin. repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin.
  - intros iv Hin. cbn in Hin. destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn; lia.
  - intros n Hn. cbn. unfold PNTS.TOPK, PNTS.TOPB. lia.
Qed.


(* [comment removed for export] *)
Lemma budget0 : forall sp n, valid_sp sp -> 0 <= n < 67108864 ->
  Bs0DrvG_u.cred (HeapInst0_u.L0 (bv_unsigned sp))
    (HeapInst0_u.KPM + 4 * fst (ll_credit (PNTS.TopLay (HeapInst0_u.L0 (bv_unsigned sp))) n))
    (n + HeapInst0_u.BOV + 4 * snd (ll_credit (PNTS.TopLay (HeapInst0_u.L0 (bv_unsigned sp))) n)) 0
    (debit (HeapInst0_u.L0 (bv_unsigned sp)) (HeapInst0_u.K0, HeapInst0_u.B0) 65536).
Proof.
  intros sp n Hsp Hn. unfold Bs0DrvG_u.cred, Bs0DrvG_u.CAPk, debit. cbn [fst snd hl_k_per_malloc hl_b_overhead HeapInst0_u.L0 ll_credit PNTS.TopLay].
  unfold PNTS.TOPK, PNTS.TOPB.
  replace HeapInst0_u.BOV with 6350523 by (vm_compute; reflexivity). replace HeapInst0_u.KPM with 8 by (vm_compute; reflexivity).
  replace HeapInst0_u.K0 with 8000 by (vm_compute; reflexivity). replace HeapInst0_u.B0 with (2 ^ 33) by (vm_compute; reflexivity). lia.
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sptop_window (sptop : Z) : Prop := 0x7fff80000000 <= sptop <= 2 ^ 47.
Lemma valid_sp_window : forall sp, valid_sp sp -> sptop_window (bv_unsigned sp).
Proof.
  intros sp (Hlo & Hhi & _). unfold sptop_window. unfold sp_window_lo in Hlo. unfold sp_window_hi in Hhi.
  split; [exact Hlo | exact Hhi].
Qed.

(* [comment removed for export] *)
Definition PACKAGES_src : Prop := forall sptop, sptop_window sptop -> @PNH.harness_deps ScfgP_cfg0 _ (L0 sptop) (HI0 sptop).

Lemma LIB0_of_packages : PACKAGES_src ->
  forall sp, valid_sp sp -> lib_iface_ok (PNTS.TopLay (L0 (bv_unsigned sp))) cfg0 (HI0 (bv_unsigned sp)) PNTS.TopLS.
Proof.
  intros PK sp V. pose proof (valid_sp_window sp V) as W.
  assert (LY : PMS.layout (L0 (bv_unsigned sp))) by (apply pm_layout_L0; unfold sptop_window in W; lia).
  exact (@PNHT.harness_iface_ok ScfgP_cfg0 _ (L0 (bv_unsigned sp)) (HI0 (bv_unsigned sp)) LY (HI0_ok_closed (bv_unsigned sp) cfg0 eq_refl) (PK _ W)).
Qed.


End FPX_1.
