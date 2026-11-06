(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlgX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.ShapeEF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.Spec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.BigintSpec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap Require HnIface HnInst0. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0283. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0283. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.HnIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.HnInst0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0283.HnClosed OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0283.HnV16 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0283.HnPmLayout.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0258. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Ns0HeapBridgeHn. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0106. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0211. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0286. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0258. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0258.Ns0DrvLibL OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0258.Ns0DrvG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0258.Ns0DrvMain OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Ns0HeapBridgeHn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PnQStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnTopS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnVis OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0106.PnSHarnessStmts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0211.PnSHarness OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0143.PnSExitCells OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnVisN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124.PnRunN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0286.NTopAsmS.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import FrmInit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition cfg0 : SpuriousCfg := mkSpuriousCfg false true true true true true.
#[export] Instance ScfgP_cfg0 : ScfgP := {| SCFG := cfg0 |}.

Section FPX_1.
#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma drv_lib_layout_top0 : forall sp, valid_sp sp ->
  Ns0DrvLibL.drv_lib_layout (PQTS.TopLay (HnInst0.L0 (bv_unsigned sp))) (HnInst0.L0 (bv_unsigned sp)).
Proof.
  intros sp Hsp. constructor; try reflexivity; try (cbn; lia).
  - intros iv Hin. unfold PQTS.TopLay, pm_foot in Hin. cbn in Hin. repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin.
  - intros iv Hin. cbn in Hin. destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn; lia.
  - intros n Hn. cbn. unfold PQTS.TOPK, PQTS.TOPB. lia.
Qed.

(* [comment removed for export] *)
Lemma budget0 : forall sp n, valid_sp sp -> 0 <= n < 67108864 ->
  Ns0DrvG.cred (HnInst0.L0 (bv_unsigned sp))
    (1 + 4 * fst (ll_credit (PQTS.TopLay (HnInst0.L0 (bv_unsigned sp))) n))
    (n + 2 ^ 20 + 4 * snd (ll_credit (PQTS.TopLay (HnInst0.L0 (bv_unsigned sp))) n)) 0
    (debit (HnInst0.L0 (bv_unsigned sp)) (HnInst0.K0, HnInst0.B0) 65536).
Proof.
  intros sp n Hsp Hn. unfold Ns0DrvG.cred, Ns0DrvG.CAPk, debit. cbn [fst snd hl_k_per_malloc hl_b_overhead HnInst0.L0 ll_credit PQTS.TopLay].
  unfold PQTS.TOPK, PQTS.TOPB.
  replace HnInst0.K0 with 8192 by (vm_compute; reflexivity). replace HnInst0.B0 with (2 ^ 34 - 161677312 - 85427352) by (vm_compute; reflexivity). lia.
Qed.

Definition sptop_window (sptop : Z) : Prop := 0x7fff80000000 <= sptop <= 2 ^ 47.
Lemma valid_sp_window : forall sp, valid_sp sp -> sptop_window (bv_unsigned sp).
Proof.
  intros sp (Hlo & Hhi & _). unfold sptop_window. unfold sp_window_lo in Hlo. unfold sp_window_hi in Hhi.
  split; [exact Hlo | exact Hhi].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition open_S : Prop :=
  forall (bmK : BMode) (L : heap_layout) (HI : heap_iface),
    PMS.layout L -> @heap_iface_ok L cfg0 bmK HI -> @heap_ifaceR_ok L cfg0 bmK HI -> @NTASM.open_S ScfgP_cfg0 bmK L HI.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section AnyMode.
Context {bmK : BMode}.

(* [comment removed for export] *)
Lemma LIB0_of_ledger : open_S ->
  forall sp, valid_sp sp -> lib_iface_ok (PQTS.TopLay (HnInst0.L0 (bv_unsigned sp))) cfg0 (HnV16.HIV0 (bv_unsigned sp)) PQTS.TopLS.
Proof.
  intros OS sp V. pose proof (valid_sp_window sp V) as W.
  assert (LY : PMS.layout (HnInst0.L0 (bv_unsigned sp))) by (apply pm_layout_L0; unfold sptop_window in W; lia).
  pose proof (HnV16.HIV0_ok (bv_unsigned sp) cfg0 eq_refl) as HIok.
  pose proof (Ns0HeapBridgeHn.HIV0_okR_at cfg0 eq_refl sp) as HIRok.
  assert (LM : PQH.layoutM (HnInst0.L0 (bv_unsigned sp))) by (unfold PQH.layoutM; cbn; lia).
  exact (@NTASM.top_iface_of_open ScfgP_cfg0 bmK (HnInst0.L0 (bv_unsigned sp)) (HnV16.HIV0 (bv_unsigned sp)) LY HIok HIRok LM
           (HnV16.HIV0_mallocN (bv_unsigned sp) cfg0 eq_refl) (OS bmK _ _ LY HIok HIRok)).
Qed.

Theorem msgpack_enc_src_at (lim : Z) : open_S -> bm_on = true \/ 2 ^ 34 <= lim -> Ns0DrvMain.src_realizes_stmt2 cfg0 lim.
Proof.
  intros OS HL.
  exact (Ns0HeapBridgeHn.src0_realizes_spec_heap cfg0 eq_refl eq_refl
           (fun sp => PQTS.TopLay (HnInst0.L0 (bv_unsigned sp))) (fun _ => PQTS.TopLS)
           drv_lib_layout_top0 (LIB0_of_ledger OS) (fun sp _ => PQSXC.top_lsx) budget0 lim HL).
Qed.
End AnyMode.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem msgpack_enc_src : open_S -> Ns0DrvMain.src_realizes_stmt2 cfg0 source_alloc_limit.
Proof. intros OS. apply (msgpack_enc_src_at source_alloc_limit OS). right. vm_compute. discriminate. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma open_S_closed : open_S.
Proof. intros bmK L HI LY HIok HIRok. constructor. intros _ _ _; exact I. Qed.

End FPX_1.
