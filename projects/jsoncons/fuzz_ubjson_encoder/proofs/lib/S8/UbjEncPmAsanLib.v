(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StoreOk AsanAcct HeapIface HeapIfaceA HeapIfaceAEx HeapIfaceAEr IcptIfaceA LibIface LibIfaceAB LibIfaceAE L5Defs L5Core L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeSpecsAa PeSpecsAmc PeCSinkA PeCSpecsA PeCSpecsAa PeCTopA PeCTopAsmA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition lib_ok_stmtFX (FAMP : asan_run -> (list (list Z) -> asan_iface) -> Prop) (L : asan_layout) (Lay : lib_layoutA) (LSt : lib_statics)
           (PayOk PayExport : list byte -> Prop) : Prop :=
  forall (ar : asan_run) (HIk : list (list Z) -> asan_iface), FAMP ar HIk ->
    lla_L Lay = L /\ lib_iface_okA_x Lay ar SCFG (HAJ.strict_of (HIk [])) LSt PayOk PayExport.

Section A.
Variables (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (LR : HAR.layoutR) (P : PESKA.sink_policyA).
Hypothesis LY : PMA.layout L C.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis MCC : PMAMC.mcmp_cells C.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Hypothesis PMODE : PESKA.spa_mode P.
Hypothesis NMAXOK : PESKA.spa_nmax P <= HAR.NREQ.
Hypothesis LEARNOK : forall n, 0 < n <= PESKA.spa_nmax P -> HAR.ngrant n -> PESKA.spa_cap P n.

Hypothesis ROWS : forall ar HIk, PECASMA.fam_ok L C IL LR ar HIk -> PECASMA.rows_open L ar HIk P.
Theorem lib_okFX_A (PayOk PayExport : list byte -> Prop) :
  PECSA.pay_in P PayOk -> PECSA.pay_out P PayExport ->
  lib_ok_stmtFX (PECASMA.fam_ok L C IL LR) L (PECASMA.LayA L P) PECASMA.TopLSA PayOk PayExport.
Proof.
  intros PIN POUT ar HIk FAM. split; [reflexivity|].
  exact (PECASMA.top_iface_asm L C IL LR ar HIk P LY ILY MCC PO PMODE NMAXOK LEARNOK FAM (ROWS ar HIk FAM) PayOk PayExport PIN POUT).
Qed.
End A.

Section SA.
Variables (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (LR : HAR.layoutR).
Hypothesis LY : PMA.layout L C.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis MCC : PMAMC.mcmp_cells C.
Definition P_SA : PESKA.sink_policyA := PESKA.SP_SA L 34.
Lemma P_SA_ok : PESKA.sink_policyA_ok L P_SA.
Proof.
  pose proof (PMA.ly_cost L C LY) as (HK & HL & HO).
  apply (PESKA.SP_SA_ok L 34); [lia| rewrite HK; lia| rewrite HL; lia| rewrite HO; apply Z.pow_nonneg; lia].
Qed.
Lemma P_SA_mode : PESKA.spa_mode P_SA.
Proof. reflexivity. Qed.
Lemma P_SA_nmax : PESKA.spa_nmax P_SA <= HAR.NREQ.
Proof. cbn [P_SA PESKA.SP_SA PESKA.spa_nmax]. unfold HAR.NREQ. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma P_SA_learn : forall n, 0 < n <= PESKA.spa_nmax P_SA -> HAR.ngrant n -> PESKA.spa_cap P_SA n.
Proof. exact (PESKA.SP_SA_learn L 34 HAR.ngrant (fun n H => H)). Qed.
Lemma P_SA_pay_in : PECSA.pay_in P_SA (fun _ => True).
Proof. intros payload _ _ n. exact I. Qed.
Lemma P_SA_pay_out : PECSA.pay_out P_SA (fun _ => True).
Proof. intros payload c _ _ _ _. exact I. Qed.

Lemma P_SA_credit : PECASMA.tk P_SA = 1304 /\ PECASMA.tb P_SA = 107447582717.
Proof.
  pose proof (PMA.ly_cost L C LY) as (HK & HL & HO).
  unfold PECASMA.tk, PECASMA.tb, PECASMA.TOPK0, PECASMA.TOPB0, P_SA, PESKA.SP_SA, PESKA.potT. cbn [PESKA.spa_pot fst snd].
  rewrite HK, HL, HO. vm_compute. split; reflexivity.
Qed.
Theorem lib_okFX_SA :
  lib_ok_stmtFX (PECASMA.fam_ok L C IL LR) L (PECASMA.LayA L P_SA) PECASMA.TopLSA (fun _ => True) (fun _ => True).
Proof.
  exact (lib_okFX_A L C IL LR P_SA LY ILY MCC P_SA_ok P_SA_mode P_SA_nmax P_SA_learn (fun ar HIk _ => PECASMA.rows_closed L ar HIk P_SA)
           (fun _ => True) (fun _ => True) P_SA_pay_in P_SA_pay_out).
Qed.
End SA.
End SCFG_1.
