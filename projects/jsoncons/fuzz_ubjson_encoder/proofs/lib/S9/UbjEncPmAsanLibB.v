(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec StoreOk AsanAcct HeapIface HeapIfaceA HeapIfaceAEx HeapIfaceAEr IcptIfaceAB0 LibIface LibIfaceAB LibIfaceAE L5Defs L5Core L5DefsAB0.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeSpecsAb PeSpecsAmc PeCSinkA PeCSpecsA PeCSpecsAb PeCTopB PeCTopAsmB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition lib_ok_stmtFX (FAMP : asan_run -> (list (list Z) -> asan_iface) -> Prop) (L : asan_layout) (Lay : lib_layoutA) (LSt : lib_statics)
           (PayOk PayExport : list byte -> Prop) : Prop :=
  forall (ar : asan_run) (HIk : list (list Z) -> asan_iface), FAMP ar HIk ->
    lla_L Lay = L /\ lib_iface_okA_x Lay ar SCFG (HAJ.strict_of (HIk [])) LSt PayOk PayExport.

Section LibB.
Variables (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (LR : HAR.layoutR) (P : PESKA.sink_policyA).
Hypothesis LY : PMB.layout L C.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis MCC : PMAMC.mcmp_cells_b C.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Hypothesis PMODE : PESKA.spa_mode P.
Hypothesis NMAXOK : PESKA.spa_nmax P <= HAR.NREQ.
Hypothesis LEARNOK : forall n, 0 < n <= PESKA.spa_nmax P -> HAR.ngrant n -> PESKA.spa_cap P n.
Hypothesis ROWS : forall ar HIk, PECASMB.fam_ok L C IL LR ar HIk -> PECASMB.rows_open L ar HIk P.
Theorem lib_okFX_B (PayOk PayExport : list byte -> Prop) :
  PECSB.pay_in P PayOk -> PECSB.pay_out P PayExport ->
  lib_ok_stmtFX (PECASMB.fam_ok L C IL LR) L (PECASMB.LayA L P) PECASMB.TopLSA PayOk PayExport.
Proof.
  intros PIN POUT ar HIk FAM. split; [reflexivity|].
  exact (PECASMB.top_iface_asm L C IL LR ar HIk P LY ILY MCC PO PMODE NMAXOK LEARNOK FAM (ROWS ar HIk FAM) PayOk PayExport PIN POUT).
Qed.
End LibB.

Section SB.
Variables (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (LR : HAR.layoutR).
Hypothesis LY : PMB.layout L C.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis MCC : PMAMC.mcmp_cells_b C.
Definition P_SB : PESKA.sink_policyA := PESKA.SP_SA L 34.
Lemma P_SB_ok : PESKA.sink_policyA_ok L P_SB.
Proof.
  pose proof (PMB.ly_cost L C LY) as (HK & HL & HO).
  apply (PESKA.SP_SA_ok L 34); [lia| rewrite HK; lia| rewrite HL; lia| rewrite HO; apply Z.pow_nonneg; lia].
Qed.
Lemma P_SB_mode : PESKA.spa_mode P_SB.
Proof. reflexivity. Qed.
Lemma P_SB_nmax : PESKA.spa_nmax P_SB <= HAR.NREQ.
Proof. cbn [P_SB PESKA.SP_SA PESKA.spa_nmax]. unfold HAR.NREQ. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma P_SB_learn : forall n, 0 < n <= PESKA.spa_nmax P_SB -> HAR.ngrant n -> PESKA.spa_cap P_SB n.
Proof. exact (PESKA.SP_SA_learn L 34 HAR.ngrant (fun n H => H)). Qed.
Lemma P_SB_pay_in : PECSB.pay_in P_SB (fun _ => True).
Proof. intros payload _ _ n. exact I. Qed.
Lemma P_SB_pay_out : PECSB.pay_out P_SB (fun _ => True).
Proof. intros payload c _ _ _ _. exact I. Qed.

Lemma P_SB_credit : PECASMB.tk P_SB = 1304 /\ PECASMB.tb P_SB = 107447582717.
Proof.
  pose proof (PMB.ly_cost L C LY) as (HK & HL & HO).
  unfold PECASMB.tk, PECASMB.tb, PECASMB.TOPK0, PECASMB.TOPB0, P_SB, PESKA.SP_SA, PESKA.potT. cbn [PESKA.spa_pot fst snd].
  rewrite HK, HL, HO. vm_compute. split; reflexivity.
Qed.
Theorem lib_okFX_SB :
  lib_ok_stmtFX (PECASMB.fam_ok L C IL LR) L (PECASMB.LayA L P_SB) PECASMB.TopLSA (fun _ => True) (fun _ => True).
Proof.
  exact (lib_okFX_B L C IL LR P_SB LY ILY MCC P_SB_ok P_SB_mode P_SB_nmax P_SB_learn (fun ar HIk _ => PECASMB.rows_closed L ar HIk P_SB)
           (fun _ => True) (fun _ => True) P_SB_pay_in P_SB_pay_out).
Qed.
End SB.
End SCFG_1.
