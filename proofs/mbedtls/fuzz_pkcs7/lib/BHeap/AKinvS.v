(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AKinv AJ HMLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AKinvS () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.BHeap.AKinv.kinv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.mstepA"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.Run.mi_account_step"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.mo_mat"; "Corelib.Init.Datatypes.option"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "Corelib.Init.Datatypes.None"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.mstepsA"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.spinningJ"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_mem"].

Section ARUN_1. Context {hAR : arun}.
Section GlueS.
Variable segs : list Segment.
Variable L : asan_layout.

(* [comment removed for export] *)
#[using="Type"] Lemma mstepA_K : ltac2:(CDefT.buildp (gd_tbl_AKinvS ()) "PCS,P,$0.SpPK,P,$1.SpPms,$2.Pms',$2.Pmo,$1.P,(3.VhAR,VL,R5.R4.)P,A1.R5.R2.P,(4.Vsegs,VL,R7.R5.R4.)(5.$1.Lmo',$1.(6.(7.(8.(9.$2.$1.))(:.Vsegs,R7.R5.)(;.(9.$2.$1.)(<.$2.$1.R6.R1.)))(6.A1.R8.R1.(6.(=.R5.R1.)(7.(>.(?.&40.))(10.R7.)(11.(?.&40.)))))))")
(* [comment removed for export] *).
Proof.
  intros CS K ms ms' mo KL HK [Hsvc (acc & Hst & OK)].
  ddestruct (mi_account_step_ok segs L (KAI CS K) (KAI_laws L CS K KL) CS ms ms' acc mo (conj HK (fun x H => H)) Hst OK)
    as (mo' & Hacc & [HK' _] & MM).
  exists mo'. split; [exact Hacc|]. split; [exact HK'|]. split; [exact MM| exact Hsvc].
Qed.

#[using="Type"] Lemma evtA_aevtS_K : ltac2:(CDefT.buildp (gd_tbl_AKinvS ()) "PCS,P,$0.SpPK,P,$1.SpPP,P,$2.SpPQ,P,$12.SpPms,$2.Pmo,$1.P,(3.VhAR,VL,R6.R5.)P,A1.R6.R2.P,(13.Vsegs,VL,R8.R6.R4.)P,Pms',$2.Pmo',$1.P,A1.R9.R2.P,A1.R;.R2.P,(=.R8.R3.)(14.Vsegs,R;.(15.R5.R4.))(14.Vsegs,R7.(15.R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros CS K P Q ms mo KL HK EV CONT.
  eapply aevtS_bind.
  - eapply (evtA_aevtS segs L (KAI CS K) (KAI_laws L CS K KL) CS P ms mo); [| exact EV]. split; [exact HK| auto].
  - (intros [ms' mo'] dd_H; ddestruct dd_H as (HP & [HK' _] & MM)). cbn in *. apply CONT; assumption.
Qed.

#[using="Type"] Lemma mstepsA_orS_K : ltac2:(CDefT.buildp (gd_tbl_AKinvS ()) "PCS,P,$0.SpPK,P,$1.SpPQ,P,$12.SpPms,$2.Pms',$2.Pmo,$1.P,(3.VhAR,VL,R6.R5.)P,A1.R6.R2.P,(16.Vsegs,VL,R8.R5.R4.)P,Pmo',$1.P,A1.R9.R1.P,(=.R6.R2.)(17.(14.Vsegs,R:.(15.R8.R3.))(18.Vsegs,(15.R8.R3.)))(17.(14.Vsegs,R8.(15.R7.R5.))(18.Vsegs,(15.R7.R5.)))")
(* [comment removed for export] *).
Proof.
  intros CS K Q ms ms' mo KL HK H. revert mo HK.
  induction H as [ms | ms ms1 ms2 H1 H IH]; intros mo HK CONT.
  - apply CONT; [exact HK| apply mo_mat_refl].
  - ddestruct (mstepA_K CS K ms ms1 mo KL HK H1) as (mo1 & Hacc & HK1 & MM1 & Hsvc).
    destruct (IH mo1 HK1 ltac:(intros mo' HK' MM'; apply CONT; [exact HK'| eapply mo_mat_trans; eauto])) as [A | SP].
    + left. apply aevtS_step.
      * exists (mkCfg ms1 mo1). split; [| exact A]. apply sstep_instr; [exact (ki_halted KL mo HK)| exact Hsvc| exact Hacc].
      * intros e st Hs. destruct (sstep_acc_inv segs _ _ _ _ _ _ Hsvc Hacc Hs) as [-> ->]. split; [reflexivity| congruence].
      * intros e c' Hs. destruct (sstep_acc_inv segs _ _ _ _ _ _ Hsvc Hacc Hs) as [_ E]. inversion E; subst. left. exact A.
    + right. eapply spinningJ_step; [exact Hsvc| exact Hacc| exact SP].
Qed.

#[using="Type"] Lemma evtA_orS_K : ltac2:(CDefT.buildp (gd_tbl_AKinvS ()) "PCS,P,$0.SpPK,P,$1.SpPP,P,$2.SpPQ,P,$12.SpPms,$2.Pmo,$1.P,(3.VhAR,VL,R6.R5.)P,A1.R6.R2.P,(13.Vsegs,VL,R8.R6.R4.)P,Pms',$2.Pmo',$1.P,A1.R9.R2.P,A1.R;.R2.P,(=.R8.R3.)(17.(14.Vsegs,R;.(15.R5.R4.))(18.Vsegs,(15.R5.R4.)))(17.(14.Vsegs,R7.(15.R6.R5.))(18.Vsegs,(15.R6.R5.)))")
(* [comment removed for export] *).
Proof.
  (intros CS K P Q ms mo KL HK dd_H; ddestruct dd_H as (ms' & H & HP); intros CONT).
  eapply mstepsA_orS_K; [exact KL| exact HK| exact H|]. intros mo' HK' MM. apply CONT; assumption.
Qed.

#[using="Type"] Lemma evtA_spinJ_K : ltac2:(CDefT.buildp (gd_tbl_AKinvS ()) "PCS,P,$0.SpPK,P,$1.SpPP,P,$2.SpPms,$2.Pmo,$1.P,(3.VhAR,VL,R5.R4.)P,A1.R5.R2.P,(13.Vsegs,VL,R7.R5.R4.)P,Pms',$2.Pmo',$1.P,A1.R8.R2.P,A1.R:.R2.P,(=.R8.R3.)(18.Vsegs,(15.R5.R4.))(18.Vsegs,(15.R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros CS K P ms mo KL HK EV CONT.
  destruct (evtA_orS_K CS K P (fun _ => False) ms mo KL HK EV ltac:(intros; right; apply CONT; assumption)) as [A | SP]; [| exact SP].
  exfalso. clear - A. remember (mkCfg ms mo) as c. clear Heqc. revert c A.
  apply aevtS_ind2; [intros c F; exact F|]. (intros c dd_H; ddestruct dd_H as (c' & _ & _ & F); intros _ _). exact F.
Qed.

End GlueS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section GlueSJ.
Variable segs : list Segment.
Variable L : asan_layout.
Hypothesis WVH : forall (m : word -> option byte) (x : word), JF <= bv_unsigned x -> wview segs m x = m x.

#[using="WVH"] Lemma evtA_aevtS_KJ0 : ltac2:(CDefT.buildp (gd_tbl_AKinvS ()) "PCS,P,$0.SpPK,P,$1.SpPP,P,$2.SpPQ,P,$12.SpPms,$2.Pmo,$1.P,(3.VhAR,VL,R6.R5.)P,A1.R6.R2.P,(19.(1:.R4.)R3.)P,(13.Vsegs,VL,R9.R7.R5.)P,Pms',$2.Pmo',$1.P,A1.R:.R2.P,A1.R<.R2.P,(=.R9.R3.)P,(19.(1:.R5.)R4.)(14.Vsegs,R=.(15.R6.R5.))(14.Vsegs,R8.(15.R7.R6.))")
(* [comment removed for export] *).
Proof.
  intros CS K P Q ms mo KL HK HJ EV CONT.
  eapply (evtA_aevtS_K segs L CS K _ Q ms mo KL HK (evtA_nwmono segs L CS P ms EV)).
  cbn beta. intros ms' mo' [HP NW] HK' MM. apply CONT; try assumption.
  apply (J_nwmono segs WVH _ _ _ NW). eapply J_mat; eauto.
Qed.

#[using="WVH"] Lemma evtA_orS_KJ0 : ltac2:(CDefT.buildp (gd_tbl_AKinvS ()) "PCS,P,$0.SpPK,P,$1.SpPP,P,$2.SpPQ,P,$12.SpPms,$2.Pmo,$1.P,(3.VhAR,VL,R6.R5.)P,A1.R6.R2.P,(19.(1:.R4.)R3.)P,(13.Vsegs,VL,R9.R7.R5.)P,Pms',$2.Pmo',$1.P,A1.R:.R2.P,A1.R<.R2.P,(=.R9.R3.)P,(19.(1:.R5.)R4.)(17.(14.Vsegs,R=.(15.R6.R5.))(18.Vsegs,(15.R6.R5.)))(17.(14.Vsegs,R8.(15.R7.R6.))(18.Vsegs,(15.R7.R6.)))")
(* [comment removed for export] *).
Proof.
  intros CS K P Q ms mo KL HK HJ EV CONT.
  eapply (evtA_orS_K segs L CS K _ Q ms mo KL HK (evtA_nwmono segs L CS P ms EV)).
  cbn beta. intros ms' mo' [HP NW] HK' MM. apply CONT; try assumption.
  apply (J_nwmono segs WVH _ _ _ NW). eapply J_mat; eauto.
Qed.
End GlueSJ.

(* [comment removed for export] *)
Definition evtA_aevtS_KJ (L : asan_layout) := evtA_aevtS_KJ0 asegs L wview_high.
Definition evtA_orS_KJ (L : asan_layout) := evtA_orS_KJ0 asegs L wview_high.


End ARUN_1.
