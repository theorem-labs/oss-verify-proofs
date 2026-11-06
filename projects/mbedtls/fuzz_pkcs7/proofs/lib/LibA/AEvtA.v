(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Shape PropExec MState Mem Exec AEvt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS.

Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AEvtA () : Init.string Init.list := ["LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.Riscv.Instr.instr"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.Riscv.DecodeC.decode_any"; "Corelib.Init.Datatypes.pair"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.access_report"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step_accesses"; "OSSVerify.KrLib.Lib.MState.MS"; "WithSegs.liftA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.interp_eff_accesses"; "LinuxProcessSemantics.Riscv.Sem.exec"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.Riscv.Sem.Core"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_access"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.mkAccessReport"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step"; "Corelib.Init.Logic.and"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.LibA.ALazy.acc_ok"; "WithSegs.WithLayout.mstepA"; "WithSegs.WithLayout.mstepsA"; "WithSegs.WithLayout.evtA"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "LinuxProcessSemantics.LinuxProcessSem.Run.step_to"; "LinuxProcessSemantics.LinuxProcessSem.Run.mi_account_step"; "LinuxProcessSemantics.LinuxProcessSem.Run.sstep"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.Run.SNext"; "OSSVerify.KrLib.LibA.ALazy.mo_mat"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "OSSVerify.KrLib.Lib.AEvt.aevt"; "LinuxProcessSemantics.LinuxProcessSem.Run.cfg_ms"; "LinuxProcessSemantics.LinuxProcessSem.Run.cfg_model"; "OSSVerify.KrLib.LibA.AEvtS.aevtS"; "WithSegs.WithLayout.WithAI.kinv_laws"; "WithSegs.WithLayout.WithAI.aevtA"].


Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition liftA (ro : word -> option byte) (r : machine_result (access_report (core * (word -> option byte))))
  : machine_result (access_report machine_state) :=
  match r with
  | MachineOk rep =>
      let '(c, m') := @access_value _ rep in
      MachineOk (@mkAccessReport machine_state (MS_of_core c m' ro) (@accessed_ranges _ rep))
  | MachineFault => MachineFault
  | MachineUnmodeled => MachineUnmodeled
  end.

#[using="Type"] Lemma step_accesses_gen : ltac2:(CDefT.buildp (gd_tbl_AEvtA ()) "PR,(0.&5.(1.&40.))PF,(0.&5.(1.&40.))Ppc,(1.&40.)Pfc,(1.&20.)Prv,(2.(1.&40.))Pm,P,(1.&40.)(2.(1.&8.))Pro,P,(1.&40.)(2.(1.&8.))Pw,(1.&20.)Pi,$3.Psz,$4.P,(5.(2.(1.&20.))(6.Vsegs,R8.)(7.(1.&20.)R3.))P,(5.$8.(9.R4.)$:.)P,(5.(2.(;.$3.$4.))(<.R5.)(7.(;.$3.$4.)(=.$3.$4.R4.R3.)))(5.(>.(?.$10.))(11.Vsegs,(12.R=.R<.R;.R:.R9.R8.R7.))(13.R7.(14.Vsegs,(15.(16.&40.R4.)R5.(17.R=.R<.R;.R:.R9.))R8.)))")
(* [comment removed for export] *).
Proof.
  intros R F pc fc rv m ro w i sz Hf He Hd.
  unfold step_accesses. cbn [ms_pc ms_pc_val MS]. rewrite Hf.
  unfold decode_exec_accesses. rewrite He, Hd. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom MS].
  destruct (interp_eff_accesses segs (exec (Z_to_bv 64 sz) i _) m) as [[[c m'] acc]| |]; reflexivity.
Qed.

#[using="Type"] Lemma step_accesses_step : ltac2:(CDefT.buildp (gd_tbl_AEvtA ()) "Pms,$10.Pms',$10.Pacc,(18.$19.)P,(5.(>.(?.$10.))(11.Vsegs,R3.)(1:.(?.$10.)(1;.$10.R2.R1.)))(5.(>.$10.)(1<.Vsegs,R4.)(1:.$10.R3.))")
(* [comment removed for export] *).
Proof.
  intros ms ms' acc H. rewrite <- drop_step_accesses. rewrite H. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithLayout.
Variable L : asan_layout.

Definition mstepA (CS : Z -> Prop) (ms ms' : machine_state) : Prop := ltac2:(CDefT.buildp (gd_tbl_AEvtA ()) "(1=.(5.(2.(1.&40.))(1>.O2.)(1?.(1.&40.)))(20.(18.$19.)Lacc,(18.$19.)(1=.(5.(>.(?.$10.))(11.Vsegs,O2.)(1:.(?.$10.)(1;.$10.O1.R1.)))(21.VL,O3.R1.))))")
(* [comment removed for export] *).

Inductive mstepsA (CS : Z -> Prop) : machine_state -> machine_state -> Prop :=
| mstepsA_refl : forall ms, mstepsA CS ms ms
| mstepsA_cons : forall ms ms1 ms2, mstepA CS ms ms1 -> mstepsA CS ms1 ms2 -> mstepsA CS ms ms2.

#[using="Type"] Lemma mstepsA_trans : forall CS a b c, mstepsA CS a b -> mstepsA CS b c -> mstepsA CS a c.
Proof. intros CS a b c H; induction H; intros; [assumption|]. eapply mstepsA_cons; eauto. Qed.

#[using="Type"] Lemma mstepA_mstep : forall CS ms ms', mstepA CS ms ms' -> mstep segs ms ms'.
Proof. intros CS ms ms' [Hs (acc & H & _)]. split; [exact Hs|]. eapply step_accesses_step; eauto. Qed.

#[using="Type"] Lemma mstepsA_msteps : forall CS ms ms', mstepsA CS ms ms' -> msteps segs ms ms'.
Proof. intros CS ms ms' H; induction H; [apply msteps_refl|]. eapply msteps_cons; [eapply mstepA_mstep|]; eauto. Qed.

#[using="Type"] Lemma mstepA_mono : ltac2:(CDefT.buildp (gd_tbl_AEvtA ()) "PCS,P,$4.SpPCS',P,$4.SpPms,$10.Pms',$10.P,Px,$4.P,A1.R5.R1.A1.R5.R2.P,(22.R5.R3.R2.)(22.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros CS CS' ms ms' HS [Hs (acc & H & OK)]. split; [exact Hs|]. exists acc. split; [exact H|].
  eapply acc_ok_mono; eauto.
Qed.

#[using="Type"] Lemma mstepsA_mono : ltac2:(CDefT.buildp (gd_tbl_AEvtA ()) "PCS,P,$4.SpPCS',P,$4.SpPms,$10.Pms',$10.P,Px,$4.P,A1.R5.R1.A1.R5.R2.P,(23.R5.R3.R2.)(23.R5.R4.R3.)")
(* [comment removed for export] *).
Proof. intros CS CS' ms ms' HS H; induction H; [constructor|]. eapply mstepsA_cons; [eapply mstepA_mono|]; eauto. Qed.

Definition evtA (CS : Z -> Prop) (Q : machine_state -> Prop) (ms : machine_state) : Prop :=
  exists ms', mstepsA CS ms ms' /\ Q ms'.

#[using="Type"] Lemma evtA_done : forall CS (Q : machine_state -> Prop) ms, Q ms -> evtA CS Q ms.
Proof. intros CS Q ms H. exists ms. split; [constructor| exact H]. Qed.

#[using="Type"] Lemma evtA_step : ltac2:(CDefT.buildp (gd_tbl_AEvtA ()) "PCS,P,$4.SpPQ,P,$10.SpPms,$10.Pms1,$10.Pacc,(18.$19.)P,(1=.(5.(2.(1.&40.))(1>.R3.)(1?.(1.&40.)))(5.(>.(?.$10.))(11.Vsegs,R3.)(1:.(?.$10.)(1;.$10.R2.R1.))))P,(21.VL,R6.R2.)P,(24.R7.R6.R4.)(24.R8.R7.R6.)")
(* [comment removed for export] *).
Proof.
  intros CS Q ms ms1 acc [Hs H] OK (ms' & Hr & HQ). exists ms'. split; [|exact HQ].
  eapply mstepsA_cons; [|exact Hr]. split; [exact Hs|]. exists acc. split; assumption.
Qed.

#[using="Type"] Lemma evtA_cut : ltac2:(CDefT.buildp (gd_tbl_AEvtA ()) "PCS,P,$4.SpPP,P,$10.SpPQ,P,$10.SpPms,$10.P,(24.R4.R3.R1.)P,Pms',$10.P,A1.R5.R1.(24.R7.R5.R2.)(24.R6.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros CS P Q ms (ms1 & H1 & HP) K. destruct (K ms1 HP) as (ms2 & H2 & HQ).
  exists ms2. split; [eapply mstepsA_trans; eauto| exact HQ].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma evtA_cut_mono : ltac2:(CDefT.buildp (gd_tbl_AEvtA ()) "PCS,P,$4.SpPCS',P,$4.SpPP,P,$10.SpPQ,P,$10.SpPms,$10.P,(24.R4.R3.R1.)P,Px,$4.P,A1.R6.R1.A1.R8.R2.P,Pms',$10.P,A1.R6.R1.(24.R9.R6.R2.)(24.R8.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros CS CS' P Q ms (ms1 & H1 & HP) HS K. destruct (K ms1 HP) as (ms2 & H2 & HQ).
  exists ms2. split; [| exact HQ]. eapply mstepsA_trans; [eapply mstepsA_mono; eauto| exact H2].
Qed.

#[using="Type"] Lemma evtA_mono : ltac2:(CDefT.buildp (gd_tbl_AEvtA ()) "PCS,P,$4.SpPP,P,$10.SpPQ,P,$10.SpPms,$10.P,(24.R4.R3.R1.)P,Pms',$10.P,A1.R5.R1.A1.R5.R2.(24.R6.R4.R3.)")
(* [comment removed for export] *).
Proof. intros CS P Q ms H K. eapply evtA_cut; [exact H|]. intros ms' HP. apply evtA_done, K, HP. Qed.

#[using="Type"] Lemma evtA_cs_mono : forall (CS CS' : Z -> Prop) Q ms,
  evtA CS Q ms -> (forall x, CS x -> CS' x) -> evtA CS' Q ms.
Proof. intros CS CS' Q ms (ms' & H & HQ) HS. exists ms'. split; [eapply mstepsA_mono; eauto| exact HQ]. Qed.

#[using="Type"] Lemma evtA_eq : forall CS Q ms ms', ms = ms' -> evtA CS Q ms' -> evtA CS Q ms.
Proof. intros; subst; assumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma evtA_evt : forall CS Q ms, evtA CS Q ms -> evt segs Q ms.
Proof. intros CS Q ms (ms' & H & HQ). exists ms'. split; [eapply mstepsA_msteps; eauto| exact HQ]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma sstep_acc_inv : ltac2:(CDefT.buildp (gd_tbl_AEvtA ()) "Pms,$10.Pmo,$25.Pms',$10.Pmo',$25.Pevs,(18.$26.)Pst,$27.P,(5.(2.(1.&40.))(1>.R6.)(1?.(1.&40.)))P,(5.(>.(;.$10.$25.))(28.Vsegs,R7.R6.)(1:.(;.$10.$25.)(=.$10.$25.R5.R4.)))P,(29.Vsegs,(2:.R8.R7.)R4.R3.)(1=.(5.(18.$26.)R5.(2;.$26.))(5.$27.R4.(2<.(2:.R7.R6.))))")
(* [comment removed for export] *).
Proof.
  intros ms mo ms' mo' evs st Hsvc Hacc Hss.
  inversion Hss; subst; try congruence.
  match goal with H : mi_account_step segs ms mo = MachineOk _ |- _ =>
    rewrite Hacc in H; inversion H; subst end.
  split; reflexivity.
Qed.

Section WithAI.
Variable AI : (Z -> Prop) -> Model -> Prop.
Hypothesis LAWS : ainv_laws L AI.

#[using="LAWS"] Lemma mi_account_step_ok : ltac2:(CDefT.buildp (gd_tbl_AEvtA ()) "PCS,P,$4.SpPms,$10.Pms',$10.Pacc,(18.$19.)Pmo,$25.P,A2.VAI,R5.R1.P,(5.(>.(?.$10.))(11.Vsegs,R5.)(1:.(?.$10.)(1;.$10.R4.R3.)))P,(21.VL,R7.R4.)(20.$25.Lmo',$25.(1=.(5.(>.(;.$10.$25.))(28.Vsegs,R8.R5.)(1:.(;.$10.$25.)(=.$10.$25.R7.R1.)))(1=.A2.VAI,R9.R1.(2=.R5.R1.))))")
(* [comment removed for export] *).
Proof.
  intros CS ms ms' acc mo HA Hst OK.
  destruct (ai_mat LAWS CS mo acc HA OK) as (mo' & Hm & HA' & MM).
  exists mo'. split; [| split; assumption].
  unfold mi_account_step. rewrite Hst. cbn [accessed_ranges access_value]. rewrite Hm. reflexivity.
Qed.

#[using="LAWS"] Lemma aevt_mstepA : ltac2:(CDefT.buildp (gd_tbl_AEvtA ()) "PCS,P,$4.SpPQ,P,$2>.SpPms,$10.Pms',$10.Pmo,$25.P,A2.VAI,R5.R1.P,(22.R6.R4.R3.)P,Pmo',$25.P,A2.VAI,R8.R1.P,(2=.R5.R2.)(2?.Vsegs,R9.(2:.R7.R3.))(2?.Vsegs,R7.(2:.R6.R4.))")
(* [comment removed for export] *).
Proof.
  intros CS Q ms ms' mo HA [Hsvc (acc & Hst & OK)] K.
  destruct (mi_account_step_ok CS ms ms' acc mo HA Hst OK) as (mo' & Hacc & HA' & MM).
  pose proof (ai_halted LAWS CS mo HA) as Hh.
  apply aevt_step.
  - exists (mkCfg ms' mo'). apply sstep_instr; assumption.
  - intros e st Hs. destruct (sstep_acc_inv _ _ _ _ _ _ Hsvc Hacc Hs) as [-> ->]. split; [reflexivity| congruence].
  - intros e c' Hs. destruct (sstep_acc_inv _ _ _ _ _ _ Hsvc Hacc Hs) as [_ E]. inversion E; subst.
    apply K; assumption.
Qed.

#[using="LAWS"] Lemma aevt_mstepsA : ltac2:(CDefT.buildp (gd_tbl_AEvtA ()) "PCS,P,$4.SpPQ,P,$2>.SpPms,$10.Pms',$10.Pmo,$25.P,A2.VAI,R5.R1.P,(23.R6.R4.R3.)P,Pmo',$25.P,A2.VAI,R8.R1.P,(2=.R5.R2.)(2?.Vsegs,R9.(2:.R7.R3.))(2?.Vsegs,R7.(2:.R6.R4.))")
(* [comment removed for export] *).
Proof.
  intros CS Q ms ms' mo HA H. revert mo HA.
  induction H as [ms | ms ms1 ms2 H1 H IH]; intros mo HA K.
  - apply K; [exact HA| apply mo_mat_refl].
  - eapply aevt_mstepA; [exact HA| exact H1|].
    intros mo1 HA1 MM1. apply IH; [exact HA1|]. intros mo' HA' MM'. apply K; [exact HA'|].
    eapply mo_mat_trans; eauto.
Qed.

(* [comment removed for export] *)
#[using="LAWS"] Lemma evtA_aevt : ltac2:(CDefT.buildp (gd_tbl_AEvtA ()) "PCS,P,$4.SpPP,P,$10.SpPms,$10.Pmo,$25.P,A2.VAI,R4.R1.P,(24.R5.R4.R3.)(2?.Vsegs,Lc,$2>.(1=.A1.R6.(30.R1.)(1=.A2.VAI,R7.(31.R1.)(2=.R4.(31.R1.))))(2:.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros CS P ms mo HA (ms' & H & HP). eapply aevt_mstepsA; [exact HA| exact H|].
  intros mo' HA' MM. apply aevt_now. cbn. split; [exact HP|]. split; [exact HA'| exact MM].
Qed.

(* [comment removed for export] *)
#[using="LAWS"] Lemma aevtS_mstepA : ltac2:(CDefT.buildp (gd_tbl_AEvtA ()) "PCS,P,$4.SpPQ,P,$2>.SpPms,$10.Pms',$10.Pmo,$25.P,A2.VAI,R5.R1.P,(22.R6.R4.R3.)P,Pmo',$25.P,A2.VAI,R8.R1.P,(2=.R5.R2.)(32.Vsegs,R9.(2:.R7.R3.))(32.Vsegs,R7.(2:.R6.R4.))")
(* [comment removed for export] *).
Proof.
  intros CS Q ms ms' mo HA [Hsvc (acc & Hst & OK)] K.
  destruct (mi_account_step_ok CS ms ms' acc mo HA Hst OK) as (mo' & Hacc & HA' & MM).
  pose proof (ai_halted LAWS CS mo HA) as Hh.
  apply aevtS_step.
  - exists (mkCfg ms' mo'). split; [apply sstep_instr; assumption | apply K; assumption].
  - intros e st Hs. destruct (sstep_acc_inv _ _ _ _ _ _ Hsvc Hacc Hs) as [-> ->]. split; [reflexivity| congruence].
  - intros e c' Hs. destruct (sstep_acc_inv _ _ _ _ _ _ Hsvc Hacc Hs) as [_ E]. inversion E; subst.
    left. apply K; assumption.
Qed.

#[using="LAWS"] Lemma aevtS_mstepsA : ltac2:(CDefT.buildp (gd_tbl_AEvtA ()) "PCS,P,$4.SpPQ,P,$2>.SpPms,$10.Pms',$10.Pmo,$25.P,A2.VAI,R5.R1.P,(23.R6.R4.R3.)P,Pmo',$25.P,A2.VAI,R8.R1.P,(2=.R5.R2.)(32.Vsegs,R9.(2:.R7.R3.))(32.Vsegs,R7.(2:.R6.R4.))")
(* [comment removed for export] *).
Proof.
  intros CS Q ms ms' mo HA H. revert mo HA.
  induction H as [ms | ms ms1 ms2 H1 H IH]; intros mo HA K.
  - apply K; [exact HA| apply mo_mat_refl].
  - eapply aevtS_mstepA; [exact HA| exact H1|].
    intros mo1 HA1 MM1. apply IH; [exact HA1|]. intros mo' HA' MM'. apply K; [exact HA'|].
    eapply mo_mat_trans; eauto.
Qed.

#[using="LAWS"] Lemma evtA_aevtS : ltac2:(CDefT.buildp (gd_tbl_AEvtA ()) "PCS,P,$4.SpPP,P,$10.SpPms,$10.Pmo,$25.P,A2.VAI,R4.R1.P,(24.R5.R4.R3.)(32.Vsegs,Lc,$2>.(1=.A1.R6.(30.R1.)(1=.A2.VAI,R7.(31.R1.)(2=.R4.(31.R1.))))(2:.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros CS P ms mo HA (ms' & H & HP). eapply aevtS_mstepsA; [exact HA| exact H|].
  intros mo' HA' MM. apply aevtS_now. cbn. split; [exact HP|]. split; [exact HA'| exact MM].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition aevtA (K : Model -> Prop) (Q : config -> Prop) (ms : machine_state) : Prop :=
  forall mo, K mo -> aevtS segs Q (mkCfg ms mo).

Record kinv_laws (CS : Z -> Prop) (K : Model -> Prop) := {
  k_ai : forall mo, K mo -> AI CS mo;
  k_closed : forall mo mo', K mo -> AI CS mo' -> mo_mat mo mo' -> K mo'
}.

#[using="Type"] Lemma aevtA_done : forall K (Q : config -> Prop) ms,
  (forall mo, K mo -> Q (mkCfg ms mo)) -> aevtA K Q ms.
Proof. intros K Q ms H mo HK. apply aevtS_now. apply H, HK. Qed.

#[using="LAWS"] Lemma aevtA_step : ltac2:(CDefT.buildp (gd_tbl_AEvtA ()) "PCS,P,$4.SpPK,P,$25.SpPQ,P,$2>.SpPms,$10.Pms1,$10.Pacc,(18.$19.)P,(33.R6.R5.)P,(1=.(5.(2.(1.&40.))(1>.R4.)(1?.(1.&40.)))(5.(>.(?.$10.))(11.Vsegs,R4.)(1:.(?.$10.)(1;.$10.R3.R2.))))P,(21.VL,R8.R3.)P,(34.R8.R7.R5.)(34.R9.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros CS K Q ms ms1 acc KL [Hs Hst] OK H mo HK.
  eapply aevtS_mstepA; [eapply (k_ai _ _ KL); exact HK| |].
  - split; [exact Hs|]. exists acc; split; [exact Hst| exact OK].
  - intros mo' HA' MM. apply H. eapply (k_closed _ _ KL); eauto.
Qed.

#[using="LAWS"] Lemma aevtA_cut_evtA : ltac2:(CDefT.buildp (gd_tbl_AEvtA ()) "PCS,P,$4.SpPCS',P,$4.SpPK,P,$25.SpPP,P,$10.SpPQ,P,$2>.SpPms,$10.P,(33.R6.R4.)P,(24.R6.R4.R2.)P,Px,$4.P,A1.R8.R1.A1.R:.R2.P,Pms',$10.P,A1.R7.R1.(34.R9.R7.R2.)(34.R8.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros CS CS' K P Q ms KL H HS Kc mo HK.
  eapply aevtS_bind.
  - eapply evtA_aevtS; [eapply (k_ai _ _ KL); exact HK|]. eapply evtA_cs_mono; eauto.
  - intros [ms' mo'] (HP & HA' & MM). cbn in *. apply Kc; [exact HP|]. eapply (k_closed _ _ KL); eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aevtA_cut : ltac2:(CDefT.buildp (gd_tbl_AEvtA ()) "PK,P,$25.SpPP,P,$2>.SpPQ,P,$2>.SpPms,$10.P,(34.R4.R3.R1.)P,Pms',$10.Pmo',$25.P,A1.R6.(2:.R2.R1.)(32.Vsegs,R6.(2:.R3.R2.))(34.R6.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros K P Q ms H Kc mo HK. eapply aevtS_bind; [apply H, HK|]. intros [ms' mo'] HP. apply Kc, HP.
Qed.

#[using="Type"] Lemma aevtA_enter : forall K Q ms mo, K mo -> aevtA K Q ms -> aevtS segs Q (mkCfg ms mo).
Proof. intros K Q ms mo HK H. apply H, HK. Qed.

#[using="Type"] Lemma aevtA_mono : forall K (P Q : config -> Prop) ms,
  aevtA K P ms -> (forall c, P c -> Q c) -> aevtA K Q ms.
Proof. intros K P Q ms H HPQ mo HK. eapply aevtS_mono; [apply H, HK| exact HPQ]. Qed.

#[using="Type"] Lemma aevtA_eq : forall K Q ms ms', ms = ms' -> aevtA K Q ms' -> aevtA K Q ms.
Proof. intros; subst; assumption. Qed.

End WithAI.
End WithLayout.
End WithSegs.

Arguments mstepA segs L CS ms ms' /.
Arguments evtA segs L CS Q ms : simpl never.
Arguments aevtA segs K Q ms /.
