(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import SimInv ExitSim.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StoreOk ShapeX SymExec BBFrame MemcpyLib AgentLib.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import SymExec2 SymExec2Sound SymRun SymDrive.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA Restrict RestrictLib NodesA.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_SymDriveA () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "Drive.DcovZ"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.PropExec.rdn"; "OSSVerify.KrLib.LibA.Restrict.restrict"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "OSSVerify.KrLib.LibA.Restrict.rms"; "OSSVerify.KrLib.Lib.PropExec.mkst"; "OSSVerify.KrLib.Lib.PropExec.fx0"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.LibA.ALazy.acc_ok"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.LibA.ALazy.mo_mat"; "OSSVerify.KrLib.Lib.Shape.TSet"; "OSSVerify.KrLib.LibA.AEvtA.mstepA"; "OSSVerify.KrLib.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.LibA.AEvtA.mstepsA"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.BB.SymExec2.SX2.scripts"; "OSSVerify.KrLib.BB.SymExec2.SX2.expr"; "OSSVerify.KrLib.BB.SymExec2.SX2.kentry"; "OSSVerify.KrLib.BB.SymExec2.SX2.sym_state"; "OSSVerify.KrLib.BB.SymExec2.SX2.sidecond"; "OSSVerify.KrLib.BB.SymExec2.SX2.env"; "OSSVerify.KrLib.BB.SymExec2.SX2.sym_exec"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.BB.SymExec2.SX2.SS"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.BB.SymExec2.SX2.sentry"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.BB.SymExec2.SX2.carry"; "OSSVerify.KrLib.BB.SymExec2.SX2.s_log"; "OSSVerify.KrLib.BB.SymExec2Sound.SX2S.regs_ok"; "OSSVerify.KrLib.BB.SymExec2Sound.SX2S.know_ok"; "Drive.kn_inD"; "OSSVerify.KrLib.BB.SymExec2Sound.SX2S.scs_denot"; "OSSVerify.KrLib.BB.SymExec2.SX2.s_regs"; "OSSVerify.KrLib.BB.SymExec2Sound.SX2S.mem_denot"; "Corelib.Init.Datatypes.false"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.BB.SymExec2.SX2.s_pc"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"].

#[local] Existing Instance Lib.PropExec.fx0.

Section Drive.
Variable segs : list Segment.
Variable D : word -> bool.

#[warnings="-deprecated"] Notation rst := (restrict D).

(* [comment removed for export] *)
Definition DcovZ (lo hi : Z) : Prop := forall z, (lo <= z < hi)%Z -> D (Z_to_bv 64 z) = true.

(* [comment removed for export] *)
Definition kentry_inD (E : env) (K : kentry) : Prop :=
  match K with
  | KWord a w _ => DcovZ (estart E a) (estart E a + Z.of_nat w)
  | KZero a n => DcovZ (estart E a) (estart E a + elenZ E n)
  | KBlob a n _ => DcovZ (estart E a) (estart E a + elenZ E n)
  | KImg lo hi => DcovZ lo hi
  | KWr a n => DcovZ (estart E a) (estart E a + n)
  | KAlign _ _ | KRange _ _ _ | KDisj _ _ _ _ => True
  end.
Definition kn_inD (E : env) (kn : list kentry) : Prop := Forall (kentry_inD E) kn.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma rdn_restrict_in : ltac2:(CDefT.buildp (gd_tbl_SymDriveA ()) "PM,P,(0.&40.)(1.(0.&8.))Pa,(0.&40.)Pn,$2.P,(3.(4.(5.&40.R2.)(6.R1.))(7.+2.+40.))P,(8.(5.&40.R3.)(4.(5.&40.R3.)(6.R2.)))(9.(1.(:.(0.&8.)))(;.Vsegs,(<.VD,R5.)R4.R3.)(;.Vsegs,R5.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros M a n Hnw HD. apply rdn_ext; [exact Hnw|].
  intros x Hx. apply restrict_in. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply HD. exact Hx.
Qed.

#[using="Type"] Lemma store_ok_restrict_in : ltac2:(CDefT.buildp (gd_tbl_SymDriveA ()) "Pn,$2.PM,P,(0.&40.)(1.(0.&8.))Pa,(0.&40.)P,(3.(4.(5.&40.R1.)(6.R3.))(7.+2.+40.))P,(8.(5.&40.R2.)(4.(5.&40.R2.)(6.R4.)))(9.$=.(>.Vsegs,(<.VD,R4.)R3.R5.)(>.Vsegs,R4.R3.R5.))")
(* [comment removed for export] *).
Proof.
  induction n as [|n IH]; intros M a Hnw HD; [reflexivity|].
  cbn [RiscvSemantics.store_ok].
  pose proof (u64_range a) as Ra.
  rewrite (wview_restrict_in segs D M a) by (rewrite <- (Z_to_bv_bv_unsigned 64 a); apply HD; lia).
  destruct (wview segs M a); [|reflexivity].
  destruct n as [|n']; [reflexivity|].
  assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
  apply IH; [rewrite Hu1; lia|]. intros z Hz. apply HD. rewrite Hu1 in Hz. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma kentry_ok_restrict : forall E M K,
  kentry_ok segs E M K -> kentry_inD E K -> kentry_ok segs E (rst M) K.
Proof.
  intros E M K HK HD. destruct K; cbn in HK, HD |- *.
  - destruct HK as (Hw & Hfl & Hrd). split; [exact Hw|]. split; [exact Hfl|].
    rewrite rdn_restrict_in; [exact Hrd | |]; rewrite (flat_u _ _ _ Hfl); [destruct Hfl; lia | exact HD].
  - destruct HK as [Hfl H]. split; [exact Hfl|]. intros i Hi. rewrite restrict_in; [apply H; exact Hi|]. apply HD. lia.
  - destruct HK as (Hfl & Hl & H). split; [exact Hfl|]. split; [exact Hl|]. intros i Hi.
    rewrite restrict_in; [apply H; exact Hi|]. apply HD. lia.
  - destruct HK as (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros i Hi.
    unfold restrict. rewrite (H i Hi). destruct (D (Z_to_bv 64 i)); reflexivity.
  - exact HK.
  - exact HK.
  - destruct HK as [Hfl H]. split; [exact Hfl|]. intros d m Hd Hdm.
    destruct m as [|m']; [reflexivity|].
    pose proof Hfl as (F0 & F1 & F2 & F3).
    assert (Hu : bv_unsigned (Z_to_bv 64 (estart E a + d)) = (estart E a + d)%Z) by (rewrite u64_lit; lia).
    rewrite store_ok_restrict_in; [apply H; assumption | rewrite Hu; lia |].
    intros z Hz. apply HD. rewrite Hu in Hz. lia.
  - exact HK.
Qed.

#[using="Type"] Lemma know_ok_restrict : forall E M kn,
  know_ok segs E M kn -> kn_inD E kn -> know_ok segs E (rst M) kn.
Proof.
  intros E M kn HK HD. unfold know_ok, kn_inD in *.
  induction kn as [|K kn IH]; [constructor|].
  inversion HK; inversion HD; subst. constructor; [apply kentry_ok_restrict; assumption | apply IH; assumption].
Qed.

#[using="Type"] Lemma kentry_ok_unrestrict : forall E M K,
  kentry_ok segs E (rst M) K -> kentry_inD E K -> kentry_ok segs E M K.
Proof.
  intros E M K HK HD. destruct K; cbn in HK, HD |- *.
  - destruct HK as (Hw & Hfl & Hrd). split; [exact Hw|]. split; [exact Hfl|].
    rewrite <- rdn_restrict_in; [exact Hrd | |]; rewrite (flat_u _ _ _ Hfl); [destruct Hfl; lia | exact HD].
  - destruct HK as [Hfl H]. split; [exact Hfl|]. intros i Hi. rewrite <- (restrict_in D M); [apply H; exact Hi|]. apply HD. lia.
  - destruct HK as (Hfl & Hl & H). split; [exact Hfl|]. split; [exact Hl|]. intros i Hi.
    rewrite <- (restrict_in D M); [apply H; exact Hi|]. apply HD. lia.
  - destruct HK as (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros i Hi.
    specialize (H i Hi). unfold restrict in H. rewrite (HD i Hi) in H. exact H.
  - exact HK.
  - exact HK.
  - destruct HK as [Hfl H]. split; [exact Hfl|]. intros d m Hd Hdm.
    destruct m as [|m']; [reflexivity|].
    pose proof Hfl as (F0 & F1 & F2 & F3).
    assert (Hu : bv_unsigned (Z_to_bv 64 (estart E a + d)) = (estart E a + d)%Z) by (rewrite u64_lit; lia).
    rewrite <- store_ok_restrict_in; [apply H; assumption | rewrite Hu; lia |].
    intros z Hz. apply HD. rewrite Hu in Hz. lia.
  - exact HK.
Qed.

#[using="Type"] Lemma know_ok_unrestrict : forall E M kn,
  know_ok segs E (rst M) kn -> kn_inD E kn -> know_ok segs E M kn.
Proof.
  intros E M kn HK HD. unfold know_ok, kn_inD in *.
  induction kn as [|K kn IH]; [constructor|].
  inversion HK; inversion HD; subst. constructor; [apply kentry_ok_unrestrict; assumption | apply IH; assumption].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rms_eq_mkst : ltac2:(CDefT.buildp (gd_tbl_SymDriveA ()) "Pms1,$?.PR,(10.&5.(0.&40.))Ppc,(0.&40.)PmD,P,(0.&40.)(1.(0.&8.))Prom,P,(0.&40.)(1.(0.&8.))P,(9.$?.(11.VD,R5.)(12.$13.R4.R3.R2.R1.))(14.P,(0.&40.)(1.(0.&8.))LM1,P,(0.&40.)(1.(0.&8.))(15.(9.$?.R7.(12.$13.R6.R5.R1.R3.))(9.P,(0.&40.)(1.(0.&8.))(<.VD,R1.)R4.)))")
(* [comment removed for export] *).
Proof.
  intros [R0 F0 pc0 svc rv0 fc0 m0 ro0] R pc mD rom H. exists m0.
  unfold rms, Restrict.set_mem, mkst in H |- *. cbn in H. inversion H. subst. split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithK.
Variable AL : asan_layout.
Variable CS : Z -> Prop.
Variable K : Model -> Prop.
Hypothesis K_halted : forall mo, K mo -> m_halted mo = None.
Hypothesis K_mat : ltac2:(CDefT.buildp (gd_tbl_SymDriveA ()) "Pmo,$16.Pacc,(:.(17.(0.&40.)$2.))P,A1.VK,R2.P,(18.VAL,VCS,R2.)(14.$16.Lmo',$16.(15.(9.(1.$16.)(19.R5.R4.)(1:.$16.R1.))(15.A1.VK,R1.(1;.R5.R1.))))")
(* [comment removed for export] *).

#[using="K_halted K_mat"] Lemma rz_mstepA_K : ltac2:(CDefT.buildp (gd_tbl_SymDriveA ()) "Pms,$?.Pms',$?.Pmo,$16.PT,$1<.P,A1.VK,R2.P,(1=.Vsegs,VAL,VCS,R5.R4.)P,Pmo',$16.P,A1.VK,R1.P,(1;.R6.R2.)(1>.Vsegs,(1?.R8.R3.)R6.)(1>.Vsegs,(1?.R7.R5.)R4.)")
(* [comment removed for export] *).
Proof.
  intros ms ms' mo T HK [Hsvc (acc & Hst & OK)] Hc.
  destruct (K_mat mo acc HK OK) as (mo' & Hm & HK' & MM).
  eapply rz_step_acc; [exact (K_halted mo HK) | exact Hsvc | | apply Hc; [exact HK' | exact MM]].
  unfold mi_account_step. rewrite Hst. cbn [accessed_ranges access_value]. rewrite Hm. reflexivity.
Qed.

#[using="K_halted K_mat"] Lemma rz_mstepsA_K : ltac2:(CDefT.buildp (gd_tbl_SymDriveA ()) "Pms,$?.Pms',$?.Pmo,$16.PT,$1<.P,A1.VK,R2.P,(20.Vsegs,VAL,VCS,R5.R4.)P,Pmo',$16.P,A1.VK,R1.P,(1;.R6.R2.)(1>.Vsegs,(1?.R8.R3.)R6.)(1>.Vsegs,(1?.R7.R5.)R4.)")
(* [comment removed for export] *).
Proof.
  intros ms ms' mo T HK H. revert mo HK.
  induction H as [ms | ms ms1 ms2 H1 H IH]; intros mo HK Hc.
  - apply Hc; [exact HK | apply mo_mat_refl].
  - eapply rz_mstepA_K; [exact HK | exact H1 |].
    intros mo1 HK1 MM1. apply IH; [exact HK1|]. intros mo' HK' MM'. apply Hc; [exact HK'|].
    eapply mo_mat_trans; eauto.
Qed.

(* [comment removed for export] *)
#[using="K_halted K_mat"] Lemma rz_evtA_K : ltac2:(CDefT.buildp (gd_tbl_SymDriveA ()) "PP,P,$?.SpPms,$?.Pmo,$16.PT,$1<.P,A1.VK,R2.P,(21.Vsegs,VAL,VCS,R5.R4.)P,Pms',$?.Pmo',$16.P,A1.R8.R2.P,A1.VK,R2.P,(1;.R8.R3.)(1>.Vsegs,(1?.R5.R4.)R8.)(1>.Vsegs,(1?.R6.R5.)R4.)")
(* [comment removed for export] *).
Proof.
  intros P ms mo T HK (ms' & H & HP) Hc. eapply rz_mstepsA_K; [exact HK | exact H |].
  intros mo' HK' MM. apply Hc; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Hypothesis Dseg : forall a : word, segcov segs (bv_unsigned a) = true -> D a = true.
Hypothesis SEGTOP : forallb (fun seg => (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? 2^64)%Z) segs = true.
Hypothesis DOK : forall a, D a = true -> aok_addr AL CS (bv_unsigned a).
Hypothesis D0 : D (Z_to_bv 64 0) = false.

#[using="AL CS K_halted K_mat Dseg SEGTOP DOK D0"] Theorem rz_runA : ltac2:(CDefT.buildp (gd_tbl_SymDriveA ()) "Pfuel,$2.Pstops,(:.$22.)Pscr,$23.Ppc,$22.Psr,(:.$24.)Pkn,(:.$25.)Pnx,$2.Pss',$26.Pscs,(:.$27.)Pscr',$23.Pkn',(:.$25.)Pscs2,(:.$27.)Phs2,(:.$=.)PE,$28.PM,P,(0.&40.)(1.(0.&8.))PR,(10.&5.(0.&40.))Pmo,$16.PT,$1<.P,(9.(17.(17.$26.(:.$27.))$23.)(29.Vsegs,R12.$2:.R11.R10.(2;.R?.R>.(2<.$2=.)R=.R<.)(2<.$27.))(2>.(17.$26.(:.$27.))$23.(2>.$26.(:.$27.)R;.R:.)R9.))P,(9.(17.(17.(:.$25.)(:.$27.))(:.$=.))(2?.(30.R<.)R>.(2<.$=.))(2>.(17.(:.$25.)(:.$27.))(:.$=.)(2>.(:.$25.)(:.$27.)R9.R8.)R7.))P,(31.R7.R10.R5.)P,(32.Vsegs,R8.R7.R10.)P,(33.R9.R11.)P,(33.R:.R=.)P,(34.Vsegs,(<.VD,R:.)R;.R10.)P,(34.Vsegs,(<.VD,R;.)R<.R>.)P,A1.VK,R:.P,PR',(10.&5.(0.&40.))PM',P,(0.&40.)(1.(0.&8.))Pmo',$16.P,(31.R11.(35.R17.)R3.)P,(32.Vsegs,R12.R3.R15.)P,(9.P,(0.&40.)(1.(0.&8.))(<.VD,R4.)(36.R13.(<.VD,R12.)(30.R19.)))P,Pa,(0.&40.)P,(9.$=.A1.VD,R1.$37.)(9.(1.(0.&8.))A1.R7.R2.A1.R15.R2.)P,A1.VK,R5.P,(1;.R13.R6.)(1>.Vsegs,(1?.(12.$13.R9.(38.&40.(39.R1=.))R8.(3:.Vsegs,))R7.)R13.)(1>.Vsegs,(1?.(12.$13.R=.(38.&40.R19.)R>.(3:.Vsegs,))R<.)R;.)")
(* [comment removed for export] *).
Proof.
  intros fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M R mo T
         Hex Hc HR HK HKD HKD' Hsc Hsc2 HKmo Hcont.
  pose proof (know_ok_restrict E M kn HK HKD) as HKr.
  destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E (rst M) (seg_rom segs) R Hex HR HKr Hsc)
    as (R' & HR' & Hlf & Hms).
  (* [comment removed for export] *)
  assert (Hrms : mkst R (Z_to_bv 64 pc) (rst M) (seg_rom segs) = rms D (mkst R (Z_to_bv 64 pc) M (seg_rom segs))) by reflexivity.
  rewrite Hrms in Hms.
  destruct (smsteps_restrict segs D Dseg SEGTOP AL CS DOK D0 _ _ Hms _ eq_refl) as (ms1' & HA & Hr & Hout).
  eapply rz_mstepsA_K; [exact HKmo | exact HA |].
  intros mo' HK' MM.
  (* [comment removed for export] *)
  destruct (rms_eq_mkst _ _ _ _ _ Hr) as (M1 & -> & EM). cbn [ms_mem mkst] in Hout.
  apply (Hcont R' M1 mo' HR'); [ | exact EM | exact Hout | exact HK' | exact MM].
  apply know_ok_unrestrict; [|exact HKD']. rewrite EM. eapply carry_after; eassumption.
Qed.

End WithK.
End Drive.
