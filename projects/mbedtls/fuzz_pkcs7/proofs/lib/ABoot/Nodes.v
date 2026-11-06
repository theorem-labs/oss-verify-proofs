(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import SimInv ExitSim CatSim FileSim ShapeAlg.

Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_Nodes () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "LinuxProcessSemantics.LinuxProcessSem.Run.step_to"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.Run.sstep"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect"; "Corelib.Init.Logic.and"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.check_result"; "LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.check_syscall"; "LinuxProcessSemantics.LinuxProcessSem.Run.sys_input"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.CheckOk"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.None"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "LinuxProcessSemantics.LinuxProcessSem.State.syscall_effect_accesses"; "LinuxProcessSemantics.LinuxProcessSem.Run.SNext"; "LinuxProcessSemantics.LinuxProcessSem.Run.advance_past_svc"; "LinuxProcessSemantics.LinuxProcessSem.Run.apply_effect"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.Run.SError"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "WithSegs.halt_ev"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.CheckUnmodeled"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.ABoot.ShapeAlg.node_ok"; "Corelib.Init.Logic.iff"; "Corelib.Init.Datatypes.unit"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.check_ret_only"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.set_gpr0"; "Corelib.Init.Datatypes.nat"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.check_ret_only_copyins"; "OSSVerify.KrLib.ABoot.ShapeAlg.TSet"; "OSSVerify.KrLib.ABoot.ShapeAlg.realizes"; "OSSVerify.KrLib.ABoot.ShapeAlg.t_emit"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "OSSVerify.KrLib.ABoot.ShapeAlg.t_alt"; "OSSVerify.KrLib.ABoot.ExitSim.is_exit_no"; "OSSVerify.KrLib.ABoot.ShapeAlg.t_exit"; "stdpp.bitvector.definitions.bv_and"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "OSSVerify.KrLib.ABoot.FileSim.check_open_result_copyins"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "LinuxProcessSemantics.LinuxProcessSem.State.alloc_fd"; "WithSegs.open_I"; "WithSegs.open_nx"; "Corelib.Numbers.BinNums.Z"; "Stdlib.Lists.List.In"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open.openat_errnos"; "LinuxProcessSemantics.LinuxProcessSem.State.errno_ret"; "OSSVerify.KrLib.ABoot.ShapeAlg.t_alt2"].


Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition halt_ev (m' : Model) (code : word) : event :=
  match m_killed m' with
  | Some sig => KillEv sig (m_fs m')
  | None => ExitEv code (m_fs m')
  end.

#[using="Type"] Lemma sstep_svc_inv : ltac2:(CDefT.buildp (gd_tbl_Nodes ()) "Pms,$0.Pmodel,$1.Px8,(2.&40.)Pe,(3.$4.)Pst,$5.P,(6.(7.(2.&40.))(8.R5.)(9.(2.&40.)R3.))P,(:.Vsegs,(;.R6.R5.)R3.R2.)(<.(=.$>.Leff,$>.(=.$1.Lmodel',$1.(=.(3.$4.)Levs,(3.$4.)(?.(6.$10.(11.(12.Vsegs,R:.R8.)R3.R9.)(13.R2.R1.))(<.(=.$1.Lmodel'',$1.(?.(6.(7.(2.&40.))(14.R3.)(15.(2.&40.)))(?.(6.(3.$4.)R8.R2.)(?.(6.(7.$1.)(16.R3.(17.R4.))(9.$1.R1.))(6.$5.R7.(18.(;.(19.(1:.R;.R4.))R1.)))))))(<.(?.(6.(7.(2.&40.))(14.R2.)(15.(2.&40.)))(?.(6.(3.$4.)R7.(1;.$4.))(?.(6.(7.$1.)(16.R2.(17.R3.))(15.$1.))(6.$5.R6.$1<.))))(=.(2.&40.)Lcode,(2.&40.)(?.(6.(7.(2.&40.))(14.R3.)(9.(2.&40.)R1.))(?.(6.(3.$4.)R8.(1=.$4.R2.(1>.$4.(1?.R3.R1.)(1;.$4.))))(6.$5.R7.(18.(;.R;.R3.))))))))))))(=.$>.Leff,$>.(?.(6.$10.(11.(12.Vsegs,R8.R6.)R1.R7.)$20.)(?.(6.(3.$4.)R5.(1;.$4.))(6.$5.R4.$1<.)))))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 e st Hsvc Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + left. eexists. repeat split; eauto.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + right. left. repeat split; auto.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + right. right. eexists. repeat split; eauto.
      unfold halt_ev. match goal with Hk : m_killed _ = None |- _ => rewrite Hk end. reflexivity.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + right. right.
      match goal with Hk : m_killed ?mm = Some _ |- _ =>
        destruct (m_halted mm) as [code|] eqn:Hhc;
          [| rewrite (m_killed_of_m_halted_none _ Hhc) in Hk; discriminate Hk];
        exists code; split; [reflexivity | split; [unfold halt_ev; rewrite Hk; reflexivity | reflexivity]]
      end.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    right. exists (mkEffect (Z_to_bv 64 0) [] []). split; [|split; reflexivity].
    apply check_syscall_err_iff. assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sstep_of_check : ltac2:(CDefT.buildp (gd_tbl_Nodes ()) "Pms,$0.Pmodel,$1.Px8,(2.&40.)Peff,$>.Pm',$1.Pevs,(3.$4.)P,(6.(7.(2.&40.))(14.R5.)(15.(2.&40.)))P,(6.(7.(2.&40.))(8.R7.)(9.(2.&40.)R5.))P,(6.$10.(11.(12.Vsegs,R8.R6.)R5.R7.)(13.R4.R3.))P,(6.(7.(2.&40.))(14.R5.)(15.(2.&40.)))P,(6.(3.(21.(2.&40.)(2.&40.)))(22.R6.)(1;.(21.(2.&40.)(2.&40.))))(:.Vsegs,(;.R;.R:.)R6.(18.(;.(19.(1:.R;.R8.))R7.)))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 eff m' evs Hh Hsvc Hc Hh' Hlazy.
  apply (sstep_syscall segs ms model x8 eff m' m' evs Hh Hsvc).
  - apply check_syscall_ok_iff. exact Hc.
  - exact Hh'.
  - apply materialize_model_accesses_no_lazy. exact Hlazy.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma node_chk_ev : ltac2:(CDefT.buildp (gd_tbl_Nodes ()) "Pms,$0.Pmodel,$1.Px8,(2.&40.)PI,StPeffs,P,R1.$>.Pms',P,R2.$1.Pevs,P,R3.(3.$4.)P,(6.(7.(2.&40.))(14.R6.)(15.(2.&40.)))P,(6.(7.(2.&40.))(8.R8.)(9.(2.&40.)R6.))P,Pi,R6.(6.$10.(11.(12.Vsegs,R:.R8.)A1.R6.R1.R9.)(13.A1.R5.R1.A1.R4.R1.))P,Peff,$>.Pm',$1.Pev,(3.$4.)P,(6.$10.(11.(12.Vsegs,R=.R;.)R3.R<.)(13.R2.R1.))(=.R;.Li,R;.(?.(6.$>.R5.A1.R;.R1.)(?.(6.$1.R4.A1.R:.R1.)(6.(3.$4.)R3.A1.R9.R1.))))P,Peff,$>.(23.(6.$10.(11.(12.Vsegs,R<.R:.)R1.R;.)$20.))P,Pi,R9.(6.(7.(2.&40.))(14.A1.R8.R1.)(15.(2.&40.)))P,Pi,R:.(6.(3.(21.(2.&40.)(2.&40.)))(22.A1.R9.R1.)(1;.(21.(2.&40.)(2.&40.))))(24.Vsegs,(;.R>.R=.)R;.R8.Li,R;.(;.(19.(1:.R?.A1.R;.R1.))A1.R:.R1.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hnu Hh' Hlazy. split.
  - intros i. apply (sstep_of_check ms model x8); auto.
  - intros e st Hss.
    destruct (sstep_svc_inv ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat.
      injection Hmat as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite Hh' in Hh2. discriminate.
    + exfalso. exact (Hnu eff Hc).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma node_chk : ltac2:(CDefT.buildp (gd_tbl_Nodes ()) "Pms,$0.Pmodel,$1.Px8,(2.&40.)PI,StPeffs,P,R1.$>.Pms',P,R2.$1.P,(6.(7.(2.&40.))(14.R5.)(15.(2.&40.)))P,(6.(7.(2.&40.))(8.R7.)(9.(2.&40.)R5.))P,Pi,R5.(6.$10.(11.(12.Vsegs,R9.R7.)A1.R5.R1.R8.)(13.A1.R4.R1.(1;.$4.)))P,Peff,$>.Pm',$1.Pevs,(3.$4.)P,(6.$10.(11.(12.Vsegs,R<.R:.)R3.R;.)(13.R2.R1.))(=.R:.Li,R:.(?.(6.$>.R5.A1.R:.R1.)(?.(6.$1.R4.A1.R9.R1.)(6.(3.$4.)R3.(1;.$4.)))))P,Peff,$>.(23.(6.$10.(11.(12.Vsegs,R;.R9.)R1.R:.)$20.))P,Pi,R8.(6.(7.(2.&40.))(14.A1.R7.R1.)(15.(2.&40.)))P,Pi,R9.(6.(3.(21.(2.&40.)(2.&40.)))(22.A1.R8.R1.)(1;.(21.(2.&40.)(2.&40.))))(24.Vsegs,(;.R=.R<.)R:.L,R:.(1;.$4.)Li,R:.(;.(19.(1:.R>.A1.R:.R1.))A1.R9.R1.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 I effs ms' Hh Hsvc Hok Hinv Hnu Hh' Hlazy.
  apply (node_chk_ev ms model x8 I effs ms' (fun _ => []) Hh Hsvc Hok); auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma node_det : ltac2:(CDefT.buildp (gd_tbl_Nodes ()) "Pms,$0.Pmodel,$1.Px8,(2.&40.)Peff0,$>.Pm0,$1.Pevs0,(3.$4.)P,(6.(7.(2.&40.))(14.R5.)(15.(2.&40.)))P,(6.(7.(2.&40.))(8.R7.)(9.(2.&40.)R5.))P,Peff,$>.Pm',$1.Pevs,(3.$4.)(25.(6.$10.(11.(12.Vsegs,R;.R9.)R3.R:.)(13.R2.R1.))(?.(6.$>.R3.R8.)(?.(6.$1.R2.R7.)(6.(3.$4.)R1.R6.))))P,Peff,$>.(23.(6.$10.(11.(12.Vsegs,R:.R8.)R1.R9.)$20.))P,(6.(7.(2.&40.))(14.R6.)(15.(2.&40.)))P,(6.(3.(21.(2.&40.)(2.&40.)))(22.R7.)(1;.(21.(2.&40.)(2.&40.))))(24.Vsegs,(;.R<.R;.)$26.L,$26.R8.L,$26.(;.(19.(1:.R=.R:.))R9.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 eff0 m0 evs0 Hh Hsvc Hchk Hnu Hh0 Hlazy0.
  apply (node_chk_ev ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0) Hh Hsvc).
  - intros []. apply (proj2 (Hchk eff0 m0 evs0)). auto.
  - intros eff m' ev Hc. apply Hchk in Hc as (-> & -> & ->). exists tt. auto.
  - exact Hnu.
  - intros []; exact Hh0.
  - intros []; exact Hlazy0.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma node_ret_only : ltac2:(CDefT.buildp (gd_tbl_Nodes ()) "Pms,$0.Pmodel,$1.Px8,(2.&40.)Pr,(2.&40.)Pm',$1.Pevs,(3.$4.)P,(6.(7.(2.&40.))(14.R5.)(15.(2.&40.)))P,(6.(7.(2.&40.))(8.R7.)(9.(2.&40.)R5.))P,Peff,$>.(6.$10.(11.(12.Vsegs,R9.R7.)R1.R8.)(27.R1.R6.R5.R4.))P,(6.(7.(2.&40.))(14.R5.)(15.(2.&40.)))P,(6.(3.(21.(2.&40.)(2.&40.)))(22.R6.)(1;.(21.(2.&40.)(2.&40.))))(24.Vsegs,(;.R;.R:.)$26.L,$26.R7.L,$26.(;.(19.(28.R<.R9.))R8.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 r m' evs Hh Hsvc Hchk Hh' Hlazy.
  rewrite <- (apply_effect_no_write ms r).
  apply (node_det ms model x8 (mkEffect r [] []) m' evs Hh Hsvc).
  - intros eff m'' evs'. rewrite Hchk. apply check_ret_only_ok_iff.
  - intros eff. rewrite Hchk. apply check_ret_only_no_unmodeled.
  - exact Hh'.
  - exact Hlazy.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma node_ret_only_copyins : ltac2:(CDefT.buildp (gd_tbl_Nodes ()) "Pms,$0.Pmodel,$1.Px8,(2.&40.)Preads,(3.(21.(2.&40.)$29.))Pr,(2.&40.)Pm',$1.Pevs,(3.$4.)P,(6.(7.(2.&40.))(14.R6.)(15.(2.&40.)))P,(6.(7.(2.&40.))(8.R8.)(9.(2.&40.)R6.))P,Peff,$>.(6.$10.(11.(12.Vsegs,R:.R8.)R1.R9.)(2:.R7.R1.R6.R5.R4.))P,(6.(7.(2.&40.))(14.R5.)(15.(2.&40.)))P,(6.(3.(21.(2.&40.)(2.&40.)))(22.R6.)(1;.(21.(2.&40.)(2.&40.))))(24.Vsegs,(;.R<.R;.)$26.L,$26.R7.L,$26.(;.(19.(28.R=.R9.))R8.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 reads r m' evs Hh Hsvc Hchk Hh' Hlazy.
  rewrite <- (apply_effect_copyins_no_write ms r reads).
  apply (node_det ms model x8 (with_copyins reads (mkEffect r [] [])) m' evs Hh Hsvc).
  - intros eff m'' evs'. rewrite Hchk. apply check_ret_only_copyins_ok_iff.
  - intros eff. rewrite Hchk. apply check_ret_only_copyins_no_unmodeled.
  - exact Hh'.
  - exact Hlazy.
Qed.

#[using="Type"] Lemma rz_ret_only : ltac2:(CDefT.buildp (gd_tbl_Nodes ()) "Pms,$0.Pmodel,$1.Px8,(2.&40.)Pr,(2.&40.)Pm',$1.Pevs,(3.$4.)PT,$2;.P,(6.(7.(2.&40.))(14.R6.)(15.(2.&40.)))P,(6.(7.(2.&40.))(8.R8.)(9.(2.&40.)R6.))P,Peff,$>.(6.$10.(11.(12.Vsegs,R:.R8.)R1.R9.)(27.R1.R7.R6.R5.))P,(6.(7.(2.&40.))(14.R6.)(15.(2.&40.)))P,(6.(3.(21.(2.&40.)(2.&40.)))(22.R7.)(1;.(21.(2.&40.)(2.&40.))))P,(2<.Vsegs,(;.(19.(28.R<.R9.))R8.)R6.)(2<.Vsegs,(;.R=.R<.)(2=.R8.R7.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 r m' evs T Hh Hsvc Hchk Hh' Hlazy Hc.
  eapply rz_emit1; [eapply node_ret_only; eassumption | exact Hc].
Qed.

#[using="Type"] Lemma rz_ret_only_copyins : ltac2:(CDefT.buildp (gd_tbl_Nodes ()) "Pms,$0.Pmodel,$1.Px8,(2.&40.)Preads,(3.(21.(2.&40.)$29.))Pr,(2.&40.)Pm',$1.Pevs,(3.$4.)PT,$2;.P,(6.(7.(2.&40.))(14.R7.)(15.(2.&40.)))P,(6.(7.(2.&40.))(8.R9.)(9.(2.&40.)R7.))P,Peff,$>.(6.$10.(11.(12.Vsegs,R;.R9.)R1.R:.)(2:.R8.R1.R7.R6.R5.))P,(6.(7.(2.&40.))(14.R6.)(15.(2.&40.)))P,(6.(3.(21.(2.&40.)(2.&40.)))(22.R7.)(1;.(21.(2.&40.)(2.&40.))))P,(2<.Vsegs,(;.(19.(28.R=.R9.))R8.)R6.)(2<.Vsegs,(;.R>.R=.)(2=.R8.R7.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 reads r m' evs T Hh Hsvc Hchk Hh' Hlazy Hc.
  eapply rz_emit1; [eapply node_ret_only_copyins; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_ret_only_silent : ltac2:(CDefT.buildp (gd_tbl_Nodes ()) "Pms,$0.Pmodel,$1.Px8,(2.&40.)Pr,(2.&40.)Pm',$1.PT,$2;.P,(6.(7.(2.&40.))(14.R5.)(15.(2.&40.)))P,(6.(7.(2.&40.))(8.R7.)(9.(2.&40.)R5.))P,Peff,$>.(6.$10.(11.(12.Vsegs,R9.R7.)R1.R8.)(27.R1.R6.R5.(1;.$4.)))P,(6.(7.(2.&40.))(14.R5.)(15.(2.&40.)))P,(6.(3.(21.(2.&40.)(2.&40.)))(22.R6.)(1;.(21.(2.&40.)(2.&40.))))P,(2<.Vsegs,(;.(19.(28.R;.R8.))R7.)R6.)(2<.Vsegs,(;.R<.R;.)R7.)")
(* [comment removed for export] *).
Proof.
  intros ms model x8 r m' T Hh Hsvc Hchk Hh' Hlazy Hc.
  eapply rz_silent1; [eapply node_ret_only; eassumption | exact Hc].
Qed.

#[using="Type"] Lemma rz_ret_only_copyins_silent : ltac2:(CDefT.buildp (gd_tbl_Nodes ()) "Pms,$0.Pmodel,$1.Px8,(2.&40.)Preads,(3.(21.(2.&40.)$29.))Pr,(2.&40.)Pm',$1.PT,$2;.P,(6.(7.(2.&40.))(14.R6.)(15.(2.&40.)))P,(6.(7.(2.&40.))(8.R8.)(9.(2.&40.)R6.))P,Peff,$>.(6.$10.(11.(12.Vsegs,R:.R8.)R1.R9.)(2:.R7.R1.R6.R5.(1;.$4.)))P,(6.(7.(2.&40.))(14.R5.)(15.(2.&40.)))P,(6.(3.(21.(2.&40.)(2.&40.)))(22.R6.)(1;.(21.(2.&40.)(2.&40.))))P,(2<.Vsegs,(;.(19.(28.R<.R8.))R7.)R6.)(2<.Vsegs,(;.R=.R<.)R7.)")
(* [comment removed for export] *).
Proof.
  intros ms model x8 reads r m' T Hh Hsvc Hchk Hh' Hlazy Hc.
  eapply rz_silent1; [eapply node_ret_only_copyins; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_det : ltac2:(CDefT.buildp (gd_tbl_Nodes ()) "Pms,$0.Pmodel,$1.Px8,(2.&40.)Peff0,$>.Pm0,$1.PT,$2;.P,(6.(7.(2.&40.))(14.R5.)(15.(2.&40.)))P,(6.(7.(2.&40.))(8.R7.)(9.(2.&40.)R5.))P,Peff,$>.Pm',$1.Pevs,(3.$4.)(25.(6.$10.(11.(12.Vsegs,R;.R9.)R3.R:.)(13.R2.R1.))(?.(6.$>.R3.R8.)(?.(6.$1.R2.R7.)(6.(3.$4.)R1.(1;.$4.)))))P,Peff,$>.(23.(6.$10.(11.(12.Vsegs,R:.R8.)R1.R9.)$20.))P,(6.(7.(2.&40.))(14.R6.)(15.(2.&40.)))P,(6.(3.(21.(2.&40.)(2.&40.)))(22.R7.)(1;.(21.(2.&40.)(2.&40.))))P,(2<.Vsegs,(;.(19.(1:.R<.R9.))R8.)R7.)(2<.Vsegs,(;.R=.R<.)R8.)")
(* [comment removed for export] *).
Proof.
  intros ms model x8 eff0 m0 T Hh Hsvc Hchk Hnu Hh0 Hlazy0 Hc.
  eapply rz_silent1; [eapply node_det; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_cases : ltac2:(CDefT.buildp (gd_tbl_Nodes ()) "Pc,$2>.PI,StPnx,P,R1.$2>.PT,P,R2.$2;.Pi0,R3.P,(24.Vsegs,R5.R4.L,R4.(1;.$4.)R3.)P,Pi,R5.(2<.Vsegs,A1.R5.R1.A1.R4.R1.)(2<.Vsegs,R7.(2?.R6.R4.))")
(* [comment removed for export] *).
Proof.
  intros c I nx T i0 Hnode Hc.
  apply (rz_conseq segs c (t_alt (fun i => t_emit [] (T i)))).
  - apply (rz_node segs c I (fun _ => []) nx T i0 Hnode Hc).
  - intros tr. split.
    + intros [i Hi]. exists i.
      exact (proj1 (t_emit_nil_eq (T i) (realizes_nonempty segs _ _ (Hc i)) tr) Hi).
    + intros [i Hi]. exists i.
      exact (proj2 (t_emit_nil_eq (T i) (realizes_nonempty segs _ _ (Hc i)) tr) Hi).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_exit_chk : ltac2:(CDefT.buildp (gd_tbl_Nodes ()) "Pms,$0.Pmodel,$1.Px8,(2.&40.)P,(6.(7.(2.&40.))(14.R2.)(15.(2.&40.)))P,(6.(7.(2.&40.))(8.R4.)(9.(2.&40.)R2.))P,(30.R3.)(2<.Vsegs,(;.R6.R5.)(31.(32.&40.(33.R6.#0.)(34.&40.+??.))(35.R5.)))")
(* [comment removed for export] *).
Proof. intros. eapply rz_exit; eassumption. Qed.

(* [comment removed for export] *)
Definition open_I (model : Model) : Type := {e : Z | In e openat_errnos} + unit.

Definition open_nx (ms : machine_state) (model : Model) (mk : word -> Model)
  (i : open_I model) : config :=
  match i with
  | inl (exist _ e _) => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
  | inr _ => mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model))))
                   (mk (alloc_fd (m_fds model)))
  end.

#[using="Type"] Lemma node_open : ltac2:(CDefT.buildp (gd_tbl_Nodes ()) "Pms,$0.Pmodel,$1.Px8,(2.&40.)Preads,(3.(21.(2.&40.)$29.))Pmk,P,(2.&40.)$1.P,(6.(7.(2.&40.))(14.R4.)(15.(2.&40.)))P,(6.(3.(21.(2.&40.)(2.&40.)))(22.R5.)(1;.(21.(2.&40.)(2.&40.))))P,(6.(7.(2.&40.))(8.R7.)(9.(2.&40.)R5.))P,Peff,$>.(6.$10.(11.(12.Vsegs,R9.R7.)R1.R8.)(36.R6.R1.R8.R5.))P,Pfd,(2.&40.)(6.(7.(2.&40.))(14.A1.R6.R1.)(15.(2.&40.)))P,Pfd,(2.&40.)(6.(3.(21.(2.&40.)(2.&40.)))(22.A1.R7.R1.)(1;.(21.(2.&40.)(2.&40.))))P,(6.(7.$37.)(38.(39.R:.)(3:.(39.R:.)))(15.$37.))(24.Vsegs,(;.R<.R;.)(3;.R;.)L,(3;.R;.)(1;.$4.)(3<.R<.R;.R8.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 reads mk Hh Hlazy Hsvc Hchk Hmk Hmklazy Hfree. split.
  - intros [[e He] | []]; cbn [open_nx].
    + rewrite <- (apply_effect_copyins_no_write ms (errno_ret e) reads).
      apply (sstep_of_check ms model x8); [exact Hh | exact Hsvc | | exact Hh | exact Hlazy].
      rewrite Hchk. apply check_open_result_copyins_ok_iff. left. exists e. auto.
    + rewrite <- (apply_effect_copyins_no_write ms (alloc_fd (m_fds model)) reads).
      apply (sstep_of_check ms model x8); [exact Hh | exact Hsvc | | apply Hmk | apply Hmklazy].
      rewrite Hchk. apply check_open_result_copyins_ok_iff.
      right. exists (alloc_fd (m_fds model)). auto.
  - intros e st Hss.
    destruct (sstep_svc_inv ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat. injection Hmat as <-.
        exists (inl (exist _ er Her)). cbn [open_nx].
        rewrite apply_effect_copyins_no_write. split; reflexivity.
      * subst fd. rewrite (materialize_model_accesses_no_lazy _ _ (Hmklazy _)) in Hmat.
        injection Hmat as <-.
        exists (inr tt). cbn [open_nx]. rewrite apply_effect_copyins_no_write. split; reflexivity.
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat. discriminate.
      * rewrite (materialize_model_accesses_no_lazy _ _ (Hmklazy _)) in Hmat. discriminate.
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * congruence.
      * rewrite Hmk in Hh2. discriminate.
    + exfalso. rewrite Hchk in Hc. exact (check_open_result_copyins_never_unmodeled _ _ _ _ Hc).
Qed.

#[using="Type"] Lemma rz_open : ltac2:(CDefT.buildp (gd_tbl_Nodes ()) "Pms,$0.Pmodel,$1.Px8,(2.&40.)Preads,(3.(21.(2.&40.)$29.))Pmk,P,(2.&40.)$1.PA,$2;.PB,$2;.P,(6.(7.(2.&40.))(14.R6.)(15.(2.&40.)))P,(6.(3.(21.(2.&40.)(2.&40.)))(22.R7.)(1;.(21.(2.&40.)(2.&40.))))P,(6.(7.(2.&40.))(8.R9.)(9.(2.&40.)R7.))P,Peff,$>.(6.$10.(11.(12.Vsegs,R;.R9.)R1.R:.)(36.R8.R1.R:.R7.))P,Pfd,(2.&40.)(6.(7.(2.&40.))(14.A1.R8.R1.)(15.(2.&40.)))P,Pfd,(2.&40.)(6.(3.(21.(2.&40.)(2.&40.)))(22.A1.R9.R1.)(1;.(21.(2.&40.)(2.&40.))))P,(6.(7.$37.)(38.(39.R<.)(3:.(39.R<.)))(15.$37.))P,Pe,$3=.P,(3>.$3=.R1.$3?.)(2<.Vsegs,(;.(19.(28.R10.(40.R2.)))R?.)R;.)P,(2<.Vsegs,(;.(19.(28.R?.(3:.(39.R>.))))A1.R;.(3:.(39.R>.)))R9.)(2<.Vsegs,(;.R10.R?.)(41.R;.R:.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 reads mk A B Hh Hlazy Hsvc Hchk Hmk Hmklazy Hfree HA HB.
  apply (rz_alt2 segs (mkCfg ms model) {e : Z | In e openat_errnos} unit
           (open_nx ms model mk) A B (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
  - eapply node_open; eassumption.
  - intros [e He]. cbn [open_nx]. apply HA. exact He.
  - intros []. cbn [open_nx]. exact HB.
Qed.

End WithSegs.
