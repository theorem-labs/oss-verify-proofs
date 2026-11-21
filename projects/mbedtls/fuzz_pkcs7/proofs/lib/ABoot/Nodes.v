(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (removed the syscall-node lemmas node_chk_ev, node_chk, node_det, node_ret_only, node_ret_only_copyins, rz_ret_only, rz_ret_only_copyins, rz_ret_only_silent, rz_ret_only_copyins_silent and rz_det, and the open node open_I, open_nx, node_open and rz_open). *)
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

End WithSegs.
