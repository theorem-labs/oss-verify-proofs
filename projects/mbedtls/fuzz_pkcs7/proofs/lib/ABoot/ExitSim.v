(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import SimInv.

Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_ExitSim () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.State.SyscallInput"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "is_exit_no"; "LinuxProcessSemantics.LinuxProcessSem.State.in_sysno"; "LinuxProcessSemantics.LinuxProcessSem.Specs.syscall_spec"; "LinuxProcessSemantics.LinuxProcessSem.Monad.Ok"; "LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect"; "LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.State.MemCopy"; "Corelib.Init.Datatypes.nat"; "LinuxProcessSemantics.LinuxProcessSem.State.with_halted"; "stdpp.bitvector.definitions.bv_and"; "LinuxProcessSemantics.LinuxProcessSem.State.in_arg"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "Corelib.Init.Datatypes.None"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "Corelib.Init.Datatypes.bool"; "WithSegs.sim_c"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.S"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.orb"; "Stdlib.ZArith.BinInt.Z.eqb"; "stdpp.bitvector.definitions.bv_unsigned"; "LinuxProcessSemantics.Riscv.Prelude.bv_eqb"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_pc"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_reg"; "LinuxProcessSemantics.LinuxProcessSem.Run.step_to"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.Run.sstep"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "LinuxProcessSemantics.LinuxProcessSem.Run.SNext"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.cons"; "LinuxProcessSemantics.LinuxProcessSem.State.ExitEv"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.outcome"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.exits_with"; "WithSegs.to_exit"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.exec"; "WithSegs.exit_post"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "LinuxProcessSemantics.LinuxProcessSem.Run.star"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.Run.cfg_model"; "LinuxProcessSemantics.LinuxProcessSem.Run.cfg_ms"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.Run.reaches_error"; "Corelib.Init.Peano.lt"; "Corelib.Init.Datatypes.length"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.stack_to_mem"; "Stdlib.Lists.List.nth_error"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.PhdrInfo"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.EntryDraw"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.build_stack_bytes"; "Corelib.Init.Datatypes.app"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.word_le8"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.nat_to_word"; "Corelib.Init.Peano.le"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Numbers.BinNums.N"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_mem"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_machine_state"; "overlay_argc_bytes"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.Build_machine_state"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_regs"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_fregs"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_pc_val"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_resv"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_fcsr"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_rom"; "enum_state"; "LinuxProcessSemantics.LinuxProcessSem.State.ProcInput"; "sim_c"; "LinuxProcessSemantics.LinuxProcessSem.State.in_argv"; "LinuxProcessSemantics.LinuxProcessSem.State.in_envp"; "LinuxProcessSemantics.LinuxProcessSem.State.in_uid"; "LinuxProcessSemantics.LinuxProcessSem.State.in_hwcap"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.omni_run"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkEntry"; "exit_post"; "LinuxProcessSemantics.LinuxProcessSem.State.in_fs"; "Corelib.Init.Logic.iff"; "LinuxProcessSemantics.LinuxProcessSem.Run.obs_trace"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_config"; "LinuxProcessSemantics.LinuxProcessSem.Run.is_prefix"; "LinuxProcessSemantics.EquivalenceDefinition.MustExit.must_exit_with"; "LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.omni_strong_equiv"; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence.modeled"; "LinuxProcessSemantics.LinuxProcessSem.Run.run"; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence.equiv"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition is_exit_no (no : word) : Prop :=
  bv_unsigned no = 93%Z \/ bv_unsigned no = 94%Z.

Lemma syscall_spec_exit : forall i m o,
  is_exit_no (in_sysno i) ->
  syscall_spec i m o <-> exit_spec (in_arg i 0) i m o.
Proof.
  intros i m o [E|E]; unfold syscall_spec, dispatch; rewrite E; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma exit_dispatch_ok : ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "Pi,$0.Pm,$1.P,(2.(3.R2.))(4.R3.R2.(5.$6.(7.(8.&40.=)(9.(:.(;.&40.)(<.(;.&8.))))(9.(:.(;.&40.)(;.&40.)))(9.(:.(;.&40.)(;.&40.)))(9.$=.)(9.(:.(;.&40.)$>.)))(?.(10.&40.(11.R3.#0.)(8.&40.+??.))R2.)(9.$12.)))")
(* [comment removed for export] *).
Proof.
  intros i m Hno. apply (proj2 (syscall_spec_exit i m _ Hno)).
  unfold exit_spec, set_halted, ret_only, modify, bind, pure. cbn.
  eexists tt, (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m),
    [], []. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma exit_dispatch_ok_inv : ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "Pi,$0.Pm,$1.Peff,$6.Pm',$1.Pevs,(<.$12.)P,(2.(3.R5.))P,(4.R6.R5.(5.$6.R4.R3.R2.))(13.(14.$6.R5.(7.(8.&40.=)(9.(:.(;.&40.)(<.(;.&8.))))(9.(:.(;.&40.)(;.&40.)))(9.(:.(;.&40.)(;.&40.)))(9.$=.)(9.(:.(;.&40.)$>.))))(13.(14.$1.R4.(?.(10.&40.(11.R7.#0.)(8.&40.+??.))R6.))(14.(<.$12.)R3.(9.$12.))))")
(* [comment removed for export] *).
Proof.
  intros i m eff m' evs Hno Hspec.
  apply (proj1 (syscall_spec_exit i m _ Hno)) in Hspec.
  unfold exit_spec, set_halted, ret_only, modify, bind, pure in Hspec. cbn in Hspec.
  sys_destruct. rewrite app_nil_l in *. repeat split; congruence.
Qed.

(* [comment removed for export] *)
Lemma exit_dispatch_no_unmodeled : forall i m,
  is_exit_no (in_sysno i) -> ~ syscall_spec i m Unmodeled.
Proof.
  intros i m Hno Hspec.
  apply (proj1 (syscall_spec_exit i m _ Hno)) in Hspec.
  unfold exit_spec, set_halted, ret_only, modify, bind, pure in Hspec. cbn in Hspec.
  sys_destruct.
Qed.

(* [comment removed for export] *)
Lemma in_arg0_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma in_sysno_sys_input : forall segs ms x8,
  in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.
Variable code : word.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive to_exit : machine_state -> Prop :=
| te_here : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    ms_gpr ms 0 = code ->
    to_exit ms
| te_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_exit ms' ->
    to_exit ms.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint sim_c (fuel : nat) (ms : machine_state) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    match ms_svc_pending ms with
    | Some x8 => ((bv_unsigned x8 =? 93)%Z || (bv_unsigned x8 =? 94)%Z)
                 && bv_eqb (ms_gpr ms 0) code
    | None =>
      match RiscvSemantics.step segs ms with
      | MachineOk ms' => sim_c fuel' ms'
      | MachineFault | MachineUnmodeled => false
      end
    end
  end.

#[using="Type"] Lemma sim_c_to_exit : forall fuel ms, sim_c fuel ms = true -> to_exit ms.
Proof.
  induction fuel as [|fuel IH]; intros ms H; [discriminate|].
  cbn in H. destruct (ms_svc_pending ms) as [x8|] eqn:Hsvc.
  - apply andb_true_iff in H as [Hx8 Hgpr].
    apply bv_eqb_eq in Hgpr.
    eapply te_here; eauto.
    apply orb_true_iff in Hx8. destruct Hx8 as [H|H]; apply Z.eqb_eq in H;
      [left|right]; exact H.
  - destruct (RiscvSemantics.step segs ms) as [ms'| |] eqn:Hstep;
      [|discriminate|discriminate].
    eapply te_step; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma sim_step : ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "Pfuel,$>.Pms,$15.Pms',$15.P,(14.(16.(;.&40.))(17.R2.)(18.(;.&40.)))P,(14.(19.$15.)(1:.Vsegs,R3.)(1;.$15.R2.))P,(14.$1<.(1=.R5.R3.)$1>.)(14.$1<.(1=.(1?.R6.)R5.)$1>.)")
(* [comment removed for export] *).
Proof.
  intros fuel ms ms' Hsvc Hstep Hrec.
  cbn [sim_c]. rewrite Hsvc. cbv beta iota. rewrite Hstep. exact Hrec.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sim_c_exit_now : ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "Pfuel,$>.Pms,$15.Px8,(;.&40.)P,(14.(16.(;.&40.))(17.R2.)(20.(;.&40.)R1.))P,(14.$1<.(21.(22.(23.&40.R2.)+5=.)(22.(23.&40.R2.)+5>.))$1>.)P,(14.$1<.(24.&40.(25.R4.#0.)Vcode,)$1>.)(14.$1<.(1=.(1?.R6.)R5.)$1>.)")
(* [comment removed for export] *).
Proof.
  intros fuel ms x8 Hsvc Hx8 Hcode.
  cbn [sim_c]. rewrite Hsvc. cbv beta iota. rewrite Hx8. cbn [andb]. exact Hcode.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sim_ecall_exit : ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "Pfuel,$>.Pms,$15.P,(14.(16.(;.&40.))(17.R1.)(18.(;.&40.)))P,(14.(16.(;.&20.))(26.Vsegs,(27.R2.))(20.(;.&20.)(28.&20.+73.$29.)))P,(14.$1<.(21.(22.(23.&40.(2:.R3.(28.&5.+11.$29.)))+5=.)(22.(23.&40.(2:.R3.(28.&5.+11.$29.)))+5>.))$1>.)P,(14.$1<.(24.&40.(25.R4.#0.)Vcode,)$1>.)(14.$1<.(1=.(1?.(1?.R6.))R5.)$1>.)")
(* [comment removed for export] *).
Proof.
  intros fuel ms Hsvc Hfetch Hcheck Hcode.
  set (ms1 := {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
                 ms_svc_pending := Some (ms_reg ms 17); ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
                 ms_mem := ms_mem ms; ms_rom := ms_rom ms |}).
  apply (sim_step (S fuel) ms ms1 Hsvc).
  - change (drop_access_report (step_accesses segs ms) = MachineOk ms1).
    unfold step_accesses. rewrite Hfetch. unfold ms1. reflexivity.
  - apply (sim_c_exit_now fuel ms1 (ms_reg ms 17)).
    + subst ms1. reflexivity.
    + exact Hcheck.
    + exact Hcode.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma sstep_instr_inv : ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "Pms,$15.Pmodel,$1.Pms',$15.Pevs,(<.$12.)Pst,$2;.P,(14.(<.(:.(;.&40.)(;.&40.)))(2<.R4.)(9.(:.(;.&40.)(;.&40.))))P,(14.(16.(;.&40.))(17.R6.)(18.(;.&40.)))P,(14.(19.$15.)(1:.Vsegs,R7.)(1;.$15.R5.))P,(2=.Vsegs,(2>.R8.R7.)R5.R4.)(13.(14.(<.$12.)R6.(9.$12.))(14.$2;.R5.(2?.(2>.R7.R8.))))")
(* [comment removed for export] *).
Proof.
  intros ms model ms' evs st Hlazy Hsvc Hstep Hss.
  inversion Hss; subst.
  - (* [comment removed for export] *)
    match goal with H : mi_account_step segs ms model = MachineOk _ |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; inversion H; subst end.
    split; reflexivity.
  - (* [comment removed for export] *)
    match goal with H : mi_account_step segs ms model = MachineFault |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* [comment removed for export] *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* [comment removed for export] *) congruence.
  - (* [comment removed for export] *) congruence.
  - (* [comment removed for export] *) congruence.
  - (* [comment removed for export] *) congruence.
  - (* [comment removed for export] *) congruence.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sstep_exit_inv : ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "Pms,$15.Pmodel,$1.Px8,(;.&40.)Pevs,(<.$12.)Pst,$2;.P,(14.(16.(;.&40.))(30.R4.)(18.(;.&40.)))P,(14.(16.(;.&40.))(17.R6.)(20.(;.&40.)R4.))P,(2.R5.)P,(2=.Vsegs,(2>.R8.R7.)R5.R4.)(13.(14.(<.$12.)R6.(31.$12.(32.(10.&40.(25.R9.#0.)(8.&40.+??.))(33.R8.))(9.$12.)))(14.$2;.R5.(2?.(2>.R9.(?.(10.&40.(25.R9.#0.)(8.&40.+??.))R8.)))))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 evs st Hh Hsvc Hx8 Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
    autorewrite with model in *.
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_halted ?model' = None |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (_ & Hm & _); rewrite Hm in H6;
      autorewrite with model in H6; discriminate
    end.
  - (* [comment removed for export] *)
    autorewrite with model in *.
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_halted ?model' = None |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (_ & Hm & _); rewrite Hm in H6;
      autorewrite with model in H6; discriminate
    end.
  - (* [comment removed for export] *)
    autorewrite with model in *.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' ?evs0),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (Heff & Hm & Hevs);
      rewrite in_arg0_sys_input in Hm;
      subst evs0 model';
      assert (Hcode : code = bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
        by (autorewrite with model in H6; congruence);
      subst code
    end.
    cbn. split; reflexivity.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_killed ?model' = Some _ |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (_ & Hm & _); rewrite Hm in H6;
      autorewrite with model in H6; discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled,
      H2 : ms_svc_pending ms = Some ?x |- _ =>
      eapply exit_dispatch_no_unmodeled; [| exact H3];
      rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8
    end.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma star_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star segs c tr c' -> tr = [] /\ c' = c.
Proof.
  intros c tr c' Hh Hstar. inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
  - split; reflexivity.
  - exfalso. destruct c as [ms model]. cbn in Hh.
    inversion Hss; subst; cbn in Hh; congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition exit_post (fs : Fs.Fs) : post := ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "Ltr,(<.$12.)Lo,$34.(13.(14.(<.$12.)R2.(31.$12.(32.(10.&40.Vcode,(8.&40.+??.))O1.)(9.$12.)))(35.(10.&40.Vcode,(8.&40.+??.))R2.R1.))")
(* [comment removed for export] *).

#[using="Type"] Lemma to_exit_exec : ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "Pms,$15.Pmodel,$1.P,(14.(16.(;.&40.))(30.R1.)(18.(;.&40.)))P,(14.(<.(:.(;.&40.)(;.&40.)))(2<.R2.)(9.(:.(;.&40.)(;.&40.))))P,(36.R4.)(37.Vsegs,(2>.R5.R4.)(38.(33.R4.)))")
(* [comment removed for export] *).
Proof.
  intros ms model Hh Hlazy Hte.
  induction Hte as [ms x8 Hsvc Hx8 Hgpr | ms ms' Hsvc Hstep Hte IH].
  - (* [comment removed for export] *)
    apply (exec_step_only segs _ _
             [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
             (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
    + replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
        with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
                       (m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
        by (cbn; reflexivity).
      apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
               (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
      * exact Hh.
      * exact Hsvc.
      * apply (exit_dispatch_ok (sys_input segs ms x8) model).
        rewrite in_sysno_sys_input. exact Hx8.
      * cbn. reflexivity.
      * apply m_killed_with_halted.
    + intros evs st Hss. exact (sstep_exit_inv ms model x8 evs st Hh Hsvc Hx8 Hss).
    + apply exec_halt.
      * cbn. rewrite m_halted_with_halted. discriminate.
      * unfold exit_post. cbn beta. rewrite app_nil_r, Hgpr. split; [reflexivity |].
        cbn [exits_with cfg_model]. split;
          [ rewrite m_halted_with_halted; reflexivity
          | apply m_killed_with_halted ].
  - (* [comment removed for export] *)
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact IH |]. intros tr o H. cbn [app]. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma to_exit_star_only : ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "Pms,$15.Pmodel,$1.P,(14.(16.(;.&40.))(30.R1.)(18.(;.&40.)))P,(14.(<.(:.(;.&40.)(;.&40.)))(2<.R2.)(9.(:.(;.&40.)(;.&40.))))P,(36.R4.)Ptr,(<.$12.)Pc,$39.P,(3:.Vsegs,(2>.R7.R6.)R2.R1.)(3;.(14.(<.$12.)R3.(9.$12.))(14.(<.$12.)R3.(31.$12.(32.(10.&40.Vcode,(8.&40.+??.))(33.R7.))(9.$12.))))")
(* [comment removed for export] *).
Proof.
  intros ms model Hh Hlazy Hte tr c Hstar.
  destruct (exec_realizes _ _ _ (exec_star _ _ _ _ _ (to_exit_exec ms model Hh Hlazy Hte) Hstar))
    as (tr' & o & _ & HQ).
  unfold exit_post in HQ. cbn beta in HQ. destruct HQ as (Heq & _).
  destruct (app_eq_unit _ _ Heq) as [(-> & _) | (-> & _)]; [left | right]; reflexivity.
Qed.

#[using="Type"] Lemma to_exit_star_admits : ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "Pms,$15.Pmodel,$1.P,(14.(16.(;.&40.))(30.R1.)(18.(;.&40.)))P,(14.(<.(:.(;.&40.)(;.&40.)))(2<.R2.)(9.(:.(;.&40.)(;.&40.))))P,(36.R4.)(3<.$39.Lc,$39.(3:.Vsegs,(2>.R6.R5.)(31.$12.(32.(10.&40.Vcode,(8.&40.+??.))(33.R5.))(9.$12.))R1.))")
(* [comment removed for export] *).
Proof.
  intros ms model Hh Hlazy Hte.
  destruct (exec_realizes _ _ _ (to_exit_exec ms model Hh Hlazy Hte))
    as (tr & [c' | c'] & Hm & Heq & Hx); [| destruct Hx].
  subst tr. destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
  exists c'. exact Hstar.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition on_path (c : config) : Prop := ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "(3;.(13.(14.(16.(;.&40.))(30.(3=.O1.))(18.(;.&40.)))(13.(14.(<.(:.(;.&40.)(;.&40.)))(2<.(3=.O1.))(9.(:.(;.&40.)(;.&40.))))(36.(3>.O1.))))(3?.(14.(16.(;.&40.))(30.(3=.O1.))(18.(;.&40.)))))")
(* [comment removed for export] *).

#[using="Type"] Lemma on_path_step : forall c evs c',
  on_path c -> sstep segs c evs (SNext c') -> on_path c'.
Proof.
  intros [ms model] evs [ms' model'] Hop Hss.
  unfold on_path in *; cbn in Hop |- *.
  destruct Hop as [[Hh [Hlazy Hte]] | Hh].
  - destruct Hte as [ms0 x8 Hsvc Hx8 Hgpr | ms0 ms0' Hsvc Hstep Hte].
    + (* [comment removed for export] *)
      destruct (sstep_exit_inv ms0 model x8 evs (SNext (mkCfg ms' model'))
                  Hh Hsvc Hx8 Hss) as [_ Hc'].
      inversion Hc'; subst. right. cbn. discriminate.
    + (* [comment removed for export] *)
      destruct (sstep_instr_inv ms0 model ms0' evs (SNext (mkCfg ms' model'))
                  Hlazy Hsvc Hstep Hss) as [_ Hc'].
      inversion Hc'; subst. left. repeat split; assumption.
  - (* [comment removed for export] *)
    exfalso. inversion Hss; subst; cbn in Hh; congruence.
Qed.

#[using="Type"] Lemma on_path_no_error : forall c evs, on_path c -> ~ sstep segs c evs SError.
Proof.
  intros [ms model] evs Hop Hss.
  unfold on_path in *; cbn in Hop.
  destruct Hop as [[Hh [Hlazy Hte]] | Hh].
  - destruct Hte as [ms0 x8 Hsvc Hx8 Hgpr | ms0 ms0' Hsvc Hstep Hte].
    + destruct (sstep_exit_inv ms0 model x8 evs SError Hh Hsvc Hx8 Hss) as [_ Hc'].
      discriminate.
    + destruct (sstep_instr_inv ms0 model ms0' evs SError Hlazy Hsvc Hstep Hss) as [_ Hc'].
      discriminate.
  - inversion Hss; subst; cbn in Hh; congruence.
Qed.

#[using="Type"] Lemma star_on_path : forall c tr c',
  on_path c -> star segs c tr c' -> on_path c'.
Proof. exact (star_inv segs on_path on_path_step). Qed.

#[using="Type"] Lemma to_exit_no_error : ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "Pms,$15.Pmodel,$1.P,(14.(16.(;.&40.))(30.R1.)(18.(;.&40.)))P,(14.(<.(:.(;.&40.)(;.&40.)))(2<.R2.)(9.(:.(;.&40.)(;.&40.))))P,(36.R4.)(3?.(40.Vsegs,(2>.R5.R4.)))")
(* [comment removed for export] *).
Proof.
  intros ms model Hh Hlazy Hte. apply exec_no_error.
  eapply exec_conseq; [exact (to_exit_exec ms model Hh Hlazy Hte) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition overlay_argc_bytes (sp : word) (argc : nat)
    (base_mem : word -> option byte) : word -> option byte :=
  let bytes := word_le8 (nat_to_word argc) in
  fun addr =>
    if (bv_unsigned addr =? bv_unsigned sp)%Z then nth_error bytes 0
    else if (bv_unsigned addr =? bv_unsigned sp + 1)%Z then nth_error bytes 1
    else if (bv_unsigned addr =? bv_unsigned sp + 2)%Z then nth_error bytes 2
    else if (bv_unsigned addr =? bv_unsigned sp + 3)%Z then nth_error bytes 3
    else if (bv_unsigned addr =? bv_unsigned sp + 4)%Z then nth_error bytes 4
    else if (bv_unsigned addr =? bv_unsigned sp + 5)%Z then nth_error bytes 5
    else if (bv_unsigned addr =? bv_unsigned sp + 6)%Z then nth_error bytes 6
    else if (bv_unsigned addr =? bv_unsigned sp + 7)%Z then nth_error bytes 7
    else base_mem addr.

Lemma stm_at (sp : word) (bytes : list byte) (addr : word) (i : nat) : ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "P,(41.O1.(42.(;.&8.)O3.))P,(14.$43.(23.&40.O2.)(44.(23.&40.O4.)(45.O1.)))(14.(16.(;.&8.))(46.O4.O3.O2.)(47.(;.&8.)O3.O1.))")
(* [comment removed for export] *).
Proof.
  intros Hi Haddr. unfold stack_to_mem. rewrite Haddr. cbv beta zeta.
  destruct (Z.leb (bv_unsigned sp) (bv_unsigned sp + Z.of_nat i)) eqn:E1.
  2: { apply Z.leb_gt in E1; lia. }
  replace (bv_unsigned sp + Z.of_nat i - bv_unsigned sp)%Z with (Z.of_nat i) by lia.
  destruct (Z.ltb (Z.of_nat i) (Z.of_nat (length bytes))) eqn:E2.
  - rewrite Nat2Z.id. reflexivity.
  - apply Z.ltb_ge in E2. lia.
Qed.

Lemma build_stack_starts_with_argc : ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "Pph,$48.Psp,(;.&40.)Pargv,(<.(<.(;.&8.)))Penvp,(<.(<.(;.&8.)))Puid,(;.&40.)Phw,(;.&40.)Prnd,$49.(3<.(<.(;.&8.))Lrest,(<.(;.&8.))(14.(<.(;.&8.))(4:.R8.R7.R6.R5.R4.R3.R2.)(4;.(;.&8.)(4<.(4=.(42.(<.(;.&8.))R6.)))R1.)))")
(* [comment removed for export] *).
Proof.
  intros ph sp argv envp uid hw rnd. unfold build_stack_bytes, len_word, nat_to_word.
  destruct (string_addrs _ argv) as [? ?]. destruct (string_addrs _ envp) as [? ?].
  eexists. exact (eq_sym (app_assoc _ _ _)).
Qed.

Lemma word_le8_length : forall v, length (word_le8 v) = 8%nat.
Proof. intro v. reflexivity. Qed.

Lemma build_stack_min_length : ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "Pph,$48.Psp,(;.&40.)Pargv,(<.(<.(;.&8.)))Penvp,(<.(<.(;.&8.)))Puid,(;.&40.)Phw,(;.&40.)Prnd,$49.(4>.#8.(42.(;.&8.)(4:.R7.R6.R5.R4.R3.R2.R1.)))")
(* [comment removed for export] *).
Proof.
  intros ph sp argv envp uid hw rnd.
  destruct (build_stack_starts_with_argc ph sp argv envp uid hw rnd) as [rest Hr].
  rewrite Hr, length_app, word_le8_length. lia.
Qed.

(* [comment removed for export] *)
Lemma init_first8 : ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "Psegs,(<.$4?.)Pinit_pc,$50.Pph,$48.Pinit_sp,(;.&40.)Pinit_rnd,$49.Pargv,(<.(<.(;.&8.)))Penvp,(<.(<.(;.&8.)))Paddr,(;.&40.)Pi,$>.Puid,(;.&40.)Phw,(;.&40.)P,(41.R3.#8.)P,(14.$43.(23.&40.R5.)(44.(23.&40.R9.)(45.R4.)))(14.(16.(;.&8.))(51.(52.R=.R<.R;.R:.R9.R8.R7.R4.R3.)R6.)(47.(;.&8.)(4<.(4=.(42.(<.(;.&8.))R8.)))R5.))")
(* [comment removed for export] *).
Proof.
  intros segs init_pc ph init_sp init_rnd argv envp addr i uid hw Hi Haddr.
  assert (Hstk : stack_to_mem init_sp (entry_stack_image ph init_sp argv envp uid hw init_rnd) addr
                 = nth_error (word_le8 (nat_to_word (length argv))) i).
  { rewrite stack_to_mem_image_in_block
      by (pose proof (build_stack_min_length ph init_sp argv envp uid hw init_rnd);
          unfold entry_block_top; lia).
    rewrite (stm_at init_sp _ addr i);
      [ | pose proof (build_stack_min_length ph init_sp argv envp uid hw init_rnd); lia
        | exact Haddr ].
    destruct (build_stack_starts_with_argc ph init_sp argv envp uid hw init_rnd) as [rest Hr].
    rewrite Hr. apply nth_error_app1. rewrite word_le8_length. lia. }
  change (ms_mem (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw) addr)
    with (match stack_to_mem init_sp (entry_stack_image ph init_sp argv envp uid hw init_rnd) addr with
          | Some b => Some b
          | None =>
              if andb (Z.leb (bv_unsigned init_sp - stack_max_size)
                             (bv_unsigned addr))
                      (Z.ltb (bv_unsigned addr) (bv_unsigned init_sp))
              then Some (Z_to_bv 8 0) else None
          end).
  rewrite Hstk.
  destruct (nth_error (word_le8 (nat_to_word (length argv))) i) eqn:E; [reflexivity|].
  apply nth_error_None in E. rewrite word_le8_length in E. lia.
Qed.

Lemma actual_mem_is_overlay : ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "Psegs,(<.$4?.)Pinit_pc,$50.Pph,$48.Pinit_sp,(;.&40.)Pinit_rnd,$49.Pargv,(<.(<.(;.&8.)))Penvp,(<.(<.(;.&8.)))Puid,(;.&40.)Phw,(;.&40.)(14.P,(;.&40.)(16.(;.&8.))(51.(52.R9.R8.R7.R6.R5.R4.R3.R2.R1.))(53.R6.(42.(<.(;.&8.))R4.)(51.(52.R9.R8.R7.R6.R5.R4.R3.R2.R1.))))")
(* [comment removed for export] *).
Proof.
  intros segs init_pc ph init_sp init_rnd argv envp uid hw.
  apply functional_extensionality. intro addr.
  unfold overlay_argc_bytes.
  destruct ((bv_unsigned addr =? bv_unsigned init_sp)%Z) eqn:E0;
    [ apply Z.eqb_eq in E0;
      apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 0 uid hw); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 1)%Z) eqn:E1;
    [ apply Z.eqb_eq in E1;
      apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 1 uid hw); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 2)%Z) eqn:E2;
    [ apply Z.eqb_eq in E2;
      apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 2 uid hw); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 3)%Z) eqn:E3;
    [ apply Z.eqb_eq in E3;
      apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 3 uid hw); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 4)%Z) eqn:E4;
    [ apply Z.eqb_eq in E4;
      apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 4 uid hw); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 5)%Z) eqn:E5;
    [ apply Z.eqb_eq in E5;
      apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 5 uid hw); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 6)%Z) eqn:E6;
    [ apply Z.eqb_eq in E6;
      apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 6 uid hw); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 7)%Z) eqn:E7;
    [ apply Z.eqb_eq in E7;
      apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 7 uid hw); lia | ].
  reflexivity.
Qed.

Lemma machine_state_eta : ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "Pms,$15.(14.$15.R1.(54.(55.R1.)(56.R1.)(57.R1.)(17.R1.)(58.R1.)(59.R1.)(51.R1.)(5:.R1.)))")
(* [comment removed for export] *).
Proof. intros []; reflexivity. Qed.

(* [comment removed for export] *)
Definition enum_state (segs : list Segment) (init_pc : N) (ph : PhdrInfo)
    (init_sp : word) (init_rnd : EntryDraw) (argc : nat)
    (base : word -> option byte) (uid : word)
    (hw : word) : machine_state := ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "(54.(55.(52.O9.O8.O7.O6.O5.(9.(<.(;.&8.)))(9.(<.(;.&8.)))O2.O1.))(56.(52.O9.O8.O7.O6.O5.(9.(<.(;.&8.)))(9.(<.(;.&8.)))O2.O1.))(57.(52.O9.O8.O7.O6.O5.(9.(<.(;.&8.)))(9.(<.(;.&8.)))O2.O1.))(17.(52.O9.O8.O7.O6.O5.(9.(<.(;.&8.)))(9.(<.(;.&8.)))O2.O1.))(58.(52.O9.O8.O7.O6.O5.(9.(<.(;.&8.)))(9.(<.(;.&8.)))O2.O1.))(59.(52.O9.O8.O7.O6.O5.(9.(<.(;.&8.)))(9.(<.(;.&8.)))O2.O1.))(53.O6.O4.O3.)(5:.(52.O9.O8.O7.O6.O5.(9.(<.(;.&8.)))(9.(<.(;.&8.)))O2.O1.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Lemma init_eq_enum_state : ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "Psegs,(<.$4?.)Pinit_pc,$50.Pph,$48.Pinit_sp,(;.&40.)Pinit_rnd,$49.Pargv,(<.(<.(;.&8.)))Penvp,(<.(<.(;.&8.)))Puid,(;.&40.)Phw,(;.&40.)(14.$15.(52.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(5;.R9.R8.R7.R6.R5.(42.(<.(;.&8.))R4.)(51.(52.R9.R8.R7.R6.R5.R4.R3.R2.R1.))R2.R1.))")
(* [comment removed for export] *).
Proof.
  intros segs init_pc ph init_sp init_rnd argv envp uid hw. unfold enum_state.
  rewrite (machine_state_eta (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw)) at 1.
  f_equal; try reflexivity. apply actual_mem_is_overlay.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma exit_omni_run : ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "Psegs,(<.$4?.)Ppc,$50.Pph,$48.Psp,(;.&40.)Pbrk0,(;.&40.)Pmb,(;.&40.)Prnd,$49.Plim,$43.Pcode,(;.&40.)Pinp,$5<.PF,$>.P,(14.$1<.(5=.R;.R3.R1.(52.R;.R:.R9.R8.R5.(5>.R2.)(5?.R2.)(60.R2.)(61.R2.)))$1>.)(62.(63.R<.R;.R:.)R5.(64.R9.R8.R7.R6.)R3.(65.R4.(66.R3.)))")
(* [comment removed for export] *).
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F Hsim.
  cbn [omni_run]. unfold init_config.
  exact (to_exit_exec segs code
           (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
           (init_model (segments_reserved segs) brk0 mb sp lim inp)
           eq_refl eq_refl (sim_c_to_exit segs code F _ Hsim)).
Qed.

Lemma exit_obs_iff : ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "Psegs,(<.$4?.)Ppc,$50.Pph,$48.Psp,(;.&40.)Pbrk0,(;.&40.)Pmb,(;.&40.)Prnd,$49.Plim,$43.Pcode,(;.&40.)Pinp,$5<.PF,$>.P,(14.$1<.(5=.R;.R3.R1.(52.R;.R:.R9.R8.R5.(5>.R2.)(5?.R2.)(60.R2.)(61.R2.)))$1>.)Ptr,(<.$12.)(67.(68.R=.(69.R=.R<.R;.R:.R9.R8.R7.R6.R4.)R1.)(6:.$12.R1.(31.$12.(32.(10.&40.R5.(8.&40.+??.))(66.R4.))(9.$12.))))")
(* [comment removed for export] *).
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F Hsim tr.
  apply exec_obs_iff.
  eapply exec_conseq; [exact (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) |].
  intros tr' o (Heq & Hx). split; [exact Heq | exact (exits_with_never_errors _ _ _ Hx)].
Qed.

Lemma exit_no_error_run : ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "Psegs,(<.$4?.)Ppc,$50.Pph,$48.Psp,(;.&40.)Pbrk0,(;.&40.)Pmb,(;.&40.)Prnd,$49.Plim,$43.Pcode,(;.&40.)Pinp,$5<.PF,$>.P,(14.$1<.(5=.R;.R3.R1.(52.R;.R:.R9.R8.R5.(5>.R2.)(5?.R2.)(60.R2.)(61.R2.)))$1>.)(3?.(40.R<.(69.R<.R;.R:.R9.R8.R7.R6.R5.R3.)))")
(* [comment removed for export] *).
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F Hsim. apply exec_no_error.
  eapply exec_conseq; [exact (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* [comment removed for export] *)
Lemma exit_must_exit_with : ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "Psegs,(<.$4?.)Ppc,$50.Pph,$48.Psp,(;.&40.)Pbrk0,(;.&40.)Pmb,(;.&40.)Prnd,$49.Plim,$43.Pcode,(;.&40.)Pinp,$5<.PF,$>.P,(14.$1<.(5=.R;.R3.R1.(52.R;.R:.R9.R8.R5.(5>.R2.)(5?.R2.)(60.R2.)(61.R2.)))$1>.)(6;.(10.&40.R4.(8.&40.+??.))(63.R<.R;.R:.)R5.(64.R9.R8.R7.R6.)R3.)")
(* [comment removed for export] *).
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F Hsim. apply must_exit_with_iff.
  eapply exec_conseq; [exact (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) |].
  intros tr o (_ & Hx). exact Hx.
Qed.

Lemma exit_omni_run_code_unique : ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "Psegs,(<.$4?.)Ppc,$50.Pph,$48.Psp,(;.&40.)Pbrk0,(;.&40.)Pmb,(;.&40.)Prnd,$49.Plim,$43.Pcode,(;.&40.)Pinp,$5<.PF,$>.Pcode',(;.&40.)P,(14.$1<.(5=.R<.R4.R2.(52.R<.R;.R:.R9.R6.(5>.R3.)(5?.R3.)(60.R3.)(61.R3.)))$1>.)P,(62.(63.R=.R<.R;.)R6.(64.R:.R9.R8.R7.)R4.(35.R2.))(14.(;.&40.)R3.(10.&40.R6.(8.&40.+??.)))")
(* [comment removed for export] *).
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F code' Hsim Hex.
  pose proof (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) as Hrun.
  cbn [omni_run] in Hrun, Hex.
  destruct (exec_realizes _ _ _ Hrun) as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
  cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
  rewrite Hx in Hx'. injection Hx' as Hx'. symmetry. exact Hx'.
Qed.

(* [comment removed for export] *)
Lemma exit_omni_strong_equiv : ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "Psource_segs,(<.$4?.)Prpc,$50.Prph,$48.Prsp,(;.&40.)Prbrk,(;.&40.)Prmb,(;.&40.)Prrnd,$49.Ptarget_segs,(<.$4?.)Papc,$50.Paph,$48.Pasp,(;.&40.)Pabrk,(;.&40.)Pamb,(;.&40.)Parnd,$49.Pcode,(;.&40.)Pinp,$5<.PFR,$>.PFA,$>.P,(14.$1<.(5=.R12.R4.R2.(52.R12.R11.R10.R?.R<.(5>.R3.)(5?.R3.)(60.R3.)(61.R3.)))$1>.)P,(14.$1<.(5=.R<.R5.R2.(52.R<.R;.R:.R9.R6.(5>.R4.)(5?.R4.)(60.R4.)(61.R4.)))$1>.)(6<.(63.R14.R13.R12.)(63.R=.R<.R;.)(64.R11.R10.R?.R>.)(64.R:.R9.R8.R7.)R5.)")
(* [comment removed for export] *).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd code inp FR FA
    Hsource Htarget.
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [apply exec_coexec;
       exact (exit_omni_run source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit code inp FR Hsource) |].
    intros tr o (_ & Hx).
    exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (exit_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit code inp FR Hsource tr).
    rewrite (exit_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit code inp FA Htarget tr).
    reflexivity.
  - apply bh_errors_iff. cbn.
    apply (exit_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit code inp FA Htarget).
Qed.

(* [comment removed for export] *)
Lemma exit_strong_equiv : ltac2:(CDefT.buildp (gd_tbl_ExitSim ()) "Psource_segs,(<.$4?.)Prpc,$50.Prph,$48.Prsp,(;.&40.)Prbrk,(;.&40.)Prmb,(;.&40.)Prrnd,$49.Prlim,$43.Ptarget_segs,(<.$4?.)Papc,$50.Paph,$48.Pasp,(;.&40.)Pabrk,(;.&40.)Pamb,(;.&40.)Parnd,$49.Palim,$43.Pcode,(;.&40.)Pinp,$5<.PFR,$>.PFA,$>.P,(14.$1<.(5=.R14.R4.R2.(52.R14.R13.R12.R11.R>.(5>.R3.)(5?.R3.)(60.R3.)(61.R3.)))$1>.)P,(14.$1<.(5=.R=.R5.R2.(52.R=.R<.R;.R:.R7.(5>.R4.)(5?.R4.)(60.R4.)(61.R4.)))$1>.)(13.(6=.(6>.(63.R16.R15.R14.)R?.(64.R13.R12.R11.R10.)R5.))(6?.(6>.(63.R16.R15.R14.)R?.(64.R13.R12.R11.R10.)R5.)(6>.(63.R>.R=.R<.)R7.(64.R;.R:.R9.R8.)R5.)))")
(* [comment removed for export] *).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim code inp FR FA
    Hsource Htarget.
  split.
  { apply no_error_run_modeled.
    apply (exit_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim code inp FR Hsource). }
  right. split.
  - intro tr. cbn.
    rewrite (exit_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim code inp FR Hsource tr).
    rewrite (exit_obs_iff target_segs apc aph asp abrk amb arnd alim code inp FA Htarget tr).
    reflexivity.
  - cbn. apply (exit_no_error_run target_segs apc aph asp abrk amb arnd alim code inp FA Htarget).
Qed.
