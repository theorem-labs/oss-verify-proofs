(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PropExec.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
Local Ltac div_vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_DivergeSim () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.access_report"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step_accesses"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.mkAccessReport"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_access"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.Run.mi_account_step"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.option"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "Corelib.Init.Datatypes.None"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_pc"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall"; "Corelib.Init.Datatypes.false"; "LinuxProcessSemantics.Riscv.Instr.instr"; "LinuxProcessSemantics.Riscv.DecodeC.decode_any"; "LinuxProcessSemantics.Riscv.Instr.Jal"; "LinuxProcessSemantics.Riscv.Sem.is_x0"; "Corelib.Init.Datatypes.true"; "stdpp.bitvector.definitions.bv_signed"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step"; "OSSVerify.KrLib.ABoot.PropExec.mkst"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.and"; "LinuxProcessSemantics.LinuxProcessSem.Run.cfg_model"; "LinuxProcessSemantics.LinuxProcessSem.Run.cfg_ms"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "Stdlib.Lists.List.In"; "WithFP1.WithSegs.silent_loop"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "LinuxProcessSemantics.LinuxProcessSem.Run.step_to"; "LinuxProcessSemantics.LinuxProcessSem.Run.sstep"; "LinuxProcessSemantics.LinuxProcessSem.Run.SNext"; "LinuxProcessSemantics.LinuxProcessSem.Run.star"; "Corelib.Init.Logic.or"; "Corelib.Init.Datatypes.app"; "WithFP1.WithSegs.to_spin"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "Corelib.Init.Logic.iff"; "LinuxProcessSemantics.LinuxProcessSem.Run.obs_trace"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.Run.reaches_error"; "LinuxProcessSemantics.LinuxProcessSem.Run.SError"; "LinuxProcessSemantics.LinuxProcessSem.Run.reaches_unmodeled"; "LinuxProcessSemantics.LinuxProcessSem.Run.all_traces_error"; "LinuxProcessSemantics.LinuxProcessSem.Run.is_prefix"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.EntryDraw"; "LinuxProcessSemantics.LinuxProcessSem.State.ProcInput"; "to_spin"; "SelfJumpImage.spin_segs"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_machine_state"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkPhdrInfo"; "LinuxProcessSemantics.LinuxProcessSem.State.in_argv"; "LinuxProcessSemantics.LinuxProcessSem.State.in_envp"; "LinuxProcessSemantics.LinuxProcessSem.State.in_uid"; "LinuxProcessSemantics.LinuxProcessSem.State.in_hwcap"; "LinuxProcessSemantics.LinuxProcessSem.State.init_model"; "LinuxProcessSemantics.LinuxProcessSem.Run.segments_reserved"].


Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma is_prefix_nil_inv {A} : forall (tr : list A),
  is_prefix tr [] -> tr = [].
Proof. destruct tr; [reflexivity | contradiction]. Qed.

#[using="Type"] Lemma is_prefix_app_mono {A} : forall (e a b : list A),
  is_prefix a b -> is_prefix (e ++ a) (e ++ b).
Proof. induction e; cbn; auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma materialize_model_accesses_nil : forall m,
  materialize_model_accesses m [] = Some m.
Proof.
  intros [fd [maps lazy materialized] io fs proc lim].
  unfold materialize_model_accesses; cbn.
  unfold materialize_accesses, newly_materialized_pages; cbn.
  reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mi_account_step_of_accesses : forall segs ms model ms' ranges,
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  mi_account_step segs ms model =
    match materialize_model_accesses model ranges with
    | Some model' => MachineOk (ms', model')
    | None => MachineFault
    end.
Proof.
  intros segs ms model ms' ranges Hstep.
  unfold mi_account_step. rewrite Hstep. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mi_account_step_no_access : ltac2:(CDefT.buildp (gd_tbl_DivergeSim ()) "Psegs,(0.$1.)Pms,$2.Pmodel,$3.Pms',$2.P,(4.(5.(6.$2.))(7.R4.R3.)(8.(6.$2.)(9.$2.R1.(:.$;.))))(4.(5.(<.$2.$3.))(=.R5.R4.R3.)(8.(<.$2.$3.)(>.$2.$3.R2.R3.)))")
(* [comment removed for export] *).
Proof.
  intros segs ms model ms' Hstep.
  rewrite (mi_account_step_of_accesses segs ms model ms' [] Hstep).
  rewrite materialize_model_accesses_nil. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mi_account_step_halted : ltac2:(CDefT.buildp (gd_tbl_DivergeSim ()) "Psegs,(0.$1.)Pms,$2.Pmodel,$3.Pms',$2.Pmodel',$3.P,(4.(5.(<.$2.$3.))(=.R5.R4.R3.)(8.(<.$2.$3.)(>.$2.$3.R2.R1.)))(4.(?.(10.&40.))(11.R2.)(11.R4.))")
(* [comment removed for export] *).
Proof.
  intros segs ms model ms' model' Hacc.
  destruct (mi_account_step_model_frame segs ms model ms' model' Hacc)
    as (_ & _ & _ & _ & _ & Hproc & _).
  unfold m_halted. rewrite Hproc. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma v_addi_0 : forall a : word, v_addi a 0 = a.
Proof.
  intro a. unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma self_jump_step_accesses : ltac2:(CDefT.buildp (gd_tbl_DivergeSim ()) "Psegs,(0.$1.)Pms,$2.Pw,(10.&20.)Prd,(10.&5.)Pimm,(10.&15.)Psz,$12.P,(4.(?.(10.&40.))(13.R5.)(14.(10.&40.)))P,(4.(?.(10.&20.))(15.R7.(16.R6.))(17.(10.&20.)R5.))P,(4.$18.(19.R6.)$1:.)P,(4.(?.(<.$1;.$12.))(1<.R7.)(17.(<.$1;.$12.)(>.$1;.$12.(1=.R6.R5.)R4.)))P,(4.$18.(1>.R7.)$1?.)P,(4.$12.(20.&15.R7.)=)(4.(5.(6.$2.))(7.R<.R;.)(8.(6.$2.)(9.$2.R;.(:.$;.))))")
(* [comment removed for export] *).
Proof.
  intros segs ms w rd imm sz Hsvc Hfetch Hecall Hdecode Hx0 Himm.
  unfold RiscvSemantics.step_accesses.
  rewrite Hfetch.
  unfold RiscvSemantics.decode_exec_accesses.
  rewrite Hecall. cbv beta iota.
  rewrite Hdecode. cbv beta iota.
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses Sem.exec
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc
     Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv].
  rewrite Hx0. cbv beta iota.
  rewrite b_addsext, Himm, v_addi_0.
  destruct ms; cbn in Hsvc; subst; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma self_jump_account_fix : ltac2:(CDefT.buildp (gd_tbl_DivergeSim ()) "Psegs,(0.$1.)Pms,$2.Pmodel,$3.Pw,(10.&20.)Prd,(10.&5.)Pimm,(10.&15.)Psz,$12.P,(4.(?.(10.&40.))(13.R6.)(14.(10.&40.)))P,(4.(?.(10.&20.))(15.R8.(16.R7.))(17.(10.&20.)R5.))P,(4.$18.(19.R6.)$1:.)P,(4.(?.(<.$1;.$12.))(1<.R7.)(17.(<.$1;.$12.)(>.$1;.$12.(1=.R6.R5.)R4.)))P,(4.$18.(1>.R7.)$1?.)P,(4.$12.(20.&15.R7.)=)(4.(5.(<.$2.$3.))(=.R=.R<.R;.)(8.(<.$2.$3.)(>.$2.$3.R<.R;.)))")
(* [comment removed for export] *).
Proof.
  intros. eapply mi_account_step_no_access.
  eapply self_jump_step_accesses; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma step_j_self : ltac2:(CDefT.buildp (gd_tbl_DivergeSim ()) "Psegs,(0.$1.)Pregs,(21.&5.(10.&40.))Ppc,(10.&40.)Pmem,P,(10.&40.)(?.(10.&8.))Prom,P,(10.&40.)(?.(10.&8.))Pw,(10.&20.)Prd,(10.&5.)Pimm,(10.&15.)Psz,$12.P,(4.(?.(10.&20.))(15.R9.R7.)(17.(10.&20.)R4.))P,(4.$18.(19.R5.)$1:.)P,(4.(?.(<.$1;.$12.))(1<.R6.)(17.(<.$1;.$12.)(>.$1;.$12.(1=.R5.R4.)R3.)))P,(4.$18.(1>.R6.)$1?.)P,(4.$12.(20.&15.R6.)=)(4.(5.$2.)(22.R>.(23.Vfx,R=.R<.R;.R:.))(8.$2.(23.Vfx,R=.R<.R;.R:.)))")
(* [comment removed for export] *).
Proof.
  intros segs regs pc mem rom w rd imm sz Hf He Hd Hx0 Hi.
  unfold RiscvSemantics.step.
  rewrite (self_jump_step_accesses segs (mkst regs pc mem rom) w rd imm sz
             eq_refl Hf He Hd Hx0 Hi).
  reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition silent_loop (P : config -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_DivergeSim ()) "Pc,$24.P,A1.O1.R1.(25.(4.(?.(10.&40.))(11.(26.R2.))(14.(10.&40.)))(25.(4.(?.(10.&40.))(13.(27.R2.))(14.(10.&40.)))(28.$2.Lms',$2.(28.$3.Lmodel',$3.(25.(4.(5.(<.$2.$3.))(=.Vsegs,(27.R4.)(26.R4.))(8.(<.$2.$3.)(>.$2.$3.R2.R1.)))A1.O1.(29.R2.R1.))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
#[using="Type"] Lemma silent_loop_cycle : ltac2:(CDefT.buildp (gd_tbl_DivergeSim ()) "Pcs,(0.$24.)P,Pc,$24.P,(2:.$24.R1.R2.)(25.(4.(?.(10.&40.))(11.(26.R2.))(14.(10.&40.)))(25.(4.(?.(10.&40.))(13.(27.R2.))(14.(10.&40.)))(28.$2.Lms',$2.(28.$3.Lmodel',$3.(25.(4.(5.(<.$2.$3.))(=.Vsegs,(27.R4.)(26.R4.))(8.(<.$2.$3.)(>.$2.$3.R2.R1.)))(2:.$24.(29.R2.R1.)R5.))))))(2;.Lc,$24.(2:.$24.R1.R3.))")
(* [comment removed for export] *).
Proof. intros cs H c. exact (H c). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma silent_loop_sstep : ltac2:(CDefT.buildp (gd_tbl_DivergeSim ()) "PP,P,$24.SpPc,$24.Pevs,(0.$2<.)Pto,$2=.P,(2;.R4.)P,A1.R5.R4.P,(2>.Vsegs,R5.R4.R3.)(25.(4.(0.$2<.)R5.(:.$2<.))(28.$24.Lc',$24.(25.(4.$2=.R5.(2?.R1.))A1.R8.R1.)))")
(* [comment removed for export] *).
Proof.
  intros P c evs to Hloop HP Hstep.
  destruct (Hloop c HP) as (Hh & Hsvc & ms' & model' & Hacc & HP').
  destruct c as [ms model]; cbn in Hh, Hsvc, Hacc.
  inversion Hstep; subst; try congruence.
  (* [comment removed for export] *)
  repeat match goal with
  | H : mi_account_step ?s ?a ?b = MachineOk ?x,
    H' : mi_account_step ?s ?a ?b = MachineOk ?y |- _ =>
      rewrite H in H'; injection H'; intros; subst; clear H
  end.
  eauto 7.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma star_case : ltac2:(CDefT.buildp (gd_tbl_DivergeSim ()) "Pc,$24.Ptr,(0.$2<.)Pc',$24.P,(30.Vsegs,R3.R2.R1.)(31.(25.(4.(0.$2<.)R3.(:.$2<.))(4.$24.R2.R4.))(28.(0.$2<.)Levs,(0.$2<.)(28.$24.Lc2,$24.(28.(0.$2<.)Ltr2,(0.$2<.)(25.(2>.Vsegs,R7.R3.(2?.R2.))(25.(30.Vsegs,R2.R1.R5.)(4.(0.$2<.)R6.(32.$2<.R3.R1.))))))))")
(* [comment removed for export] *).
Proof.
  intros c tr c' H;
    destruct H as [c | c1 evs c2 tr2 c3 Hstep Htail];
    [left; auto | right; exists evs, c2, tr2; auto].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma silent_loop_star : forall P, silent_loop P ->
  forall c tr c', star segs c tr c' -> P c -> tr = [] /\ P c'.
Proof.
  intros P Hloop c tr c' Hstar.
  induction Hstar as [c | c evs c2 tr c3 Hstep Hstar IH]; intros HP.
  - auto.
  - destruct (silent_loop_sstep P c evs _ Hloop HP Hstep)
      as (-> & c2' & Heq & HP2).
    injection Heq as <-.
    destruct (IH HP2) as (-> & HP3). auto.
Qed.

#[using="Type"] Lemma silent_loop_star_nil : forall P c tr c',
  silent_loop P -> P c -> star segs c tr c' -> tr = [].
Proof.
  intros P c tr c' Hloop HP Hstar.
  exact (proj1 (silent_loop_star P Hloop c tr c' Hstar HP)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma silent_loop_no_error : forall P c,
  silent_loop P -> P c -> ~ reaches_error segs c.
Proof.
  intros P c Hloop HP (tr & c2 & evs & Hstar & Herr).
  destruct (silent_loop_star P Hloop c tr c2 Hstar HP) as (_ & HP2).
  destruct (silent_loop_sstep P c2 evs _ Hloop HP2 Herr)
    as (_ & c' & Heq & _).
  discriminate Heq.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma silent_loop_no_unmodeled : forall P c,
  silent_loop P -> P c -> ~ reaches_unmodeled segs c.
Proof.
  intros P c Hloop HP.
  exact (no_error_no_unmodeled segs c (silent_loop_no_error P c Hloop HP)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma silent_loop_obs_iff : forall P c,
  silent_loop P -> P c -> forall tr, obs_trace segs c tr <-> tr = [].
Proof.
  intros P c Hloop HP tr. split.
  - intros (tr' & c2 & Hstar & Hpre).
    rewrite (silent_loop_star_nil P c tr' c2 Hloop HP Hstar) in Hpre.
    exact (is_prefix_nil_inv tr Hpre).
  - intros ->. apply obs_trace_nil.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma silent_loop_not_all_errors : forall P c,
  silent_loop P -> P c -> ~ all_traces_error segs c.
Proof.
  intros P c Hloop HP Hall. revert HP.
  induction Hall as [c Hprog Hnext IH]; intros HP.
  destruct (Hloop c HP) as (Hh & Hsvc & ms' & model' & Hacc & HP').
  destruct c as [ms model]; cbn in Hh, Hsvc, Hacc.
  apply (IH [] (mkCfg ms' model')); [|exact HP'].
  apply sstep_instr; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive to_spin : machine_state -> Model -> Prop :=
| ts_spin : forall ms model,
    ms_svc_pending ms = None ->
    mi_account_step segs ms model = MachineOk (ms, model) ->
    to_spin ms model
| ts_step : forall ms model ms' model',
    ms_svc_pending ms = None ->
    mi_account_step segs ms model = MachineOk (ms', model') ->
    to_spin ms' model' ->
    to_spin ms model.

(* [comment removed for export] *)

#[using="Type"] Lemma ts_spin_no_access : ltac2:(CDefT.buildp (gd_tbl_DivergeSim ()) "Pms,$2.Pmodel,$3.P,(4.(?.(10.&40.))(13.R2.)(14.(10.&40.)))P,(4.(5.(6.$2.))(7.Vsegs,R3.)(8.(6.$2.)(9.$2.R3.(:.$;.))))(33.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros ms model Hsvc Hstep.
  apply ts_spin; [exact Hsvc | exact (mi_account_step_no_access segs ms model ms Hstep)].
Qed.

#[using="Type"] Lemma ts_step_no_access : ltac2:(CDefT.buildp (gd_tbl_DivergeSim ()) "Pms,$2.Pmodel,$3.Pms',$2.P,(4.(?.(10.&40.))(13.R3.)(14.(10.&40.)))P,(4.(5.(6.$2.))(7.Vsegs,R4.)(8.(6.$2.)(9.$2.R2.(:.$;.))))P,(33.R3.R4.)(33.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros ms model ms' Hsvc Hstep Hspin.
  exact (ts_step ms model ms' model Hsvc
           (mi_account_step_no_access segs ms model ms' Hstep) Hspin).
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma ts_spin_no_lazy : ltac2:(CDefT.buildp (gd_tbl_DivergeSim ()) "Pms,$2.Pmodel,$3.P,(4.(?.(10.&40.))(13.R2.)(14.(10.&40.)))P,(4.(0.(<.(10.&40.)(10.&40.)))(34.R2.)(:.(<.(10.&40.)(10.&40.))))P,(4.(5.$2.)(22.Vsegs,R4.)(8.$2.R4.))(33.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros ms model Hsvc Hlazy Hstep.
  apply ts_spin; [exact Hsvc|].
  rewrite (mi_account_step_no_lazy segs ms model Hlazy).
  rewrite Hstep. reflexivity.
Qed.

#[using="Type"] Lemma ts_step_no_lazy : ltac2:(CDefT.buildp (gd_tbl_DivergeSim ()) "Pms,$2.Pmodel,$3.Pms',$2.P,(4.(?.(10.&40.))(13.R3.)(14.(10.&40.)))P,(4.(0.(<.(10.&40.)(10.&40.)))(34.R3.)(:.(<.(10.&40.)(10.&40.))))P,(4.(5.$2.)(22.Vsegs,R5.)(8.$2.R3.))P,(33.R4.R5.)(33.R7.R6.)")
(* [comment removed for export] *).
Proof.
  intros ms model ms' Hsvc Hlazy Hstep Hspin.
  apply (ts_step ms model ms' model); [exact Hsvc| |exact Hspin].
  rewrite (mi_account_step_no_lazy segs ms model Hlazy).
  rewrite Hstep. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ts_spin_of_step_j : ltac2:(CDefT.buildp (gd_tbl_DivergeSim ()) "Pms,$2.Pmodel,$3.Pw,(10.&20.)Prd,(10.&5.)Pimm,(10.&15.)Psz,$12.P,(4.(?.(10.&40.))(13.R6.)(14.(10.&40.)))P,(4.(?.(10.&20.))(15.Vsegs,(16.R7.))(17.(10.&20.)R5.))P,(4.$18.(19.R6.)$1:.)P,(4.(?.(<.$1;.$12.))(1<.R7.)(17.(<.$1;.$12.)(>.$1;.$12.(1=.R6.R5.)R4.)))P,(4.$18.(1>.R7.)$1?.)P,(4.$12.(20.&15.R7.)=)(33.R<.R;.)")
(* [comment removed for export] *).
Proof.
  intros. eapply ts_spin_no_access; [assumption|].
  eapply self_jump_step_accesses; eassumption.
Qed.

(* [comment removed for export] *)
Definition spinning (c : config) : Prop :=
  to_spin (cfg_ms c) (cfg_model c) /\ m_halted (cfg_model c) = None.

#[using="Type"] Lemma spinning_silent_loop : silent_loop spinning.
Proof.
  intros [ms model] [Hspin Hh]; cbn in Hspin, Hh; cbn.
  revert Hh.
  destruct Hspin as [ms model Hsvc Hfix | ms model ms' model' Hsvc Hacc Hspin'];
    intros Hh.
  - refine (conj Hh (conj Hsvc _)).
    exists ms, model. split; [exact Hfix|].
    split; cbn; [apply ts_spin; assumption | exact Hh].
  - refine (conj Hh (conj Hsvc _)).
    exists ms', model'. split; [exact Hacc|].
    split; cbn; [exact Hspin'|].
    rewrite (mi_account_step_halted segs ms model ms' model' Hacc). exact Hh.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Theorem spin_star_nil : ltac2:(CDefT.buildp (gd_tbl_DivergeSim ()) "Pms,$2.Pmodel,$3.Ptr,(0.$2<.)Pc',$24.P,(33.R4.R3.)P,(4.(?.(10.&40.))(11.R4.)(14.(10.&40.)))P,(30.Vsegs,(29.R6.R5.)R4.R3.)(4.(0.$2<.)R5.(:.$2<.))")
(* [comment removed for export] *).
Proof.
  intros ms model tr c' Hspin Hh Hstar.
  exact (silent_loop_star_nil spinning (mkCfg ms model) tr c'
           spinning_silent_loop (conj Hspin Hh) Hstar).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem spin_obs_iff : ltac2:(CDefT.buildp (gd_tbl_DivergeSim ()) "Pms,$2.Pmodel,$3.P,(33.R2.R1.)P,(4.(?.(10.&40.))(11.R2.)(14.(10.&40.)))Ptr,(0.$2<.)(35.(36.Vsegs,(29.R5.R4.)R1.)(4.(0.$2<.)R1.(:.$2<.)))")
(* [comment removed for export] *).
Proof.
  intros ms model Hspin Hh.
  exact (silent_loop_obs_iff spinning (mkCfg ms model)
           spinning_silent_loop (conj Hspin Hh)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem spin_no_error_run : ltac2:(CDefT.buildp (gd_tbl_DivergeSim ()) "Pms,$2.Pmodel,$3.P,(33.R2.R1.)P,(4.(?.(10.&40.))(11.R2.)(14.(10.&40.)))(37.(38.Vsegs,(29.R4.R3.)))")
(* [comment removed for export] *).
Proof.
  intros ms model Hspin Hh.
  exact (silent_loop_no_error spinning (mkCfg ms model)
           spinning_silent_loop (conj Hspin Hh)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem spin_no_sstep_error : ltac2:(CDefT.buildp (gd_tbl_DivergeSim ()) "Pms,$2.Pmodel,$3.P,(33.R2.R1.)P,(4.(?.(10.&40.))(11.R2.)(14.(10.&40.)))Pevs,(0.$2<.)(37.(2>.Vsegs,(29.R5.R4.)R1.$39.))")
(* [comment removed for export] *).
Proof.
  intros ms model Hspin Hh evs Herr.
  destruct (silent_loop_sstep spinning (mkCfg ms model) evs SError
              spinning_silent_loop (conj Hspin Hh) Herr)
    as (_ & c' & Heq & _).
  discriminate Heq.
Qed.

#[using="Type"] Theorem spin_no_unmodeled : ltac2:(CDefT.buildp (gd_tbl_DivergeSim ()) "Pms,$2.Pmodel,$3.P,(33.R2.R1.)P,(4.(?.(10.&40.))(11.R2.)(14.(10.&40.)))(37.(3:.Vsegs,(29.R4.R3.)))")
(* [comment removed for export] *).
Proof.
  intros ms model Hspin Hh.
  exact (silent_loop_no_unmodeled spinning (mkCfg ms model)
           spinning_silent_loop (conj Hspin Hh)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem spin_not_all_errors : ltac2:(CDefT.buildp (gd_tbl_DivergeSim ()) "Pms,$2.Pmodel,$3.P,(33.R2.R1.)P,(4.(?.(10.&40.))(11.R2.)(14.(10.&40.)))(37.(3;.Vsegs,(29.R4.R3.)))")
(* [comment removed for export] *).
Proof.
  intros ms model Hspin Hh.
  exact (silent_loop_not_all_errors spinning (mkCfg ms model)
           spinning_silent_loop (conj Hspin Hh)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma obs_trace_of_star : forall c0 evs c tr,
  star segs c0 evs c -> is_prefix tr evs -> obs_trace segs c0 tr.
Proof. intros c0 evs c tr Hstar Hpre. exists evs, c. auto. Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem spin_reach_obs : ltac2:(CDefT.buildp (gd_tbl_DivergeSim ()) "Pc0,$24.PP,(0.$2<.)Pms,$2.Pmodel,$3.P,(30.Vsegs,R4.R3.(29.R2.R1.))P,(33.R3.R2.)P,(4.(?.(10.&40.))(11.R3.)(14.(10.&40.)))(25.Ptr,(0.$2<.)P,(3<.$2<.R1.R7.)(36.Vsegs,R9.R2.)Ptr,(0.$2<.)Pc',$24.P,(30.Vsegs,(29.R7.R6.)R2.R1.)(4.(0.$2<.)(32.$2<.R9.R3.)R9.))")
(* [comment removed for export] *).
Proof.
  intros c0 P ms model Hstar Hspin Hh. split.
  - intros tr Hpre. exact (obs_trace_of_star c0 P _ tr Hstar Hpre).
  - intros tr c' Htail.
    rewrite (spin_star_nil ms model tr c' Hspin Hh Htail).
    apply app_nil_r.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition is_self_jump (ms : machine_state) : bool :=
  match ms_svc_pending ms with
  | Some _ => false
  | None =>
    match fetch_word segs (ms_pc ms) with
    | Some w =>
      if is_ecall w then false else
      match decode_any w with
      | Some (Jal rd imm, _) => is_x0 rd && (bv_signed imm =? 0)%Z
      | _ => false
      end
    | None => false
    end
  end.

#[using="Type"] Lemma is_self_jump_to_spin : forall ms model,
  is_self_jump ms = true -> to_spin ms model.
Proof.
  intros ms model H. unfold is_self_jump in H.
  destruct (ms_svc_pending ms) eqn:Hsvc; [discriminate|].
  destruct (fetch_word segs (ms_pc ms)) as [w|] eqn:Hfetch; [|discriminate].
  destruct (is_ecall w) eqn:Hecall; [discriminate|].
  destruct (decode_any w) as [[i sz]|] eqn:Hdecode; [|discriminate].
  destruct i; try discriminate.
  apply andb_prop in H as [Hx0 Himm].
  apply Z.eqb_eq in Himm.
  eapply ts_spin_of_step_j; eassumption.
Qed.

(* [comment removed for export] *)
Fixpoint spin_c (fuel : nat) (ms : machine_state) (model : Model) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    if is_self_jump ms then true
    else
      match ms_svc_pending ms with
      | Some _ => false
      | None =>
        match mi_account_step segs ms model with
        | MachineOk (ms', model') => spin_c fuel' ms' model'
        | _ => false
        end
      end
  end.

#[using="Type"] Lemma spin_c_to_spin : forall fuel ms model,
  spin_c fuel ms model = true -> to_spin ms model.
Proof.
  induction fuel as [|fuel IH]; intros ms model H; cbn in H;
    [discriminate|].
  destruct (is_self_jump ms) eqn:Hj;
    [exact (is_self_jump_to_spin ms model Hj)|].
  destruct (ms_svc_pending ms) eqn:Hsvc; [discriminate|].
  destruct (mi_account_step segs ms model) as [[ms' model']| |] eqn:Hacc;
    try discriminate.
  exact (ts_step ms model ms' model' Hsvc Hacc (IH ms' model' H)).
Qed.

End WithSegs.

(* [comment removed for export] *)
End WithFP1.
Ltac prove_to_spin fuel :=
  apply (spin_c_to_spin _ fuel);
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
Section WithFP2.
Context {fx : FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section TwoBranchToy.
Variable segs : list Segment.
Variable c0 : config.
Variable evs_g : list event.
Variable c_g c_r : config.
Variable T : list event.
Variable P : config -> Prop.

Hypothesis Hsplit : ltac2:(CDefT.buildp (gd_tbl_DivergeSim ()) "Pevs,(0.$2<.)Pto,$2=.P,(2>.Vsegs,Vc0,R2.R1.)(31.(25.(4.(0.$2<.)R3.Vevs_g,)(4.$2=.R2.(2?.Vc_g,)))(25.(4.(0.$2<.)R3.(:.$2<.))(4.$2=.R2.(2?.Vc_r,))))")
(* [comment removed for export] *).
Hypothesis Hstep_g : sstep segs c0 evs_g (SNext c_g).
Hypothesis Hg_obs : forall tr, obs_trace segs c_g tr <-> is_prefix tr T.
Hypothesis Hg_noerr : ~ reaches_error segs c_g.
Hypothesis Hloop : silent_loop segs P.
Hypothesis HP_r : P c_r.

#[using="c_g c_r P Hsplit Hstep_g Hg_obs Hloop HP_r"] Theorem spin_branch_toy_obs_iff : forall tr,
  obs_trace segs c0 tr <-> is_prefix tr (evs_g ++ T).
Proof.
  intro tr. split.
  - intros (tr' & cend & Hstar & Hpre).
    destruct (star_case segs c0 tr' cend Hstar)
      as [[-> _] | (evs & c2 & tr2 & Hstep & Htail & ->)].
    + apply is_prefix_nil_inv in Hpre. subst tr. apply is_prefix_nil.
    + destruct (Hsplit evs _ Hstep) as [[-> Heq] | [-> Heq]];
        injection Heq as ->.
      * (* [comment removed for export] *)
        assert (Hobs2 : obs_trace segs c_g tr2)
          by (exists tr2, cend; split; [exact Htail | apply is_prefix_refl]).
        apply Hg_obs in Hobs2.
        eapply is_prefix_trans; [exact Hpre|].
        apply is_prefix_app_mono. exact Hobs2.
      * (* [comment removed for export] *)
        rewrite (silent_loop_star_nil segs P c_r tr2 cend Hloop HP_r Htail)
          in Hpre.
        apply is_prefix_nil_inv in Hpre. subst tr. apply is_prefix_nil.
  - intro Hpre.
    destruct (proj2 (Hg_obs T) (is_prefix_refl T))
      as (tr'' & cend & Hstar & HpreT).
    exists (evs_g ++ tr''), cend. split.
    + exact (star_step segs c0 evs_g c_g tr'' cend Hstep_g Hstar).
    + eapply is_prefix_trans; [exact Hpre|].
      apply is_prefix_app_mono. exact HpreT.
Qed.

#[using="evs_g c_g c_r P Hsplit Hg_noerr Hloop HP_r"] Theorem spin_branch_toy_no_error : ~ reaches_error segs c0.
Proof.
  intros (tr & cerr & evs & Hstar & Herr).
  destruct (star_case segs c0 tr cerr Hstar)
    as [[_ ->] | (evs1 & c2 & tr2 & Hstep & Htail & _)].
  - destruct (Hsplit evs SError Herr) as [[_ Heq] | [_ Heq]]; discriminate.
  - destruct (Hsplit evs1 _ Hstep) as [[_ Heq] | [_ Heq]];
      injection Heq as ->.
    + apply Hg_noerr. exists tr2, cerr, evs. auto.
    + apply (silent_loop_no_error segs P c_r Hloop HP_r).
      exists tr2, cerr, evs. auto.
Qed.

End TwoBranchToy.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP2.
Module SelfJumpImage.

Definition spin_seg : Segment := {|
  seg_base := 0x10000;
  seg_size := 4;
  seg_perms := "r-x"%string;
  seg_bytes := ["6f000000"%pstring]
|}.
Definition spin_segs : list Segment := [spin_seg].
Definition spin_img : Image :=
  mkImage spin_segs 0x10000 (mkPhdrInfo 0x10040 56 6).

Example j_dot_decodes :
  decode_any (Z_to_bv 32 0x6f) = Some (Jal 0 (Z_to_bv 21 0), 4%Z).
Proof. div_vm_refl. Qed.

Lemma spin_img_to_spin : ltac2:(CDefT.buildp (gd_tbl_DivergeSim ()) "Psp,(10.&40.)Pbrk0,(10.&40.)Pmbase,(10.&40.)Prnd,$3=.Plim,$12.Pinp,$3>.(3?.$40.(41.$40.&10000.(42.&10040.&38.&6.)R6.R3.(43.R1.)(44.R1.)(45.R1.)(46.R1.))(47.(48.$40.)R5.R4.R6.R2.R1.))")
(* [comment removed for export] *).
Proof.
  intros sp brk0 mbase rnd lim inp.
  eapply ts_spin_of_step_j with (w := Z_to_bv 32 0x6f).
  - reflexivity.
  - div_vm_refl.
  - div_vm_refl.
  - apply j_dot_decodes.
  - div_vm_refl.
  - div_vm_refl.
Qed.

Example spin_img_obs_iff : forall lim en inp tr,
  bh_traces (run spin_img lim en inp) tr <-> tr = [].
Proof.
  intros lim [sp brk0 mbase rnd] inp tr.
  cbn [run bh_traces spin_img]. unfold init_config.
  apply spin_obs_iff.
  - apply spin_img_to_spin.
  - reflexivity.
Qed.

Example spin_img_no_error : forall lim en inp,
  ~ bh_errors (run spin_img lim en inp).
Proof.
  intros lim [sp brk0 mbase rnd] inp.
  cbn [run bh_errors spin_img]. unfold init_config.
  apply spin_no_error_run.
  - apply spin_img_to_spin.
  - reflexivity.
Qed.

Example spin_img_not_all_errors : forall lim en inp,
  ~ bh_all_errors (run spin_img lim en inp).
Proof.
  intros lim [sp brk0 mbase rnd] inp.
  cbn [run bh_all_errors spin_img]. unfold init_config.
  apply spin_not_all_errors.
  - apply spin_img_to_spin.
  - reflexivity.
Qed.

(* [comment removed for export] *)
Example spin_img_to_spin_by_execution :
  to_spin spin_segs
    (init_machine_state spin_segs 0x10000 (mkPhdrInfo 0x10040 56 6)
       (Z_to_bv 64 65536) (mkDraw (Z_to_bv 128 0) (fun _ => Z_to_bv 8 0))
       [[]] [] (Z_to_bv 64 1000) hwcap_rv64gc)
    (init_model (segments_reserved spin_segs) (Z_to_bv 64 1048576)
       (Z_to_bv 64 0x7fff7f800000) (Z_to_bv 64 65536) 0x40000000%Z
       (mkProcInput [[]] [] [] IEof (Z_to_bv 64 1000) (Z_to_bv 64 1002) []
          net_silent default_nofile (Z_to_bv 64 0) hwcap_rv64gc false Sv48)).
Proof. prove_to_spin 1%nat. Qed.

End SelfJumpImage.
