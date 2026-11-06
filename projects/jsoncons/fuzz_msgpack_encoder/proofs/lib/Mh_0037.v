(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool String PrimString. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode.
Module DivergeSim.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
(* [comment removed for export] *)
Local Ltac div_vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Section WithFP1.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma is_prefix_nil_inv {A} : forall (tr : list A),
  is_prefix tr [] -> tr = [].
Proof. destruct tr; [reflexivity | contradiction]. Qed.

Lemma is_prefix_app_mono {A} : forall (e a b : list A),
  is_prefix a b -> is_prefix (e ++ a) (e ++ b).
Proof. induction e; cbn; auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma materialize_model_accesses_nil : forall m,
  materialize_model_accesses m [] = Some m.
Proof.
  intros [fd [maps lazy materialized] io fs proc lim].
  unfold materialize_model_accesses; cbn.
  unfold materialize_accesses, newly_materialized_pages; cbn.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mi_account_step_of_accesses : forall segs ms model ms' ranges,
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
Lemma mi_account_step_no_access : forall segs ms model ms',
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' []) ->
  mi_account_step segs ms model = MachineOk (ms', model).
Proof.
  intros segs ms model ms' Hstep.
  rewrite (mi_account_step_of_accesses segs ms model ms' [] Hstep).
  rewrite materialize_model_accesses_nil. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mi_account_step_halted : forall segs ms model ms' model',
  mi_account_step segs ms model = MachineOk (ms', model') ->
  m_halted model' = m_halted model.
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
Lemma v_addi_0 : forall a : word, v_addi a 0 = a.
Proof.
  intro a. unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
Lemma self_jump_step_accesses : forall segs ms w (rd : reg) (imm : bv 21) sz,
  ms_svc_pending ms = None ->
  fetch_word segs (ms_pc ms) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (Jal rd imm, sz) ->
  is_x0 rd = true ->
  bv_signed imm = 0%Z ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms []).
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
Lemma self_jump_account_fix : forall segs ms model w (rd : reg) (imm : bv 21) sz,
  ms_svc_pending ms = None ->
  fetch_word segs (ms_pc ms) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (Jal rd imm, sz) ->
  is_x0 rd = true ->
  bv_signed imm = 0%Z ->
  mi_account_step segs ms model = MachineOk (ms, model).
Proof.
  intros. eapply mi_account_step_no_access.
  eapply self_jump_step_accesses; eassumption.
Qed.

(* [comment removed for export] *)
Lemma step_j_self : forall segs regs pc mem rom w (rd : reg) (imm : bv 21) sz,
  fetch_word segs pc = Some w ->
  is_ecall w = false ->
  decode_any w = Some (Jal rd imm, sz) ->
  is_x0 rd = true ->
  bv_signed imm = 0%Z ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs pc mem rom).
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
Definition silent_loop (P : config -> Prop) : Prop :=
  forall c, P c ->
    m_halted (cfg_model c) = None /\
    ms_svc_pending (cfg_ms c) = None /\
    exists ms' model',
      mi_account_step segs (cfg_ms c) (cfg_model c) = MachineOk (ms', model') /\
      P (mkCfg ms' model').

(* [comment removed for export] *)
Lemma silent_loop_cycle : forall (cs : list config),
  (forall c, In c cs ->
     m_halted (cfg_model c) = None /\
     ms_svc_pending (cfg_ms c) = None /\
     exists ms' model',
       mi_account_step segs (cfg_ms c) (cfg_model c) = MachineOk (ms', model') /\
       In (mkCfg ms' model') cs) ->
  silent_loop (fun c => In c cs).
Proof. intros cs H c. exact (H c). Qed.

(* [comment removed for export] *)
Lemma silent_loop_sstep : forall P c evs to,
  silent_loop P -> P c -> sstep segs c evs to ->
  evs = [] /\ exists c', to = SNext c' /\ P c'.
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
Lemma star_case : forall c tr c', star segs c tr c' ->
  (tr = [] /\ c' = c) \/
  exists evs c2 tr2,
    sstep segs c evs (SNext c2) /\ star segs c2 tr2 c' /\ tr = evs ++ tr2.
Proof.
  intros c tr c' H;
    destruct H as [c | c1 evs c2 tr2 c3 Hstep Htail];
    [left; auto | right; exists evs, c2, tr2; auto].
Qed.

(* [comment removed for export] *)
Lemma silent_loop_star : forall P, silent_loop P ->
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

Lemma silent_loop_star_nil : forall P c tr c',
  silent_loop P -> P c -> star segs c tr c' -> tr = [].
Proof.
  intros P c tr c' Hloop HP Hstar.
  exact (proj1 (silent_loop_star P Hloop c tr c' Hstar HP)).
Qed.

(* [comment removed for export] *)
Lemma silent_loop_no_error : forall P c,
  silent_loop P -> P c -> ~ reaches_error segs c.
Proof.
  intros P c Hloop HP (tr & c2 & evs & Hstar & Herr).
  destruct (silent_loop_star P Hloop c tr c2 Hstar HP) as (_ & HP2).
  destruct (silent_loop_sstep P c2 evs _ Hloop HP2 Herr)
    as (_ & c' & Heq & _).
  discriminate Heq.
Qed.

(* [comment removed for export] *)
Lemma silent_loop_no_unmodeled : forall P c,
  silent_loop P -> P c -> ~ reaches_unmodeled segs c.
Proof.
  intros P c Hloop HP.
  exact (no_error_no_unmodeled segs c (silent_loop_no_error P c Hloop HP)).
Qed.

(* [comment removed for export] *)
Lemma silent_loop_obs_iff : forall P c,
  silent_loop P -> P c -> forall tr, obs_trace segs c tr <-> tr = [].
Proof.
  intros P c Hloop HP tr. split.
  - intros (tr' & c2 & Hstar & Hpre).
    rewrite (silent_loop_star_nil P c tr' c2 Hloop HP Hstar) in Hpre.
    exact (is_prefix_nil_inv tr Hpre).
  - intros ->. apply obs_trace_nil.
Qed.

(* [comment removed for export] *)
Lemma silent_loop_not_all_errors : forall P c,
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

Lemma ts_spin_no_access : forall ms model,
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms []) ->
  to_spin ms model.
Proof.
  intros ms model Hsvc Hstep.
  apply ts_spin; [exact Hsvc | exact (mi_account_step_no_access segs ms model ms Hstep)].
Qed.

Lemma ts_step_no_access : forall ms model ms',
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' []) ->
  to_spin ms' model ->
  to_spin ms model.
Proof.
  intros ms model ms' Hsvc Hstep Hspin.
  exact (ts_step ms model ms' model Hsvc
           (mi_account_step_no_access segs ms model ms' Hstep) Hspin).
Qed.

(* [comment removed for export] *)

Lemma ts_spin_no_lazy : forall ms model,
  ms_svc_pending ms = None ->
  m_vm_lazy model = [] ->
  RiscvSemantics.step segs ms = MachineOk ms ->
  to_spin ms model.
Proof.
  intros ms model Hsvc Hlazy Hstep.
  apply ts_spin; [exact Hsvc|].
  rewrite (mi_account_step_no_lazy segs ms model Hlazy).
  rewrite Hstep. reflexivity.
Qed.

Lemma ts_step_no_lazy : forall ms model ms',
  ms_svc_pending ms = None ->
  m_vm_lazy model = [] ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  to_spin ms' model ->
  to_spin ms model.
Proof.
  intros ms model ms' Hsvc Hlazy Hstep Hspin.
  apply (ts_step ms model ms' model); [exact Hsvc| |exact Hspin].
  rewrite (mi_account_step_no_lazy segs ms model Hlazy).
  rewrite Hstep. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ts_spin_of_step_j : forall ms model w (rd : reg) (imm : bv 21) sz,
  ms_svc_pending ms = None ->
  fetch_word segs (ms_pc ms) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (Jal rd imm, sz) ->
  is_x0 rd = true ->
  bv_signed imm = 0%Z ->
  to_spin ms model.
Proof.
  intros. eapply ts_spin_no_access; [assumption|].
  eapply self_jump_step_accesses; eassumption.
Qed.

(* [comment removed for export] *)
Definition spinning (c : config) : Prop :=
  to_spin (cfg_ms c) (cfg_model c) /\ m_halted (cfg_model c) = None.

Lemma spinning_silent_loop : silent_loop spinning.
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
Theorem spin_star_nil : forall ms model tr c',
  to_spin ms model -> m_halted model = None ->
  star segs (mkCfg ms model) tr c' -> tr = [].
Proof.
  intros ms model tr c' Hspin Hh Hstar.
  exact (silent_loop_star_nil spinning (mkCfg ms model) tr c'
           spinning_silent_loop (conj Hspin Hh) Hstar).
Qed.

(* [comment removed for export] *)
Theorem spin_obs_iff : forall ms model,
  to_spin ms model -> m_halted model = None ->
  forall tr, obs_trace segs (mkCfg ms model) tr <-> tr = [].
Proof.
  intros ms model Hspin Hh.
  exact (silent_loop_obs_iff spinning (mkCfg ms model)
           spinning_silent_loop (conj Hspin Hh)).
Qed.

(* [comment removed for export] *)
Theorem spin_no_error_run : forall ms model,
  to_spin ms model -> m_halted model = None ->
  ~ reaches_error segs (mkCfg ms model).
Proof.
  intros ms model Hspin Hh.
  exact (silent_loop_no_error spinning (mkCfg ms model)
           spinning_silent_loop (conj Hspin Hh)).
Qed.

(* [comment removed for export] *)
Theorem spin_no_sstep_error : forall ms model,
  to_spin ms model -> m_halted model = None ->
  forall evs, ~ sstep segs (mkCfg ms model) evs SError.
Proof.
  intros ms model Hspin Hh evs Herr.
  destruct (silent_loop_sstep spinning (mkCfg ms model) evs SError
              spinning_silent_loop (conj Hspin Hh) Herr)
    as (_ & c' & Heq & _).
  discriminate Heq.
Qed.

Theorem spin_no_unmodeled : forall ms model,
  to_spin ms model -> m_halted model = None ->
  ~ reaches_unmodeled segs (mkCfg ms model).
Proof.
  intros ms model Hspin Hh.
  exact (silent_loop_no_unmodeled spinning (mkCfg ms model)
           spinning_silent_loop (conj Hspin Hh)).
Qed.

(* [comment removed for export] *)
Theorem spin_not_all_errors : forall ms model,
  to_spin ms model -> m_halted model = None ->
  ~ all_traces_error segs (mkCfg ms model).
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
Lemma obs_trace_of_star : forall c0 evs c tr,
  star segs c0 evs c -> is_prefix tr evs -> obs_trace segs c0 tr.
Proof. intros c0 evs c tr Hstar Hpre. exists evs, c. auto. Qed.

(* [comment removed for export] *)
Theorem spin_reach_obs : forall c0 P ms model,
  star segs c0 P (mkCfg ms model) ->
  to_spin ms model -> m_halted model = None ->
  (forall tr, is_prefix tr P -> obs_trace segs c0 tr) /\
  (forall tr c', star segs (mkCfg ms model) tr c' -> P ++ tr = P).
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

Lemma is_self_jump_to_spin : forall ms model,
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

Lemma spin_c_to_spin : forall fuel ms model,
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
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


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

Hypothesis Hsplit : forall evs to, sstep segs c0 evs to ->
  (evs = evs_g /\ to = SNext c_g) \/ (evs = [] /\ to = SNext c_r).
Hypothesis Hstep_g : sstep segs c0 evs_g (SNext c_g).
Hypothesis Hg_obs : forall tr, obs_trace segs c_g tr <-> is_prefix tr T.
Hypothesis Hg_noerr : ~ reaches_error segs c_g.
Hypothesis Hloop : silent_loop segs P.
Hypothesis HP_r : P c_r.

Theorem spin_branch_toy_obs_iff : forall tr,
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

Theorem spin_branch_toy_no_error : ~ reaches_error segs c0.
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

Lemma spin_img_to_spin : forall sp brk0 mbase (rnd : EntryDraw) lim inp,
  to_spin spin_segs
    (init_machine_state spin_segs 0x10000 (mkPhdrInfo 0x10040 56 6) sp rnd
       (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (init_model (segments_reserved spin_segs) brk0 mbase sp lim inp).
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

End DivergeSim.
From Stdlib Require ZArith NArith List Lia Bool.
Module LazyFrame.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition access_outside_range (a : word) (n : nat) (lo sz : word) : Prop :=
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z /\
  (bv_unsigned a + Z.of_nat n <= bv_unsigned lo
   \/ bv_unsigned lo + bv_unsigned sz <= bv_unsigned a)%Z.

(* [comment removed for export] *)
Definition accesses_outside_lazy
    (accs : list (word * nat)) (lazy : list (word * word)) : Prop :=
  forall a n lo sz, In (a, n) accs -> In (lo, sz) lazy ->
    access_outside_range a n lo sz.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma filter_all_false {A} : forall (f : A -> bool) (l : list A),
  (forall x, In x l -> f x = false) -> List.filter f l = [].
Proof.
  intros f l H; induction l as [|x l IH]; cbn; [reflexivity|].
  rewrite (H x (or_introl eq_refl)).
  apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

(* [comment removed for export] *)
Lemma with_vm_backing_id : forall m,
  with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m = m.
Proof.
  intros [fd [maps lazy materialized] io fs proc lim tm]. reflexivity.
Qed.

Lemma materialize_accesses_no_new : forall lazy materialized used limit accs,
  newly_materialized_pages lazy materialized accs = [] ->
  materialize_accesses lazy materialized used limit accs = Some materialized.
Proof.
  intros lazy materialized used limit accs Hnew.
  unfold materialize_accesses. rewrite Hnew. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma page_insert_in : forall p q pages,
  In p (page_insert q pages) -> p = q \/ In p pages.
Proof.
  intros p q pages H. unfold page_insert in H.
  destruct (page_mem q pages); [right; exact H|].
  destruct H as [Hqp | H]; [left; symmetry; exact Hqp | right; exact H].
Qed.

(* [comment removed for export] *)
Lemma access_pages_acc_in : forall n base pages p,
  In p (access_pages_acc base n pages) ->
  In p pages
  \/ exists k, (k < n)%nat /\ p = page_base_of (base + Z.of_nat k)%Z.
Proof.
  induction n as [|n IH]; cbn [access_pages_acc]; intros base pages p H.
  - left; exact H.
  - destruct (IH (base + 1)%Z _ p H) as [Hin | (k & Hk & ->)].
    + destruct (page_insert_in _ _ _ Hin) as [-> | Hin'].
      * right. exists 0%nat. split; [lia|]. f_equal. lia.
      * left; exact Hin'.
    + right. exists (S k). split; [lia|]. f_equal. lia.
Qed.

Lemma accesses_pages_in : forall accs pages p,
  In p (accesses_pages accs pages) ->
  In p pages
  \/ exists a n k, In (a, n) accs /\ (k < n)%nat /\
                   p = page_base_of (bv_unsigned a + Z.of_nat k)%Z.
Proof.
  induction accs as [|[a n] accs IH]; cbn [accesses_pages];
    intros pages p H.
  - left; exact H.
  - destruct (IH _ p H) as [Hin | (a' & n' & k & Hin & Hk & Hp)].
    + destruct (access_pages_acc_in n (bv_unsigned a) pages p Hin)
        as [Hp | (k & Hk & Hp)].
      * left; exact Hp.
      * right. exists a, n, k.
        split; [left; reflexivity | split; assumption].
    + right. exists a', n', k.
      split; [right; exact Hin | split; assumption].
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_outside : forall lazy (a : word) (n k : nat),
  (k < n)%nat ->
  (forall lo sz, In (lo, sz) lazy -> access_outside_range a n lo sz) ->
  page_in_ranges (page_base_of (bv_unsigned a + Z.of_nat k)) lazy = false.
Proof.
  intros lazy a n k Hk Hout.
  set (z := (bv_unsigned a + Z.of_nat k)%Z).
  apply Bool.not_true_is_false. intro Htrue.
  unfold page_in_ranges in Htrue.
  apply existsb_exists in Htrue.
  destruct Htrue as ([lo sz] & Hin & Htest).
  cbn [fst snd] in Htest.
  apply andb_true_iff in Htest. destruct Htest as [Hlo Hhi].
  apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
  destruct (Hout lo sz Hin) as [Hnw Hdisj].
  pose proof (bv_unsigned_in_range 64 a) as Ha.
  pose proof (bv_unsigned_in_range 64 lo) as Hlo_rg.
  pose proof (bv_unsigned_in_range 64 sz) as Hsz_rg.
  assert (Hz0 : (0 <= z)%Z) by (unfold z; lia).
  (* [comment removed for export] *)
  assert (Hq0 : (0 <= z / page_size)%Z)
    by (apply Z.div_pos; [exact Hz0 | unfold page_size; lia]).
  pose proof (Z.div_mod z page_size
                ltac:(unfold page_size; lia)) as Hdm.
  pose proof (Z.mod_pos_bound z page_size
                ltac:(unfold page_size; lia)) as Hmb.
  assert (Hpb : bv_unsigned (page_base_of z)
                = ((z / page_size) * page_size)%Z).
  { unfold page_base_of. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    change (bv_modulus 64) with (2 ^ 64)%Z.
    unfold page_size in *. unfold z in *. lia. }
  rewrite Hpb in Hlo, Hhi.
  (* [comment removed for export] *)
  unfold page_size in *. unfold z in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem materialize_model_accesses_disjoint : forall m accs,
  accesses_outside_lazy accs (m_vm_lazy m) ->
  materialize_model_accesses m accs = Some m.
Proof.
  intros m accs Hout.
  assert (Hnew : newly_materialized_pages
                   (m_vm_lazy m) (m_vm_materialized m) accs = []).
  { unfold newly_materialized_pages. apply filter_all_false.
    intros p Hp.
    destruct (accesses_pages_in accs [] p Hp)
      as [[] | (a & n & k & Hin & Hk & ->)].
    rewrite (page_in_ranges_outside (m_vm_lazy m) a n k Hk).
    - reflexivity.
    - intros lo sz Hlz. exact (Hout a n lo sz Hin Hlz). }
  unfold materialize_model_accesses.
  rewrite (materialize_accesses_no_new (m_vm_lazy m) (m_vm_materialized m)
             (vm_backing_used m) (vm_limit (m_vmmaps m)) accs Hnew).
  cbv iota beta.
  rewrite with_vm_backing_id. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mi_account_step_disjoint : forall segs ms model ms' ranges,
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  mi_account_step segs ms model = MachineOk (ms', model).
Proof.
  intros segs ms model ms' ranges Hstep Hout.
  rewrite (mi_account_step_of_accesses segs ms model ms' ranges Hstep).
  rewrite (materialize_model_accesses_disjoint model ranges Hout).
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ts_spin_disjoint : forall segs ms model ranges,
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  to_spin segs ms model.
Proof.
  intros segs ms model ranges Hsvc Hstep Hout.
  apply ts_spin; [exact Hsvc|].
  exact (mi_account_step_disjoint segs ms model ms ranges Hstep Hout).
Qed.

(* [comment removed for export] *)
Lemma ts_step_disjoint : forall segs ms model ms' ranges,
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  to_spin segs ms' model ->
  to_spin segs ms model.
Proof.
  intros segs ms model ms' ranges Hsvc Hstep Hout Hspin.
  exact (ts_step segs ms model ms' model Hsvc
           (mi_account_step_disjoint segs ms model ms' ranges Hstep Hout)
           Hspin).
Qed.

End LazyFrame.
From Stdlib Require ZArith List Bool Lia. From LinuxProcessSemantics.LinuxProcessSem Require BvBase State Monad Specs. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module AsanPlacement.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023.AsanCeil OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023.PlacementSearch.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_AsanPlacement () := "C46Stdlib5Lists4List2hdC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib7Mh_0037:DivergeSimAis_prefix_nil_invC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixc59OSSVerify5KrLib7Mh_0037:DivergeSimBis_prefix_app_monoC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem3Run>is_prefix_reflC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilC4ELinuxProcessSemantics?LinuxProcessSem3Run?is_prefix_transC4ELinuxProcessSemantics5Riscv7Prelude5bvmapI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00c59OSSVerify5KrLib7Mh_00379LazyFrame@filter_all_falseC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive01I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeI46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib5Lists4List2InI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeK47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2ex00C47Corelib4Init5Logic9False_indC47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic2or00C46Stdlib4Bool4Bool>andb_false_iffC4ELinuxProcessSemantics?LinuxProcessSem5State:iv_overlapC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool>negb_false_iffK47Corelib4Init5Logic2or01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib7Mh_0037=AsanPlacement:gap_weightC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203C46Stdlib5Lists4List6filterc59OSSVerify5KrLib7Mh_0037=AsanPlacement7live_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Peano2ltC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega5Tauto8GFormula02K46Stdlib9micromega5Tauto8GFormula01I47Corelib4Init5Peano2le00K47Corelib4Init5Peano2le01C47Corelib4Init5Peano6le_n_SC46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib5Arith8PeanoNat3Nat9lt_succ_rC56Stdlib5Arith8PeanoNat3Nat<succ_lt_monoK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses:impl_morphK46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega5Tauto4kind02C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z8inj_succc59OSSVerify5KrLib7Mh_0037=AsanPlacement8scan_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0037=AsanPlacement6gap_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0037=AsanPlacementAgap_weight_nonnegC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07c59OSSVerify5KrLib7Mh_0037=AsanPlacement:fg_u64_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0037=AsanPlacementDfg_region_free_falseC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=andb_true_iffC4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC59OSSVerify5KrLib7Mh_0023?PlacementSearchBpage_round_up_Z_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:mul_div_leK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z6ltb_gec59OSSVerify5KrLib7Mh_0037=AsanPlacement@live_weight_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0023?PlacementSearchGpage_round_up_Z_alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib7Mh_00238AsanCeil>bottomup_floorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeil=alloc_ceilingC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0037=AsanPlacementDfg_alloc_ceiling_valC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeilBbottomup_floor_valC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0037=AsanPlacement?scan_ok_or_stepC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indc59OSSVerify5KrLib7Mh_0037=AsanPlacementDgap_weight_filter_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0037=AsanPlacement4scanC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith6BinInt1Z4succC47Corelib5Lists7ListDef:Forall_indC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst7Inj_Z_Zc59OSSVerify5KrLib7Mh_0037=AsanPlacement8gw_sizesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0037=AsanPlacement@gap_weight_sizesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0037=AsanPlacementAfree_gap_of_slackC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeilChint_placement_ok_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeilLhint_placement_ok_b_of_floorC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00c59OSSVerify5KrLib7Mh_0037=AsanPlacement<ledger_splitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:in_app_iffC46Stdlib5Lists4List4inclC46Stdlib5Lists4List9filter_InC47Corelib4Init5Logic7and_indc59OSSVerify5KrLib7Mh_0037=AsanPlacementAledger_split_inclC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C4ELinuxProcessSemantics?LinuxProcessSem5StateAregion_free_introC59OSSVerify5KrLib7Mh_00238AsanCeil>placement_ok_bC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0037=AsanPlacement<fg_u64_rangeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseC46Stdlib6ZArith4Zdiv:Zminus_modc59OSSVerify5KrLib7Mh_0037=AsanPlacementHledger_split_window_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeil<placement_okC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib7Mh_00238AsanCeilBplacement_ok_b_iffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0023?PlacementSearch=no_higher_fitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1Z3minc59OSSVerify5KrLib7Mh_0037=AsanPlacementEnull_hint_grant_aboveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0037=AsanPlacement@page_multiple_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8min_specC56Stdlib6ZArith6BinInt1Z;le_gt_casesK46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z5min_lC56Stdlib6ZArith6BinInt1Z5min_rC46Stdlib6ZArith4Zdiv:Z_mod_multc59OSSVerify5KrLib7Mh_0037=AsanPlacementDledger_split_app_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0037=AsanPlacementAledger_split_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0037=AsanPlacementAledger_split_consC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0037=AsanPlacement@ledger_split_appC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes?RelationClasses;reflexivityI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02c59OSSVerify5KrLib7Mh_0037=AsanPlacement;kHighMemBegC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State=mmap_base_min".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fg_u64_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"] "h01zh12Hzp;2p;1p;3p;6p-1p10000p4p710R0p8p1000Gp4p70R1g0017R2p4p710R3p8P1P0p8P1p1001Qp4p710R4p8P1p1001mp4p710R5p8P1p1002Kp4p7210R6p8P1g002hR1p4p710R7p8p1003Fp6051000R8p1004Op4p710R9p8p1005Ep6051000R:P9p8P:p1006Op4p710R;p8P:p10071p4p710R<p8p1007Np4p70R=P3p8P=P0p8P=P4p8P=P9p8P=p1008<p4p710p8P=P5p8P=p1008Yp4p710p8P=P6p8P=P8p8P=p1009Tp4p710p8P=P:p8P=p100:Np4p710p8P=P7p8P=P<p8p100;Jp4p7210R<P3p8P<P0p8P<P4p8P<P5p8P<P6p8P<P7p8P<p100<6p4p710p8p100==p6051000R<P0p8P<P;p8P<p100>Dp4p710p8p100>`p4p70R<P3p8P<P0p8P<P4p8P<P5p8P<P6p8P<P7p8g00?Vj24Tg00@2j10Tg00@Wj11Tg00A5j25Tg00ARj23Tg00Anj22Tg00BIj1<Tg00Bgj2;TP2j3:Tg00CMj16Tg00D6j37Tg00Dbj28Tg00EHj29Tg00F2j2>TP1j6=Tg00FaR1g00G?R2f0R7'4g00G]#0R<#1%0<#0#0#0#0R<#1'5,37'2P1%<<R<f1R6';f29:17X01P71426%6<,36'2e97<618<6,9<1><6E=W1W0o"). Qed.

Lemma fg_alloc_ceiling_val : alloc_ceiling = 0x7fff7f800000.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"] "p;1p;2p-1p10000p4p710R0p8p1000Gp4p70R1g00HBR2p4p710R3p8P1P0p8P1p1001Qp4p710R4p8P1p1001mp4p710R5p8P1p1002Kp4p7210R6p8P1p1002hp4p710R1p8p1003Fp6051000R7p1004Op4p710R8p8p1005Ep6051000R9P8p8P9p1006Op4p710R:p8P9p10071p4p710R;p8p1007Np4p70R<P3p8P<P0p8P<P4p8P<P8p8P<p1008<p4p710p8P<P5p8P<p1008Yp4p710p8P<P6p8P<P7p8P<p1009Tp4p710p8P<P9p8P<p100:Np4p710p8P<P1p8P<P;p8p100;Jp4p7210R;P3p8P;P0p8P;P4p8P;P5p8P;P6p8P;P1p8P;p100<6p4p710p8p100==p6051000R;P0p8P;P:p8P;p100>Dp4p710p8p100>`p4p70R;P3p8P;P0p8P;P4p8P;P5p8P;P6p8P;P1p8g00@2j10Tg00@Wj16TP2j25Tg00H\j11Tf0R2#1#1p=7%12#1#1#1p=2%02#0p=4%02#0#0#0p=3g00Fag00G]#7#2#2#2#0#2#2#0#4#3#3#3#3#3#6'5o"). Qed.

Lemma fg_u64_range : forall x : word, 0 <= bv_unsigned x < 2 ^ 64.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"] "h01xp;1p;2p-1p10000p4p710R0p8p1000Gp4p70R1p10017p4p710R2p8P1P0p8P1p1001Qp4p710R3p8P1p1001mp4p710R4p8P1p1002Kp4p7210R5p8P1p1002hp4p710R1p8p1003Fp6051000R6p1004Op4p710R7p8p1005Ep6051000R8P7p8P8p1006Op4p710R9p8P8p10071p4p710R:p8p1007Np4p70R;P2p8P;P0p8P;P3p8P;P7p8P;p1008<p4p710p8P;P4p8P;p1008Yp4p710p8P;P5p8P;P6p8P;p1009Tp4p710p8P;P8p8P;p100:Np4p710p8P;P1p8P;P:p8p100;Jp4p7210R:P2p8P:P0p8P:P3p8P:P4p8P:P5p8P:P1p8P:p100<6p4p710p8p100==p6051000R:P0p8P:P9p8P:p100>Dp4p710p8p100>`p4p70R:P2p8P:P0p8P:P3p8P:P4p8P:P5p8P:P1p8g00@2j10Tg00BIj13Tg00IAj12Tg00Idj21Tg00G]#0#0#0#0#0#0#3R1#2f0,11W0o"). Qed.

(* [comment removed for export] *)
Lemma page_multiple_eq : forall z, z mod page_size = 0 -> z = z / 4096 * 4096.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"] "h01Hh12H0h22H1h32H2h42H3h57__arithh64__ffh76__sat0h88__varmaph95__with:4__x1h;4__x2h<4__x3h=1qh>1rh?2H4h@2HzhA6__sat1hB1zp;2p;1p;6p;3p;4p;7p;8p-1p10000p4p710R0p8p1000Gp4p70R1g0017R2p4p710R3p8P1P0p8P1p1001Qp4p710R4p8P1p1001mp4p710R5p8P1p1002Kp4p7210R6p8P1p1002hp4p710R1p8p1003Fp6051000R7p1004Op4p710R8p8p1005Ep6051000R9P8p8P9p1006Op4p710R:p8P9p10071p4p710R;p8p1007Np4p70R<P3p8P<P0p8P<P4p8P<P8p8P<p1008<p4p710p8P<P5p8P<p1008Yp4p710p8P<P6p8P<P7p8P<p1009Tp4p710p8P<P9p8P<p100:Np4p710p8P<P1p8P<P;p8p100;Jp4p7210R;P3p8P;P0p8P;P4p8P;P5p8P;P6p8P;P1p8P;p100<6p4p710p8p100==p6051000R;P0p8P;P:p8P;p100>Dp4p710p8p100>`p4p70R;P3p8P;P0p8P;P4p8P;P5p8P;P6p8P;P1p8g00JWj20Tg00@2j1:Tg00@Wj1gTg00K7j2ITg00Khj2Fj3STg00LIj1ZTg00Lbj22Tg00M?j26Tg00M\j28Tg00N9j2OTg00ARj24Tg00Anj2=Tg00N`j2JTg00?Vj2@Tg00OGj2MTg00Omj2HTg00PSj1_Tg00Q3j1^Tg00QSj1]Tg00R1j1\Tg00ROj1[Tg00S:j2DTg00S]j6YTg00TAj2XTg00HBj2WTg00Tcj2VTP2j3>Tg00UOj3UTg00Unj4TTg00V`j2QTg00WQj1PTg00Woj2RTg00XPj1CTg00Xoj2?Tg00YXj3NTg00ZAj39Tg00Zjj2LTg00[Vj3GTg00\6j2ETg00\Tj4fTg00]2j1eTg00]Tj2BTg00^7j3KTg00H\j1dTg00^Zj3cTg00_=j4aTg00_hj7bTg00`Lj8`Tg00FaR2f0R1g00G?R;3>p=5%:1#:p=71@;1p=1f1R6=>21p=3P2P6g00a0P1Cap=;P6g00aWR5g00b6R4P4g00bVR0P1g00c6Fbp=<f3R3P5P4P4P0f2R:P6P1G`p=Ag00cV,01#5g00G]R<#:R9#:#7#7#7#7#7#gR71I67%16%17R81037R=#1[[1F:7%57R>#ZR?1237,67/8=,33[1O3714;7R=f4R@/07RA#1RB14A7'=[1J@7147;RAf5RC/07RD,471@D;'=[1MC7f6RE/27#5\>1HE7f7RF/07RG/3F\>12F7P2f8RH/07P2g00dNRI#_RJ%^IRK%]2%\2RL%[2RMP5P4P4P01D27R51D2;RN';,<MEYRO1XM0R0P1P:g00e:RPg00eZRQ'W1V1:=>PQdAU2;6CTRQb6b8b9g00f:\>RPP1b5b>b=b4b3b2b1b0b75S61267,671067'8,361I:7%1:PB\8[1Q37%1312C7RB#1\8[1F@7167B/8D,3C\?1OC710E7RC#114C7'=\=1JE7147G1@G;'=\A1MF712H7#5\>1HH7f9RH/07/3H\>12H7P2f:/07P2%P<,R2RHg00fWR>#CRA#C,?2RG5N21?2ARA9N2H1?2>R>592592g00g6RH'LA92A>992G/LH=GIJ5GIPKP21E2:P61E23CfPLPMPMPO%e4R41B2<RO1B29R99K25%d<,B2R<5c2';,<MCAP4PM1;<N,<MP4AK295,;O,<MCACAP0PQb6b8b9X:2X;2X<2167:/83,36\P%531637,3:[[^:2^;2^<2P1P6P:f<PFf;O5b5b>b=b?b4b3b2b1b7bAb0W@XB2o"). Qed.

Lemma fg_region_free_false : forall maps lo n,
  region_free maps lo n = false ->
  exists b s, In (b, s) maps /\ iv_overlap lo n b s = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"] "p'0h01sh11bi001bh21Hh32H0h42loh51nh62b1h72b2h81eh94mapsh:3Hinh;3Hovh<2IHh=1ah>2b'h?1lh@1rhA2s'i011pi021xp;1p;2p;3p;4p;6p;5p-1g00gbR0p4p710R1p8p1000Gp4p70R2g0017R3p4p710R4p8P2P1p8P2g001QR5p4p710R6p8P2p1001mp4p710R7p8P2p1002Kp4p7210R8p8P2p1002hp4p710R2p8p1003Fp6051000R9p1004Op4p710R:p8p1005Ep6051000R;P:p8P;g006OR<p4p710R=p8P;p10071p4p710R>p8p1007Np4p70R?P4p8P?P1p8P?P6p8P?P:p8P?p1008<p4p710p8P?P7p8P?p1008Yp4p710p8P?P8p8P?P9p8P?p1009Tp4p710p8P?P;p8P?p100:Np4p710p8P?P2p8P?P>p8p100;Jp4p7210R>P4p8P>P1p8P>P6p8P>P7p8P>P8p8P>P2p8P>p100<6p4p710p8p100==p6051000R>P1p8P>P=p8P>p100>Dp4p710p8p100>`p4p70R>P4p8P>P1p8P>P6p8P>P7p8P>P8p8P>P2p8g00@2j19Tg00BIj1QTg00IAj1LTg00h9R2j2HTg00Q3j1PTg00hYj34Tg00iSj43Tg00j3R>j20Tg00PSj1FTP5j6ETg00jMj2OTg00[Vj3?Tg00jlj2CTg00kJR5j2=Tg00kdj2NTg00lFj48Tg00m?j1;Tg00m]j1KTP3j37TP0j36Tg00HBj2JTg00n?j3ITg00nYj4ATg00o4j4>Tg00oNj3GTP<j5MTg00AnR<j2DTg00e:R0f0R3g00ohR837p=1f3R7f2R6f1R1P3C8g00eZR4570p=:A6761/D3p=@f6R=f5R?f4R;36P7P6P1P3C8=704'Dp=2P;P7P6P1C3=??3p=5A7034p=<A?61396;7p=Bg00G]#9#9#9#9#9#9#Q#LR4/H4R9#PR:P9A4613#1P9P4P4P1P3C3R@P?P;P7P1P3C:RAC@X04,04X14,04[^54^44RBX9:%F9RC?413#1P0A4C61P0p-0P3g010Hg00f:RDn0110000020000X80g010dP8P3EEPDP9P@PCP?P;P1P3F2X04,04X14,04/O3b3W2X54X44P2P4P4A?9;7?413#1P9P@f7R2=?9=PAC@X04,04X14,04[^54^44\B^?:P3P9P4P4P?P;P7E5?413#1P<1C13#1%16RA%11RC'=[RD%13,=C1C61#1RC[%17/=A\C1N13P1n2001000000120000000X70X60PD^70^60P3P7P6P2P=C8#;RDA4?76RCP1O3%1D%1C'=P5P;P7f8R5P2C8#;#1A4=;7#1P9P@P9P4P4f;RCf:RDf9RAE5P2P=P1P3F2X04,04X14,04P3P?P;PAP5C8#;#1P<%;3#1%<1[R8%<3%;1#1RE[%<6\E%K3P1n2001000000120000000X10P8^10P3P2P=PCPDC8R0P1O2%<0P4P9P@P9P4P4f>R0f=R8f<REE5PDPAP1P3F2X04,04X14RFPEP4P9P4P4P8P3C3P9P4P4P8PEPCE5PAP5P8P3F2X04PCP9P4P4PEPCC3RGP9PGPDDBP5P2PEPCC:A79GGA69GD1J9G3IP3CAC>C>b2b3W2P3O1A42?;#1P2P=P?P3O3P9P@PDP5P2P1P3F2X04,04X14,04P>P4P9P@PCPAP5P1P3F2X04,04X14104FP3P9P@P8PCPDP1P3F2X04,04P>P4P9P4P4P6P3C3P0PEPCP6P3F2X04P9P@P9P4P4fBR6fARCf@REE5P0P8P1P3F2X04,04X14,04P3P9P4P4P;P3C3PEP0P8P;P3F2P<P4P4P?P1C3=69Cf?P0P?P1C:P9P@P9P4P4fFR0fER<fDR8E5P6PCP1P3F2X04,04X14,04P3P4P4P2P7C3fCR7569P6PCP5P;C:P4P9P@P9P4P4fIfHR@fGR;E5P<P8P1P3F2X04,04X14PAP4P9P4P4PDP3C3P9P4P4P@P;P0E5P8P7PDP3F2X04P?P9P4P4PAP?C3RDP9P4P4P;P0C3R0P<DBP7P6PAP?C:A790DA69D<;G1P3CAC>C>W;W:P1P3O2n2001000000121000000W3XA4P1P3O2n2001000000121102000W3X>4P1P3O2n2001000000121102000b8W2P3O1n200100000021100011000b2b3W2X54X44X<BX@:X04X14P1P3O2n2001101010121100100X=9P3DMW9o"). Qed.

(* [comment removed for export] *)
Fixpoint gap_weight (nZ : Z) (l : list (word * word)) : Z :=
  match l with
  | [] => 0
  | (_, s) :: r => bv_unsigned s + nZ + 4095 + gap_weight nZ r
  end.

Lemma gap_weight_app : forall nZ l1 l2,
  gap_weight nZ (l1 ++ l2) = gap_weight nZ l1 + gap_weight nZ l2.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"] "p'0h02l2h12l1h24__x1h34__x2h44__x3h54__x4h62IHh77__arithh84__ffh98__varmaph:5__with;1ah<1bi001bh=1lh>2nZh?1sh@1zi011pp;1p;2p;3p;4p;7p;6p;5p-1p10000p4p710R0p8p1000Gp4p70R1g0017R2p4p710R3p8P1P0p8P1p1001Qp4p710R4p8P1p1001mp4p710R5p8P1p1002Kp4p7210R6p8P1g002hR1p4p710R7p8p1003Fp6051000R8p1004Op4p710R9p8p1005Ep6051000R:P9p8P:g006OR;p4p710R<p8P:g0071R=p4p710R>p8p1007Np4p70R?P3p8P?P0p8P?P4p8P?P9p8P?p1008<p4p710p8P?P5p8P?p1008Yp4p710p8P?P6p8P?P8p8P?p1009Tp4p710p8P?P:p8P?p100:Np4p710p8P?P7p8P?P>p8p100;Jp4p7210R>P3p8P>P0p8P>P4p8P>P5p8P>P6p8P>P7p8P>p100<6p4p710p8p100==p6051000R>P0p8P>P<p8P>p100>Dp4p710p8p100>`p4p70R>P3p8P>P0p8P>P4p8P>P5p8P>P6p8P>P7p8g00@2j14Tg00BIj1RTg00IAj1JTg00h9R7j2CTg00Q3j1?TP=j35Tg011@j20Tg00M\j21Tg00HBj29Tg00PSj1;Tg00[Vj3=Tg00EHj2@Tg00H\j18Tg00@Wj1QTg00\6j2<Tg00QSj1PTg00\Tj4:Tg00R1j1OTg00ROj1NTg00]Tj27Tg00S:j2ITg00_=j4HTg00_hj7ETg00TAj2FTg00Tcj2GTP2j3>Tg00UOj3DTg00Unj4KTP1j6BTg00iSj4LTP;j5MTg00^Zj3ATg00FaR;f2R1f1R2f0R='13>p=2%8=#8p=6AA;2=p=3g00G]R>#4R6#4R5#4#4#4#4#RR4#JR0/C0R3#?R<P3f3R?A532=R:'010?210?=32^0<X1<g00G?R8101=R9'1,9;%;3R@=53=,01101@;29eX0<P7P0P0f5R7/0:1072107=32^0<f6R7A=3?1R9=53='01079107=32^0<[^=<P=f8R7/0:1072107=32^0<P;f9R7/01107=R:'1f4R9,@4R4f:R@'1%8>RA#6#6#6#6#6#QRB'1RC/1=10@?RD,1C10@2RC32X@;g00dNRE#;%?EP;P;1<;9P1%P;C:P21<;?C:%O;%N;REg00aWg00b6RFPFg00bVRFP;17;>17;6'31I;B'3R617;ARA17;5R5'3'3g00a0136A/35CHg00c6FE1FEFP=P1g00e:RFg00eZRE'91G=1=>FEdAD;82CKb8b9b:X2;X3;X4;X5;11=2/1BRB111?'111B1;2?^2;^3;^4;^5;P=PCPDP@P4O4b7A531=,07P2P=O1EBP0P0P9P?CL==31R1=53=,071071;2:eX0<W6X1<X?0X<0P2P=O2n2001101010121100100X;3P=DMW1X>;o"). Qed.

Lemma gap_weight_nonneg : forall nZ l, 0 <= nZ -> 0 <= gap_weight nZ l.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"] "p'0h01lh11Hh23HnZh32IHh47__arithh54__ffh68__varmaph75__with84__x1h94__x2h:4__x3h;2H0h<1ah=1bi001bh>2nZh?1si011pp;1p;2p;3p;4p;5p;7p;8p-1p10000p4p710R0p8p1000Gp4p70R1g00HBR2p4p710R3p8P1P0p8P1p1001Qp4p710R4p8P1p1001mp4p710R5p8P1p1002Kp4p7210R6p8P1p1002hp4p710R1p8p1003Fp6051000R7p1004Op4p710R8p8p1005Ep6051000R9P8p8P9g006OR:p4p710R;p8P9p10071p4p710R<p8p1007Np4p70R=P3p8P=P0p8P=P4p8P=P8p8P=p1008<p4p710p8P=P5p8P=p1008Yp4p710p8P=P6p8P=P7p8P=p1009Tp4p710p8P=P9p8P=p100:Np4p710p8P=P1p8P=P<p8p100;Jp4p7210R<P3p8P<P0p8P<P4p8P<P5p8P<P6p8P<P1p8P<p100<6p4p710p8p100==p6051000R<P0p8P<P;p8P<p100>Dp4p710p8p100>`p4p70R<P3p8P<P0p8P<P4p8P<P5p8P<P6p8P<P1p8g00@2j14Tg00BIj1]Tg00IAj1PTg00h9R1j2ITg00Q3j1ETg011@j21Tg00PSj1ATg00QSj1MTg00R1j1JTg00ROj1HTg00S:j2DTg00TAj2ZTP2j2VTg00Tcj2UTg0017j3TTg00UOj3STg00Unj4RTg00?Vj2CTg00[Vj3=Tg00Idj2OTg00EHj22Tg00CMj1NTg00ARj2;Tg00AnR2j2LTg00M\j23Tg00H\j1:Tg00@Wj1KTg00XPj19Tg00Xoj28Tg00ZAj3<Tg00Zjj2GTg00\6j2BTg00\Tj4QTg00]Tj2>Tg00]2j1FTg00^Zj3?Tg00iSj4\TP:j5[Tg00_=j4YTg00_hj7WTg00`Lj8XTg00G?R:f0R<'Cp=0g00FaR6f1R5g012EP<CYp=6P5g00aWR4g00b6R0P0g00bVR3P<g00c6FWp=7%:<#:p=5f3R;P4P0P0P3f2R4P5P<GXp=@g00G]R=#4R9#4#4#4#4#4#]R7#PR8/I8R>#ER?P>%04R@11;5#0[X0?%05g00dNRA#ARB%EARC%M6%J6RD%H6RE1D6:RF/6F'71ZE3R3P<P4g00e:RGg00eZRH'V1U<4=TGHdAS6:5CRRHb5b6b71C::P<b4%A>,14#0eW2P1P8P8f4R1#0R:f5RG/15#0[%0Gf6RIA=>;4'1#0[[^0?P<f7RJ#0f8RK/15#0[%0K1O7;127;RL#0%N7RM,;L'LP4P5O1f:RL/1;#0P2127GR2#01;2M127If<RI'3%:=R2#5#5#5#5#5#KRN'311IG'3#0P5127J#0127K/;Mg00fWRM#9RK#9RI#9,86186I186K186M5<65<65<6g00g6'G==ABPCP61B64P51B6;CQPDPE1>6=R=,6F,7E%F0R0PE1>69R9,6F,7EP0PE1>62R2,6F,7EP0A?6=91D6N5?6=?62,6F,7EC@C@C@P3PHb5b6b7X86X96X:6%0<13;1/3N/3G#0\:\@[^86^96^:6P<f@R@f9R:'1P@127LP4PJPGO6b4W;W1P5P<O2n2001000000121000000b3b1P8P8P1P;C\==>4,1:#0eW2W3X0?X?8X=8P5P<O2n2001101000121100100X<>P<D[W0X>6o"). Qed.

(* [comment removed for export] *)
Definition live_at (c : Z) (p : word * word) : bool :=
  c <? bv_unsigned (fst p) + bv_unsigned (snd p).

Lemma gap_weight_filter_le : forall nZ f l, 0 <= nZ ->
  gap_weight nZ (List.filter f l) <= gap_weight nZ l.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"] "p'0h04__x1h14__x2h24__x3h34__x4h41lh51Hh67__arithh74__ffh88__varmaph95__with:2H0h;3HnZh<2IHh=1ah>1bi001bh?2b0h@1fhA2nZhB1si011pp;1p;2p;3p;4p;5p;7p;8p-1p10000p4p710R0p8p1000Gp4p70R1g00HBR2p4p710R3p8P1P0p8P1p1001Qp4p710R4p8P1p1001mp4p710R5p8P1p1002Kp4p7210R6p8P1p1002hp4p710R1p8p1003Fp6051000R7p1004Op4p710R8p8p1005Ep6051000R9P8p8P9g006OR:p4p710R;p8P9p10071p4p710R<p8p1007Np4p70R=P3p8P=P0p8P=P4p8P=P8p8P=p1008<p4p710p8P=P5p8P=p1008Yp4p710p8P=P6p8P=P7p8P=p1009Tp4p710p8P=P9p8P=p100:Np4p710p8P=P1p8P=P<p8p100;Jp4p7210R<P3p8P<P0p8P<P4p8P<P5p8P<P6p8P<P1p8P<p100<6p4p710p8p100==p6051000R<P0p8P<P;p8P<g012lR<p4p710p8p100>`p4p70R;P3p8P;P0p8P;P4p8P;P5p8P;P6p8P;P1p8g00@2j19Tg00BIj1aTg00IAj1RTg00h9R1j2MTg00Q3j1ITP<j33Tg011@j21Tg00PSj1ETg00QSj1LTg00R1j1KTg00ROj1JTg00S:j2HTg00TAj2ZTP2j2XTg00Tcj2WTg0017j3VTg00UOj3UTg00Unj4TTg00?Vj25Tg00[Vj3<Tg00Idj2QTg00EHj2:Tg00CMj1PTg00ARj2ATg00AnR2j2OTg00iSj4=Tg00M\j20Tg00H\j1BTg00@Wj1NTg00\6j2FTg00\Tj4GTg00]Tj2@Tg00]2j1STg00XPj1CTg00Xoj2?Tg00ZAj3DTg00Zjj2_TP:j5^Tg00_=j4]Tg00_hj7\Tg00^Zj3[Tg00`Lj8YTg00G?R:f0R<'5p=2f2R;f1R6'1/5<p=4g00FaR5P6g012EP<C]p=8P6g00aWR4g00b6R0P0g00bVR3P<g00c6F\p=7%B<#Bp=;A[56<p=6f3R=P4P0P0P3P;P6P<GYp=>A3;6<,1=p=`g00G]R4#9R9#9R7#9#9#9#9#aR8#RR>/M>R?g00e:R@[%I?RAP?%2=RBf4RCA3?=611C634[X4A%2;g00dNRD#ERE%IDRF%L5RG%K5RH%J5RI1H5:RJ/8J'71ZI3R3P<P;g00eZRK,X@1W<;=V@KdAU5:6CTRKb7b8b915::P<b6%E?R:93?;11=:54=eW;P1P>P>f5R1#2f6R:A3?1611:634[%2:f7RLA<?=;RM93?:11LM34[[^4AP<f8RM#2f9RNA3?M611N634[%2N1Q8=1:8=RO#2%P8RP,AO'OP;P6O1f;ROf:RQ=3?=11O=34POP>P>P:P1C=O1P@P@f>RRP@PAP<P>P>PMPLC=f=R@=3?:RS5<?PSn01000000200001:8L/0R%B4RT#;#;#;#;#;#NRU'0RV11R:'0RW34P<P21:8:RX#2RY1AXPRZ11RSRS,0V/5WP;1:8M#2RV1:8N/APRPPEPFP5P51F5CP;PGCGP61F5=CGRGPHPI1@5TRT1@57R7'8,7I%S0R01@54R41@59R9'61H5URR'6R[/6T16[7'8,7IC>P3PKb7b8b9X05X15X25X3515;=106;/0UR[/0=10[C'5[^05^15^25^35P<fBR[/1QR\P[P?fAPQC`R]P[1:8OROP:O5b6W:W5P6P<O2n2001000000121000000P>P>PLP:C=f<=3?1RL5<?10X@/0U11@1'0RX54@eP2PYPZ15SWP;g00fWRS#CRW#CRZ#C,?51?5Z1?5W1?5S5D55D55D5g00g6'_=<DEPFPGPHPI18J9,7IP0PI18JT,7IP0PI1847,7IP0169T/6R/67,84,7IC>C>C>P3PKb7b8b9X05X15X25X35%2615;110C1/0U/0:,5=[\B[^05^15^25^35P<P\P[POP]P;PMP:O7b6X:PX5VP6P<O2n2001000000121000000A4@LXen0110000020101b?b<b5P>P>PCP=C==<?;R;93?N11Q;54QeW;W<X4AXB>X>>P6P<O2n2001101000121100100X=?P<D^W4W@XA5o"). Qed.

(* [comment removed for export] *)
Lemma live_weight_step : forall nZ l c c' b s,
  0 <= nZ -> c <= c' ->
  In (b, s) l -> live_at c (b, s) = true -> live_at c' (b, s) = false ->
  gap_weight nZ (List.filter (live_at c') l) + (bv_unsigned s + nZ + 4095)
  <= gap_weight nZ (List.filter (live_at c) l)
  /\ (length (List.filter (live_at c') l) < length (List.filter (live_at c) l))%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"] "p'0h04__x1h14__x2h22IHh31Hh44__x3h54__x4h67__arithh74__ffh88__varmaph95__with:4cstrh;5cstr0h<2H0h=1ah>2H2h?1pi001ph@2E'hA1mhB1nhC3IH0hD1lhE3Hl0hF4__x5hG4Hle0hH1bi011bhI2HlhJ2b1hK1xhL2H1hM3HinhN1yhO5HdeadhP5HlivehQ2HwhR4__p1hS4__x6hT2b0hU1ehV2s0hW4Hcc'hX3HeqhY3HlehZ5Hmonoh[3HnZh\3IHlh]1ch^2c'h_2nZh`1sp%0p%1p&0p;1p;2p;4p;3p;6p;5p;7p;<p;8p-1g00gbR0p4p710R1p8p1000Gp4p70R2g0017R3p4p710R4p8P2P1p8P2p1001Qp4p710R5p8P2g002KR6p4p710R7p8P2P6p4p7210R8p8P2g002hR2p4p710R9p8p1003Fp6051000R:p1004Op4p710R;p8p1005Ep6051000R<P;p8P<g006OR=p4p710R>p8P<p10071p4p710R?p8p1007Np4p70R@P4p8P@P1p8P@P5p8P@P;p8P@p1008<p4p710p8P@P7p8P@p1008Yp4p710p8P@P8p8P@P:p8P@p1009Tp4p710p8P@P<p8P@p100:Np4p710p8P@P9p8P@P?p8p100;Jp4p7210R?P4p8P?P1p8P?P5p8P?P7p8P?P8p8P?P9p8P?p100<6p4p710p8p100==p6051000R?P1p8P?P>p8P?g012lR?p4p710p8p100>`p4p70R>P4p8P>P1p8P>P5p8P>P7p8P>P8p8P>P9p8g00@2j1^Tg00BIk10ZTg00IAk10RTg00h9S00k20DTg00Q3k109Tg00?VR9j24Tg00iSj46TP0j3JTg013Gj19j2ETP?j30Tg00H\j1eTg00@Wk107Tg00PSk105Tg00EHj28Tg00jMk20PTg00[Vj3=Tg014Ij2@Tg00ARR?j25Tg014fk20FTg00M\j21Tg015Fj3zTg015ck300Tg011@j22Tg016@j23Tg016`R0j17Tg00AnR>j2:Tg017@R8j2;Tg017Xj1]Tg0186j6cTg018_j4OTg019Fj1NTg00XPR7j1ATg00Xoj2kTg00ZAj3tTg00Zjk20XTg00QSk10WTg00\6j2gTg00R1k10VTg00ROk10UTg00]2k10TTg019kk50QTg00]Tk201Tg01:Ok50OTg00TAk20NTg00HBj2rTg00Tck20MTg00UOk30JTg00Unk40ITg01;3R5j2CTg00S:j2qTg01;Mk10GTg00nYj4VTg00Idj2}Tg00CMk10ETP3j3LTg01;gk30CTg01<Cj4hTP=j5{TP6j6|Tg01<nk20HTP2j6iTg01=Tk20>Tg01>=k60LTg01>ak70=Tg01?El<~Tg01?jk60<Tg00\Tk40;Tg00^Zk30STg00_=j4sTg00_hj7jTg01@Tk60:Tg00`Lk806Tg01A8m<0YTg00G?R2f0R6'4p=<g00e:R=f1R3/E6g00eZR13Lp=?1E36g00ohS015L=p=I%e6#ep=lf3R4f2R@'8/13/16p=[%93=0@6p=Z134@1336';p=Df5R<f4R:'2/1412@3'4/:6p=Hf7R;f6RA'211<:/14'112@3'4/:6p=XAL=61p=Q18@3/16p=pQ019L=6p=\11@3/16p=>11@3/46p=F1;36,:@p=w1336,;@p=m13@3/;6p>08g00FaRB/r6p=Gg01A]RCPBP8P0P?g01B<P<P:P4P@P3P6M<~p=dP<P:P4P@%]3P6J0<p=M1336#7p=KPBP@P3P6H0;p=Y201B6p=bB0SB36p=BPBP3g01B^P6Csp=`P3g00aWR?g00b6R8P8g00bVRDP6g00c6REFjp>04P3P?P8P8g01CERFP6PEFjp>03P@P?P8P8P3P6J0:p>02P:P?P8P8PDP4P@P3P?P8P8PDP6PEFjL06p=WP4P?P8P8PDP@P3P6L06p=T12;A12<:'4134@1336'C':p=PP@P?P8P8PDPBP3g012ERGP6CsPEFjp=R12@3/46p=v134@1336'Cp=u14@3/:6p=nPCPBP5P0P9g01CeP<P:P4P@P3P6M<~p=aA0@36,24p=SPBP3PGP6Csp=_1136,4@p=UP=P1P4P@P3P6Eip=o1336,C@p=y12@3,44/:6p=fPCPCPBPBP7P0P0P4g01DGP@P3P6N<0Yp=x1C36,:@p>0B1236,4@p>0A12:4/1@/43/:6p>0@1136,1@p>0?12:411@3/16'1p>0Kg00G]R0#^R7#^S02#^#^#^#^$0ZRG$0RR900D9R5$09RE%<<14:4P5P9P9P:P4C6RH=J56P9P9P<P:C6RI,?;P9P9PAP<C6RJ,I;f;RKf8RL#9RM=054RNPGPAPK%e0RO#eRP#e#l#l#l#l$07RQC[PKf9RR=Z54RSP5PNP5PSCDEH[[[XDEP9P9P4P@C6RS&055RN5J51?AH1IAIf:RTAZ5;NRU18G<RVPTPQPTA05MNRMP5PUP5PMCDGX00P@WOWPWMQ00P9P9AJ5J6P9P9P;PAC6RM,?RP9P9PLP;C6RU,IRf=RWAZ5T4RX18GLS03PWPQPW%9KRY=054RZP5PXP5PZCDGX[[[A=5@3RZ9J5M1?TUP9P9PRPLC6RX,ITf>R[A=5<:R\905YRYPGPRP[PQC[P[f<R]=Z5\R\P5PYP5P\CDEH[[[[^DEP6AJ5X6P9P9PTPRC6S04,?]P9P9PKPTC6S05,I]f@R\AZ5W4RY18GKS06P\PQP\AZ5[4R^P5PYP5P^CDGX[[[Q04A=5S3S075J5Q05,?WP9P9P]PKC6S08,IWQ00P9P91?\6fBRS/?3[P6fCR^P9P9P3P6C6'?P>1@36#Q15@3RY[R_15361@@3#QR`[Ra154@\`20F36R`P3n2001000000120000000XABXBBP_^AB^BBP6fERb18G@Rc9pG4RdP3O315bdP>P_Pa1@4@#Q\YP`P6n2001000000120000000XABXBBPa^AB^BBP6fHRa18G:,1VP9P9fFRVPbC6S09=J5WR`fIRYfGR_,8GS0:18GVRd'1Re'@#QRf18GaRgQ0:'1,@Y#\RhfMRifKRjAz996B00996,8G5pGRk'@X?5Rl=05\Rm'2A>giQS0;fLRn/@kX?5=05\Ro,2i3FRp135mRm135oRo3w[[[%7m%7o'5,:p\h\f\`RfP`18GbRh,1dRp,@a#QRo1@ae#\PnfJRe/@kX?5Rmf?Rq505RrQ0:PnPQPnA05lqRl135rRr?m5lGX[[P`p-0S0<Q0<P3\3WNWKS0=PoQ0=1@_p#\Rp1@akX?5=05WRl,2eA>heQRh1@YkX?5Rs=05WRt,2e3FRu135lRl#7Rv135tRt#7Rw'5Rx':RyO2RzO2P`PoPjA05s[RsPdPjPQPjA05m[Rm135mRm:085sGX\pPoPzPoPp1;ltRo,:uPpPyPpPuPoPuPx%]uPlPv%GvPtPw%GwEdEcEMEMEMP]COPf%Nm%7m#<%Nr%7r#<P9P9PYPaC6=J5\RrP4P6P[O2W=18GeS0>18GYS0?'1,@j#\fORm1@ikX?5=05SRfQ0>?>mQS0@PmfNRw/@kX?5=05SRk1K5f1K5k'5EHRk[^=rP9P9PePYC6S0AfARr5J5RfP3P6P[O2W=Pk^=fg00dNRkg00fWRt#ARv#ARl#A,kB1kBl1kBv1kBt5tB5tB5tBg00g6+0X&05kRv3=S0B&09kRk&0WBRl1gB<S0C7Y@1gB:Ru1gBA7Y47Y3&0VBRx&0UBRo%e7#bRp%b7R7%bORy'BS0D'`-04o&0T8RzPo%^O#b%bP'BRP,`p-03oPoP?P8P8PFI0Q602oPzPo201B0RO/`P-03oPoP?P8P8PFI0O602oPzPoQ0D,`ODWCTCT20NoDRFP6P@1r=120M6@#QdB0JB23H0IR1b7b8b9X0BX1BX4BX5BXFBXSB113@RP,5411<A,@:#\11A;,@@#Q11:<S0E,54[[[^0B^1B^4B^5B^FB^SBP618GjS0F18GnS0GPi18GTRsQ06PwP;PqP\O9b6b2b2b;b:bCO3b<b3b<P9P9P@P3C6Rd9z99B0099d,8G5pG,@b#Qe1?bdeW3XN9XK9P3P6O2n2001100000121101101X?51?q61?r3[^?5P5P^%9\S0H=056RdP^%9rS0I=056R`P5PdP5P`GPXDE1422R`1CttPvPkPlPx1qB2R2=Ro2PFP1b7b8b9P`P6b6&0GtCVPS%9qS0J=05NRtPSQ0H=05NRNP5PtP5PNGPeQ00P9P9Pb%9SS0K=056RNPb%9^S0L=056RtP5PNP5PtGPPVQ0L=05ZRtPVfDRN#9S0M=05ZRZP5PtP5PZGP[^DEP6Pa%9bS0N=056RZPa%9VRt=056R`P5PZP5P`GP1}G@%<c&0EGR`,5c':1E_HP=1r=6S0O1EaI=L=6P=1EeM=L=6PwP=PEP3%9jS0P=05ARI9=5URHPIn0100000020000RcPwP=PE1EnU%9nS0Q=05ARZ9=5US0RPZn0100000020000RdP5PcP5PdGP]@P31EYJS0S#QPwPHPwP=PEP6Q0RPZn0100000020000RJP5PHP5PJGPXH=P>%9eS0T=05<S0UQ0P=05<S0V,2i5viP5Q0UP5Q0VCuPGP;PwPQC[RJ12wIS0W'112wZS0X,1J135IS0Y#A135ZS0Z#A'C3nP:Q0Q=05;S0[,2mS0\%9iS0]=05;RZ,2mS0^'4S0_P5Q0]=05LS0`P5%9wS0a=05LS0bCufQRI=>sQRsQ0a=05RRJ,2I%9mS0c=05RRH,2I,1s3F135JRJ#A135HRH#A'C1CJHS0d%7JRs%7HRd'4RcPJPs%GsPHPd%GdEaP6COPcQ0c=05TS0e,35Rc#N%7cRd#<%9IS0f=05K,35Rs#N%7s#<P>18GWRs#<15s`18G[RsfUR{;>QR|P{P5fRR}#9S0gPWCSP{P5fSR~#9S0hPWCS,1|3FPT18GqS0i#<18G\S0j/5`PvPkAYu@lS0k1gB47Y3S0lPxPoQ02#bRu9RoyPzPo1BO71qBQS02'BS0m/ByS0nQ0m/Bu'_DWPFP1b7b8b9X0BX1BX4BX5B14@411PQS0o/14S0pQ0o;U:[^0B^1B^4B^5BP6fYRPP5fWS0q#9S0rPrCSPPP5fVR|#9S0sPrCSPP18GSS0tPRO5b6W>W3P3P6O2n2001000000121000000b;b:b>B0CJH6CVWLW<P3P6O2n2001000010121000000PiQ0U9=5MRHPiQ0V9=5MRJP5PHP5PJGPe1EjMRJPKPMP6O2CoW@Q0S#\PJP=P=Q0\PmP=PEP6A=5XZPZn0100000020000RJQ0[,35S0[?y5JCfP6P>Q0WQ0X'4S0XQ0YQ0Z'CS0ZQ0\Q03/1mQ0^7>QQ0[135ZS0^#A'C3nP<fPRZQ0`Q0b,2Z3vS0`Q0dQ0e,2}S0eQ06?>}Q%9ZS06=05TRJ,2}S0b3U135JRJ#AS0\,CcS031CcJS0S%7JRM,4dS0VPcPd%GdS0UPJPM%GMS0uEaS0vP6COS0wQ0VQ06=05K,35RH#NS0x%7H#<S0yQ0g=05],35RH#NS0z%7H#<S0{P>%<sS0|15s`S0}Q0h=05[S0~,2|S10Q0i?>|QfTRs=Z5[S11,2|S123UPKQ0j#<S1318GrS14/5`S15Q0BPkQ0lPxPoARo27PzPoARoOuS16PzPoARo2yS17PzPoQ0DQ02'BS0D/BuS18,_ODWCTCTPFP1b7b8b9X0BX1BX4BX5B%<3143:%<:S19Q0E/1QS0E=U4A[[[^0B^1B^4B^5BP6fZRHfX#9S1:=05SS1;'2S1<PH18G^S1=Q0r=05SS1>,2HS1?P@PRPsO7b6W>W3P3P6O2n2001000000121000000b;b:b>Q03&070R0,1MS03,4dPcPdQ0UQ0\Q031160XKBS03PJPMQ0uCxEaQ0wQ0VQ0xQ0yQ0zQ0{P>Q0|Q0}Q0~,K5RMQ11,K5RJ;U0PKQ13Q15PvPk1gB@?Y3lS11PxPoARoO7RdPzPo1qB0,B7S0~,_ODWPFP1b7b8b9X0BX1B1463Rc11@0S0u,43[^0B^1BP6Q1;,K5Q1>,K5P;O3S1>b6W>W3P3P6O2n2001000000121000000b;b:b>ChCVWLW<P3P6O2n2001000010121000000Q0WPwQ0RQ0YQ0R7y5CfeP>Q0XQ0ZQ0_Q0[Q0^40BP<Q0`Q0dQ0eQ0b'4Q0SQ0wQ0VQ0xQ0yQ0zQ0{P>Q0|Q0}Q10Q12'4PKQ13Q15PvPkQ11PxPoPdPzPdCTPFP1b7b8b9X0BX1BRd143@\c^0B^1BRcP6Q1<Q1?PRO3b6W>W3P3P6O2n2001000000120000000b;b:b>Q0SQ0VQ0vQ0wQ0VQ0xQ0yQ0zQ0{P>Q0|Q0}14MJPKQ13Q15PdPcQ1>b6W>W3P3P6O2n2001000000121000000b;b:b>ChCVWLW<P3P6O2n2001000000121000000Q0XQ0Z':en0110101020101bJW@n0110101020101P6O1b@bJb3PYQ07905tRcPY%9_RdQ07505RJP5PcP5PJGPeW\XDEXN9XK9P3P6O2n2001100010121101101X=5P<D{PSQ0J=05<RJPSQ0H=05<RcP5PJP5PcGPg00kJP9P9PqP[C6S0H9L5UQ0H=J5APNQ0IA=5X;RU505RcQ0iPNPQPNQ0K=05URUP5PcP5PUCDGXP:P9P9P\PqC6S0i9L5XP5P9Q00P9P9P9P6P6n2001100000120101101XU5Q04P9P9PrP\C6S04P6E|AL9R\P5P9Q00P9P9P9P6P3n2001100000120101101XU5Q05P9P9PSPrC6S05P3E|AL9KSAL9]^S00P9PNAL9WNPeP9P9P3P[C6==5WRX905dRUPhPe%9aRc=05XRXP5PUP5PXCDEH[XT9Q00P9PNPeP9P9PVP6C6==5WRX905dRUPhPeA05cXRXP5PUP5PXCDEHXV9PeP=PEQ09,E_Q09A05dWRX5=5S0IPXn0100000020000S0JPhPeP=PEP6Q09A05cWRU5=5RJPUn0100000020000RMP5Q0JP5PMCDEHXH=P=Q01PeP=PEP6Q0IPXn0100000020000RMPhPePJP5PMP5PJCDEHXH=P>A05t]RJ,2YS0IA05d]S0180AY135JS0JQ01,35S09'CPePXPh12eU,1h135U#A:085XI0@PAA05c[PjP5%9YRXP[CS5vjP5A05XqP5Q0T=05qCuQ0T=05\Rq,2iQ0;Q0;Q0P=05\RX,2i'13F135qRq135XRX#A';1CqX%7qRU%7XRJ'4RMPqPU%GUPXPJ%GJEaP6COPMP9P9PjPeC6RM,?iRJP9P9PnPjC6S0;,IiS0TQ0a=05NRX,2IQ0G?>IQQ0c=05NRU,2I3FS0G135XS07135US0Z';S0X':S0`[S0d[\fQ0TQ0GQ07#7S13Q0Z#7S15'5S1>':S0{[\J\fS0zPfQ0A,?nS0y1InMQ0]=05^RM,2ZS0xQ0F/1Z<0?QS0VQ0a=05^S0a,2ZS0w'4S0v135MRMQ0a,35RJ';S0S':S1?[[PfQ0=Q0yQ0=Q0A,IjRUQ0P=05rS0P,2wS0AQ0??>wQS1<Q0Q=05rS12,2wS103FRrQ0P,35RX#7S0bQ12,35RI#7S0e'5S0^':S0[O2S0_O2PfQ0yQ0Q=05SS0Q,2mS0YQ0@'1S0RQ0]=05SS0],2mS0W'4S1;Q0Q,35RfQ0],35Rq';S0\':S0U\UQ0yQ0_Q0yPU1;XIS0y,:rPUQ0[PUPrQ0yPrQ0^%]rPXQ0bQ0b#GPIQ0eQ0e#GEdS0eEcEMEMEMP\COQ0z%Nf%7fR\#<%NJ%7JRr#<P9P9PiPnC6S0z=J5NRUP4P6PSO2W=P9P9PwPiC6S0b,ImS0[Q06=05VS0_,2~PGPwP~PQC[Q0f=05VS1@,2~3FS1AQ0_,35S0_#7Q1@,35S1@#7S1B'5':S1C[S1D^=UQ0b=J5bS1EP3P6PSO2W=Q1EQ1C]=PvPkQ0lPxPoQ16PzPoQ0D,BOS0DQ18'_DWPFP1b7b8b9X0BX1BX4BX5B1464A>@4QS18,13S16Q18;U:[^0B^1B^4B^5BP6Q0g=05_S18,2sS1EPs18GmS1CQ0f=05_S0f,2sS1FPLO5b6b2b2b;b:bCbEP>%A6S1G,;31C@3S1H[1C36%A3S1I,;@[S1JQ1H%A@S1K,;4[20H36P6n2001000000120000000XACXBCQ1J^AC^BCP6PXPIP3O3%AIS1J,;XP6bIb3CVWIWQP3P6O2n2001000010121000000Q0IPGPNPYPQC[S1H'1PYP9P9PbPNC6RIQ015=5S01Q0JQ017m5Cfe1EVIPLEi1E_IPRCoPYA=5I]S01905tS0IQ1HPYQ01905dS01P5Q0IP5Q01CDEHePWP6EiW3PWP6EiW3P6O1b3P6O1b3WXP6O1Q0i=J5;P;P6P<P:O3PbQ0K=05LS0KQ0jPbPQPbQ0L=05LS0jP5Q0KP5Q0jCDGXP>Q0L=05RS0L,2VQ14?>VQQ0M=05RS14,2V3FP5Q0LP5Q14CDP_Q0MQ08==5TRT505RVQ0tP_PQP_Q0N=05TRTP5PVP5PTCDGXP6PaP5Q0NPKCSQ1=?>aQPaP5PtPKCS3FQ0JQ09';1}G[Q0|Q0}':Q0i,EaP=Q0OQ04,EY=L=6P=P9P9P^PSC6R[,Ej=L=6PmP=PEP3P9P9PNP^C6RNQ0Q5=5RjQ0Qn0100000020000RKQ0@PmP=PE1EiNQ0]9=5NRNQ0]n0100000020000RtP5PKP5PtCDEH]@P3Q05,EeS05#QPmPjQ0@PmP=PEP6PNQ0]n0100000020000RtP5PjP5PtCDEHXH=Q0t?>wQRtQ0A'1Q1<Q10,1t3F%AXQ1J';Q0yQ0^Q0eP:COQ0^Q0YQ0W'4RX1CfqRt':%7qRj,4\RK,:XRTPXPtPXPK%]XPfP\%G\S0YPqPj%GjS0^EaEcP]COPTQ0;=J5^RTQ0z,?mRXQ0[Q1AQ0_Q1@3w[[S0[[Q1D\X\TS1DPTQ0;,?wRKQ0z,IwRtP}Q0c=05bRVPGPiP}PQC[P}Q06=05bRb135VRV135bRb';EH[S06[PTQ0=PKQ0=Q0TQ0v%7MR_/5rS0c':S0zO2S0;O2PTPKQ0dPKQ0;PKQ0TQ1?Q0TQ0zQ0TQ0vQ0SQ0vQ0cQ0v#]PMP_%G_S0vPJPr%GrRKEdEcEMEMEMPSCOQ1DQ07#NQ13#<%Nb%7b#<P>Q0:#<Q0:/5`A>gsQRbQ1F'1Q1C?>sQRTQ1E,1b3FPLQ0?#<Q0>/5`PAPSO1P9P9P~P}C6,?{P9P9PsP~C6R~,I{PPQ0s=05nR}PGPsPPPQC[PPQ0r=05nRL1K5}1K5L'5EHRL[R}[P6PaO1RbP}PbPLPvPkQ0kQ0C?Y4l7Y3RlPxPo1Bu7Q02'BRL,By=RopPzPoQ0n/BLQ0m/Bp'_DWPFP1b7b8b9X0BX1BX4BX5BXFBA>43Q=F@:Q0pA>:@QQ0o/1<3F[^0B^1B^4B^5B^FBP6f[RLP5%9PRPPwCS18G|PLP5Q1:PwCSPLQ1CPSO6b6b2b2b2W<W3P3P6O2n2001000000121000000b;b:bCbGbEP>1;36Q1KQ1I';[RSQ1IQ1G';1;@3RL[%A4Q1K';\L20>36P3n2001000000120000000XACXBCPS^AC^BCP6PfPqP<O3%Af%AqRC';P6bIb<CVPwQ0P9=5[RSQ1<PwQ129=5[RLP5PSP5PLCDEHe1En[RnP]P[P6O2CoW@Q05#\PnP=P=Q0VPZP=PEP6Q0a9=5IQ0an0100000020000RIAmM5ICfP6Q0RQ1=?>mQQ0W3U1;fCRIQ0\15\jR=PfP\Q0YPqPjQ0^EdRnP<COR[P=Q0xQ0w'4RL1CMJRS':14_rRb,:LR}PLPSPLPb%]LPMP_Q0vPJPrPKEaEcPWCORKP}Q0b,?ZRrP9P9PmPwC6,IZRwQ1FQ1E7FTRTQ0f,35RJQ18,35R_3w[[\U%7J%7_'5,:T\w\r\URrPUQ0[PUQ0=PXQ0=PtQ0{O2RwO2PUPXQ06PXPwPXPtQ0`PtQ0{PtQ0GQ0XQ0GQ1>Q0G#]Q07Q13Q13#GQ0ZQ15Q15#GEdEcEMEMEMP^CORtPr%NVRX%7V#<RVQ1@#NRwQ1B#<RUP>%<gRT15g`RgP{Q0g=05aR_18GZRZP{PQI0KRJQ0??>{QQ0h=05aRa,2{RM3UPRQ0>#<RLQ0F/5`R`PAP^O1Rb1?|~P9P9P{PsC6,I|PHQ0r=05iRsPGP{PHPQC[PHQ1:=05iRi1K5s1K5i'5EHRi[Rs[R{P6PYO1RYPsPYPiQ0<Q0BPkPlPxPoPoP?P8P8PDQ0D=RopPoP?P8P8PDP;J0LK0=PzPoARo2uPzPoQ17PzPoQ0D1BuyQ02'B/Bp'_DWCTCTPFP1b7b8b9X0BX1BX4BX5BXFBWRQ0<Q0o,16Rp?n:<Q19Q19Q0E11A<?>Q;5F4[[[^0B^1B^4B^5B^FB]RP6A05PmRP,K5RQAZ5HmRH,K5R;'5f\Ry/2HRHPZPyQ0q,8GRG12yPRPP3P<P|O9b6b2b2b2W<W3P3P6O2n2001000000121000000b;b:bCbGbEPI11j0RI,5\PfP\Q0YPCPIQ03PqPjQ0^CxEdP[P=PKP}PtPrPXPVPwPUP>PTPg1K5_R_1K5aRa/10'5PRPbP{PYPsPYPiPvPkQ11PxPo1`O7-04oR7PzPoQ0~,`ODWPFP1b7b8b9X0BX1B1563ROQ0u,53[^0B^1BP6P;PQP]O3R]b6b2b2b2X<`X3LP3P6O2n2001000000121000000b;b:bCbGbEChCVQ0RPmPNAmf5NCfeQ1;Q0\P[P=PKP}PtPrPXPVPwPUP>PTPg14JMPRPbP{PYPsPYPiPvPkQ0lPxPoQ0D=RouRuPzPuCTPFP1b7b8b9X0BX1BX4BX5B14p4Q16/4:[^0B^1B^4B^5BP6PHPyPGPPP^O5b6b2b2b2X<`X3LP3P6O2n2001000000121000000b;b:bCbGbEQ0\P=PnP[P=PKP}PtPrPXPVPwPUP>PTPg15_aPRPbP{PYPsPYPiPvPkQ11PxPoP7PzP7CTPFP1b7b8b9X0BX1B153@\O^0B^1BP]b6b2b2b2X<`X3LP3P6O2n2001000000121000000b;b:bCbGbEChCVQ0Uen0110101020101bJW@n0110101020101P6O1b@bJb3PeQ0H==5WRW905dRdPhPeA05cWRWP5PdP5PWCDEHeWIWQP3P6O2n2001000010121000000b=WMP6O1n200100001021100011000bYbZWOWPWMW2XDEXV9XT9P3P6O2n2001100010121101101X=5PAD{WWW[X`9XH9X^BX]BWDX_Bo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Gap.
  Variable L : list (word * word).
  Variable nZ : Z.
  Hypothesis HnZ : 0 <= nZ.

  (* [comment removed for export] *)
  Definition scan_inv (c : Z) : Prop :=
    c mod page_size = 0 /\ bottomup_floor <= c
    /\ c + nZ + gap_weight nZ (List.filter (live_at c) L) <= alloc_ceiling.

  Definition gap_at (c : Z) : Prop :=
    c mod page_size = 0 /\ bottomup_floor <= c /\ c + nZ <= alloc_ceiling
    /\ region_free L (Z_to_bv 64 c) (Z_to_bv 64 nZ) = true.

  Lemma scan_ok_or_step : forall c, scan_inv c ->
    gap_at c
    \/ exists c', scan_inv c'
         /\ (length (List.filter (live_at c') L) < length (List.filter (live_at c) L))%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"; "Gap"] "p'0h01Hh14__x1h27__sat67h34__x2h44__x3h54__p1h64__p2h74__x4h84__x5h94__x6h:4__x7h;4__x8h<2H0h=2H3h>7__arithh?4__ffh@8__varmaphA5__withB2c'hC1qhD1rhE2H4hF2H5hG7__sat65hH7__sat66hI4__x9hJ2H6hK2H7hL5heq_BhM5heq_ShN6heq_c'hO2H1hP2H2hQ1shR5HfreehS3HovhT5__x10hU5__x11hV1bi001bhW1mhX1nhY2HahZ5Hlen0h[7__sat68h\5__x12h]5__x13h^2b1h_2b2h`4cstrha5cstr0hb1xi011xhc1yhd1zhe1Bhf3H10hg3H11hh3H12hi3H13hj2H8hk2H9hl3Halhm4Hc64hn3Hcuho3Hcvhp5Hdeadhq3Hflhr3Hfvhs3Hgeht3Hinhu3Hlehv4Hlenhw5Hlivehx3Hnuhy2Hwhz3Hw0h{3Hwsh|1Sh}6__sat1h~6__sat2i026__sat3i031ai041ci051ei062q0i072r0p%0p%1p&0p&1p;1p;2p;3p;4p;6p;;p;7p;8p;<p-1g00gbR0p4p710R1p8p1000Gp4p70R2g0017R3p4p710R4p8P2P1p8P2g001QR5p4p710R6p8P2p1001mp4p710R7p8P2p1002Kp4p7210R8p8P2p1002hp4p710R2p8p1003Fp6051000R9p1004Op4p710R:p8p1005Ep6051000R;P:p8P;p1006Op4p710R<p8P;p10071p4p710R=p8p1007Np4p70R>P4p8P>P1p8P>P6p8P>P:p8P>p1008<p4p710p8P>P7p8P>p1008Yp4p710p8P>P8p8P>P9p8P>p1009Tp4p710p8P>P;p8P>p100:Np4p710p8P>P2p8P>P=p8p100;Jp4p7210R=P4p8P=P1p8P=P6p8P=P7p8P=P8p8P=P2p8P=p100<6p4p710p8p100==p6051000R=P1p8P=P<p8P=g012lR=p4p710p8p100>`p4p70R<P4p8P<P1p8P<P6p8P<P7p8P<P8p8P<P2p8g01Dkk10aTg00M\j23Tg00@2j1ATg00BIk10wTg00IAk10rTg00h9k20pTg011@j2ETg00AnR2j2=Tg01Enk10:Tg00kJk20ITg016@j2VTg00H\j1GTg00@Wj1tTP3j3PTg01Fok30nTg00?Vj29Tg01H;k20jTg00A5k20hTg01Hck30fTg00LIk10NTg00ARR3j22Tg00XPj1NTg00Xok20XTg00WQk110Tg00Wok20~Tg00YXk30=Tg00PSk10|Tg00Q3k10zTg00QSk10yTg00R1k10xTg00ROk10vTg00S:k20STg00]2k10tTg00]Tk20RTg01IGk30qTg00TAk20oTg00HBk20GTg00Tck20mTg00UOk30lTg00Unk40kTg00M?j2UTg01Ijk20QTg00Dbj2HTg00EHj24Tg00hYk30;Tg00nYk400Tg00n?k30gTg01Jok40eTg00iSj4mTP0k303Tg00lFj4rTg00j3S00k202Tg014Ij2|Tg00jlj2}TP5k60MTg01L>k20dTg014fk20cTg01L_j1eTg01M]k11BTg01Nlk31@Tg00Lbk201Tg00V`k21?Tg00Khk20_Tg00JWj2zTg00N9k20^Tg00N`k20]Tg00OGk20OTg00Omk20PTg01OPk31>Tg015Fk30[Tg015ck30ZTg013Gk20Yk10KTg01P3k21=Tg01PSm;19Tg01Q^k118Tg017@R5k20?Tg016`R0k10ATg018_k415Tg019Fk10WTg00o4k414Tg00oNk313TP=k30JTg00K7k212Tg00ZAk30>Tg00Zjk20UTg00[Vj3QTg00\6k211Tg00\Tk408Tg00_=j4hTg00_hj7wTg01>=k616Tg01>ak70`Tg00S]k61:Tg00^7k30}Tg00^Zk31;Tg00`Lj8TTg01S2k20TTg01?Em<0{Tf0R=g00cVR<'zp=5g00FaR8g00G?R77P=p=:g01SOS01/9=p=o%A=#Ap>0Bf2R6f1R1$0K<0J=p=C131=g01TSS02'9p=kf3R4&0K1>0J6='Vp>06f5R>f4R;&0K1>0J6=,V4+0?'=p=g2028=p=^20?1=,=6p>0H%G=#Gp=]%A=#Gp>0u%G=#Ap>0s%A=#A#A#Ap=[%G=#A#G#Ap=s197=p=1212=<p=Y127=p=x20_=<p=a201=<p=>1U<1/3=9P86p=c20^=<p=d197112=<'=p=l20]=<p=`12<119=7'=p=_20O=<p=\20P=<p=XAP81=p=020X8=p=SB0>81=p=yB0>81=:0>86p>09B0>81=g00g6R9+0Up=Rg00dNR:f6R?AQ:1=9Q:69Q:49Q:;9Q:>3Qp=iAQ:1=9Q:69Q:49Q:;p=@2118=p=JP8P6P1P=H08p=?P8P8P;P4P6H08P1P=H08p=L20R8=p=DP6g00aWR@g00b6RAPAg00bVRBP8P1g00a0RCP=Chg00c6RDFwp=8P6P@PAPAPBP8P1g01B^REP=ChPDFwp=;P1P@PAPAPBP=J16p=vP6P@PAPAPBP1P=K0`p=MP1P@PAPAPBP=J1:p>07B0}81=p=uB1;81=p=<P6P@PAPAPBP8P1g012ERFP=ChPDFwp=K20S8=p={P>P@PAPAPBP;P@PAPAPBP8P4PFP6ChPDFwP1P=GTp=ZP>P@PAPAPBP;P@PAPAPBP8P4PCP6ChPDFwP1P=GTp=WP?P@PAPAPBP>P;P4P@PAPAPBP6P1P=GTGTp=BP?P@PAPAPBP>P@PAPAPBP;P4P6GTP1P=GTp=7g00e:RGg00eZRH7P=p=61261/==p=j121=,=6p=f131=9P86p=q1361/9=p=O19=7p>0FP4P@PAPAPBP6P1P=GTp>0E1971/==p>0DAQ:1=p=n20U=9p>0ig00oh9PG=p=~141=,36p>0C131=,|6p=I136100T=p>0b20G8=p=F12=<,=1p>1A1346/3100T=p=b1361/3=p=pP8P1PCP=Chp>0\P;P@PAPAPBP4P6P1P@PAPAPBP=PDFwGTp>0@P>P@PAPAPBP;P4P6P@PAPAPBP1P=K0`GTp>05P8P1PEP=Chp>04P;P@PAPAPBP4P@PAPAPBP6PDFwP1P=GTp>0<P8P1PFP=Chp>1<1V1=-0?6p>0Lg01A]P8P5P0P3g01B<P>P;P4P6P1P=N<0{p>17P8P;P4P8P6P1P=H08H08p>0V&0a=R3P2%51#:%o1p,2nZR0,31g00G]R5#ARF#ARD#AR@#AS03$0BS04$0wRE$0rRC00pCR9p,1LRI7C1,E0'k'=&0:6P3P9P9P=PIH06RJP9P9P4PIEgXB8#^+0IP=%54#:%o;13;0AC9;IS05,E0S06'k'=P2%o>13>0AC9>IS07,E0S08'k&0:?f7RK=C9IS09,V9:0H3JXB8#^+0IP=%oKf8RL/30AC9LIS0:,E0'kg01UVQ02%G5RM#GS0;#GS0<#]#]#]#]S0=#G#]$0u#]#]#]$0s$0B#[#[#[#[#[#tRN5P8g01VeQ01%GFS0>#AS0?#s#s#s#s#s#s#s#]#[#[#[#tRO5P8f;RP=C9IRQp,3HnZS0@60n01E0Q#1f<RQ#Y%1QRR197<RSf>RT#5#1[[%tFRUQ04#tRV+0jS0A%xU%1V20hUVRW#x[[S0B%1URXg010HRYB0fUV1UWYS0C%1W\Y^YXRXf?RY#aAP8<7RV$0NRZf@R[%>[%5[S0D3c[%d[127<R\fAR]#5R^/l^[%`]12<7R_fBR`#5Ra/_a[%\`fCRb#>#:\V%XbfDRc#5Rd/0c\V%>cReP8fERf#5RgP8p-0Rhg00fWRi#NRj#NS0E#NRk#NRl#NRm#NRn#NS0F#SS0G%SmRm%SlS0H%Sj20X8iS0I'y409'RRi&105-0~8S0J%SnS0K60=8S0L%SkQ0I'yS0M'RRkPkPiPiPkPkPiPkPiPiPkPkPiPiPkPkPiPiPkPkPiPiPkPkPiPkPiPkPi&0|:RiFiD@D@D@D@D@D@&0z:R:%JLS0N&0y8Rk7?;P6%J?S0OP1%J>S0P%JKRn7?4DL&0x8Rj&0v8RlPlQ0;#DRo20S87Rp58lRq&0tARA%DMRr20R85Rs58lPAPlPlPqPA%D@R@=8lpRtPAPlPlA;lopPAA;lorf:Ru,vlS0Q5MlPAPlPlA;lpoPA1vlPS0RA;lro5MlPAPlPl207lqPA1uo@/<r98lsPAPlQ0>#DRq9KlpS0SPAPl%DDRv%{OS0T58lPAPl%AMS0U#DRM%{N58lS0VPAPl%DFRF,<sS0W/<q=KlMPAPlPlPvPsPAPlPlPrPpPAPlPlPpPFPAAKlpsS0X%{U>0q8E9;lsS0Y5MlS0ZEZEWEZFBFBF7F7F7F7F720olBRBP=P620GGH20m=6#6dB0l871H0kRHb?b@bAX18X38X48X78X88X98X:8X;8X5hW6%:?S0[1041S0\[%:KS0]f9RU#:S0^[S0_12L7S0`AjU>P[%xUS0af=Rw?f?u[%:uS0bg00f:S0c[Rx1UPQRy=q>K[%1US0d10UO10QNS0e13LU?OQw19QUS0f%:QS0gAfRQWRN\R[[[[[[[[[[[^18^38^48^78^88^98^:8^;8^5h^6hP=%11RR&0F1P6P<Q02fGRz=C9I,E0Q01P1P0PzP4P;P>P?PKPPPQPwPTPYPbQ0@OFb>bDbCb=bPbOb<b0b}b~c02PN%Yw%1w%5Y#1\S[Q0AQ0BQ0CPX%a[%>]=c]^\Z%d]1laa\\%``%5bR^/_^\_%\b%:e\V%Xc10gf\V%>fRgP8fFRe#5R{P8P2%1z12zWfHR|#1S0h12|WS0i'=PufIR}#1fJR~/2WPwP1O1S0j%1>\SS0kPiP:%J1PjPlQ0YPAPlQ0XPAQ0ZH0ES0ZH0EPBPHb?b@bAX1812=W126W-0D6\R[^18P=fMS0XP6P4O3b>b2WFWEP1P=O2n2001000000121000000bDbCb=bPbOb<b0bGbHb2-0Qw1HEw,4E/0w%YT%1TQ0D#1\S[Q0AQ0BQ0CPX%a]%>`=c`a\Z%d`1l^^\\%`b1_dd\_%\c%:g\V%Xf10{e\V%>eS0DP8%5zRgP8P2Q0hQ0i120W-0D0PP%1~fKS0i/2WQ0jQ0kQ0GQ0LQ0HQ0M'y809m'RR^P^P^P^P^P^P^P^P^P^P^P^P^P^1n^iFiD@D@P:A?n;kP6Q0OP1Q0N??>kS0h??4kDLPjPlPlPtPAA8lFvPAPlPlPtPA%GDS0Y#DRD=8lpR^PAPlPlA;l@pPAA;l@FQ0Q5MlPAPlPlA;lp@PAQ0RA;lF@5MlPAPlPl207ltPA1u@D/<F98lvPAPlQ0SPAPlQ0T98lrPAPlQ0VPAPl1<vs/<q=KlMPAPlPlPrPvPAPlPlPFPpPAQ0ZEWEZFBFBF7F7F7F7F7PBPHb?b@bAX18X38X48X78X88X98X:8X;8X5hX6hQ0[106;[Q0_Q0`AjU;P[Q0aAfw>u[AqLy?\xQ0d10LOS0ZQ0e13PL?OQw19PQS0V%:PS0S%1PPN[[[[[[[[[[[[^18^38^48^78^88^98^:8^;8^5h^6hP=%1?S0d&0F?S0ePKP<Q02fNRN=C9I,E0PNQ01P?P0PLPUPuPPPQP`PbPcPfPeP~Q0@OFb>b2WFWEP1P=O2n2001000000121000000bDbCb=bPbOb<b0bGbHb2-0Q01HE0Rt,4ERR/001HEY>0;ItPG20GG=1HE[>0;It=PG=PG1HE`S0l>0;ItS0m=PG=&0:bP3PJP9P9PcPIEgXB8#^+0I]RP11HE]>0;ItS0n#6&0:`S0oP3PJP9P9PbPIEgXB8#^S0p%:a%o`S0q1k`0S0rQ0m#6Ra'=Rb'=PTQ0qPbPuQ0rPa%Y`%1`%1d\S[Q0AQ0BQ0CPX%afQ0D=ce{\Z%de1lgg\\%`z%5|Rg/_g\_%\|%>}#:\V%X}%5~/0~\V%>~P8Q0i#5P8P2fLS0D#1Q0D/2WQ0X/k0PY%1NfORg/2WQ0jQ0kQ0M,ymS0M$0iR{P{P{P{P{P{P{P{P{P{P{P{P{P{1n{iFiD@D@P:%J;S0rP6Q0N???kP1PnP>PkP4PkDLDLPjPlPlP^PAA8lvsS0qPAPlPlP^PAQ0?#DS0?=8lpPAPlPlA;lDpPAA;lDvQ0Q5MlPAPlPlA;lpDPAQ0RA;lvD5MlPAPlPl207l^PAQ0?,uD/<v98lsPAPlPlPpPMPAPlQ0T98lqS0QPAPlQ0W/<M=KlrPAPlAKlqsS0mPAPlA8lvpS0sPAQ0W=KlrS0tFBFBEZF7F7F7F7F7PBPHb?b@bAX18X38X48X78X88X98X:8X;8X5hX6hQ0[10;1S0u[Q0_Q0`AjU?P[Q0aAfwKu[Aq>yL\x%1u10uO13KL?OQU19QLQ0gAOuPQS0a[[[[[[[[[[^18^38^48^78^88^98^:8^;8^5h^6hP=Q0dQ0ePKP<fRS0_=C9I,E0Q01P?Q02P0Q0_PLPUPuPPPQPePzP}P~PNODb>b2WFWEP1P=O2n2001000000121000000bDbCb=bPbOb<b0bGbHb2P=H00H00H0040gWRQ0n#~Q0oQ0pPIQ0lPtP=H0ePCPCP1P=Cm>039IRx1HEcPtP1P=Cr#6'=XQC-02CXVC-02CQ00PC1HEfPtP1P=Cr#6,=xXQC-02CXVCP3PJP9P9PfPIEgXB8#^P=1HEzPtP1P=Cr#6,=xXQC-02CQ00PCPCPCP6P=Cm>039I1HE|PtP6P=Cr#6'=XQCP3PJP9P9P}PIEgXB8#^P=PCPCP;P=Cm>039I1HE~PtP;P=Cr#6'=P2PCPCP>P1Cm>039IQ0i,HEPtP>P1Cr#6P3PJP9P9Q0XPIEgXB8#^P=PCPCPKP4Cm>039I1HENPtPLP;Cr#6P81HEg,4E14EuRt@0CE?Rx,|=AIt=R'}#6Xd8P=PgP]J0M14EURy14E>5IgAIygR'}#6P8PRfQS0014EPRR14EK3IQ00=IR='}#6Xd8P=P0P]J0MfPS0l/|xQ0l=It0'}#6P21}1=#6%66Rt%61Rx'=[RD%6=,=x1}61#6Rx[%64/=t\x20d1=P1n2001000000120000000X_GX^GPD^_G^^GP=Q0_14EQRG14EL3IRDQ0_=IG0RGP1O3%6D%6G'=P2fSS0n14EwRG;Iy#6Q0n=IG0#6P3PJP9P9fUS0`PIEgXB8#^P=Q0`14EY;IR#614E[fVS0[;I0#6P21|1=S0v#61261S0w[S0x121=1|61S0y#6RR[S0z1246\R20c1=S0{P1n2001000000120000000XW8XX8RRQ0x^W8^X8RGP=fXRy14E`RD@0CETRxP6O312yxPRPGP=14EcRGfZS0|/30RRP4O312GR14EfP8PDP8131=#eP81361RD$1B%eD,9D1346S0}Q04$0B#[#tRD%t5R540bRRQ0}#eRG#F101GRGePG14EeRG#F104GRGePGQ0i,4ES04#FQ04,0>RGePGfbS0~#YQ0~#1fdS10#5#1\S[Q0AQ0BQ0CPXfeS11#affS12Q12#>Q12#5S133c\ZQ12#dfgS14#5RG#1S1501AG\\Q14#`fhRG#5S16Q16'_\_%\GfiRx#>S17#:\V%XxfjRy#5S18/0y\V%>yP8fkS19#5S1:P8P2flRt#112tW%xDR^f_S1;fnS1<#1S1=foR{/2WS1>Q0jQ0kPiP:PkPj%{DRd9;lpPBPHb?b@bAP^P=b>b2WKWJP1P=O2n2001000000120000000bDbCbFbEb=b<b0bGbHb2bLbMbN81@D201RD,UD/9R13;4#eRR#F106RRRePR14EzS1?#FQ1?,0;RRePRQ0D,4ES1@#FQ1@,0?RRePRfcS1A#YQ1A#1Q11#5#1\S[PLPKPDP5CbRR01?D%1R%1DPuPUPDP5Cb001D#1[[Q0AQ0BQ0CPX13PuS1B@0bD500_D%:DRR$0NPQPPPDP5CbRa201aD,UD1zaD3q[20^aDPwPQPDP5CbRa/zDRb12bD+0D\^20]aD12D7PTPwPDP5CbRa/zDR^&0F^5jD[20OaDPYPTPDP5CbRa001D#:\R20PaDP[PYPDP5CbRa/zD/0a\R201aDP8P]P[PDP5Cb/zDP8Q1<#a%>{%5{S1C5c{\Z%d{fpS1D#5Ra/la\\Q1D#`fqRa#5S1EQ1E'_\_%\afrRR#>#:\V%XRfsS1F#5S1GQ1F'0\VQ1F#>P8ftS1H#5P8P2fuR^#112^W1UUDQ0=#tRb9p~}'9PGfwS0=#1S1Ifx/2WPfP1O1Q0kPiP:%J6%J47?1PjPlPl1uds1<FrS1J/<d%{561>8PA1usdQ1J%{bS1K'<5KlEZPBPHb?b@bAX18X38X481UD=P1P6PDP5Cb'91U1DAp64b'9[^18^38^48P=PNPgPTQ0iO4b>b[WiWhP1P=O2n2001000000121000000c07c06bgbfbkbjbKbDbCbJbFbEb=b<bGbHb2b[bLbMbNb0Q0}/3b,91RDePDP2Q0xQ0zQ0w1|46S0x#6[Q0{P=n2001000000120000000XW8XX8Q0z^W8^X8P=faRDQ04Q1?'313>;#eR5#F1045R5eP514E|S1?#FQ1?,0>R5eP5Q0X,4ER5#F10K5R5eP5Q10#YQ10#1Q13#1\S[Q0AQ0BQ0CPXQ14#a%>GQ165cG\Z%dG%5xS16Q16'l\\%`xQ18Q18'_\_%\yQ19#>#:\VQ19#X%5t/0t\V%>tS13P8fmR5#5S10P8P2Q1=Q1</2WfY,4EQ0`80CE,2{PDQ1D#112aWQ0jQ0kQ0KQ0HQ0I'yS0`,ymS1='RRDPDPDPDPDPDPDPDPDPDPDPDPDPD1nDiFiD@D@P:%JUS0z??UkS0{??UnP6Q0PP1Q0rQ0OQ0N7?US0O7?4DLPjPlPlQ0<#DRD=8lpS0<PAA8lqsPAPlPlQ0<PAPlQ03#DRd00\pI0@S03PAPlPlA;lDpS0wPAPlA;lDqS0}Q0RJ05PAPlPlA;lpDS1LPA1vlQS1MA;lqDS1N5MlPAPlPlQ0<-07lS1OPA1uDdS1P/<qS1Q98lsPAPlPlQ0>#G#DS0>PFPAPlPlQ0U#A#DRdPrPAPlPlQ0>/<dS1R-04sPAPlQ0T98lMS1SPAPlAKlMsPAPlA8lqpS1TPAPlQ1J-04sI0@FBI0<EWEWF7F7FBF7PBPHb?b@bAX18X38X48X78X88X98X:8X;8XI8X5hX6hQ0]Q0u[%:LQ0b[S0u12U7S1JAju?Q[%xuS1UAfTKP[Q0SQ0c[S1V1UQwS1W=q>L[10u?10QL13QwS1X,2K10QO19wU%:wS1YQ1X,2P[[[[[[[[[[[^18^38^48^78^88^98^:8^;8^I8^5h^6hP=Q0dQ0ePKP<PzP|Q01P?Q0|,4ES0|f^,4EQ1HPLPUPuPPPQP[P]Q0iPxPtQ1DOFb>b2WKWJP1P=O2n2001000000121000000bDbCbFbEb=b<b0bGbHb2bLbMbNO3b0f`S1ZPCPCP~PeCmS1[:0[CC,4EQ1[:0ZCC,4E3I#6eQ1ZQ1[+0Y#6S1[eQ1[P2Q0v#~1916S0v[19=1Q0y#~[S0yQ0vQ0x#~[21=1=P=n2001000000120000000Xc8Xb8Q0y^c8^b8P=P;Q1@Q1?'313?>#eS1@#FQ1@,0;S1@eS0yQ1@14E}S0v#FQ0v,0?S0xeS1[Q0x14ENS1Z#FS1\Q1Z,0LS1]eS1^Q1]Q11#YS1_Q11#1Q15\S[S15Q0AQ0BQ0CPX%aGS1`Q17Q165cx\ZS16%dxS17Q18Q18'l\\S18%`yS1aQ1:Q1:'_\_S1:Q19#\S19Q13#:\VS13%XtS1bQ10/05\VS10%>5S1cP8Q1<#5S1<P8P2%1{S1dQ1>Q0|Q0[,4E;O`Q0~%1aS0|12RWS0[Q0jQ0kQ0F#NR{#N#N#NS0F#SQ0J%S{S1e60=8R{'RQ0JQ0G60=8Q0LQ0J>0=8mQ0`409'RRxPxQ0F#N#S/R{PxPxPxPxPxPxPxPxPxPx1nxiFiD@D@P:%JPS0FPPPkPPPnDLP6Q0z9?k>P1PkP;Q0NP4%JuS0`9?k?DLDLPjPlPlQ0<PAA8lqoS0JPAPlQ03PAPlPlQ0wPAPlQ0}1vlwJ05PAPlPlQ1LPA1vlTQ1N5MlPAPlPlQ1OPAQ1Q98loPAPlPlPdPsPAPlPlQ0U#G#DRxPFPAPlPlPrQ0;#A#DR{PAPlPl1<dxP{PAPlQ1SPAPlAKlMoS0;PAPlQ1TPAQ0tH0EFBEZEWEWEWF7F7FBF7PBPHb?b@bAX18X38X48X78X88X98X:8X;8XI8XT8XU8X5hX6hQ0^10;?[Q0bQ0g[12P7AjQ?T[%xQAf[Kw[Q1YQ0c[1UTY=quL[10P>10wK10UYAOTY[10wO19TY%:TS1YQ1X/9T[[[[[[[[[[[[^18^38^48^78^88^98^:8^;8^I8^T8^U8^5h^6hP=Q0dQ0ePKP<13}|#eRMP|P}P^Q01P?Pzf[,4EQ1;,4EPLPUPuPPPQP[P]P`PePyP5PaOIb>b2WKWJP1P=O2n2001000000121000000bDbCbFbEb=b<b0bGbHb2bLbMbNO3b0PCPCQ0iPzCmRx:0[CC,4EB0ZCCx,4E5I4#~e20Y4x#~RxePxP0PIQ0~P;Q0DP|Q0@Q0yQ1@Q1[Q0xQ1^Q1]Q1_Q15Q0AQ0BQ0CPXQ1`Q16Q17Q18Q1aQ1:Q19Q13Q1bQ10Q1cP8Q1<P8P2Q1dQ1>Q1D/9`Q0~Q0|Q0[Q0jQ0kQ0LQ1='RRxPxPxPxPxPxPxPxPxPxPxPxPxPx1nxiFiD@D@P:Q0{??4nP6Q0P??UkP1Q0rQ0O7?UDLPjPlPlQ0<PAQ0qPAPlQ03PAPlPlQ0wPAPlA;lDvQ0RJ05PAPlPlQ1LPAQ1MA;lvD5MlPAPlPlQ1OPAQ1P/<v98lsPAPlA8lFdS1PPAPlQ0?Q0>'<RD=KldS0?PAPlPl204sDPAPlQ0QPAPlQ0mPAPlQ0sPAPl21<sFI0@S0sFBI0<FBF7F7FBF7PBPHb?b@bAX18X38X48X78X88X98X:8X;8XI8X5hX6hQ0]Q0\[Q0uQ1JAju>Q[S1JQ1UAfT?P[S1UQ1VQ1W/3KS1W,0>[10?PS0\Q0a13PQS0m,2K10POQ0fQ0gQ0V[S0V[[[[[[[[[[^18^38^48^78^88^98^:8^;8^I8^5h^6hP=Q0dQ0ePKP<PMP|P}Q01P?PzP^PLPUPuPPPQP`PeQ0DPyP5PaOFb>b2WKWJP1P=O2n2001000000121000000bDbCbFbEb=b<b0bGbHb2bLbMbNPcP1P=N;19Q06Q1??p0bQ0~=C9IRe,E03OQ05,V91V9e40HP2Q08Q0v?p0bQ1A=C9IRe,E03OQ07,V9@0L9eQ11=C9IRe,V9:0H3JXB8#^P=Q09,E0Q04?p0b1E0e3OQ0:,V9Q12=C9I80L9P8P3PJP9P9PGPIEgXB8PU&0aUAC9UIRG,V9Q14=C9I80L9%5U#:%oURJ13U01E0G'kRG'=Q1B$18PJPGQ1B#eRG#F10UGRGeS1BPGQ1\Q1Z,0PRJeS1ZPJQ0n,4ER3#F10w3R3eS0nP3P9P9PQPIH06ReP9P9PyPIH06R}+0?&0AeR|&0A}RM'2RxPeP|%F|P}PM%FMJ17P4H15S1\PxP9P9PwPIH06RM$0WS14&0AM#1S12P9P9PtPIH06Rt$0WS0:&0At#1S04%Y5S09%15Q1C#1\S[S1CQ0AQ0BQ0CPXQ1D#aS1D%>aQ1E5ca\ZS1E%daS11%5RRa/la\\S07%`RS08Q1GQ1G'_\_S1GQ1F#\S1FQ1H#>#:\VR_Q1H#XR\%5^/0^\VRV%>^RaP8fv#5RZP8P2Q1IQ0=/2WRS%o~PyfyR5#1Rtfz/2WRWQ0jQ0kQ0LQ0HQ0E#SQ0I'y609m'RRmPmPmPmPmPmPmPmPmPmPmPmPmPm1nmiFiD@D@P:A?k4nP6Q0h??UkP1Q0rPUQ0z???kPUPkI0VDLPjPlPlQ0Y#A#DRn=8lpRmPAA8lvqPAPlPlPmPAPlQ0Y#G#DRM00\pI0@R}PAPlPlA;lnpR|PAPlA;lnvQ0RJ05PAPlPlA;lpnRpPAQ1MA;lvn5MlPAPlPl207lmRePA1unMRM/<v98lqPAPlQ1PPAPlQ0?PAPlPl204qDPAPlPlPsQ0TPAPlPlPsPqPAQ0sEZEWI0<FBF7F7FBF7PBPHb?b@bAX18X38X48X78X88X98X:8X;8XI8X5hX6hQ0]104;[Q0uQ1JQ1UQ1VQ1W,0L[Q0\Q0aQ0m,2uQ0Z19UQQ0V[[[[[[[[[[^18^38^48^78^88^98^:8^;8^I8^5h^6hP=Q0dQ0ePKP<Q00Q0l'3#eQ0lQ00f}RDP?PgQ01PLPUPuPPPQPfPNfTPRP^P5OFb>b2WKWJP1P=O2n2001000000121000000bDbCbFbEb=b<b0bGbHb2bab`bZbLbMbNQ1BPGQ1ZPJQ0nP3Q1\PxQ14Q12Q0:Q04Q09Q1CQ0AQ0BQ0CPXQ1DQ1EQ11Q07Q08Q1GQ1FP_P\PVPaP8PZP8P2Q1IPS13~0AC9~I,E0'kPyQ0jQ0kQ1eQ0GQ0KQ0M409'RRyPyPyPyPyPyPyPyPyPyPyPyPyPy1nyiFiD@D@P:Q0NQ0`7?;P6%JQPwPkP?Q0FDLP1Q0PP4%Jw??UkPKPkI0VDLPjPlPlPmPAQ0JPAPlP}PAPlPlP|PAPlA;lnq1vlYJ05PAPlPlPpPA1vl[A;lqn5MlPAPlPlPePA1<Mq98loPAPlPlPdP{PAPlPl1<{FQ1K'<,<rP@PAPlPlPsQ1RQ1K'<PAPlPlQ0>1<oFRF+04PAPlQ1SPAPl1<F@=KlvPAPlQ0;PAPlQ1TPAQ0W/<r=KlvFBFBI0<EZEZEWF7F7FBF7PBPHb?b@bAX18X38X48X78X88X98X:8X;8XI8XT8XU8X\8X]8X5hX6hQ0S10>K[Q0gQ1Y[12w7AjTK[[%xTAf`LY[%:YQ0c[1U[]=qPU[10TYAp[Kb=OLwApY[b,9K13TU,2[10TO13[P?O]w19[]%:[13wT?OY[[[[[[[[[[[[[[^18^38^48^78^88^98^:8^;8^I8^T8^U8^\8^]8^5h^6hP=Q0dQ0ePKP<Q1A,4EQ0lQ00AC9DI,E0PDQ01P?Q02AC9gI,E0P0PgPLPUPuPPPQPcPzQ0XQ0_PRQ1HP^P5OLb>b2XKWXJtP1P=O2n2001000000121000000bDbCbFbEb=b<b0bGbHb2bab`bZbLbMbNH00H00P=H00H14WvW{P1P=O2n2001000000121000000c03bpbwbubsbBb|bebPb0bOb0WPWOP1P=O2n2001000000121000000bSb0bSbSWSWtP1P=O2n2001000000121000000W0XQCP1P=O2n2001000000121101000W0XVCP1P=O2n2001000000121101000c05413WRn0110000020101P=O1bRbVbxbnbmbzbrboWyWqP1P=O2n2001000000121000000W0WlP1P=O2n2001000000121000000W0Z048o"). Qed.

  Lemma scan : forall k c, (length (List.filter (live_at c) L) <= k)%nat -> scan_inv c ->
    exists g, gap_at g.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"; "Gap"] "p'0h02c'h11Hh24__x1h34__x2h41ch51kh64Hinvh72Hkh83Hk0h93Hlth:4Hlt0h;7__arithh<4__ffh=4__p1h>8__varmaph?5__with@4__x3hA4cstrhB5cstr0hC1ohD5Hinv'hE3HokhF2IHhG2_HhH5cstr1hI1ghJ1xi001xp;1p;2p;4p;3p;6p;<p;7p;8p-1p10000p4p710R0p8p1000Gp4p70R1g00HBR2p4p710R3p8P1P0p8P1p1001Qp4p710R4p8P1p1001mp4p710R5p8P1p1002Kp4p7210R6p8P1p1002hp4p710R1p8p1003Fp6051000R7p1004Op4p710R8p8p1005Ep6051000R9P8p8P9p1006Op4p710R:p8P9p10071p4p710R;p8p1007Np4p70R<P3p8P<P0p8P<P4p8P<P8p8P<p1008<p4p710p8P<P5p8P<p1008Yp4p710p8P<P6p8P<P7p8P<p1009Tp4p710p8P<P9p8P<p100:Np4p710p8P<P1p8P<P;p8p100;Jp4p7210R;P3p8P;P0p8P;P4p8P;P5p8P;P6p8P;P1p8P;p100<6p4p710p8p100==p6051000R;P0p8P;P:p8P;g012lR;p4p710p8p100>`p4p70R:P3p8P:P0p8P:P4p8P:P5p8P:P6p8P:P1p8g00@2j16Tg00BIj1nTg00IAj1XTg00h9j2PTg01;3R1j28Tg01Dkj1HTg01Enj1?Tg00j3R:j2=Tg01Wmj2UTg017@R6j22Tg00AnR5j2:Tg00kJR4j2MTg00o4j4mTg016`R0j11Tg00ARR3j2GTP2j23Tg018_j4FTg00?VR2j24Tg019Fj19Tg00XPR<j1>Tg00Xoj2CTg00ZAj3KTg00Zjj2WTg00PSj1VTg00[Vj3TTg00Q3j1QTg00\6j2BTg00\Tj4ATg00R1j1OTg00ROj1NTg00S:j2JTg00]Tj2<Tg00]2j1RTg00H\j1STg00_=j4ITg01>=j6lTg00TAj2kTg00Tcj2jTg0017j3gTg00UOj3fTg00Unj4eTg00@Wj1_Tg00M\j2ETg00QSj1`Tg00^Zj3aTg01<Cj4bTg01Y7j4\Tg013Gj1cTP;j3dTg016@j2[Tg01?El<DTg00_hj7ZTg00`Lj8hTg01A8l<iTf3R;f2R9f1R7#cf0R83d'[p=0g01A]R=g00FaR>P6P0P3g01B<f5R3f4R6P;P9P7P8M<Dp=]P=P>P1P0P2g01CeR?P;P9P7g00fWR@g00G?RAP8M<Dp=Y14A8p=7P>P7g012EP8CIp=@P7g00aWRBg00b6RCPCg00bVRDP8g00c6FZp=5P;PBPCPCPDP9P7P8Ghp=;P=P>P1P0P2P?P3P6P;P9P7P8M<Dp=LP=P=P>P>P<P0P0P;g01DGP9P7P8M<ip=^g00G]R0#6R<#6R?#6#6#6#6#n#XR2/P2R2P2P8p,1LR1C0RE/87%H7RF%?8XI>RG,=>RH[[^4>RIX5=18E@1U98RJ%?9%H8RKP2P2P;P1C0,2E':X0>,=>'MRLP4%?;RMP2P2P6P1C0RN,2E,:KX0>,=>ROPHP8%?6P>PGP3P8CmWEP8O1RGP2P2P3P1C0RP,2E,:KX0>,=>RQP:P>P2P2f6P1C0,2E,:KX0>RRPHP8P2P2f8P1C0RS,2E,:KRKP5PFP2P2P7P1C0P2P2f9P1C0'2RTPHP8%H;RUP2P2f<P1C0,2NRNP2P2f=RVP1C0RW,2P%1PRX%1WRY'GRZPPPX13>XR[PWPY13>YE]P8CFRYPZP2P2f>RWP1C0R\/8@%1\R]/4AR^P\P]13>]R_13>ACYPVCFP^P2P2f7P1C0R^#9%1^#7P2P2f@R^P1C0R`#9%1`#7p-0R`g00dNRa%>@Rb#>,C>1C>b1C>@5K>5K>g00g6'W%Va3TR@%QaRaP>1B>7P91B>9CA%O>Rb%N>Rc1J>ARd1<><R<'@,5c%RCRePc%S0,<>Rf/@d,5cPePcP>P<g01B^RdPfCI,5cPePcPBPCPCPDP6ElC;C;C;1kcDRDP8P9g00e:RCg00eZRB'31j89=gCBdAf>A7CeRBb<b>b?X2>X3>W=%78149A1G9;P3[[[^2>^3>^=`P8PHP2P2fBP1C0#1P2P2f:P1C0#1P9P;P6O6b;bBbAb8b:W9WGP7P8O2n2001000000121000000W1X0>P7P8O2n2001000000121100000W1P8O1n200100000021000011000bCX6FW7X4>%>9,8EPJPLP4PMPOPHP8PGP:P>PRPHP8P5PFPTPHP8PWP3f?RW,8P%1WRH,4XPPPXP[PWPH13>HELPYPZ%>^RZ,8\%1^RY%_0RH'E,4]RWP\P]P_PZ1E8HXJ>RZPYO1PZP^PY13>YC^ELPVCFPWfARW#9%1W#7%9S%1S#7P2P2PWP1C0RW#9%1W#7P@PaP>P>1B>;P9%`>RaCAP7PaCAPbPc1<>?R?1J>H9a><'@,5cPePcP>1<>0R0PdP?CI,5cPe1@0<,5cC;C;PDPBb<b>b?X2>X3>X@>1E7H,491G7;149;[[^2>^3>^@>P8P2P2fCP1C0#1fE#1P2P2f;P1C0#1P6P3O5b;bHbBbAb8b:CbP7O3X9NXDUP7P8O2n2001000000121000000X1KX0>P7P8O2n2001000000121100000X1QP8O1n200100000021000011000bCX6FW7X4>XFIX5=P8C\X5=o"). Qed.

  (* [comment removed for export] *)
  Theorem free_gap_of_slack :
    bottomup_floor + nZ + gap_weight nZ L <= alloc_ceiling ->
    exists g, g mod page_size = 0 /\ bottomup_floor <= g /\ g + nZ <= alloc_ceiling
              /\ region_free L (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"; "Gap"] "h04__x1h17__arithh24__ffh38__varmaph45__with54__x2h64__x3h74__x4h84__x5h91Hh:4Hinvh;6Hslackh<1zp;2p;3p;1p;6p;4p;7p;8p-1p10000p4p710R0p8p1000Gp4p70R1g0017R2p4p710R3p8P1P0p8P1p1001Qp4p710R4p8P1p1001mp4p710R5p8P1p1002Kp4p7210R6p8P1g002hR1p4p710R7p8p1003Fp6051000R8p1004Op4p710R9p8p1005Ep6051000R:P9p8P:p1006Op4p710R;p8P:p10071p4p710R<p8p1007Np4p70R=P3p8P=P0p8P=P4p8P=P9p8P=p1008<p4p710p8P=P5p8P=p1008Yp4p710p8P=P6p8P=P8p8P=p1009Tp4p710p8P=P:p8P=p100:Np4p710p8P=P7p8P=P<p8p100;Jp4p7210R<P3p8P<P0p8P<P4p8P<P5p8P<P6p8P<P7p8P<p100<6p4p710p8p100==p6051000R<P0p8P<P;p8P<g012lR<p4p710p8p100>`p4p70R;P3p8P;P0p8P;P4p8P;P5p8P;P6p8P;P7p8g00M\j22Tg011@j2BTg00?Vj21Tg00JWj2>TP2j3;Tg00@2j14Tg00BIj1TTg00IAj1NTg00h9j2LTg013Gj1HTP<j3FTg00Anj2ETg00H\j15Tg00@Wj1ZTg00HBj2ATP1j6XTg00PSj1WTg00Q3j1VTg00\6j2:Tg00R1j1STg00ROj1RTg00]Tj26Tg00TAj2MTg00Tcj2KTg00UOj3ITg00Unj4JTg01YXj4GTg00XPj1?Tg00Xoj29Tg00ZAj3@Tg00Zjj2OTg00[Vj3PTg00QSj1QTg00\Tj4=Tg00]2j1UTg00^Zj3<Tg00nYj4CTg01Dkj1`Tg016@j2_Tg01;Mj1^Tg01Zgj4]Tg00_=j4\Tg00_hj7[Tg00`Lj8YTf0R1#4#4p=0%41#5p=a%41#5#4#5p=3g00FaR<f1R2g012EP1C\p=7P2g00aWR7g00b6R;P;g00bVR6P1g00c6F[p=8f3R5P7P;P;P6f2R7P2P1GYp=Dg01SOR4p,2nZR0'2R3p,1LR=,B0R:'2g01TSR8'1g00cVR9,>4g00G?R>5;<1144R?g00G]R@#4RA#4RB#0#0#T#NRC/LCRC%H4RD;F=RE,B0RF,23/18R3'EP<%5ARG#a#3#3#3#3#3#3#3#5#0#0#0#0#0#0#Z1>19=;<>X<<1A<>P4g01VeEXP?P3g00dNR3#WR?%V3R91:<2%S<RH%R<RI16<@RJ/7J'81MI6R6P1P7g00e:RKg00eZRL'A1K17=;KLdAI<>2CJR>b2b3b4X0<1111^0<P1P4O1b1P0PDP=p,3HnZCG11F:g00fWR=#?RD#?,9<19<D19<=5@<5@<g00g6'O=P3?P9P<P<f4R9,:<P7%Q<R?C=P2P<f5R3,:<P5P?C=C=PHPI%5@,6<R@16<GRG'7,8I%U;R;PI16<A9<<JRJ=<<G16<BRB'7,8IP;A<<J@/7B,8ICDCDP6P>b2b3b4X0<X5<X6<X7<X8<11791227/23/191275/29/13[[^0<^5<^6<^7<^8<P1P:P8PFP0P4P2P7O7b1b9CCCC%`41_CEREP4%^EP1C]b:W;o"). Qed.
End Gap.

(* [comment removed for export] *)
Lemma gap_weight_bound : forall nZ N l,
  0 <= nZ ->
  Forall (fun p => bv_unsigned (snd p) <= N) l ->
  gap_weight nZ l <= Z.of_nat (length l) * (N + nZ + 4095).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"] "p'0h04__x1h14__x2h21lh31pi001ph41xh57__arithh64__ffh78__varmaph85__with94__x3h:4__x4h;4__x5h<1Hh=3HnZh>2Hsh?2IHh@1NhA2_HhB1bi011bhC4cstrhD1mhE1nhF2nZhG1shH1yhI1zp;1p;2p;3p;4p;6p;7p;<p;Bp;8p-1p10000p4p710R0p8p1000Gp4p70R1g00HBR2p4p710R3p8P1P0p8P1p1001Qp4p710R4p8P1p1001mp4p710R5p8P1p1002Kp4p7210R6p8P1g002hR1p4p710R7p8p1003Fp6051000R8p1004Op4p710R9p8p1005Ep6051000R:P9p8P:p1006Op4p710R;p8P:p10071p4p710R<p8p1007Np4p70R=P3p8P=P0p8P=P4p8P=P9p8P=p1008<p4p710p8P=P5p8P=p1008Yp4p710p8P=P6p8P=P8p8P=p1009Tp4p710p8P=P:p8P=p100:Np4p710p8P=P7p8P=P<p8p100;Jp4p7210R<P3p8P<P0p8P<P4p8P<P5p8P<P6p8P<P7p8P<p100<6p4p710p8p100==p6051000R<P0p8P<P;p8P<p100>Dp4p710p8p100>`p4p70R<P3p8P<P0p8P<P4p8P<P5p8P<P6p8P<P7p8g00@2j16Tg00BIj1oTg00IAj1ZTg00h9R7j2RTg00Q3j1OTg00?VR<j20Tg015cj3ITg00EHj2:Tg01[fj3CTg011@j23Tg016@j25Tg016`R6j11Tg00H\j1?Tg00@Wj1KTg00M?R5j2<Tg017Xj1_TP2j29Tg01\Gj4\Tg00PSj1JTg00\6j2DTg00QSj1WTg00\Tj4@Tg00R1j1VTg00ROj1UTg00S:j2BTg00]Tj28Tg00^7j3ATg00TAj2QTg00Tcj2PTg0017j3STg00UOj3TTg00Unj4nTg01<Cj4mTg00[Vj3HTg00iSj4NTg01\jj1gTg00M\j24Tg019Fj1fTg00XPj1ETg00Xoj2GTg00ZAj3LTg00Zjj2aTg00]2j1`Tg01DGj1bTP1j6cTg01]Hj7dTg01A8l<eTg01]klB^Tg01?El<]Tg00^Zj3hTg00_=j4iTg00_hj7jTg00`Lj8kTf0R1#?#?p=;f4R2f3R4f2R0f1R3'4/41'<'0p=21403/41p=Fg01A]R;g00FaR=P=P=P6P6P4P0P3g00fWR6g00G?R:P1M<ep=[P=P=P=P=P=P=P5P1P3P0P5P4P2P:f5R5f6R8f7f8R9MB^p=YP=P=P<P5P<P2P:P:P4P0P3P1M<]p=XAh=31p=7P=P3g012EP1Cip=>P3g00aWR<g00b6R>P>g00bVR?P1g00c6Fjp==1<31,00p=lP4P<P>P>P?P0P3P1Gkp=Mg00G]R<#6R@#6RA#6#6#6#6#oRB#ZRC/RCRD#ORE10:0AICC1,:BRF/04X3D=CD3PD10F2X3D135115D1#1P2P5%?<RG#;#;#;#;#;#KRHD2X2E%16RIAF42HRJ'<RK,0:1<:JRL,0:P1X4=RM1031#_XH=X4=19=:RNPKPLPMPMPMP=P=g01^Q1<31C\,9=XD=XE=PIPMPM%11,9=X4;PNC[PJPJ19=JM9YEXg00dNRN#JR;%ONRMP=1D=0P3%W=RIC@%V=RL%U=RK1B=:RO18=<RP18=@RQ'71B=HRR'7RS9A=O'>'=1QK?R?P1P0g00e:ROg00eZRT'91P10=SOTdAT=:3CnRTb6b7b8X0=X1=P:P:P1P3PHD2^0=^1=P1P5P2O2b5Cm%JDRO,3215DO#1;lJeP7PCPCAICC3,:B/0810F9X3D=CD3f9R7/3015D0#1RJP9P7PHD2f:R9AHD24RO'315DO#1P7P9PHD2[[[^2EP1PCPCP0P3CN9ICC,:B/07f;R7,0FX3D=CD3f<RF/30PJP7PFPHD2P=15D4R7#1RJ#g1:B5f>R9'413927FHP1f=ROP9PHD2XI=%f710:J%E6RJ#E,G=1G=J1G=65L=5L=g00g6'a=HN;PMP=P=1D=2P0PIC@P3P=1D=5P4PIC@C@PLPK18=GRG18=ARA%?@,8=R@/7Q/7RRR5A='>,=K%`>R>PK1>P@,=KP>17SG%K<R<,B=,7A=A=R'>,=KCMCMP?PTb6b7b8X0=X1=X9=X:=X;=P0P4P2P3PHD210351404?FH2145<P8P4PHD2[[^0=^1=^9=^:=^;=P1P915D5#1f?R9/35P91:B8P0P2O7b5bC%E7#1%b7EcPCPCP5P2CN=HD4R4,3O15D4#1PFPOPHD2eW?WAW>X2EXGCXBCP3P1O2n2001100010121101101X4DP0P1FdW<W=W2X@=XF=o"). Qed.

(* [comment removed for export] *)
Fixpoint gw_sizes (l : list (word * word)) : Z :=
  match l with [] => 0 | iv :: r => bv_unsigned (snd iv) + gw_sizes r end.

Lemma gap_weight_sizes : forall nZ l,
  gap_weight nZ l = gw_sizes l + Z.of_nat (length l) * (nZ + 4095).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"] "p'0h01lh14__x1h24__x2h34__x3h44__x4h51zh62IHh77__arithh84__ffh98__varmaph:5__with;1ah<1bi001bh=4cstrh>2nZh?1si011pp;1p;2p;3p;4p;7p;6p;5p-1p10000p4p710R0p8p1000Gp4p70R1g0017R2p4p710R3p8P1P0p8P1p1001Qp4p710R4p8P1p1001mp4p710R5p8P1p1002Kp4p7210R6p8P1g002hR1p4p710R7p8p1003Fp6051000R8p1004Op4p710R9p8p1005Ep6051000R:P9p8P:g006OR;p4p710R<p8P:p10071p4p710R=p8p1007Np4p70R>P3p8P>P0p8P>P4p8P>P9p8P>p1008<p4p710p8P>P5p8P>p1008Yp4p710p8P>P6p8P>P8p8P>p1009Tp4p710p8P>P:p8P>p100:Np4p710p8P>P7p8P>P=p8p100;Jp4p7210R=P3p8P=P0p8P=P4p8P=P5p8P=P6p8P=P7p8P=p100<6p4p710p8p100==p6051000R=P0p8P=P<p8P=p100>Dp4p710p8p100>`p4p70R=P3p8P=P0p8P=P4p8P=P5p8P=P6p8P=P7p8g00@2j17Tg00BIj1\Tg00IAj1VTg00h9R7j2MTg00Q3j1HTg011@j26Tg01_5j14Tg016@j25Tg016`j11Tg00H\j1;Tg00@Wj1<Tg00M\j20Tg00HBj2FTg00PSj1ETg00[Vj3DTg00EHj2BTg00XPj1ATg01\jj1XTg019Fj1WTg00?Vj2UTg00\6j2@Tg00QSj1TTg00\Tj4>Tg00R1j1QTg00ROj1PTg00]Tj29Tg00S:j2=Tg00^7j3CTg00_=j4LTg00_hj7NTg00TAj2KTg00Tcj2OTP2j3?Tg00UOj3JTg00Unj4RTg01DGj1STP1j6ITg00iSj4[TP;j5ZTg00M?j2GTg00^Zj3YTf0R;#;#;p=8g00FaR1f3R2f2R=f1R6/G;'03?p=21G6;,0=p=:AY16;p=3g00G]R5#7R4#7R0#7#7#7#7#\R3#VR</M<R>#HR:P>16=;%4;R815>;#1R9%;5R?#8#8#8#8#8#<R@,0=C2X0:g00G?RAg00fW#1106@RB3:,F1%E>RC,66%4C15>C#1PBC2eP7P<P<f4R7/6;P8P9107@C2f5RCAD>=6RD'6%4D15>D#110C@C2[^0:P;f7RC/6;P8P910C@C2P1%4615>6RC#1R9f8R8/0@RD3:1B32REf9RF'0/0@RG/0;%4=RH,0ERE15>=RI#A#110F@RFC2X51P1%X9%1I=:HF,0GPEP;PFC2X51%WC1UA9g00dNR9#E%H9P1P11@17P=%T1C>P61@12C>%Q1%P1R9g00aWg00b6RFPFg00bVRFP11915RE1914R4'31=1@RG'3191?R?1910R0134GRG5C1'3'3g00a013E?%<5R5,=1,30=C1G'3CLg00c6FN1K9FP;P=g00e:RFg00eZR9'F1O;==?F9dAJ1A6CRb8b9b:X11X21X31X4110;6/0@A:=2B'010;=1025PBC2^11^21^31^41P;15>2#1%42f:1B37O4b7b=%AC#1%SCEI1686P;EIP<P<P2P=C[=D>6R=,68%4=15>=#1PDC2eW6X0:X?<X<<P6P;O2n2001101010121100100X;>P;DZW0X>1o"). Qed.

Theorem free_gap_of_totals : forall (h : VmMaps) nZ tot,
  0 <= nZ ->
  gw_sizes (vm_reserved h ++ vm_maps h) <= tot ->
  bottomup_floor + nZ + tot + Z.of_nat (length (vm_reserved h ++ vm_maps h)) * (nZ + 4095) <= alloc_ceiling ->
  exists g, g mod page_size = 0 /\ bottomup_floor <= g /\ g + nZ <= alloc_ceiling
            /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true
            /\ hint_placement_ok_b (Z_to_bv 64 0) h g nZ = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"] "p'0h01gh11Hh24__x1h34__x2h44__x3h54__x4h64__x5h74__x6h83Halh95Hbandh:2Hch;3Hflh<5Hfreeh=3HnZh>4Htoth?7__arithh@4__ffhA8__varmaphB5__withC4cstrhD1ehE1hhF2nZhG3tothH1zi001xp;2p;1p;3p;4p;6p;5p;7p;8p-1p10000p4p710R0p8p1000Gp4p70R1g00HBR2p4p710R3p8P1P0p8P1p1001Qp4p710R4p8P1p1001mp4p710R5p8P1p1002Kp4p7210R6p8P1g002hR1p4p710R7p8p1003Fp6051000R8p1004Op4p710R9p8p1005Ep6051000R:P9p8P:p1006Op4p710R;p8P:g0071R<p4p710R=p8p1007Np4p70R>P3p8P>P0p8P>P4p8P>P9p8P>p1008<p4p710p8P>P5p8P>p1008Yp4p710p8P>P6p8P>P8p8P>p1009Tp4p710p8P>P:p8P>p100:Np4p710p8P>P7p8P>P=p8p100;Jp4p7210R=P3p8P=P0p8P=P4p8P=P5p8P=P6p8P=P7p8P=p100<6p4p710p8p100==p6051000R=P0p8P=P;p8P=p100>Dp4p710p8p100>`p4p70R=P3p8P=P0p8P=P4p8P=P5p8P=P6p8P=P7p8g00?Vj22Tg00@2j17Tg00BIj1fTg00IAj1_Tg00h9j2wTg01_5j1MTg00M\j20Tg016@j2JTg016`j1ITg00H\j1CTg00@Wj1[Tg00M?j2DTg019Fj1mTg00XPj1XTg00Xoj2NTg00ZAj3WTg00Zjj2jTg00PSj1hTg00[Vj3gTg00Q3j1eTg00\6j2LTg00\Tj4KTg00QSj1cTg00R1j1bTg00ROj1aTg00]Tj28Tg00S:j2`Tg00^7j3^Tg00]2j1]Tg00TAj2\TP2j2ZTg00Tcj2YTg00UOj3vTg00Unj4uTg011@j2tTg01`8j2sTP1j6rTg01aCj4qTg00JWj2ATg00Dbj21Tg00j3R1j2=Tg01bOj49Tg00AnR2j23Tg01cXj5iTg00nYj4ETg00o4j4kTg01djj1QTg01edj1OTP<j3PTg00^Zj3nTg00_=j4dTg00_hj7oTg00`Lj8pTg0017j3<Tg00hYj3RTf2R<f1R7#Qf0R=#O3Pp=B%C=#Cp=@107=g01TSR6'2p=6g00FaR5?n7=p=:P5P7g012EP=Cdp=HP7g00aWR4g00b6R0P0g00bVR3P=g00c6Fop=Gf3R;P4P0P0P3P<P7P=Gpp=Tg00e:R4g00eZR>7<=p=Sg00G?R:9<5=p=Fg01SOR8/2=p=;f4R9%Q;%O<3P?R7==<4>p=?10<7/26/3=,3;,39p=5117=9R;<=<4>p=lf5R?%Q9%O;3P117=7R<=<4>p=4A<4=>,37p=>137=,3<p=U10<7/26/3=p=Vg01fZ12:7g00G]R@#7RA#7RB#7#7#7#7#fRC#_RD/wDRD?B;;#M/27108;/0<ABD99,JD#I%C@RE#@#@#@#@#@#[RF,0;RG'D'6ABD??RHP9P<P5%MH1JDHRI#IRJ109F'D'0108?/6=XH5%mI12:Jg00dNRJg00fWRI#XRK#X,N51N5K1N5I5W55W5g00g6'j%hJ3g%eJP5P51L59P<f6RJ,L5CKP7P51L5?P;%c5CKCK%b5%a5RI185@185AR@':RK%7E,85RL':185B1`5F,:@5^5R@':%CA,85RA'H,GI%]0R0PI185ERE/HL,GIP01:E@,:K/HA,GICTCT1\I3P=P<1Z4>1Y=<#SdAv5:7Cub@bAbBX25X35X45X55X65X7510=7/0?107F,D;'0/2912;J10<;1D?G,09'0/2J[[^25^35^45^55^65^75P=P?P6f7R6=BD6RG,JD#I%MGPJP8P<P;O8b?bC1t9H1s9HErCqg00cVRH,A=#FR<%;=R8P=P?PDPJPJ11C=RF11C?R>D?D5X05,=5P1P5P<P8P=PJPGPFPCPJClD5X05P<P8P=P6PDf8RJPJPFPCP6E411C:R:PJP=P6C9'>D5X05,=5P=P<P8P=PJPDf9RGPGPF11CJR1D?D5P21A7H#F%;7167GPDf:R4P411C711CGR4D?3UP<P8P=f;RIPDf<R3P3PFPCPIE4P:P3P=PIC9'>D5X05,=5P=1A;H#F%;91693PDf=R;P;11C911C3R3D?3UP2%;?PDf>R9P9P>11C;R>D?9V?;P<P8P=f?R9PDf@RAPAPFPCP9E4P:PAP=P9C9'>D5X05,=5P=%;6PDfAR6P6P1PCPAE49VJAP216G6PDfBR2P2P4PCP6E4P<P8P=fCR6PDfDR4P4PFPCP6E4P:P4P=P6C9'>D5X05,=5P=16I6PDfER6P6P3PCP4E4P5P<P8P=fFR8PDfGR<P<PFPCP8E4P:P<P=P8C9'>D5X05P;1A;H#F%;;RH16;6R<PDP8P8P>PCP6E4RCP:P8P;P6C9#SR>'3RD'3RF'3PGPHPFP?P<PDP7PCP>P=P:P8P;P6P?DiCECECECECkW<W:P7P=O2n2001000000121000000W1W;P7P=O2n2001000000121000000W1W8P7P=O2n2001000000121000000W1X05P7P=O2n2001000000121100000bDW9W>W=XG5XF5WEo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Definition ledger_split (l : list (word * word)) (K Y : Z) : Prop :=
  forall b s, In (b, s) l -> bv_unsigned b + bv_unsigned s <= K \/ Y <= bv_unsigned b.

Lemma ledger_split_nil : forall K Y, ledger_split [] K Y.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"] "h01Hh11Kh21Yh31bh41sp;1p;2p;4p;3p-1g00gbR0p4p710R1p8p1000Gp4p70R2p10017p4p710R3p8P2P1p8P2p1001Qp4p710R4p8P2p1001mp4p710R5p8P2p1002Kp4p7210R6p8P2p1002hp4p710R2p8p1003Fp6051000R7p1004Op4p710R8p8p1005Ep6051000R9P8p8P9p1006Op4p710R:p8P9p10071p4p710R;p8p1007Np4p70R<P3p8P<P1p8P<P4p8P<P8p8P<p1008<p4p710p8P<P5p8P<p1008Yp4p710p8P<P6p8P<P7p8P<p1009Tp4p710p8P<P9p8P<p100:Np4p710p8P<P2p8P<P;p8p100;Jp4p7210R;P3p8P;P1p8P;P4p8P;P5p8P;P6p8P;P2p8P;p100<6p4p710p8p100==p6051000R;P1p8P;P:p8P;p100>Dp4p710p8p100>`p4p70R;P3p8P;P1p8P;P4p8P;P5p8P;P6p8P;P2p8g00@2j10Tg00BIj1;Tg00IAj14Tg00h9j23Tg00iSj4:Tg00PSj19TP0j36Tg00EHj21Tg00M\j25Tg00?Vj22Tg00kJj27Tg01gQj38Tg00FaR0g00G]#0#0#0#0#0#0#;R2#4R;13;;R6P;P;f1R5f0R4C:%96R636g00f:f3,12R1f2,12'5f5'2f4/21'7P4n010000000W0X4;W3A8654eX20W1o"). Qed.

Lemma ledger_split_mono : forall l K Y Y',
  ledger_split l K Y -> Y' <= Y -> ledger_split l K Y'.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"] "h04__x1h14__x2h24__x3h32H0h47__arithh54__ffh68__varmaph75__with81Hh92HYh:3Hinh;1Kh<1Yh=2Y'h>1bh?1lh@1ohA1sp;1p;2p;3p;4p;7p;8p-1g00gbR0p4p710R1p8p1000Gp4p70R2g00HBR3p4p710R4p8P2P1p8P2p1001Qp4p710R5p8P2p1001mp4p710R6p8P2p1002Kp4p7210R7p8P2p1002hp4p710R2p8p1003Fp6051000R8p1004Op4p710R9p8p1005Ep6051000R:P9p8P:p1006Op4p710R;p8P:p10071p4p710R<p8p1007Np4p70R=P4p8P=P1p8P=P5p8P=P9p8P=p1008<p4p710p8P=P6p8P=p1008Yp4p710p8P=P7p8P=P8p8P=p1009Tp4p710p8P=P:p8P=p100:Np4p710p8P=P2p8P=P<p8p100;Jp4p7210R<P4p8P<P1p8P<P5p8P<P6p8P<P7p8P<P2p8P<p100<6p4p710p8p100==p6051000R<P1p8P<P;p8P<p100>Dp4p710p8p100>`p4p70R<P4p8P<P1p8P<P5p8P<P6p8P<P7p8P<P2p8g00@2j11Tg00BIj1WTg00IAj1JTg00h9j2ATg00Q3j1<Tg01gQj3;Tg00?Vj20Tg00iSj4ITP0j3CTg00EHj23Tg00M\j22Tg00kJR0j2=Tg00PSj1?Tg00\6j2>Tg00\Tj4VTg00R1j1UTg00ROj1OTg00]Tj28Tg00^Zj3NTg00H\j1MTg00]2j1HTg00TAj2DTP3j2ETg00Tcj2FTg0017j3GTg00UOj3BTg00Unj4KTg00n?j3LTg00XPj1:Tg00Xoj26Tg00ZAj39Tg00Zjj2@Tg00[Vj3PTg00oNj3QTg00_=j4RTg00_hj7STg00`Lj8TTg00FaR3f1R2g012Ef0R<CRp=5P2g00aWR7g00b6R6P6g00bVR5P<g00c6FSp=4f3R1P7P6P6P5f2R7P2P<GTp=7g00G]R4#1R;#1#1#1#1#1#WR=#JR:/A:R8#<A;1721027P:P:P2P<CIf7R95C8f4R8P7P2P<O313=7R>13=2'2/09f6R?/0>'=P013=1R0/2>f8R>'0109013=8R@/20f9R0'0RA109@'=P<f5RB,3=RC/2@f:RD'0RE10>CRFg00dNRG#?RH%<GRIP31>37P21>31CVRJ%U3RK%O3RL1834RM183;R;5N3%M4,83R4'5,4LRN%H6R6PNC71DL5R5P<P7g00e:RNg00eZRO'E1F<7=GNOdg00G?=B32CKROb5b6b7X03X13X2312<2/071227/01[^03^13^23P<f;PC13=?R?P2O4b43LX3AP<O110>@g00fWR@#:R>#:,63163>163@593593g00g6'@=PGHPIPJPKPL154;,4LP6PL15M4,4LP615M;,4LC7C7P5POb5b6b7X03X13X23107210211071[[^03^13^23P<PDP?P0P2P9O5b49QEFW3P<O1n200100000021100011000b@W:XA:X>:A;B87eW9W8X=3X<3X;3W?o"). Qed.

Lemma ledger_split_cons : forall l K Y b s,
  ledger_split l K Y ->
  bv_unsigned b + bv_unsigned s <= K \/ Y <= bv_unsigned b ->
  ledger_split ((b, s) :: l) K Y.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"] "p'0h02H0h12b'h21eh32s'h41Hh53Hbsh63Heqh73Hinh81Kh91Yh:1bi001bh;1lh<1si011pp;1p;2p;3p;4p;6p-1g00gbR0p4p710R1p8p1000Gp4p70R2g0017R3p4p710R4p8P2P1p8P2g001QR5p4p710R6p8P2g002KR7p4p710R8p8P2P7p4p7210R9p8P2p1002hp4p710R2p8p1003Fp6051000R:p1004Op4p710R;p8p1005Ep6051000R<P;p8P<p1006Op4p710R=p8P<p10071p4p710R>p8p1007Np4p70R?P4p8P?P1p8P?P6p8P?P;p8P?p1008<p4p710p8P?P8p8P?p1008Yp4p710p8P?P9p8P?P:p8P?p1009Tp4p710p8P?P<p8P?p100:Np4p710p8P?P2p8P?P>p8p100;Jp4p7210R>P4p8P>P1p8P>P6p8P>P8p8P>P9p8P>P2p8P>p100<6p4p710p8p100==p6051000R>P1p8P>P=p8P>p100>Dp4p710p8p100>`p4p70R>P4p8P>P1p8P>P6p8P>P8p8P>P9p8P>P2p8g00@2j13Tg00BIj1?Tg00IAj1=Tg00h9R2j2<Tg00Q3j1>Tg01gQj39Tg00EHj22Tg00M\j26Tg00?Vj21Tg00kJR>j25Tg00iSj40Tg00[Vj38TP0j37TP3j34TP7j6;TP5j6:Tg00G]#3#3#3#3#3#3#?R5#=R7/<7R3#>g00FaR0f4R9f3R8f2R6391256R1f1R4,25R='6/191181'5P7P7P4f0R?C0P7P7f5R<P9C0R:f8R;583573P>P7P7f6R>P<C0P7P7P6P4C0R@543f9RA973@1258R@/61/1A11;@'5P?P7P7f7R@P>C0P7P7P8P6C0R6543P3P7P2P7P7P7P?P?n2001101000120100100X23P7P7P;P@C0P7P7P9P8C0P?E;A47@8P3P7P2P7P7P7P?P4n2001101000120100100X23P7P7PAP;C0P:P4E;A47A<f:R4=47>R:P7f;R2A472@125;,6=f?R;'1f>R1/1='5[X17P7P2f=,25R2125?'6/1;1112'5X37PAP@P?E:X0:P@P?E:W0P?O1b0P?O1b0W6P?O1A7364P>P9P8P?O3W7P?O1n200100000021100010000W0X37X17A836>?9<9eW5W4X<7X:7X90W8W;o"). Qed.

Lemma ledger_split_app : forall l1 l2 K Y,
  ledger_split l1 K Y -> ledger_split l2 K Y -> ledger_split (l1 ++ l2) K Y.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"] "h03Hinh11Ah21ah31lh42l'h51Hh62H1h72H2h81Kh91Yh:1bh;2l1h<2l2h=1sp;1p;2p;3p;4p-1g00gbR0p4p710R1p8p1000Gp4p70R2p10017p4p710R3p8P2P1p8P2p1001Qp4p710R4p8P2p1001mp4p710R5p8P2p1002Kp4p7210R6p8P2p1002hp4p710R2p8p1003Fp6051000R7p1004Op4p710R8p8p1005Ep6051000R9P8p8P9p1006Op4p710R:p8P9g0071R;p4p710R<p8p1007Np4p70R=P3p8P=P1p8P=P4p8P=P8p8P=g008<p4p710R8p8P=P5p8P=p1008Yp4p710p8P=P6p8P=P7p8P=p1009Tp4p710p8P=P9p8P=p100:Np4p710p8P=P2p8P=P<p8p100;Jp4p7210R<P3p8P<P1p8P<P4p8P<P5p8P<P6p8P<P2p8P<p100<6p4p710p8p100==p6051000R<P1p8P<P:p8P<p100>Dp4p710p8p100>`p4p70R<P3p8P<P1p8P<P4p8P<P5p8P<P6p8P<P2p8g00@2j11Tg00BIj1=Tg00IAj1<Tg00h9j2;Tg00Q3j16Tg01gQj35Tg00iSj44TP;j33TP0j30Tg00kJR0j22Tg01hXj4:Tg00EHj27Tg00M\j29Tg00?Vj28Tg00G]#1#1#1#1#1#1#=R;#<R2/;2R<#6R6g00FaR5f3R4f1R1f0R335f2R:=541P2P2P1P3C4f7R=f6R953<50<%63R7%61R>g00AnA34:19043f4R??014A0?1:'2[R@A043:A0431'2A3?4:90?1RA[f5RB?0:?A0B:4'2\AP4P:P1P3C:P1n2001000000120000000X2:W4W3X18P@^2:^4>^37^18P3P<f9R8f8R7P2P2P4P:C4R>P1O5A0<>8A0<>7'2P0P2P2P?P4C4R0f:R>50<A0<0817;BR017;?'9/881870'2P3P2P2PBP?C4R0f;50<P7P9PBP3O3W0P3O1A0<0>P=P9PBP3O3W0P3O1n200100000021000010000b0b5W0X=2X:2A3<B??54:eW7W6X95W8X<6W;o"). Qed.

Lemma ledger_split_app_inv : forall l1 l2 K Y,
  ledger_split (l1 ++ l2) K Y -> ledger_split l1 K Y /\ ledger_split l2 K Y.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"] "h01Ah12H0h23Hinh31ah41bh51lh62l'h71sh81Hh91Kh:1Yh;2l1h<2l2p;1p;2p;3p;4p-1g00gbR0p4p710R1p8p1000Gp4p70R2p10017p4p710R3p8P2P1p8P2p1001Qp4p710R4p8P2p1001mp4p710R5p8P2p1002Kp4p7210R6p8P2p1002hp4p710R2p8p1003Fp6051000R7p1004Op4p710R8p8p1005Ep6051000R9P8p8P9p1006Op4p710R:p8P9g0071R;p4p710R<p8p1007Np4p70R=P3p8P=P1p8P=P4p8P=P8p8P=g008<p4p710R8p8P=P5p8P=p1008Yp4p710p8P=P6p8P=P7p8P=p1009Tp4p710p8P=P9p8P=p100:Np4p710p8P=P2p8P=P<p8p100;Jp4p7210R<P3p8P<P1p8P<P4p8P<P5p8P<P6p8P<P2p8P<p100<6p4p710p8p100==p6051000R<P1p8P<P:p8P<p100>Dp4p710p8p100>`p4p70R<P3p8P<P1p8P<P4p8P<P5p8P<P6p8P<P2p8g00@2j11Tg00BIj1=Tg00IAj1;Tg00h9j27Tg00Q3j14TP;j32Tg01gQj33Tg00iSj46TP0j30Tg00kJj25Tg01hXj48Tg00n?j39Tg00oNj3:Tg00nYj4<Tg00G]#1#1#1#1#1#1#=#;R0/70R;#4R2g00FaR<f3R6f2R552;f1R4f0R133f4R3?354R:A3654R=P0P0P4P1C6R9f650;P6P5P4%41R7%44R>g00AnA26549061A0346A0345'5R?[A0615A0614'5A23659034[R@f5RAA2A36705\?P6P5P4P1C8P1n2001000000120000000X35W6W5X08R?P@^35^6>^57^08R8P1P;f8R7f7R>P0P0P6P5C6R@A0;@7R3A0;@>RB;94O5b1O3W2X70X40P:eA0;9AP6P5P4P?P8P1P;P7P>P@A:3B4O5b1O3W2X70X40P=eC<W8X:<W9X<2W;o"). Qed.

(* [comment removed for export] *)
Lemma ledger_split_incl : forall l l' K Y,
  ledger_split l K Y -> incl l' l -> ledger_split l' K Y.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"] "h01Hh13Hinh25Hinclh31Kh41Yh51bh61lh72l'h81sp;1p;2p;3p;4p-1g00gbR0p4p710R1p8p1000Gp4p70R2p10017p4p710R3p8P2P1p8P2p1001Qp4p710R4p8P2p1001mp4p710R5p8P2p1002Kp4p7210R6p8P2p1002hp4p710R2p8p1003Fp6051000R7p1004Op4p710R8p8p1005Ep6051000R9P8p8P9p1006Op4p710R:p8P9p10071p4p710R;p8p1007Np4p70R<P3p8P<P1p8P<P4p8P<P8p8P<p1008<p4p710p8P<P5p8P<p1008Yp4p710p8P<P6p8P<P7p8P<p1009Tp4p710p8P<P9p8P<p100:Np4p710p8P<P2p8P<P;p8p100;Jp4p7210R;P3p8P;P1p8P;P4p8P;P5p8P;P6p8P;P2p8P;p100<6p4p710p8p100==p6051000R;P1p8P;P:p8P;p100>Dp4p710p8p100>`p4p70R;P3p8P;P1p8P;P4p8P;P5p8P;P6p8P;P2p8g00@2j10Tg00BIj18Tg00IAj14Tg00h9j23Tg00Q3j17Tg01gQj32Tg01i7j36Tg00iSj41TP0j35Tg00G]#0#0#0#0#0#0#8#4R0/30R2#7R;g00FaR6f3R5f1R4f0R132f4R39625P0P0P4P1C1f6552P3f2R2P4P5P0P0P2P4C1P1O2O3W1X80X50A2352eW2W0X46W3X7;W6o"). Qed.

Lemma ledger_split_filter : forall f l K Y,
  ledger_split l K Y -> ledger_split (List.filter f l) K Y.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"] "h01fh11lh21xh31Ah42H0h52Hxh61Hh72H1h81Kh91Yp;1p;2p;3p;4p;5p;6p-1g00gbR0p4p710R1p8p1000Gp4p70R2g0017R3p4p710R4p8P2P1p8P2p1001Qp4p710R5p8P2p1001mp4p710R6p8P2p1002Kp4p7210R7p8P2p1002hp4p710R2p8p1003Fp6051000R8p1004Op4p710R9p8p1005Ep6051000R:P9p8P:p1006Op4p710R;p8P:p10071p4p710R<p8p1007Np4p70R=P4p8P=P1p8P=P5p8P=P9p8P=p1008<p4p710p8P=P6p8P=p1008Yp4p710p8P=P7p8P=P8p8P=p1009Tp4p710p8P=P:p8P=p100:Np4p710p8P=P2p8P=P<p8p100;Jp4p7210R<P4p8P<P1p8P<P5p8P<P6p8P<P7p8P<P2p8P<p100<6p4p710p8p100==p6051000R<P1p8P<P;p8P<g00>Dp4p710R<p8p100>`p4p70R;P4p8P;P1p8P;P5p8P;P6p8P;P7p8P;P2p8g00@2j12Tg00BIj1>Tg00IAj17Tg00h9j26Tg00Q3j15Tg01gQj3;Tg012lj33TP0j30Tg00AnR0j24Tg01iPj48Tg01inj59Tg01i7j3:Tg01jKj6=TP3j3<Tg00e:R3f0R2g00eZ3<p=1g00G]#2#2#2#2#2#2#>#7R;/6;R;P3[%5;g00FaR7f2R6f1R5;;2f3R1f4R4=3;1R=P6P5P2f5R:=3;490;2P3\2R3%56R8P0A31629015A0465P1P6O1#1'4[R0A0152P6P5O1#1'4A34159046R9[A0:16P4P1O1#1'4\9P1P6P5P2C8P5n2001000000120000000W1X25W0X3<P0^18^25^03^3<P2P;f7R<P6f6R3P5O5A0;63P<P6O1#1'4A0;1<R<f8P1O1#1P<f9P4O1#1P5W7X4<P2D9b5b4W5X2;A:;=1eE=W6X97W8W1W0o"). Qed.

(* [comment removed for export] *)
Lemma ledger_split_window_free : forall l K Y nZ,
  0 <= K -> 0 < nZ -> K + 2 * nZ <= Y -> Y < 2 ^ 64 ->
  ledger_split l K Y ->
  region_free l (Z_to_bv 64 (Y - nZ)) (Z_to_bv 64 nZ) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"] "h04__x1h14__x2h24__x3h32H0h47__arithh54__ffh67__sat65h77__sat66h88__varmaph95__with:1Hh;2Hah<4__x4h=4__x5h>2b1h?2b2h@1xhA1yhB1zhC2HKhD2HYhE4HY64hF5HhighhG3HinhH4HlowhI3HnZhJ6HsplithK1KhL1YhM1bhN1lhO2nZhP1ohQ1sp;1p;2p;3p;4p;6p;7p;8p-1g00gbR0p4p710R1p8p1000Gp4p70R2g0017R3p4p710R4p8P2P1p8P2p1001Qp4p710R5p8P2p1001mp4p710R6p8P2p1002Kp4p7210R7p8P2g002hR2p4p710R8p8p1003Fp6051000R9p1004Op4p710R:p8p1005Ep6051000R;P:p8P;p1006Op4p710R<p8P;p10071p4p710R=p8p1007Np4p70R>P4p8P>P1p8P>P5p8P>P:p8P>p1008<p4p710p8P>P6p8P>p1008Yp4p710p8P>P7p8P>P9p8P>p1009Tp4p710p8P>P;p8P>p100:Np4p710p8P>P8p8P>P=p8p100;Jp4p7210R=P4p8P=P1p8P=P5p8P=P6p8P=P7p8P=P8p8P=p100<6p4p710p8p100==p6051000R=P1p8P=P<p8P=p100>Dp4p710p8p100>`p4p70R=P4p8P=P1p8P=P5p8P=P6p8P=P7p8P=P8p8g00@2j1>Tg00BIj1{Tg00IAj1hTg00h9j2_Tg00Q3j1ZTg00@Wj1UTg00M?j2LTg00A5j2^Tg00ARj29Tg01gQj3\Tg01S2j23Tg00Dbj2ATg00iSj4xTP0j3vTg00EHj20Tg00M\j25Tg014Ij22Tg00jlj2?Tg00Idj2gTg00CMj1eTg00AnR0j2ITg00?Vj26Tg00kJR8j2MTg00kdj2cTg01P3j2bTg01H;j2aTg01Hcj3`Tg00XPj1ETg00Xoj2BTg00Zjj2JTg00PSj1]Tg00[Vj3HTg00\6j2FTg00QSj1[Tg00\Tj4GTg00R1j1zTg00ROj1yTg00]Tj2DTg00^Zj3CTg00H\j1YTg00]2j1wTg00S:j2XTg00^7j3KTg01OPj3WTg00TAj2uTg00HBj2tTg00Tcj2pTP3j3TTg00UOj3oTg00Unj4nTg00n?j3mTg00oNj3lTg01kWj2iTg01l@j3jTg01IGj3kTg01Ijj2QTP2j6RTg00lFj4qTg01lij4rTg00ZAj3sTg00_=j4OTg00_hj7PTg00`Lj8NTg01>aj7dTg00G?R2f0R3'6p=41923p==f2R=f1R7'5/63p=7g00e:R6g00oh7T3p=1g00FaR5?s73p=:P5P7g012ER1P3COp=;P5P7g01B^P3COp=<P=g00aWR4g00b6R<P<g00bVR>P5P7P1P3COg00c6R1FPp=@f4R;P4P<P<P>f3R9P4P<P<P>P=P1FPP7P3GNp=8P7P4P<P<P>P3P1FPp=SP=P4P<P<P>P7P3Fdp=Vf6R1P4P<P<P>f5R:P;P9P4P<P<P>P=P7P3GNGNp=fg00G]R4#>R?#>R@#>#>#>#>RA#{RB#hRC/_CRD#Z%4=%=7%U?RE/L=RF=7;9%UARA,^ERG,9;RHf7RI?\1:f8RJ131:,AB1AB:PCPCP7P3Cxf:RK5vDP5f9RD/3JRL10B9RM10B='5RN,231ABD,0B,53,2M'?#1XB5P5PJ13KDRO/2N15O3,2M'?#1XB51gB710B7RO#4%eBRP,9O'IP;P9P=P7O3f;RO,6N16KM'MP810B;R8f<RN77M16O813NORM10B:RQ/58R8'215MO,2Q'?#1P3f=RM,68P01?73#1%1=%17R8'MRR[%13,M81?=7#1[R81?9=#1\R1c73P3n2001000000120000000X?6X>6RRP8^?6^>6R8P3f>RS/3MRT10BIRU10B1'5'2RV15TM,2URT%1VRW%1TRXP01273#1167=RY[163712=7#1[RZ129=#1\Y1b73P3n2001000000120000000XA5X@5RYPZ^A5^@5RZP3f?R[/3SR\10BJR]/5U1aEARU%=E%4A%=G[[R^%4ER_g010HR`A`EA7UW;RA%4G\`^;_R_P010BDR`#4Ra19`PR`10BORb10BKfBRcfARd'3Re37PI%4bRf10BN/9PRPg00dNRgg00fWRh#ERi#ERj#ERk,B5Rl1B5jRj1B5iRi1B5hRh':':':g00g6Rm'JRn%]gRo3H%ZgRpP5P51F5;P=%[5RqCGP7P51F5:P9PqCGCG%z5Rq%y5RrPr1D54Rs1D5?Rt5C5Ru%Y?,D5R?';%w<R<PrPr1X5ERv1D5@R@5K59C5?%Y4,D5R4';P<PrPr1X52R?/<@P<AW54@9@ruD8D8D81ur>R>P3P=g00eZRu,t61p3==T6udAo527CnR2b5b8b9X05X15X25X<5X=5A737;1LE;=7:9%=:13:1979;[[[^05^15^25^<5^=5P3fGfER1fFRu10BS10B[R[PDPcfCO8b4W3W:P7P3O2n2001000000121000000b6b7O3b33mO3b3WHP3O116NQPRP8P3PVPTPYPZP3P]15\SPUP^PAP_P0PaP`A7edbPIPoPpP51F5=P71F59CGRePqPrPr1;s4P<AW5stRd=C5t=@r4D8P>P2b5b8b9X05X15X25163=137=?7=9[^05^15^25P3P[P1PuPDO4b4X3PX:fP7P3O2n2001000000120000000b6b7O3b39lWXO3b3WFP3O1n200100000021100011000bPb:1ABJRX,0BPUP^PAP_%Ek,B5Rk1i5E=j5h,:i,:l':/Jm=HgoPpPePqPrPrAk5vBRl,<4P<PrPrAK5vs9C5t/;4P<PrPr1<?sP<PrPr1;?tP<A@r?s1<sl,SrRi5VrD8D8D8D8P>P2b5b8b9X05X15X2519=G1LE7=7=9%==%4;RE1IEH[[[[^05^15^25P3PNPMPOPIPJPDPKO7b4b6b7,QJER1ABLRE,0BPUP^PAP_1:jh,:k/Jm=Hgo9HgnPpPePqPrPiP<PrAK5vt9C54=@rsP<PrPr1<?tP<PrPr1;?4P<A@r?d1<dl,Sr5VrD8D8FfP>P2b5b8b9X05X15X25193GA79F7%=9%4:13;:R:#419:G'I[[[[^05^15^25P3PMPOPNPIPJPDPKO7b4b6b7,QLERPEPXP=P7Cq#1eWGXQCXMCCrWJWEWDWIWCXO5XL5XK5WNo"). Qed.

(* [comment removed for export] *)
Theorem null_hint_grant_above : forall h (a : word) nZ K Y,
  0 < nZ -> nZ mod page_size = 0 ->
  bv_unsigned a mod page_size = 0 ->
  Y mod page_size = 0 -> Y <= bv_unsigned (vm_mmap_base h) ->
  0 <= K -> K + 2 * nZ <= Y ->
  ledger_split (vm_reserved h ++ vm_maps h) K Y ->
  placement_ok_b h (bv_unsigned a) nZ = true ->
  bottomup_floor <= bv_unsigned a \/ Y - 2 * nZ < bv_unsigned a.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"] "p'0h04__x1h14__x2h24__x3h31Hh42Hah57__arithh64__ffh78__varmaph85__with91zh:3Hnoh;3Hplh<2H0h=2H1h>2H2h?2HBh@2HKhA2HYhB4HY64hC3HYBhD4HYalhE4HaAlhF3HflhG5HfreehH4HgAlhI3HgehJ3HlthK4HnAlhL3HnZhM4HnhfhN6HsplithO1KhP1YhQ6__sat0hR6__sat1hS1ahT1bi001bhU1ehV1hhW2nZhX1op;1p;2p;3p;4p;6p;9p;7p;8p-1p10000p4p710R0p8p1000Gp4p70R1g0017R2p4p710R3p8P1P0p8P1g001QR4p4p710R5p8P1p1001mp4p710R6p8P1p1002Kp4p7210R7p8P1g002hR1p4p710R8p8p1003Fp6051000R9p1004Op4p710R:p8p1005Ep6051000R;P:p8P;p1006Op4p710R<p8P;g0071R=p4p710R>p8p1007Np4p70R?P3p8P?P0p8P?P5p8P?P:p8P?p1008<p4p710p8P?P6p8P?p1008Yp4p710p8P?P7p8P?P9p8P?p1009Tp4p710p8P?P;p8P?p100:Np4p710p8P?P8p8P?P>p8p100;Jp4p7210R>P3p8P>P0p8P>P5p8P>P6p8P>P7p8P>P8p8P>p100<6p4p710p8p100==p6051000R>P0p8P>P<p8P>p100>Dp4p710p8p100>`p4p70R>P3p8P>P0p8P>P5p8P>P6p8P>P7p8P>P8p8g00@2j1>Tg00BIj1zTg00IAj1fTg00ARj20Tg00EHj23Tg00?Vj22Tg00@Wj1NTg00M?j27Tg00M\j2BTg00h9j2yTg01djj19Tg01edj1=TP=j3<Tg01gQj3pTg01mij3JTg01nmj1UTg00A5j2gTg00AnR=j2STg0204j1MTg01H;j2cTg01Hcj3bTg00XPj1QTg00Xoj2HTg00ZAj3PTg00Zjj2aTg00PSj1`Tg00[Vj3_Tg00Q3j1^Tg00\6j2OTg00QSj1]Tg00\Tj4LTg00R1j1\Tg00ROj1[Tg00]Tj2DTg00S:j2ZTg01IGj3xTg00_=j4KTg00]2j1wTg00TAj2tTg00HBj2YTg00Tcj2sTg00UOj3rTg00Unj4qTg01S2j21TP1j6ETg020oj3oTg021Ol9nTg00Dbj2;Tg00hYj3FTg022bj3ITg023dj3jTg024?j7iTg025Gj4TTg00kJR1j2RTg00n?j3hTg026Qj2kTg00H\j1lTg00^7j3mTg01OPj3GTg00^Zj3VTP2j3ATP4j6WTg00jMj2XTg00oNj3eTg00JWj2dTg00_hj7uTg00`Lj8vTf0R4g00cVR2'dp=5g00FaR8g00G?R>7A4p=:f1R7%M4'3p=612>4p=4g00e:R6g00eZR57A4p=?P7g00aWR0g00b6R3P3g00bVR<P4g00c6Fup=8P8P7g012EP4CKp=@f3R?P0P3P3P<f2R0P7P4Gvp=Cg01fZg00G]R;#>R9#>#>#>#>#>R:#zR@#fRA10>0%5?#:RBf5RC,3@#5#:f4RDf8RE,6@'2f6RF#4f7RG%N9RH/7E'B/2F1yAARAf;RI#9%=I3<?pEGf<RJ13@If:RK3J#?%UJ13@JRL#4%N:R:,gHRM,0L'Sf>RL#MRN#U13@NRN#410NM'S1cH:10>H%4:10>M[[%4HRNg010HROAbH:7UW4%4M\O^4NP=fARN,6@R:#410:M10LMP0fCR:,6@#4fDRP,6@RQ/0Mg00dNRRg00fWRS#QRT#Q,H81H8T1H8S5P85P8g00g6'a%`RRS3_%^RRRP81O80RTP7%]8CL%\8RU%[8RVP81D89R9g01B^RW1Z8HRX=x8@RYCK,8V%w3R3PV1D8;RZ/@9,8VP3P8PZPWPYCK,8VCCCC1tV<R<P4P01Y651s40#?dAr8>7CqRYb6b7b8X08X18107M1270100M[[^08^18P4fFRW,6@fBR[P7f=R\O4b5W<W3P7P4O2n2001000000121000000bQbR10IMP8%5JR]%5LR^'1#5%:4X98P8P>f?R_#5,14#5#:X98P8P>11>4#5#:X981Y8>P^PKEEP]PEEE11JL#5REAoJL2EE%:E%9N%=N5<AREPLP\P_PGPJPFP7PCM9n11\_,;@1;@_5FE#?P=13@NR=f@RE5J[#?13@[R_=I:NRG[RLAI[=EAJ:_N#?R_[13@:R2=IP[\_P[P=PE%4=10=M;jDP\PIPJFiP7n2001000000120000000PLP4PFO1PGP1g01SORG/22%9P%=P5<AP2P[PQCT13@PRQ,2GR217H:,1N/0Q'RP4fERN,3@RF,2GRG17HP,1[RL/0FRJ;h4XF2P4O1%9N%=N5<APQP:16@NCT1kLF12FL,RJP117HN,1:R:13@WR1'0121:17HW,1PRPfGR1,3@R:'0RLP4P4XJLP4O112:P17H1,1NfHR:,3@RP'0PSPRP8PTP71O8?CLRTPUPV%l;,D8R;Am8X95G8,@Z,8VP3AV8Z9AG8;9'@,8VCCP<PYb6b7b8X08X18X2817H7,10,241B7011?0'2[^08^18^28P4PWP:fIRH,3@P7O4b51BP111N1'2PSPRPTPUPV1@Z;,8VP3AG8Z9=V89/@;,8VCCP<PYb6b7b8X08X18X2812401170/B0/2?[^08^18^28P4fKR?,6@PHP1P[O4b511W:/B:fJRW,6@'2PC111HR1PKP7P4O4%9?%=?5<A1;@11;@H3Fg00ohRH5A6P6fLR1#9%=15<A11:W,;@1;@W3FAA64HXT6P4P5PKEWAA65HP6P5P6p-0P4POg00f:ROn0110000020000XU6g010dPHP4EWPO1XO4b3b:b:b>b='XWIP4O1n200100000021000011000bX9eGJWMP4O1n200100000021000011000b;b3bGbHbBb?b4W;WNWAW@WCXDBWEWKWLXP8XO8XW8WSWVo"). Qed.

(* [comment removed for export] *)
Theorem null_hint_grant_step : forall h (a n : word) nZ K Y,
  0 < nZ -> nZ mod page_size = 0 ->
  bv_unsigned a mod page_size = 0 ->
  Y mod page_size = 0 -> Y <= bv_unsigned (vm_mmap_base h) ->
  0 <= K -> K < bottomup_floor -> K + 2 * nZ <= Y ->
  ledger_split (vm_reserved h ++ vm_maps h) K Y ->
  placement_ok_b h (bv_unsigned a) nZ = true ->
  let Y' := Z.min Y (bv_unsigned a) in
  K < bv_unsigned a
  /\ (bottomup_floor <= Y' \/ Y - 2 * nZ + page_size <= Y') /\ Y' <= Y
  /\ Y' mod page_size = 0 /\ Y' <= bv_unsigned (vm_mmap_base h)
  /\ ledger_split (vm_reserved h ++ (a, n) :: vm_maps h) K Y'.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"] "h04__x1h14__x2h24__x3h34__x4h44__x5h57__arithh64__x6h74__ffh88__varmaph95__with:2H4h;6heq_Y'h<2z4h=1Hh>4__p1h?4__x7h@2H0hA6HsplithB1YhC4__x8hD1ohE1zhF2E1hG2E2hH2E3hI2HKhJ4HKflhK2HYhL3HYBhM4HYalhN4HaAlhO6HabovehP3HflhQ3HfvhR3HlthS2HmhT4HnAlhU3HnZhV5HpagehW3HplhX3HqnhY2HrhZ1Kh[2Y'h\1ah]1hh^1nh_2nZh`2qaha2qnhb2qyp%0p&0p;1p;2p;3p;>p;4p;5p;6p;7p;8p-1p10000p4p710R0p8p1000Gp4p70R1g0017R2p4p710R3p8P1P0p8P1p1001Qp4p710R4p8P1p1001mp4p710R5p8P1p1002Kp4p7210R6p8P1g002hR1p4p710R7p8p1003Fp6051000R8p1004Op4p710R9p8p1005Ep6051000R:P9p8P:p1006Op4p710R;p8P:g0071R<p4p710R=p8p1007Np4p70R>P3p8P>P0p8P>P4p8P>P9p8P>p1008<p4p710p8P>P5p8P>p1008Yp4p710p8P>P6p8P>P8p8P>p1009Tp4p710p8P>P:p8P>p100:Np4p710p8P>P7p8P>P=p8p100;Jp4p7210R=P3p8P=P0p8P=P4p8P=P5p8P=P6p8P=P7p8P=p100<6p4p710p8p100==p6051000R=P0p8P=P;p8P=p100>Dp4p710p8p100>`p4p70R=P3p8P=P0p8P=P4p8P=P5p8P=P6p8P=P7p8g00@2j1@Tg00BIk10@Tg00IAk10;Tg00ARj21Tg00JWj2YTg00EHj23Tg0204j1gTg00?Vj20Tg00@Wj1jTg00M?j25Tg00h9k20PTg01djj1LTg01edj1QTP<j3lTg01gQj3=Tg01mik30GTP2j3WTg0276j2:Tg027Sm>0BTg00kJR2j24Tg00H\j1BTg028cj2oTg00Lbj2^Tg00HBj2TTg029nj2dTg00XPj1MTg00Xoj2uTg00PSk10OTg00Q3k10NTg00QSk10MTg00R1k10JTg00ROk10ITg00]Tk203Tg00S:j2kTg00]2k10HTg00TAk20FTg00Tck20ETg00UOk30DTg00Unk40CTg00M\j2tTg00n?k301Tg01kWk200Tg01l@j3sTg00WQj1~Tg00Woj2}Tg00YXj3_Tg01OPj3{Tg00^Zj3rTg01S2j2NTg00oNj3hTg00iSj4eTg00[Vj3]Tg00AnS00j2;Tg02:Pk20>Tg02;5j2xTg02;ak30=Tg02<@k30<Tg02<_j2vTg02=?k509Tg02>Nj6zTg02?Zk708Tg02@fk60ATg00nYj4aTg00ZAj3[Tg00Zjk202Tg00\6k207Tg00\Tj4\Tg00^7k306Tg00_=j4bTg00_hj7mTg00`Lj8nTg02B1k705TP1k604Tg01>=k60KTg01>ak70LTf0R1#@#@p=>g00FaR<g00G?R77W1p=Xf2R=f1R6't/01p=6g01SOR5/01p=71561,N=p=E%@1#Bp>0?%@1#B#@#Bp=KAW<61p=2AW<61,;=p=P10=6/;1p=C1u<1p=RA[<61g00g6R4+02p=FA[<=6/x1p=Hg00dNR0?]61p=8207<1p=SP<P=P6P1C\p=<P<P<f4R3f3R;P=C\P6P1C\p=G203<1p=IB06<61p=ZP<P6g00a0R>P1Cbp=cP=g00aWR:g00b6R8P8g00bVR9P<P6P>P1Cbg00c6R>Fmp=AP<P6g01B^P1Cbp=VP=P:P8P8P9P<P6g012ER?P1CbP>Fmp=?P3P:P8P8P9P;P:P8P8P9P=P>FmP6P1Gnp=Df6R@P:P8P8P9f5RAP3P;P:P8P8P9P=P6P1GnGnp=9A[<61p=JA[<619[<=p=O20214p=|P=P:P8P8P9P6P1K05p=iP6P:P8P8P9P1P>Fmp=qP;P:P8P8P9P=P6P1Gnp=f1N=6/t1p=yP<P3P;P<P=P6P1C\C\p=pP<P3P;P=P6P1J04p=UP6P:P8P8P9P1J0Kp=wP=P:P8P8P9P6P1K0Lp=`P<P6P?P1Cbp>0:g01fZg00G]R?#@R:#@R>#@R4#@#>RB$0@RC$0;RD117=g00cVRE,Y;#XS0113C@/YE#XQ01f9RF#g,3C,03107@f7RG/15f8RH%j:RI/5F;6G20PDDRJf=RK#L%QK3l?=FHg00e:RLf>RM13CKf;RN40Gg00eZRO3Wf:RP13CM':P<f@RQf?RRPKf<RSPNPPPFPHPGP@PAP;P=P6N>0B13CRRT#7AENIK/1T'4g01Ve%B:S02$0?#K#K#K#K#K#K#K#B#>#>#>#>#>#>#j9W<5fART,3CRU/oP%>B#>#>#jRB,^U/5B,2U1oMP1^MB/5B,2M1oTK1^TBRU/5B,2TfDRV,3CS03/^BP<PUP<1^VBP<fCRUfGRW,3C':RX,T<12HXRXePXfHRX,3CRY,dV11VY1:VYRZ;PV12ZY9CYV'4fERZfIR[,3CR\':R]P<g00fWR^#MR_#MR`#MRa#MRb#RRc%R_R_1u<^R^/F_3H&0O0Rd'8&0N0R0%SAS04&0M<Re7<@S05P=PeP6%S@S06?<@eS07%S3S087<;DGS09&0J<Rf&0I<RgPg%I:Rh203<?Ri1k<BRj'Z'c&0H8R8Pg%B?Rk#IRl%B>#IRm/ZjS0:5AgS0;P8Pg%Bk#IRn%I4/ZjR45AgS0<P8PgPg1k<7/VhP8%j?Ro,k<Rp=?giDDF9DD20Fg9R9P1P=1TLO20E1==WLOdB0D<76H0CROb7b8b9X0<X1<X2<X3<X4<X6<151B,2615@BRL,2;Rq12ALRr117310o3[[[[^0<^1<^2<^3<^4<^6<P1PAP@fKR7,3CRsPWP[P3PGPHPFfFRtO:b5b<b:b;10o1P2%7YS0=AEVItS0>/1Y%7\RuAEZIWRv/tBS0?/0\'4PHfJRw,3CRx#7RyAEtIXS0@?6BxS0A<011XPuP1O111v\S0BQ0A1:txRv,T<12NvRzePz1dWs11Ws1:WsRz;PW12zs9CsW'4fLR{,3CR|,:XR}P<200<IS0C=s<c%~?,}<R?%RaRa5_<R~%R`R`/J_S0D'J%~:,}<S0E%MbS0F#RRb5_<AOc~_1J_^R~#|S0G3H3H/8dP0Q09PfPgA?gpmS09P8PgQ0:9AghS0HP8PgPg1ci4P8PgPg1ZnjS0I,clP8PgPg1k<IS0J/Zh9{<iRp/VlP8Ar<pjS0K=?glS0LDDDDDDF9P9POb7b8b9X0<X1<X2<X3<X4<X6<10oA12=LRp15IAS0M,N3/1@15I@S0N,NA?6BG[\r\p[[^0<^1<^2<^3<^4<^6<P1PGPHPFfNRm,3CR:P{PwP@PPPNPSP3O;b5b<b:b;5hyWRP1O1n200100000021000011000Q0=Q0>?6BY'411t\%7PQ0?/0P'4S0?10PZS0=1YPB#XS0>%gw,3C,0PS0A%LwS0OPDPDP[PXCe%QwS0P5]J5lJ?=tPS0Q';S0R';S0S';S0T';P2PuQ0B11WxPF1T<z12SzS0BeS0UQ0B1dX|S0V11X|?P}X12}|9C|X'4S0WfMRu,3CRY,:[S0XP<Q0F#MS0F#M#RS0Y1J`^'FQ0Y/F~/8d'8P0%SGS0Y?<3eP=Q04P6%SHPHPeP;Q06DGDGPfPg%@k#IRk=?gh%I>R>Q0J/ZlRl5{<S0J=r<j=?gh5igP8PgQ09P8PgQ0;P8PgAAg>4S0ZP8PgQ0I9AghS0IP8PgAr<il=?g>RlP8PgPg1VikP81Vih,qgS0[DDF9F9F9P9POb7b8b9X0<X1<X2<X3<X4<X6<X?<XC<103615I=S0\,N;?6B6'410oH15FBRk,2312@k12Ak15IG=6AH11@P11GH[[[[[[[^0<^1<^2<^3<^4<^6<^?<^C<P1PHPFPPP5P7PufORk,3CRjP{P@PGPNPSPKPUPVO?b5b<b:b;X=yP1O1Q0@/1xQ0UQ0BQ0VQ0WQ0XP<Q0C=s<bA_<?cRy?Oa`200<B=s<^S0CQ0EQ0F#RS0F5_<Q0D,Jy7Ob'F3H/8dP0Q06?<3eP=PeP6Q0YPGPeP;Q04DGDGPfPgQ0;P8PgQ0ZP8PgQ0IP8PgQ0J/Vh,qgP8PgPlP8Q0[CfF9F9P9POb7b8b9X0<X1<X2<X3<X4<X6<X?<123LRlQ0M,N@/13Q0N=63G11A@[[\q[\p^0<^1<^2<^3<^4<^6<^?<P1PHPFPPP7PuPjP{PNPSPKP3PUO<b5b<b:b;W=P1O1n200100000021100011000Q0?Q0T20>Z\S0T10Z\11\Z'4S0?P210txS0N11xtS0M%7zAEWI[?6Bz'4P110WsS0JPX%7115I7=y[BS0I/01'4XE<S0Z%7X15Iw=yXBR\/0XA_<?`R?1F^c5H^,x^/8dP0%S=RpP6%S;Ry?<;eP;PeDpPfPgQ09P8PgQ0HP8Q0K=?giF9P9POb7b8b9X0<X1<X2<10o=15;B,2=AE=I;?6B=[[^0<^1<^2<P1P@P7P[PAPFO5b53hP}PdP0A<p6eS0KPfPgA?gihRoP8PoCfP9POb7b8b9X0<X1<S091016106=S0;[^0<^1<S0YP1PYP[P6O3b5:0=X|S0DDUW=P1O111sWS0EP|Q0ZP2%7|10\|%7YR\Q0I/0YS0I'4P;%7:S0ZAEwI{?6B:RsQ09Q0YP1PjP5P6O3b5401X@\P1O1Q0IQ0ZPdP0A<p6yPfPgQ0LP8Q0LCfP9POb7b8b9X0<X1<X2<AE1I6?6B=Q0\,N6?6B;[^0<^1<^2<P1PjPuP7P6O4b57hsW@P1O1n200100000021000011000P}PdP0Q0KPfPgQ0[P8PoCfP9POb7b8b9X0<X1<1116Q0;[^0<^1<P1P[PYP6O3b5:0<X|S0;DUW=P1O1n200100000021100011000bDQ0=Q0S1T<]12P]R]eS0SP]1dtxS0=11tx?Pvt12vx9Cxt'4S0[PzP<p-0RxAOa?~Q0CQ0F?Oa?'F5Hc1Ja^,FcS0C/8d'8P0Q08?<@eP=PeP6Q05P@Q06P;PeDpDGPfPg1wgHQ02#B#IR^=Agh5`gRvA?gnhAAg^nRs5`g5igP8PgAAgi^RiP8PgQ0HP8PgQ0<P8PoF9F9P9POb7b8b9X0<X1<X2<X3<X4<X6<W>S0<AP@A6Rp12A=R\9C=6'4126@R5103AS0H\r\q[[^0<^1<^2<^3<^4<^6<^>xRqP111[YRrP6PGPHPYP[PMP=P;PPPNO;b5b<b:b;Q0>Q0RQ0TQ0?P2Q0NQ0M1YzB#XP1Q0JPX1Y1B#XR2XE<RNPLP2XB<1v@BPXPFDUP}Q0DDUW=P1O1Q0EP|PN15GBPN1vGBP|PPDUP}Q0;DUW=P1O1n200100000021100011000bDQ0AQ0QQ0SP]Q0=Q0[PzP<AOa`~R~,Fc%|~/8d'8P0PyP=PeP6PePAQ04P3PeDpDGPfPg1wgGAAg^>R^5`gA?gn>=`gs5igP8PgPiP8PgPg20:>hP8PoDDF9P9POb7b8b9X0<X1<X2<X3<X4<X>xAPA3=123;9C;='4126A103;10;3[[[^0<^1<^2<^3<^4<^>xP1PrP6PYP[%gm,3CPMP=P;PVO9b5b<b:b;Q0OQ0PPtPZPSI09Q0O?=tZQ0P?=tZ';Q00%L7?=Wt%Q7?=Wt%L{PDPDP7PwCe%Q{5]J5lJ?=XSP1%Lu?=[X%Qm?=w[%LkR[PDPDPmPuCe%QkRk5]JP7PRP[P7PwPRP61:w:R[,T<12R[R[eRXP[1d7jRt117j1:7jRW;P712Wj9Cj7'4RjfP,3C,:{R{P<Q0<PqP1fR,3CRq,1mP6PSPKPqPmPUP=P;PRPQO;b5b<b:b;RWEzPkP7PRPmPuPkP7PwPRP1PWEzA6:Y710R:PXP[PtPjP{P<Q0C1J?_R?AOca?Q0G5Hb5Hb/8d'8P0Q08?<;eP=PeP6Q05Q077<@DGPfPg1V>h,qg=`g^=igvP8PgPiP8PgPgQ0:,c>P8PgPg1ch4P8PoDDDDF9P9POb7b8b9X0<X1<X2<X3<X4<X6<X>x11=6/;\/4pQ0H\l\l\5[^0<^1<^2<^3<^4<^6<^>xP110qmP6PSPKPmPqPUP=P;PRPQO;b5b<b:b;3hK08J0AWSWYP6P1O2n2001000000121000000bACaCaCaCaCabVbXbabbb`Q03,1T%7AfB9EQI?6EA'41YAE#X%gZ,3C%LZPDPDPVPUCe%QZ5]J5lJ?=TA5CA';9CAQ';';ebHbGbFbQbOb[WWWAWKWJWIWLWMWNWTWUXB<XZ<X_<X^DW\W]o"). Qed.

(* [comment removed for export] *)
Definition kHighMemBeg : Z := 0x10007fff8000.

Lemma kHighMemBeg_below_mmap_base_min :
  kHighMemBeg + 0x544d555f000 = mmap_base_min /\ mmap_base_min < bottomup_floor.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"] "h01zp;1p;2p;3p;4p;6p-1p10000p4p710R0p8p1000Gp4p70R1g0017R2p4p710R3p8P1P0p8P1p1001Qp4p710R4p8P1p1001mp4p710R5p8P1p1002Kp4p7210R6p8P1g002hR1p4p710R7p8p1003Fp6051000R8p1004Op4p710R9p8p1005Ep6051000R:P9p8P:p1006Op4p710R;p8P:p10071p4p710R<p8p1007Np4p70R=P3p8P=P0p8P=P4p8P=P9p8P=p1008<p4p710p8P=P5p8P=p1008Yp4p710p8P=P6p8P=P8p8P=p1009Tp4p710p8P=P:p8P=p100:Np4p710p8P=P7p8P=P<p8p100;Jp4p7210R<P3p8P<P0p8P<P4p8P<P5p8P<P6p8P<P7p8P<p100<6p4p710p8p100==p6051000R<P0p8P<P;p8P<p100>Dp4p710p8p100>`p4p70R<P3p8P<P0p8P<P4p8P<P5p8P<P6p8P<P7p8g00@2j10Tg00@Wj17Tg00M\j2<TP2j3;j1DTg00ARj29Tg00Anj2>Tg02BUj1CTg02CDj4BTg00HBj2ATg00nYj4@TP1j6?Tg00H\j12Tf0R1#2#0#2#0p=4%21#0p==%21#2p=1%01#0#0#0p=8%01#0#0#0#0#0#0#0p=5%01#0p=:%01#2p=6%01#2#0#2p=3g00FaR2g00G]#0R7#4R<#=R6#4#4#4#4#4#4#1#8#5#7R5%07#:#5#6#1#1#1#1#1#1#1#=#:#8#5#7%0<#6#:#1#6#3#3#3#1#1#8#5#7R<'<%06#6#3#3#3#3#3#1#8#5#7R65;2R71961'>X02P71965P2%D2%C2P6CBg02D2g02DX'AC@g01SOR6g01VeE?g02E>/<<g02FDR<5;219<6'>eo"). Qed.

(* [comment removed for export] *)
Corollary kHighMemBeg_le : forall h (a : word) nZ Y,
  0 < nZ -> nZ mod page_size = 0 ->
  bv_unsigned a mod page_size = 0 ->
  Y mod page_size = 0 -> Y <= bv_unsigned (vm_mmap_base h) ->
  kHighMemBeg + 2 * nZ <= Y ->
  ledger_split (vm_reserved h ++ vm_maps h) kHighMemBeg Y ->
  placement_ok_b h (bv_unsigned a) nZ = true ->
  kHighMemBeg < bv_unsigned a.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlacement ()) ["FPX_1"] "h04__x1h17__arithh24__ffh38__varmaph45__with53Hflh64__x2h74__x3h84__x4h92HKh:2HYh;3HYBh<4HYalh=4HaAlh>3Hlth?4HnAlh@3HnZhA3HplhB6HsplithC1YhD1ahE1hhF2nZhG1ohH1zp;1p;2p;3p;4p;>p;6p;7p;8p-1p10000p4p710R0p8p1000Gp4p70R1g0017R2p4p710R3p8P1P0p8P1g001QR4p4p710R5p8P1p1001mp4p710R6p8P1p1002Kp4p7210R7p8P1p1002hp4p710R1p8p1003Fp6051000R8p1004Op4p710R9p8p1005Ep6051000R:P9p8P:p1006Op4p710R;p8P:g0071R<p4p710R=p8p1007Np4p70R>P3p8P>P0p8P>P5p8P>P9p8P>p1008<p4p710p8P>P6p8P>p1008Yp4p710p8P>P7p8P>P8p8P>p1009Tp4p710p8P>P:p8P>p100:Np4p710p8P>P1p8P>P=p8p100;Jp4p7210R=P3p8P=P0p8P=P5p8P=P6p8P=P7p8P=P1p8P=p100<6p4p710p8p100==p6051000R=P0p8P=P;p8P=p100>Dp4p710p8p100>`p4p70R=P3p8P=P0p8P=P5p8P=P6p8P=P7p8P=P1p8g00@2j10Tg00BIj1ZTg00IAj1STg00ARj22Tg00JWj2CTg00EHj23Tg0204j1VTg00?Vj21Tg00@Wj1>Tg00M?j28Tg00M\j2GTg00h9j2kTg01djj1iTg01edj1gTP<j3fTg01gQj3`Tg01mij3_TP2j3ATg00PSj1\Tg00Q3j1[Tg00QSj1YTg00R1j1XTg00ROj1WTg00S:j2:Tg00TAj2RTg00HBj2QTg00Tcj2NTg00UOj3OTg00Unj4PTg027Sl>MTg01S2j2<Tg00kJR2j2TTP4j6jTg00\6j2ETg00]Tj2;Tg00]2j1hTg00XPj1LTg00Xoj2?Tg00ZAj3JTg00Zjj2eTg00[Vj3dTg00\Tj4ITg00H\j17Tg00^7j3aTg01OPj3bTg00^Zj3cTg00_=j4KTg00_hj7^Tg00`Lj8]Tf0R4#0#0#0#0p=4g00FaR<g00G?R17A4p=@%04#0p=H%04#7p=U%74#7p=5%74#0p=FP<f1R=g012EP4CKp==P=g00aWR7g00b6R6P6g00bVR5P4g00c6F^p=9%74#0#7#0p=6P<P=g01B^P4CKp=Df3R0P7P6P6P5f2R7P=P4G]p=Bg01fZg00G]R3#0R;#0R>#4R:#ZR8#SR9121=g00cVR?,C7#@f4R@,38/C?#@1C0?#@f7R?#V,38,1@g02E>RA%>;RBf6RC'8'Gf5RD'11k99f9R9#i%g93f?`ACg00e:REf:RF1389f8RG3_g00eZRH3Ag00dNRI#\RJ%[IRK%Y<RL%X<RM%W<RN1:<1%H:#4#U#5#5#5#5#5#5#5#F#H#4#4#4#>R:,:<RO'='91RN5R5P4P71QEH1N47=AEHdAO<1=CPRHb2b3b4111:P4b1111AR1eP1f<R1f;REPFPAP9PGP?PCPDP@P4P0P7P=M>Mg01SORD138ERC'118BF,<9/2C'TP21381R2,1D18BE,<F/22f=R2,38RF,2AP411DFP<PDf?,38RD,14XH<P4%F;#6#6#6#6#6#6#6#5#4#4#4#>RCg01VeEjf>R9,38,1CPJPK1E<=PMPN1:<C1;<3RG'=,9N%h6R61DOG,9NCBP5PHb2b3b4X0<11C412:=[^0<P4f@,38P=O2b112ADeb5W5P4O118B1,<E/2Fg00fWRF#LRE#L,?<1?<E1?<F5J<5J<g00g6'e=dIJPKP<P<1E<@P7PLCIP=1E<0CIPMPN1;<>R>1:<B%73,;<5a<R35b<1;<;R;'D,9NP6PNAc<G3/=>,9NP61DG;,9NCBCBP5PHb2b3b4X0<X6<X7<X8<18B7,<0/2=18B0,G=/1@1270[[^0<^6<^7<^8<P4P2P9PDPAP=P?O6b1W>P4O1n200100000021100011000bGb9WAWBW:W;W<W=W?W@XC<XF<WDWEo"). Qed.

End FPX_1.

End AsanPlacement.
