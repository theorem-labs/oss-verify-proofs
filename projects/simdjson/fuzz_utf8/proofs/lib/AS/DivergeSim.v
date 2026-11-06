(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AS Require Import PropExec.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
Local Ltac div_vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Section WithFP1.
Context {fx : FPState}.

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
