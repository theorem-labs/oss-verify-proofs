(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import PropExec MState Mem Exec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition resp := SyscallEffect.
Definition nret (ms : machine_state) (eff : resp) : machine_state :=
  advance_past_svc (apply_effect ms eff).

Module Exc.
#[universes(template)]
Inductive exc (A : Type) : Type := Unr | Ok (a : A).
Arguments Unr {A}.
Arguments Ok {A} a.
End Exc.
Import Exc.

Section ITree.

Variable node : Type.

Inductive itree (R : Type) : Type :=
| Ret (r : R)
| Vis (n : node) (k : resp -> itree R).
Arguments Ret {R} r.
Arguments Vis {R} n k.

Fixpoint bind {A B} (t : itree A) (f : A -> itree B) : itree B :=
  match t with
  | Ret r => f r
  | Vis n k => Vis n (fun x => bind (k x) f)
  end.

Variable segs : list Segment.

Variable cfg : SpuriousCfg.

Variable at_node : node -> machine_state -> Prop.

Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.

Variable nsafe : node -> Model -> Prop.

Record node_sound : Prop := {

  ns_lazy : forall mo, minv mo -> m_vm_lazy mo = [];

  ns_pending : forall n ms, at_node n ms -> ms_svc_pending ms <> None;

  ns_complete : forall n ms mo evs X, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      sstep_cfg segs cfg (mkCfg ms mo) evs X ->
        (exists rsp mo', X = SNext (mkCfg (nret ms rsp) mo') /\ nstep n mo rsp mo' evs)
     \/ (exists code mo', X = SNext (mkCfg ms mo') /\ nexit n mo code mo' /\ evs = [ExitEv code (m_fs mo')]);

  ns_sound : forall n ms mo rsp mo' evs, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      nstep n mo rsp mo' evs ->
      m_halted mo' = None /\ minv mo'
      /\ sstep_cfg segs cfg (mkCfg ms mo) evs (SNext (mkCfg (nret ms rsp) mo'));
  ns_exit : forall n ms mo code mo', at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      nexit n mo code mo' ->
      m_halted mo' = Some code /\ sstep_cfg segs cfg (mkCfg ms mo) [ExitEv code (m_fs mo')] (SNext (mkCfg ms mo'));

  ns_progress : forall n ms mo, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      (exists rsp mo' evs, nstep n mo rsp mo' evs) \/ (exists code mo', nexit n mo code mo')
}.

Fixpoint impl {R} (t : itree R) (Q : R -> machine_state -> Prop) (ms : machine_state) : Prop :=
  match t with
  | Ret r => evt segs (Q r) ms
  | Vis n k => evt segs (fun ms1 => at_node n ms1 /\ forall rsp, impl (k rsp) Q (nret ms1 rsp)) ms
  end.

Lemma impl_ret_intro : forall {R} (r : R) Q ms, evt segs (Q r) ms -> impl (Ret r) Q ms.
Proof. intros. exact H. Qed.

Lemma impl_mono : forall {R} (t : itree R) (Q Q' : R -> machine_state -> Prop) ms,
  impl t Q ms -> (forall r ms', Q r ms' -> Q' r ms') -> impl t Q' ms.
Proof.
  induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
  - eapply evt_mono; eauto.
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp. eapply IH; eauto.
Qed.

Lemma impl_evt : forall {R} (t : itree R) Q P ms,
  evt segs P ms -> (forall ms', P ms' -> impl t Q ms') -> impl t Q ms.
Proof.
  intros R t Q P ms H K. destruct t; cbn in *; eapply evt_cut; eauto; intros ms' HP; apply (K _ HP).
Qed.

Lemma impl_bind : forall {A B} (t : itree A) (f : A -> itree B) Q1 Q ms,
  impl t Q1 ms -> (forall r ms', Q1 r ms' -> impl (f r) Q ms') -> impl (bind t f) Q ms.
Proof.
  induction t as [r|n k IH]; intros f Q1 Q ms H Hf; cbn [bind].
  - cbn in H. eapply impl_evt; [exact H|]. intros ms' HQ. exact (Hf _ _ HQ).
  - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.

Fixpoint ttrace {R} (t : itree R) (mo : Model) (tr : list event) : Prop :=
  match t with
  | Ret _ => tr = []
  | Vis n k => (exists code mo', nexit n mo code mo' /\ tr = [ExitEv code (m_fs mo')])
            \/ (exists rsp mo' evs tr', nstep n mo rsp mo' evs /\ ttrace (k rsp) mo' tr' /\ tr = evs ++ tr')
  end.

Fixpoint tsafe {R} (t : itree R) (mo : Model) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => nsafe n mo /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> tsafe (k rsp) mo'
  end.

Fixpoint tpath {R} (t : itree R) (mo : Model) (tr : list event) (r : R) (mo' : Model) : Prop :=
  match t with
  | Ret r0 => r0 = r /\ mo' = mo /\ tr = []
  | Vis n k => exists rsp mo1 evs tr', nstep n mo rsp mo1 evs /\ tpath (k rsp) mo1 tr' r mo' /\ tr = evs ++ tr'
  end.

Fixpoint texit {R} (t : itree R) (mo : Model) (tr : list event) : Prop :=
  match t with
  | Ret _ => False
  | Vis n k => (exists code mo', nexit n mo code mo' /\ tr = [ExitEv code (m_fs mo')])
            \/ (exists rsp mo' evs tr', nstep n mo rsp mo' evs /\ texit (k rsp) mo' tr' /\ tr = evs ++ tr')
  end.

Lemma ttrace_split : forall {R} (t : itree R) mo tr,
  ttrace t mo tr <-> texit t mo tr \/ exists r mo', tpath t mo tr r mo'.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo tr; cbn.
  - split.
    + intros ->. right. exists r, mo. repeat split; reflexivity.
    + intros [F|(r' & mo' & _ & _ & ->)]; [destruct F|reflexivity].
  - split.
    + intros [Hex|(rsp & mo' & evs & tr' & Hst & Ht & ->)]; [left; left; exact Hex|].
      destruct (proj1 (IH rsp mo' tr') Ht) as [Hx|(r & mo'' & Hp)].
      * left; right. exists rsp, mo', evs, tr'. repeat split; assumption.
      * right. exists r, mo'', rsp, mo', evs, tr'. repeat split; assumption.
    + intros [[Hex|(rsp & mo' & evs & tr' & Hst & Hx & ->)]|(r & mo'' & rsp & mo' & evs & tr' & Hst & Hp & ->)].
      * left; exact Hex.
      * right. exists rsp, mo', evs, tr'. split; [assumption|]; split; [|reflexivity]. apply (proj2 (IH rsp mo' tr')). left; exact Hx.
      * right. exists rsp, mo', evs, tr'. split; [assumption|]; split; [|reflexivity]. apply (proj2 (IH rsp mo' tr')). right; eauto.
Qed.

Definition leaves_unreachable {R} (t : itree R) (ms : machine_state) : Prop :=
  impl t (fun _ _ => False) ms.

Definition leaves_unreachable_m {R} (t : itree R) (mo : Model) : Prop :=
  forall tr r mo', tpath t mo tr r mo' -> False.

Lemma leaves_unreachable_m_ret : forall {R} (r : R) mo, leaves_unreachable_m (Ret r) mo -> False.
Proof. intros R r mo H. apply (H [] r mo). cbn. repeat split; reflexivity. Qed.

Lemma leaves_unreachable_m_step : forall {R} n (k : resp -> itree R) mo rsp mo' evs,
  leaves_unreachable_m (Vis n k) mo -> nstep n mo rsp mo' evs -> leaves_unreachable_m (k rsp) mo'.
Proof.
  intros R n k mo rsp mo' evs H Hst tr r mo'' Hp. apply (H (evs ++ tr) r mo''). cbn.
  exists rsp, mo', evs, tr. repeat split; assumption.
Qed.

Lemma tsafe_step : forall {R} n (k : resp -> itree R) mo rsp mo' evs,
  tsafe (Vis n k) mo -> nstep n mo rsp mo' evs -> tsafe (k rsp) mo'.
Proof. intros R n k mo rsp mo' evs [_ Hk] Hst. eapply Hk; eassumption. Qed.

Lemma star_cfg_one : forall c evs c',
  sstep_cfg segs cfg c evs (SNext c') -> star_cfg segs cfg c evs c'.
Proof.
  intros c evs c' H. rewrite <- (app_nil_r evs). eapply star_cfg_step; [exact H| apply star_cfg_refl].
Qed.

Lemma star_cfg_trans : forall c1 t1 c2 t2 c3,
  star_cfg segs cfg c1 t1 c2 -> star_cfg segs cfg c2 t2 c3 -> star_cfg segs cfg c1 (t1 ++ t2) c3.
Proof.
  intros c1 t1 c2 t2 c3 H1 H2. induction H1 as [c|ca evs cb tr cc Hss Hst IH]; [exact H2|].
  rewrite <- app_assoc. eapply star_cfg_step; [exact Hss| exact (IH H2)].
Qed.

Lemma sstep_mstep_inv : forall ms mo ms' evs X,
  m_vm_lazy mo = [] ->
  mstep segs ms ms' ->
  sstep_cfg segs cfg (mkCfg ms mo) evs X ->
  evs = [] /\ X = SNext (mkCfg ms' mo).
Proof.
  intros ms mo ms' evs X Hlz [Hsvc Hstep] Hss.
  inversion Hss; subst; try congruence;
  match goal with H : mi_account_step segs ms mo = _ |- _ =>
    rewrite (mi_account_step_no_lazy segs ms mo Hlz) in H; rewrite Hstep in H; inversion H; subst end.
  split; reflexivity.
Qed.

Lemma sstep_not_halted : forall ms mo evs X,
  sstep_cfg segs cfg (mkCfg ms mo) evs X -> m_halted mo = None.
Proof. intros ms mo evs X Hss. inversion Hss; subst; assumption. Qed.

Lemma star_halted_nil : forall ms mo tr c',
  m_halted mo <> None -> star_cfg segs cfg (mkCfg ms mo) tr c' -> tr = [] /\ c' = mkCfg ms mo.
Proof.
  intros ms mo tr c' Hh Hstar. inversion Hstar; subst.
  - split; reflexivity.
  - exfalso. apply Hh. eapply sstep_not_halted; eassumption.
Qed.

Lemma mstep_sstep : forall ms ms' mo,
  m_halted mo = None -> m_vm_lazy mo = [] -> mstep segs ms ms' ->
  sstep_cfg segs cfg (mkCfg ms mo) [] (SNext (mkCfg ms' mo)).
Proof.
  intros ms ms' mo Hh Hlz [Hsvc Hstep]. apply sstep_cfg_instr; try assumption.
  rewrite (mi_account_step_no_lazy segs ms mo Hlz), Hstep. reflexivity.
Qed.

Lemma msteps_star : forall ms ms' mo,
  m_halted mo = None -> m_vm_lazy mo = [] -> msteps segs ms ms' ->
  star_cfg segs cfg (mkCfg ms mo) [] (mkCfg ms' mo).
Proof.
  intros ms ms' mo Hh Hlz Hm. induction Hm as [ms|ms ms1 ms2 H1 H2 IH].
  - apply star_cfg_refl.
  - change ([] : list event) with ([] ++ [] : list event).
    eapply star_cfg_step; [apply mstep_sstep; eassumption| exact IH].
Qed.

Lemma is_prefix_app_l {A} : forall (l l1 l2 : list A),
  is_prefix l1 l2 -> is_prefix (l ++ l1) (l ++ l2).
Proof. induction l; cbn; auto. Qed.

Lemma impl_inv : forall {R} (t : itree R) Q ms mo,
  impl t Q ms -> leaves_unreachable_m t mo ->
  exists n k ms1, t = Vis n k /\ msteps segs ms ms1 /\ at_node n ms1
               /\ forall rsp, impl (k rsp) Q (nret ms1 rsp).
Proof.
  intros R t Q ms mo H Hl. destruct t as [r|n k]; cbn in H.
  - destruct (leaves_unreachable_m_ret r mo Hl).
  - destruct H as (ms1 & Hm & Hat & Hk). exists n, k, ms1. repeat split; assumption.
Qed.

Definition tree_at {R} (t : itree R) Q (ms : machine_state) (mo : Model) : Prop :=
  impl t Q ms /\ leaves_unreachable_m t mo /\ m_halted mo = None /\ minv mo /\ tsafe t mo.

Lemma tree_at_step : node_sound -> forall {R} n (k : resp -> itree R) Q ms1 mo rsp mo' evs,
  at_node n ms1 -> (forall rsp, impl (k rsp) Q (nret ms1 rsp)) ->
  leaves_unreachable_m (Vis n k) mo -> m_halted mo = None -> minv mo -> tsafe (Vis n k) mo ->
  nstep n mo rsp mo' evs ->
  tree_at (k rsp) Q (nret ms1 rsp) mo' /\ sstep_cfg segs cfg (mkCfg ms1 mo) evs (SNext (mkCfg (nret ms1 rsp) mo')).
Proof.
  intros NS R n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hst.
  destruct (ns_sound NS n ms1 mo rsp mo' evs Hat Hh Hinv (proj1 Hsf) Hst) as (Hh' & Hinv' & Hss).
  split; [|exact Hss]. split; [apply Hk|]. split; [eapply leaves_unreachable_m_step; eassumption|].
  split; [exact Hh'|]. split; [exact Hinv'|]. eapply tsafe_step; eassumption.
Qed.

Lemma ttrace_exists : node_sound -> forall {R} (t : itree R) Q ms mo,
  tree_at t Q ms mo -> exists full, ttrace t mo full.
Proof.
  intros NS R t. induction t as [r|n k IH]; intros Q ms mo HT.
  - destruct HT as (_ & Hl & _). destruct (leaves_unreachable_m_ret r mo Hl).
  - destruct HT as (Ht & Hl & Hh & Hinv & Hsf).
    cbn in Ht. destruct Ht as (ms1 & Hm & Hat & Hk).
    destruct (ns_progress NS n ms1 mo Hat Hh Hinv (proj1 Hsf)) as [(rsp & mo' & evs & Hst)|(code & mo' & Hex)].
    + destruct (tree_at_step NS n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hst) as [HT' _].
      destruct (IH rsp Q (nret ms1 rsp) mo' HT') as (full' & Hfull').
      exists (evs ++ full'). cbn. right. exists rsp, mo', evs, full'. repeat split; assumption.
    + exists [ExitEv code (m_fs mo')]. cbn. left. exists code, mo'. split; [assumption|reflexivity].
Qed.

Lemma impl_sstep_inv : node_sound -> forall {R} (t : itree R) Q ms mo evs X,
  tree_at t Q ms mo ->
  sstep_cfg segs cfg (mkCfg ms mo) evs X ->
     (exists ms', X = SNext (mkCfg ms' mo) /\ evs = [] /\ mstep segs ms ms' /\ tree_at t Q ms' mo)
  \/ (exists n k rsp mo', t = Vis n k /\ at_node n ms /\ X = SNext (mkCfg (nret ms rsp) mo')
        /\ nstep n mo rsp mo' evs /\ tree_at (k rsp) Q (nret ms rsp) mo')
  \/ (exists n k code mo', t = Vis n k /\ at_node n ms /\ X = SNext (mkCfg ms mo')
        /\ nexit n mo code mo' /\ evs = [ExitEv code (m_fs mo')] /\ m_halted mo' = Some code).
Proof.
  intros NS R t Q ms mo evs X HT Hss. destruct HT as (Ht & Hl & Hh & Hinv & Hsf).
  destruct (impl_inv t Q ms mo Ht Hl) as (n & k & ms1 & -> & Hm & Hat & Hk).
  inversion Hm; subst.
  -
    destruct (ns_complete NS n ms1 mo evs X Hat Hh Hinv (proj1 Hsf) Hss)
      as [(rsp & mo' & HX & Hst)|(code & mo' & HX & Hex & Hevs)].
    + right; left. destruct (tree_at_step NS n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hst) as [HT' _].
      exists n, k, rsp, mo'. split; [reflexivity|]. split; [exact Hat|]. split; [exact HX|]. split; [exact Hst|exact HT'].
    + right; right. destruct (ns_exit NS n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as (Hh' & _).
      exists n, k, code, mo'. repeat split; auto.
  -
    left. match goal with H1 : mstep segs ms ?x, H2 : msteps segs ?x ms1 |- _ =>
      destruct (sstep_mstep_inv ms mo x evs X (ns_lazy NS mo Hinv) H1 Hss) as (-> & ->);
      exists x; split; [reflexivity|]; split; [reflexivity|]; split; [exact H1|];
      split; [cbn; exists ms1; split; [exact H2|]; split; [exact Hat|exact Hk]|];
      split; [exact Hl|]; split; [exact Hh|]; split; [exact Hinv|exact Hsf] end.
Qed.

Definition run_inv {R} Q (c : config) : Prop :=
  (exists t : itree R, tree_at t Q (cfg_ms c) (cfg_model c))
  \/ m_halted (cfg_model c) <> None.

Lemma run_inv_sstep : node_sound -> forall {R} Q c evs X,
  run_inv (R:=R) Q c -> sstep_cfg segs cfg c evs X -> exists c', X = SNext c' /\ run_inv (R:=R) Q c'.
Proof.
  intros NS R Q [ms mo] evs X Hg Hss. destruct Hg as [(t & HT)|Hh]; cbn in *.
  - destruct (impl_sstep_inv NS t Q ms mo evs X HT Hss)
      as [(ms' & -> & _ & _ & HT')|[(n & k & rsp & mo' & _ & _ & -> & _ & HT')
         |(n & k & code & mo' & _ & _ & -> & _ & _ & Hh')]].
    + eexists; split; [reflexivity|]. left. exists t. exact HT'.
    + eexists; split; [reflexivity|]. left. exists (k rsp). exact HT'.
    + eexists; split; [reflexivity|]. right. cbn. congruence.
  - exfalso. apply Hh. eapply sstep_not_halted; eassumption.
Qed.

Lemma run_inv_star : node_sound -> forall {R} Q c tr c',
  star_cfg segs cfg c tr c' -> run_inv (R:=R) Q c -> run_inv (R:=R) Q c'.
Proof.
  intros NS R Q c tr c' Hstar. induction Hstar as [c|c1 evs c2 tr c3 Hss Hstar IH]; intros Hg; [exact Hg|].
  destruct (run_inv_sstep NS Q c1 evs (SNext c2) Hg Hss) as (c2' & E & Hg'). inversion E; subst. auto.
Qed.

Lemma star_ttrace_prefix : node_sound -> forall {R} Q c tr c',
  star_cfg segs cfg c tr c' ->
  forall (t : itree R) ms mo, c = mkCfg ms mo -> tree_at t Q ms mo ->
  exists full, ttrace t mo full /\ is_prefix tr full.
Proof.
  intros NS R Q c tr c' Hstar.
  induction Hstar as [c|c1 evs c2 tr c3 Hss Hstar IH]; intros t ms mo -> HT.
  - destruct (ttrace_exists NS t Q ms mo HT) as (full & Hf).
    exists full. split; [exact Hf| apply is_prefix_nil].
  - destruct (impl_sstep_inv NS t Q ms mo evs (SNext c2) HT Hss)
      as [(ms' & E & -> & _ & HT')|[(n & k & rsp & mo' & -> & Hat & E & Hst & HT')
         |(n & k & code & mo' & -> & Hat & E & Hex & -> & Hh')]]; inversion E; subst.
    + exact (IH t ms' mo eq_refl HT').
    + destruct (IH (k rsp) (nret ms rsp) mo' eq_refl HT') as (full' & Hf' & Hp').
      exists (evs ++ full'). split.
      * cbn. right. exists rsp, mo', evs, full'. repeat split; assumption.
      * apply is_prefix_app_l. exact Hp'.
    + destruct (star_halted_nil ms mo' tr c3) as [-> _]; [congruence|exact Hstar|].
      exists [ExitEv code (m_fs mo')]. split.
      * cbn. left. exists code, mo'. split; [assumption|reflexivity].
      * cbn. split; [reflexivity|exact I].
Qed.

Lemma ttrace_star : node_sound -> forall {R} (t : itree R) Q ms mo full,
  ttrace t mo full -> tree_at t Q ms mo ->
  exists c', star_cfg segs cfg (mkCfg ms mo) full c'.
Proof.
  intros NS R t. induction t as [r|n k IH]; intros Q ms mo full Hf HT.
  - destruct HT as (_ & Hl & _). destruct (leaves_unreachable_m_ret r mo Hl).
  - destruct HT as (Ht & Hl & Hh & Hinv & Hsf).
    cbn in Ht. destruct Ht as (ms1 & Hm & Hat & Hk).
    pose proof (msteps_star ms ms1 mo Hh (ns_lazy NS mo Hinv) Hm) as Hs0.
    cbn in Hf. destruct Hf as [(code & mo' & Hex & ->)|(rsp & mo' & evs & tr' & Hst & Hf' & ->)].
    + destruct (ns_exit NS n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as (_ & Hss).
      exists (mkCfg ms1 mo'). change [ExitEv code (m_fs mo')] with ([] ++ [ExitEv code (m_fs mo')]).
      eapply star_cfg_trans; [exact Hs0|]. apply star_cfg_one. exact Hss.
    + destruct (tree_at_step NS n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hst) as [HT' Hss].
      destruct (IH rsp Q (nret ms1 rsp) mo' tr' Hf' HT') as (c' & Hs').
      exists c'. change (evs ++ tr') with ([] ++ (evs ++ tr')).
      eapply star_cfg_trans; [exact Hs0|]. eapply star_cfg_step; [exact Hss| exact Hs'].
Qed.

Theorem impl_run_traces2 : node_sound -> forall {R} (t : itree R) Q ms mo,
  impl t Q ms -> leaves_unreachable_m t mo -> m_halted mo = None -> minv mo -> tsafe t mo ->
  ms_svc_pending ms = None ->
  forall tr, obs_trace_cfg segs cfg (mkCfg ms mo) tr <-> exists full, ttrace t mo full /\ is_prefix tr full.
Proof.
  intros NS R t Q ms mo Ht Hl Hh Hinv Hsf _ tr.
  assert (HT : tree_at t Q ms mo) by (repeat split; assumption). split.
  - intros (tr' & c & Hstar & Hp).
    destruct (star_ttrace_prefix NS Q (mkCfg ms mo) tr' c Hstar t ms mo eq_refl HT) as (full & Hf & Hp').
    exists full. split; [exact Hf| eapply is_prefix_trans; eassumption].
  - intros (full & Hf & Hp).
    destruct (ttrace_star NS t Q ms mo full Hf HT) as (c' & Hs).
    exists full, c'. split; assumption.
Qed.

Theorem impl_run_safe2 : node_sound -> forall {R} (t : itree R) Q ms mo,
  impl t Q ms -> leaves_unreachable_m t mo -> m_halted mo = None -> minv mo -> tsafe t mo ->
  ms_svc_pending ms = None ->
  ~ reaches_error_cfg segs cfg (mkCfg ms mo).
Proof.
  intros NS R t Q ms mo Ht Hl Hh Hinv Hsf _ (tr & c & evs & Hstar & Hss).
  assert (Hg : run_inv (R:=R) Q c).
  { eapply run_inv_star; [exact NS|exact Hstar|]. left. exists t. cbn. repeat split; assumption. }
  destruct (run_inv_sstep NS Q c evs SError Hg Hss) as (c' & E & _). discriminate E.
Qed.

Theorem impl_run_modeled2 : node_sound -> forall {R} (t : itree R) Q ms mo,
  impl t Q ms -> leaves_unreachable_m t mo -> m_halted mo = None -> minv mo -> tsafe t mo ->
  ms_svc_pending ms = None ->
  ~ reaches_unmodeled_cfg segs cfg (mkCfg ms mo).
Proof.
  intros NS R t Q ms mo Ht Hl Hh Hinv Hsf Hsvc.
  intros Hu. apply (reaches_unmodeled_cfg_reaches_error_cfg segs cfg) in Hu. revert Hu. eapply impl_run_safe2; eassumption.
Qed.

Definition ebind {A B} (t : itree (exc A)) (f : A -> itree (exc B)) : itree (exc B) :=
  bind t (fun r => match r with Unr => Ret Unr | Ok a => f a end).

Definition epost {A} (Q : A -> machine_state -> Prop) : exc A -> machine_state -> Prop :=
  fun r ms => match r with Unr => True | Ok a => Q a ms end.

Lemma impl_ret_unr : forall {A} (Q : A -> machine_state -> Prop) ms, impl (Ret Unr) (epost Q) ms.
Proof. intros A Q ms. cbn. apply evt_done. exact I. Qed.

Lemma impl_ebind : forall {A B} (t : itree (exc A)) (f : A -> itree (exc B)) Q1 Q ms,
  impl t (epost Q1) ms -> (forall a ms', Q1 a ms' -> impl (f a) (epost Q) ms') ->
  impl (ebind t f) (epost Q) ms.
Proof.
  intros A B t f Q1 Q ms Ht Hf. unfold ebind. eapply impl_bind; [exact Ht|].
  intros [|a] ms' H'; cbn in H'.
  - apply impl_ret_unr.
  - apply Hf. exact H'.
Qed.

Lemma impl_epost_mono : forall {A} (t : itree (exc A)) (Q Q' : A -> machine_state -> Prop) ms,
  impl t (epost Q) ms -> (forall a ms', Q a ms' -> Q' a ms') -> impl t (epost Q') ms.
Proof.
  intros A t Q Q' ms H HQ. eapply impl_mono; [exact H|]. intros [|a] ms'; cbn; auto.
Qed.

Lemma ebind_ret_ok : forall {A B} (a : A) (f : A -> itree (exc B)), ebind (Ret (Ok a)) f = f a.
Proof. reflexivity. Qed.
Lemma ebind_vis : forall {A B} n k (f : A -> itree (exc B)),
  ebind (Vis n k) f = Vis n (fun rsp => ebind (k rsp) f).
Proof. reflexivity. Qed.

Lemma impl_ret_ok : forall {A} (Q : A -> machine_state -> Prop) a ms,
  evt segs (Q a) ms -> impl (Ret (Ok a)) (epost Q) ms.
Proof. intros A Q a ms H. exact H. Qed.

Definition enode {A} (n : node) (pl : resp -> option A) : itree (exc A) :=
  Vis n (fun rsp => match pl rsp with Some a => Ret (Ok a) | None => Ret Unr end).

Lemma impl_enode : forall {A} n (pl : resp -> option A) (Q : A -> machine_state -> Prop) ms,
  evt segs (fun ms1 => at_node n ms1 /\ forall rsp a, pl rsp = Some a -> evt segs (Q a) (nret ms1 rsp)) ms ->
  impl (enode n pl) (epost Q) ms.
Proof.
  intros A n pl Q ms H. cbn. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp. specialize (Hk rsp). destruct (pl rsp) as [a|]; cbn.
  - apply Hk. reflexivity.
  - apply evt_done. exact I.
Qed.

End ITree.

Arguments Ret {node R} r.
Arguments Vis {node R} n k.
Arguments impl {node} segs at_node {R} t Q ms.
Arguments ttrace {node} nstep nexit {R} t mo tr.
Arguments tsafe {node} nstep nsafe {R} t mo.
Arguments tpath {node} nstep {R} t mo tr r mo'.
Arguments texit {node} nstep nexit {R} t mo tr.
Arguments leaves_unreachable_m {node} nstep {R} t mo.
Arguments tree_at {node} segs at_node nstep minv nsafe {R} t Q ms mo.
Arguments ebind {node A B} t f.
Arguments enode {node A} n pl.
