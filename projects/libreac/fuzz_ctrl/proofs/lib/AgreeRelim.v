From Stdlib Require Import ZArith List Bool Lia Classical_Prop.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Run Specs RiscvSemantics MemImageType.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Common.LimSim Require Import
  LimSim LimSimMm LimSimArms LimSimMv LimSimWf LimSimSys LimSimRun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import RoomShapesDraft.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma src_relim : forall L m a b c,
  mremap_source_b (m_vmmaps (relim L m)) a b c = mremap_source_b (m_vmmaps m) a b c.
Proof. reflexivity. Qed.

Lemma uni_relim : forall L m a b, mremap_backing_uniform_b (relim L m) a b = mremap_backing_uniform_b m a b.
Proof. reflexivity. Qed.

Lemma stack_low_relim : forall L c p,
  stack_low (m_vmmaps (cfg_model (relim_cfg L c))) p = stack_low (m_vmmaps (cfg_model c)) p.
Proof. reflexivity. Qed.

Lemma sstep_live : forall segs cfg c evs st, sstep_cfg segs cfg c evs st -> m_halted (cfg_model c) = None.
Proof. intros segs cfg c evs st H. destruct H; cbn [cfg_model]; assumption. Qed.

Section Relim.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable Lbig Lsmall : Z.
Hypothesis HLE : Lsmall <= Lbig.
Set Default Proof Using "All".

Lemma move_mono : forall m a b c, vm_limit (m_vmmaps m) = Lbig ->
  mremap_move_budget_b (relim Lsmall m) a b c = true -> mremap_move_budget_b m a b c = true.
Proof.
  intros m a b c HM. unfold mremap_move_budget_b. rewrite mremap_move_charge_relim, rr_m_vmmaps, rr_vm_limit, HM.
  intros H. apply Z.leb_le in H. apply Z.leb_le. lia.
Qed.

Ltac leaf_core HM :=
  let H := fresh "H" in let E := fresh "E" in let E2 := fresh "E" in
  lazymatch goal with
  | |- ?A -> ?A => intros H; exact H
  | |- ?X && negb (brk_budget_ok ?m ?r) = true -> ?X && negb (brk_budget_ok (relim Lsmall ?m) ?r) = true =>
      intros H; destruct (brk_budget_ok (relim Lsmall m) r) eqn:E;
      [ rewrite (brk_budget_ok_mono Lbig Lsmall HLE m r HM E) in H; apply andb_true_iff in H;
        destruct H as [_ H]; cbn [negb] in H; discriminate H
      | apply andb_true_iff; split; [apply andb_true_iff in H; destruct H as [H _]; exact H | reflexivity] ]
  | |- negb (mmap_noreserve_backed_ok ?f ?m ?z) = true ->
       negb (mmap_noreserve_backed_ok ?f (relim Lsmall ?m) ?z) = true =>
      intros H; destruct (mmap_noreserve_backed_ok f (relim Lsmall m) z) eqn:E; [|reflexivity];
      rewrite (mmap_noreserve_backed_ok_mono Lbig Lsmall HLE f m z HM E) in H; cbn [negb] in H; discriminate H
  | |- negb (mmap_fixed_rw_budget_ok ?f ?m ?a ?n) = true ->
       negb (mmap_fixed_rw_budget_ok ?f (relim Lsmall ?m) ?a ?n) = true =>
      intros H; destruct (mmap_fixed_rw_budget_ok f (relim Lsmall m) a n) eqn:E; [|reflexivity];
      rewrite (mmap_fixed_rw_budget_ok_mono Lbig Lsmall HLE f m a n HM E) in H; cbn [negb] in H; discriminate H
  | |- negb (mmap_fixed_rw_span_budget_ok ?f ?m ?a ?n) = true ->
       negb (mmap_fixed_rw_span_budget_ok ?f (relim Lsmall ?m) ?a ?n) = true =>
      intros H; destruct (mmap_fixed_rw_span_budget_ok f (relim Lsmall m) a n) eqn:E; [|reflexivity];
      rewrite (mmap_fixed_rw_span_budget_ok_mono Lbig Lsmall HLE f m a n HM E) in H; cbn [negb] in H; discriminate H
  | |- negb (mprotect_budget_ok ?m ?a ?n) = true -> negb (mprotect_budget_ok (relim Lsmall ?m) ?a ?n) = true =>
      intros H; destruct (mprotect_budget_ok (relim Lsmall m) a n) eqn:E; [|reflexivity];
      rewrite (mprotect_budget_ok_relim Lbig Lsmall HLE m a n HM E) in H; cbn [negb] in H; discriminate H
  | |- negb (mremap_final_budget_b ?m ?o ?oo ?d ?nn && mremap_move_budget_b ?m ?o ?oo ?nn) = true ->
       negb (mremap_final_budget_b (relim Lsmall ?m) ?o ?oo ?d ?nn
             && mremap_move_budget_b (relim Lsmall ?m) ?o ?oo ?nn) = true =>
      intros H; destruct (mremap_final_budget_b (relim Lsmall m) o oo d nn) eqn:E; [|reflexivity];
      destruct (mremap_move_budget_b (relim Lsmall m) o oo nn) eqn:E2; [|reflexivity];
      rewrite (mremap_final_budget_b_mono Lbig Lsmall HLE m o oo d nn HM E), (move_mono m o oo nn HM E2) in H;
      cbn [andb negb] in H; discriminate H
  end.

Lemma alloc_mark_down : forall i m, MOK Lbig m ->
  alloc_budget_refused_b i m = true -> alloc_budget_refused_b i (relim Lsmall m) = true.
Proof.
  intros i m HM. unfold MOK in HM.
  unfold alloc_budget_refused_b, brk_budget_refused_b, mremap_budget_refused_b, mmap_budget_refused_b,
    mprotect_budget_refused_b, min_brk.
  cbv zeta.
  rewrite ?src_relim, ?uni_relim.
  autorewrite with relim_rw.
  repeat match goal with
         | |- context [if ?b then _ else _] =>
             lazymatch b with true => fail | false => fail | _ => destruct b; lazy beta iota end
         end.
  all: leaf_core HM.
Qed.

Lemma spec_up : forall i m eff m1 evs, MOK Lbig m ->
  syscall_spec i (relim Lsmall m) (Ok eff m1 evs) ->
  exists m0, syscall_spec i m (Ok eff m0 evs) /\ m1 = relim Lsmall m0 /\ MOK Lbig m0.
Proof.
  intros i m eff m1 evs HM H.
  destruct (syscall_spec_dir Lbig Lsmall HLE true i m HM ltac:(discriminate) ltac:(discriminate) _ H)
    as ([e0 m0 ev0|] & H0 & R); cbn in R; [|contradiction].
  destruct R as (<- & -> & <- & HM0). exists m0. split; [exact H0|]. split; [reflexivity | exact HM0].
Qed.

Lemma spec_down : forall i m eff m0 evs, MOK Lbig m -> MV_OK m ->
  alloc_budget_refused_b i (relim Lsmall m) = false ->
  syscall_spec i m (Ok eff m0 evs) ->
  syscall_spec i (relim Lsmall m) (Ok eff (relim Lsmall m0) evs) /\ MOK Lbig m0.
Proof.
  intros i m eff m0 evs HM MV G H.
  destruct (syscall_spec_dir Lbig Lsmall HLE false i m HM (fun _ => G) (fun _ => MV) _ H)
    as ([e1 m1 ev1|] & H1 & R); cbn in R; [|contradiction].
  destruct R as (-> & -> & -> & HM0). split; [exact H1 | exact HM0].
Qed.

Lemma refused_down : forall c, MOK Lbig (cfg_model c) -> WF (cfg_model c) ->
  budget_refused_at segs c -> budget_refused_at segs (relim_cfg Lsmall c).
Proof.
  intros [ms m] HM HW. cbn [cfg_model] in HM, HW. unfold relim_cfg. cbn [cfg_ms cfg_model].
  intros (Hh & [(Hp & report & Est & Emat) | (x8 & Hp & [Ha | (eff & m1 & evs & Hsp & Hh1 & Emat)])]);
    cbn [cfg_ms cfg_model] in *.
  - split; [exact Hh|]. cbn [cfg_ms cfg_model]. left. split; [exact Hp|]. exists report. split; [exact Est|].
    destruct (materialize_model_accesses (relim Lsmall m) (@accessed_ranges _ report)) as [m2|] eqn:E;
      [|reflexivity].
    exfalso. assert (HL : Lsmall <= vm_limit (m_vmmaps m)) by (unfold MOK in HM; rewrite HM; exact HLE).
    destruct (materialize_relim_up Lsmall m _ _ HL E) as (m0 & E0 & _). rewrite E0 in Emat. discriminate Emat.
  - split; [exact Hh|]. cbn [cfg_ms cfg_model]. right. exists x8. split; [exact Hp|]. left.
    exact (alloc_mark_down _ _ HM Ha).
  - split; [exact Hh|]. cbn [cfg_ms cfg_model]. right. exists x8. split; [exact Hp|].
    destruct (alloc_budget_refused_b (sys_input segs ms x8) (relim Lsmall m)) eqn:G; [left; reflexivity|right].
    destruct (spec_down _ _ _ _ _ HM (MV_OK_wf _ HW) G Hsp) as (Hsp' & HM1).
    exists eff, (relim Lsmall m1), evs. split; [exact Hsp'|]. split; [exact Hh1|].
    destruct (materialize_model_accesses (relim Lsmall m1) (syscall_effect_accesses eff)) as [m2|] eqn:E;
      [|reflexivity].
    exfalso. assert (HL : Lsmall <= vm_limit (m_vmmaps m1)) by (unfold MOK in HM1; rewrite HM1; exact HLE).
    destruct (materialize_relim_up Lsmall m1 _ _ HL E) as (m0 & E0 & _). rewrite E0 in Emat. discriminate Emat.
Qed.

Lemma mrip_relim : forall p s i m, MOK Lbig m -> MV_OK m -> alloc_budget_refused_b i (relim Lsmall m) = false ->
  (mremap_in_place p s i (relim Lsmall m) <-> mremap_in_place p s i m).
Proof.
  intros p s i m HM MV G. unfold mremap_in_place. split.
  - intros ((eff & m1 & evs & Hs & Hr) & Hv). split; [|exact Hv].
    destruct (spec_up _ _ _ _ _ HM Hs) as (m0 & Hs0 & _ & _). exists eff, m0, evs. split; [exact Hs0 | exact Hr].
  - intros ((eff & m1 & evs & Hs & Hr) & Hv). split; [|exact Hv].
    destruct (spec_down _ _ _ _ _ HM MV G Hs) as (Hs0 & _).
    exists eff, (relim Lsmall m1), evs. split; [exact Hs0 | exact Hr].
Qed.

Lemma cret_relim : forall p s st i m r, MOK Lbig m -> MV_OK m -> alloc_budget_refused_b i (relim Lsmall m) = false ->
  (canonical_ret p s st i (relim Lsmall m) r <-> canonical_ret p s st i m r).
Proof.
  intros p s st i m r HM MV G. unfold canonical_ret.
  pose proof (mrip_relim p s i m HM MV G) as E.
  split; intros [H | [H | [H | H]]].
  - left. exact H.
  - right. left. exact H.
  - right. right. left. destruct H as (Hn & [(Hr & Hq) | (Hq & Hf)]).
    + split; [exact Hn|]. left. split; [exact Hr | exact (proj1 E Hq)].
    + split; [exact Hn|]. right. split; [intros Hq'; exact (Hq (proj2 E Hq')) | exact Hf].
  - right. right. right. exact H.
  - left. exact H.
  - right. left. exact H.
  - right. right. left. destruct H as (Hn & [(Hr & Hq) | (Hq & Hf)]).
    + split; [exact Hn|]. left. split; [exact Hr | exact (proj2 E Hq)].
    + split; [exact Hn|]. right. split; [intros Hq'; exact (Hq (proj1 E Hq')) | exact Hf].
  - right. right. right. exact H.
Qed.

Lemma cstep_relim : forall p s st c1 c2, MOK Lbig (cfg_model c1) -> MV_OK (cfg_model c1) ->
  ~ budget_refused_at segs (relim_cfg Lsmall c1) ->
  (canonical_step p s st segs (relim_cfg Lsmall c1) (relim_cfg Lsmall c2) <-> canonical_step p s st segs c1 c2).
Proof.
  intros p s st [ms1 m1] [ms2 m2] HM MV NB. unfold relim_cfg in *. cbn [cfg_ms cfg_model] in *.
  unfold canonical_step. cbn [cfg_ms cfg_model]. split.
  - intros H x8 len Hpl.
    destruct (H x8 len Hpl) as (eff & m' & evs & m'' & Hs & Hc & Hr).
    destruct Hpl as (Hh & Hp & _).
    pose proof (not_refused_mark segs Lsmall ms1 m1 x8 NB Hh Hp) as G.
    destruct (spec_up _ _ _ _ _ HM Hs) as (m0 & Hs0 & -> & _).
    apply (f_equal cfg_ms) in Hc. cbn [cfg_ms] in Hc.
    exists eff, m0, evs, m2. split; [exact Hs0|]. split; [rewrite Hc; reflexivity|].
    exact (proj1 (cret_relim p s st _ m1 _ HM MV G) Hr).
  - intros H x8 len Hpl.
    destruct (H x8 len Hpl) as (eff & m' & evs & m'' & Hs & Hc & Hr).
    destruct Hpl as (Hh & Hp & _).
    pose proof (not_refused_mark segs Lsmall ms1 m1 x8 NB Hh Hp) as G.
    destruct (spec_down _ _ _ _ _ HM MV G Hs) as (Hs0 & _).
    apply (f_equal cfg_ms) in Hc. cbn [cfg_ms] in Hc.
    exists eff, (relim Lsmall m'), evs, (relim Lsmall m2). split; [exact Hs0|]. split; [rewrite Hc; reflexivity|].
    exact (proj2 (cret_relim p s st _ m1 _ HM MV G) Hr).
Qed.

Lemma unmap_relim : forall c1 c2 lo n, MOK Lbig (cfg_model c1) -> MV_OK (cfg_model c1) ->
  ~ budget_refused_at segs (relim_cfg Lsmall c1) ->
  (unmap_step segs (relim_cfg Lsmall c1) (relim_cfg Lsmall c2) lo n <-> unmap_step segs c1 c2 lo n).
Proof.
  intros [ms1 m1] [ms2 m2] lo n HM MV NB. unfold relim_cfg in *. cbn [cfg_ms cfg_model] in *.
  unfold unmap_step. cbn [cfg_ms cfg_model]. split.
  - intros (x8 & eff & m' & evs & m'' & Hh & Hp & Hu & Hs & Hc & Hn).
    destruct (spec_up _ _ _ _ _ HM Hs) as (m0 & Hs0 & -> & _).
    apply (f_equal cfg_ms) in Hc. cbn [cfg_ms] in Hc.
    exists x8, eff, m0, evs, m2. split; [exact Hh|]. split; [exact Hp|]. split; [exact Hu|].
    split; [exact Hs0|]. split; [rewrite Hc; reflexivity | exact Hn].
  - intros (x8 & eff & m' & evs & m'' & Hh & Hp & Hu & Hs & Hc & Hn).
    pose proof (not_refused_mark segs Lsmall ms1 m1 x8 NB Hh Hp) as G.
    destruct (spec_down _ _ _ _ _ HM MV G Hs) as (Hs0 & _).
    apply (f_equal cfg_ms) in Hc. cbn [cfg_ms] in Hc.
    exists x8, eff, (relim Lsmall m'), evs, (relim Lsmall m2). split; [exact Hh|]. split; [exact Hp|].
    split; [exact Hu|]. split; [exact Hs0|]. split; [rewrite Hc; reflexivity | exact Hn].
Qed.

Lemma strip_relim : forall p c1 c2 s s', MOK Lbig (cfg_model c1) -> MV_OK (cfg_model c1) ->
  ~ budget_refused_at segs (relim_cfg Lsmall c1) ->
  (strip_next p segs (relim_cfg Lsmall c1) (relim_cfg Lsmall c2) s s' <-> strip_next p segs c1 c2 s s').
Proof.
  intros p c1 c2 s s' HM MV NB. unfold strip_next.
  pose proof (fun lo n => unmap_relim c1 c2 lo n HM MV NB) as E.
  split; intros [(lo & n & Hu & ->) | (Hn & ->)].
  - left. exists lo, n. split; [exact (proj1 (E lo n) Hu) | reflexivity].
  - right. split; [intros lo n Hu; apply (Hn lo n); exact (proj2 (E lo n) Hu) | reflexivity].
  - left. exists lo, n. split; [exact (proj2 (E lo n) Hu) | reflexivity].
  - right. split; [intros lo n Hu; apply (Hn lo n); exact (proj1 (E lo n) Hu) | reflexivity].
Qed.

Lemma touch_relim : forall c1 c2 acc, MOK Lbig (cfg_model c1) -> MV_OK (cfg_model c1) ->
  m_halted (cfg_model c1) = None -> ~ budget_refused_at segs (relim_cfg Lsmall c1) ->
  (step_touches segs (relim_cfg Lsmall c1) (relim_cfg Lsmall c2) acc <-> step_touches segs c1 c2 acc).
Proof.
  intros [ms1 m1] [ms2 m2] acc HM MV Hh NB. unfold relim_cfg in *. cbn [cfg_ms cfg_model] in *.
  unfold step_touches. cbn [cfg_ms cfg_model]. split.
  - intros [H | (x8 & eff & m' & evs & m'' & Hp & Hs & Hc & Ha)]; [left; exact H | right].
    destruct (spec_up _ _ _ _ _ HM Hs) as (m0 & Hs0 & -> & _).
    apply (f_equal cfg_ms) in Hc. cbn [cfg_ms] in Hc.
    exists x8, eff, m0, evs, m2. split; [exact Hp|]. split; [exact Hs0|]. split; [rewrite Hc; reflexivity | exact Ha].
  - intros [H | (x8 & eff & m' & evs & m'' & Hp & Hs & Hc & Ha)]; [left; exact H | right].
    pose proof (not_refused_mark segs Lsmall ms1 m1 x8 NB Hh Hp) as G.
    destruct (spec_down _ _ _ _ _ HM MV G Hs) as (Hs0 & _).
    apply (f_equal cfg_ms) in Hc. cbn [cfg_ms] in Hc.
    exists x8, eff, (relim Lsmall m'), evs, (relim Lsmall m2). split; [exact Hp|]. split; [exact Hs0|].
    split; [rewrite Hc; reflexivity | exact Ha].
Qed.

Lemma stack_relim : forall c1 c2 st st', MOK Lbig (cfg_model c1) -> MV_OK (cfg_model c1) ->
  m_halted (cfg_model c1) = None -> ~ budget_refused_at segs (relim_cfg Lsmall c1) ->
  (stack_next segs (relim_cfg Lsmall c1) (relim_cfg Lsmall c2) st st' <-> stack_next segs c1 c2 st st').
Proof.
  intros c1 c2 st st' HM MV Hh NB. unfold stack_next.
  pose proof (fun acc => touch_relim c1 c2 acc HM MV Hh NB) as E.
  split; intros [(acc & Ht & ->) | (Hn & ->)].
  - left. exists acc. split; [exact (proj1 (E acc) Ht) | reflexivity].
  - right. split; [intros acc Ht; apply (Hn acc); exact (proj2 (E acc) Ht) | reflexivity].
  - left. exists acc. split; [exact (proj2 (E acc) Ht) | reflexivity].
  - right. split; [intros acc Ht; apply (Hn acc); exact (proj1 (E acc) Ht) | reflexivity].
Qed.

Lemma unplaced_up : forall c, MOK Lbig (cfg_model c) -> MV_OK (cfg_model c) ->
  unplaced_at segs (relim_cfg Lsmall c) -> unplaced_at segs c.
Proof.
  intros [ms m] HM MV. unfold relim_cfg. cbn [cfg_ms cfg_model] in *.
  intros (Hh & x8 & Hp & len & Hl & Hroom & G & (eff & m1 & evs & Hs) & Hall).
  cbn [cfg_ms cfg_model] in *.
  split; [exact Hh|]. exists x8. split; [exact Hp|]. exists len. cbn [cfg_ms cfg_model].
  split; [exact Hl|]. split; [exact Hroom|]. split.
  - destruct (alloc_budget_refused_b (sys_input segs ms x8) m) eqn:Ga; [|reflexivity].
    rewrite (alloc_mark_down _ _ HM Ga) in G. discriminate G.
  - split.
    + destruct (spec_up _ _ _ _ _ HM Hs) as (m0 & Hs0 & _). exists eff, m0, evs. exact Hs0.
    + intros eff' m' evs' Hs'. destruct (spec_down _ _ _ _ _ HM MV G Hs') as (Hs'' & _).
      exact (Hall _ _ _ Hs'').
Qed.

Lemma unplaced_down : forall c, MOK Lbig (cfg_model c) -> MV_OK (cfg_model c) ->
  ~ budget_refused_at segs (relim_cfg Lsmall c) ->
  unplaced_at segs c -> unplaced_at segs (relim_cfg Lsmall c).
Proof.
  intros [ms m] HM MV NB. unfold relim_cfg in *. cbn [cfg_ms cfg_model] in *.
  intros (Hh & x8 & Hp & len & Hl & Hroom & Ga & (eff & m1 & evs & Hs) & Hall).
  cbn [cfg_ms cfg_model] in *.
  pose proof (not_refused_mark segs Lsmall ms m x8 NB Hh Hp) as G.
  split; [exact Hh|]. exists x8. split; [exact Hp|]. exists len. cbn [cfg_ms cfg_model].
  split; [exact Hl|]. split; [exact Hroom|]. split; [exact G|]. split.
  - destruct (spec_down _ _ _ _ _ HM MV G Hs) as (Hs0 & _). exists eff, (relim Lsmall m1), evs. exact Hs0.
  - intros eff' m' evs' Hs'. destruct (spec_up _ _ _ _ _ HM Hs') as (m0 & Hs0 & _). exact (Hall _ _ _ Hs0).
Qed.

Lemma ccs_relim : forall p s st c, MOK Lbig (cfg_model c) -> WF (cfg_model c) ->
  ~ budget_refused_at segs (relim_cfg Lsmall c) ->
  (canon_can_step p s st segs cfg (relim_cfg Lsmall c) <-> canon_can_step p s st segs cfg c).
Proof.
  intros p s st [ms m] HM HW NB. cbn [cfg_model] in HM, HW. pose proof (MV_OK_wf _ HW) as MV.
  unfold canon_can_step. split.
  - intros (evs & c2s & Hs & Hc).
    destruct (step_up segs cfg Lbig Lsmall HLE ms m evs (SNext c2s) HM MV NB Hs) as (ms' & m0 & Hs0 & -> & HM0).
    exists evs, (mkCfg ms' m0). split; [exact Hs0|].
    exact (proj1 (cstep_relim p s st (mkCfg ms m) (mkCfg ms' m0) HM MV NB) Hc).
  - intros (evs & c2 & Hs & Hc).
    destruct (step_down_exact segs cfg Lbig Lsmall HLE ms m evs (SNext c2) HM MV NB Hs)
      as (ms' & m0 & -> & HM0 & Hs0).
    exists evs, (mkCfg ms' (relim Lsmall m0)). split; [exact Hs0|].
    exact (proj2 (cstep_relim p s st (mkCfg ms m) (mkCfg ms' m0) HM MV NB) Hc).
Qed.

Definition SafeC (p : policy) (dev : bool) (s : strip) (st : Z) (c : config) : Prop :=
  forall tr c', star_canon_fb p segs cfg dev s st c tr c' -> ~ budget_refused_at segs c'.

Lemma safe_here : forall p dev s st c, SafeC p dev s st c -> ~ budget_refused_at segs c.
Proof. intros p dev s st c H. exact (H [] c (scf_refl p segs cfg dev s st c)). Qed.

Lemma safe_canon : forall p dev s s' st st' c1 evs c2,
  SafeC p dev s st c1 -> (dev = true -> ~ unplaced_at segs c1) ->
  sstep_cfg segs cfg c1 evs (SNext c2) -> canonical_step p s st segs c1 c2 ->
  strip_next p segs c1 c2 s s' -> stack_next segs c1 c2 st st' -> SafeC p dev s' st' c2.
Proof.
  intros p dev s s' st st' c1 evs c2 H Hd Hs Hc Hsn Hst tr c' Hr.
  exact (H (evs ++ tr) c' (scf_canon p segs cfg dev s s' st st' c1 evs c2 tr c' Hd Hs Hc Hsn Hst Hr)).
Qed.

Lemma safe_fb : forall p dev s s' st st' c1 evs c2,
  SafeC p dev s st c1 -> ~ canon_can_step p s st segs cfg c1 -> ~ unplaced_at segs c1 ->
  sstep_cfg segs cfg c1 evs (SNext c2) ->
  strip_next p segs c1 c2 s s' -> stack_next segs c1 c2 st st' -> SafeC p true s' st' c2.
Proof.
  intros p dev s s' st st' c1 evs c2 H Hn Hu Hs Hsn Hst tr c' Hr.
  exact (H (evs ++ tr) c' (scf_fallback p segs cfg dev s s' st st' c1 evs c2 tr c' Hn Hu Hs Hsn Hst Hr)).
Qed.

Lemma canon_up : forall p dev s st cs tr cs', star_canon_fb p segs cfg dev s st cs tr cs' ->
  forall c, cs = relim_cfg Lsmall c -> MOK Lbig (cfg_model c) -> WF (cfg_model c) -> SafeC p dev s st cs ->
  exists c', cs' = relim_cfg Lsmall c' /\ MOK Lbig (cfg_model c') /\ WF (cfg_model c')
             /\ star_canon_fb p segs cfg dev s st c tr c'.
Proof.
  intros p dev s st cs tr cs' H.
  induction H as [dev s st cs | dev s s' st st' cs1 evs cs2 tr cs3 Hd Hs Hc Hsn Hst Hr IH
                  | dev s s' st st' cs1 evs cs2 tr cs3 Hn Hu Hs Hsn Hst Hr IH];
    intros [ms m] -> HM HW Hsafe; cbn [cfg_model] in HM, HW.
  - exists (mkCfg ms m). split; [reflexivity|]. split; [exact HM|]. split; [exact HW|]. apply scf_refl.
  - pose proof (safe_here _ _ _ _ _ Hsafe) as NB. pose proof (MV_OK_wf _ HW) as MV.
    destruct (step_up segs cfg Lbig Lsmall HLE ms m evs (SNext cs2) HM MV NB Hs) as (ms' & m0 & Hs0 & -> & HM0).
    pose proof (sstep_cfg_WF segs cfg _ _ _ Hs0 HW) as HW0.
    pose proof (sstep_live _ _ _ _ _ Hs0) as Hh.
    destruct (IH (mkCfg ms' m0) eq_refl HM0 HW0 (safe_canon _ _ _ _ _ _ _ _ _ Hsafe Hd Hs Hc Hsn Hst))
      as (c' & -> & HM' & HW' & Hr').
    exists c'. split; [reflexivity|]. split; [exact HM'|]. split; [exact HW'|].
    apply (scf_canon p segs cfg dev s s' st st' (mkCfg ms m) evs (mkCfg ms' m0) tr c').
    + intros Hdv Hu. apply (Hd Hdv). exact (unplaced_down (mkCfg ms m) HM MV NB Hu).
    + exact Hs0.
    + exact (proj1 (cstep_relim p s st (mkCfg ms m) (mkCfg ms' m0) HM MV NB) Hc).
    + exact (proj1 (strip_relim p (mkCfg ms m) (mkCfg ms' m0) s s' HM MV NB) Hsn).
    + exact (proj1 (stack_relim (mkCfg ms m) (mkCfg ms' m0) st st' HM MV Hh NB) Hst).
    + exact Hr'.
  - pose proof (safe_here _ _ _ _ _ Hsafe) as NB. pose proof (MV_OK_wf _ HW) as MV.
    destruct (step_up segs cfg Lbig Lsmall HLE ms m evs (SNext cs2) HM MV NB Hs) as (ms' & m0 & Hs0 & -> & HM0).
    pose proof (sstep_cfg_WF segs cfg _ _ _ Hs0 HW) as HW0.
    pose proof (sstep_live _ _ _ _ _ Hs0) as Hh.
    destruct (IH (mkCfg ms' m0) eq_refl HM0 HW0 (safe_fb _ _ _ _ _ _ _ _ _ Hsafe Hn Hu Hs Hsn Hst))
      as (c' & -> & HM' & HW' & Hr').
    exists c'. split; [reflexivity|]. split; [exact HM'|]. split; [exact HW'|].
    apply (scf_fallback p segs cfg dev s s' st st' (mkCfg ms m) evs (mkCfg ms' m0) tr c').
    + intros Hcan. apply Hn. exact (proj2 (ccs_relim p s st (mkCfg ms m) HM HW NB) Hcan).
    + intros Hu'. apply Hu. exact (unplaced_down (mkCfg ms m) HM MV NB Hu').
    + exact Hs0.
    + exact (proj1 (strip_relim p (mkCfg ms m) (mkCfg ms' m0) s s' HM MV NB) Hsn).
    + exact (proj1 (stack_relim (mkCfg ms m) (mkCfg ms' m0) st st' HM MV Hh NB) Hst).
    + exact Hr'.
Qed.

Lemma canon_down : forall p dev s st c tr c', star_canon_fb p segs cfg dev s st c tr c' ->
  MOK Lbig (cfg_model c) -> WF (cfg_model c) -> SafeC p dev s st (relim_cfg Lsmall c) ->
  MOK Lbig (cfg_model c') /\ WF (cfg_model c')
  /\ star_canon_fb p segs cfg dev s st (relim_cfg Lsmall c) tr (relim_cfg Lsmall c').
Proof.
  intros p dev s st c tr c' H.
  induction H as [dev s st c | dev s s' st st' c1 evs c2 tr c3 Hd Hs Hc Hsn Hst Hr IH
                  | dev s s' st st' c1 evs c2 tr c3 Hn Hu Hs Hsn Hst Hr IH];
    intros HM HW Hsafe.
  - split; [exact HM|]. split; [exact HW|]. apply scf_refl.
  - destruct c1 as [ms m]. cbn [cfg_model] in HM, HW.
    pose proof (safe_here _ _ _ _ _ Hsafe) as NB. pose proof (MV_OK_wf _ HW) as MV.
    pose proof (sstep_live _ _ _ _ _ Hs) as Hh.
    pose proof (sstep_cfg_WF segs cfg _ _ _ Hs HW) as HW2.
    destruct (step_down_exact segs cfg Lbig Lsmall HLE ms m evs (SNext c2) HM MV NB Hs)
      as (ms' & m0 & -> & HM0 & Hs0).
    assert (Hd' : dev = true -> ~ unplaced_at segs (relim_cfg Lsmall (mkCfg ms m))).
    { intros Hdv Hu. apply (Hd Hdv). exact (unplaced_up (mkCfg ms m) HM MV Hu). }
    pose proof (proj2 (cstep_relim p s st (mkCfg ms m) (mkCfg ms' m0) HM MV NB) Hc) as Hc'.
    pose proof (proj2 (strip_relim p (mkCfg ms m) (mkCfg ms' m0) s s' HM MV NB) Hsn) as Hsn'.
    pose proof (proj2 (stack_relim (mkCfg ms m) (mkCfg ms' m0) st st' HM MV Hh NB) Hst) as Hst'.
    destruct (IH HM0 HW2 (safe_canon _ _ _ _ _ _ _ _ _ Hsafe Hd' Hs0 Hc' Hsn' Hst')) as (HM' & HW' & Hr').
    split; [exact HM'|]. split; [exact HW'|].
    exact (scf_canon p segs cfg dev s s' st st' _ evs _ tr _ Hd' Hs0 Hc' Hsn' Hst' Hr').
  - destruct c1 as [ms m]. cbn [cfg_model] in HM, HW.
    pose proof (safe_here _ _ _ _ _ Hsafe) as NB. pose proof (MV_OK_wf _ HW) as MV.
    pose proof (sstep_live _ _ _ _ _ Hs) as Hh.
    pose proof (sstep_cfg_WF segs cfg _ _ _ Hs HW) as HW2.
    destruct (step_down_exact segs cfg Lbig Lsmall HLE ms m evs (SNext c2) HM MV NB Hs)
      as (ms' & m0 & -> & HM0 & Hs0).
    assert (Hn' : ~ canon_can_step p s st segs cfg (relim_cfg Lsmall (mkCfg ms m))).
    { intros Hcan. apply Hn. exact (proj1 (ccs_relim p s st (mkCfg ms m) HM HW NB) Hcan). }
    assert (Hu' : ~ unplaced_at segs (relim_cfg Lsmall (mkCfg ms m))).
    { intros Hu0. apply Hu. exact (unplaced_up (mkCfg ms m) HM MV Hu0). }
    pose proof (proj2 (strip_relim p (mkCfg ms m) (mkCfg ms' m0) s s' HM MV NB) Hsn) as Hsn'.
    pose proof (proj2 (stack_relim (mkCfg ms m) (mkCfg ms' m0) st st' HM MV Hh NB) Hst) as Hst'.
    destruct (IH HM0 HW2 (safe_fb _ _ _ _ _ _ _ _ _ Hsafe Hn' Hu' Hs0 Hsn' Hst')) as (HM' & HW' & Hr').
    split; [exact HM'|]. split; [exact HW'|].
    exact (scf_fallback p segs cfg dev s s' st st' _ evs _ tr _ Hn' Hu' Hs0 Hsn' Hst' Hr').
Qed.

Lemma guarded_up : forall cs tr cs', star_guarded segs cfg cs tr cs' ->
  forall c, cs = relim_cfg Lsmall c -> MOK Lbig (cfg_model c) -> WF (cfg_model c) ->
  exists c', cs' = relim_cfg Lsmall c' /\ MOK Lbig (cfg_model c') /\ WF (cfg_model c')
             /\ star_guarded segs cfg c tr c'.
Proof.
  intros cs tr cs' H.
  induction H as [cs | cs1 evs cs2 tr cs3 Hu Hb Hs Hr IH]; intros [ms m] -> HM HW; cbn [cfg_model] in HM, HW.
  - exists (mkCfg ms m). split; [reflexivity|]. split; [exact HM|]. split; [exact HW|]. apply sg_refl.
  - pose proof (MV_OK_wf _ HW) as MV.
    destruct (step_up segs cfg Lbig Lsmall HLE ms m evs (SNext cs2) HM MV Hb Hs) as (ms' & m0 & Hs0 & -> & HM0).
    pose proof (sstep_cfg_WF segs cfg _ _ _ Hs0 HW) as HW0.
    destruct (IH (mkCfg ms' m0) eq_refl HM0 HW0) as (c' & -> & HM' & HW' & Hr').
    exists c'. split; [reflexivity|]. split; [exact HM'|]. split; [exact HW'|].
    apply (sg_step segs cfg (mkCfg ms m) evs (mkCfg ms' m0) tr c').
    + intros Hu'. apply Hu. exact (unplaced_down (mkCfg ms m) HM MV Hb Hu').
    + intros Hb'. apply Hb. exact (refused_down (mkCfg ms m) HM HW Hb').
    + exact Hs0.
    + exact Hr'.
Qed.

End Relim.

Lemma init_safe : forall env p segs pc ph sp brk0 mbase rnd (Lsmall Lbig : Z) inp,
  ~ canon_budget_refused env p (mkImage segs pc ph) Lsmall (mkEntry sp brk0 mbase rnd) inp ->
  SafeC segs env p false full_strip
    (stack_low (m_vmmaps (cfg_model (init_config segs pc ph sp brk0 mbase rnd Lbig inp))) p)
    (relim_cfg Lsmall (init_config segs pc ph sp brk0 mbase rnd Lbig inp)).
Proof.
  intros env p segs pc ph sp brk0 mbase rnd Lsmall Lbig inp Hnr tr c Hr Hb. apply Hnr. cbn [canon_budget_refused].
  rewrite (init_config_relim segs pc ph sp brk0 mbase rnd Lbig Lsmall inp).
  exists tr, c. split; [|exact Hb]. unfold canon_run. rewrite stack_low_relim. exact Hr.
Qed.

Lemma canon_relim_nr : forall (env : SpuriousCfg) (p : RoomShapesDraft.policy) (img : Image) (Lsmall Lbig : Z) en inp,
  Lsmall <= Lbig ->
  ~ RoomShapesDraft.canon_budget_refused env p img Lsmall en inp ->
  ~ RoomShapesDraft.canon_budget_refused env p img Lbig en inp.
Proof.
  intros env p [segs pc ph] Lsmall Lbig [sp brk0 mbase rnd] inp HLE Hnr.
  pose proof (init_safe env p segs pc ph sp brk0 mbase rnd Lsmall Lbig inp Hnr) as Hsafe.
  pose proof (init_config_limit segs pc ph sp brk0 mbase rnd Lbig inp) as HM0.
  pose proof (init_config_WF segs pc ph sp brk0 mbase rnd Lbig inp) as HW0.
  intros (tr & c & Hr & Hb).
  destruct (canon_down segs env Lbig Lsmall HLE _ _ _ _ _ _ _ Hr HM0 HW0 Hsafe) as (HMc & HWc & Hr').
  exact (Hsafe _ _ Hr' (refused_down segs env Lbig Lsmall HLE c HMc HWc Hb)).
Qed.

Lemma canon_relim_pt : forall (env : SpuriousCfg) (p : RoomShapesDraft.policy) (img : Image) (Lsmall Lbig : Z) en inp,
  RoomShapesDraft.policy_ok p -> valid_entry img en inp -> valid_input inp -> Lsmall <= Lbig ->
  ~ RoomShapesDraft.canon_budget_refused env p img Lsmall en inp ->
  (RoomShapesDraft.guarded_reaches_error env p img Lsmall en inp ->
   RoomShapesDraft.guarded_reaches_error env p img Lbig en inp)
  /\ (forall tr, RoomShapesDraft.canon_trace env p img Lsmall en inp tr <->
                 RoomShapesDraft.canon_trace env p img Lbig en inp tr).
Proof.
  intros env p [segs pc ph] Lsmall Lbig [sp brk0 mbase rnd] inp _ _ _ HLE Hnr.
  pose proof (init_safe env p segs pc ph sp brk0 mbase rnd Lsmall Lbig inp Hnr) as Hsafe.
  pose proof (init_config_limit segs pc ph sp brk0 mbase rnd Lbig inp) as HM0.
  pose proof (init_config_WF segs pc ph sp brk0 mbase rnd Lbig inp) as HW0.
  split.
  - cbn [guarded_reaches_error].
    intros (tr & c & evs & Hrun & He).
    rewrite (init_config_relim segs pc ph sp brk0 mbase rnd Lbig Lsmall inp) in Hrun.
    destruct Hrun as [(Hg & Hu & Hb) | Hr].
    + destruct (guarded_up segs env Lbig Lsmall HLE _ _ _ Hg _ eq_refl HM0 HW0) as ([ms m] & -> & HMc & HWc & Hg').
      cbn [cfg_model] in HMc, HWc.
      exists tr, (mkCfg ms m), evs. split.
      * left. split; [exact Hg'|]. split.
        -- intros Hu'. apply Hu.
           exact (unplaced_down segs env Lbig Lsmall HLE (mkCfg ms m) HMc (MV_OK_wf _ HWc) Hb Hu').
        -- intros Hb'. apply Hb. exact (refused_down segs env Lbig Lsmall HLE (mkCfg ms m) HMc HWc Hb').
      * exact (step_up segs env Lbig Lsmall HLE ms m evs SError HMc (MV_OK_wf _ HWc) Hb He).
    + unfold canon_run in Hr. rewrite stack_low_relim in Hr.
      pose proof (Hsafe _ _ Hr) as Hb.
      destruct (canon_up segs env Lbig Lsmall HLE _ _ _ _ _ _ _ Hr _ eq_refl HM0 HW0 Hsafe)
        as ([ms m] & -> & HMc & HWc & Hr').
      cbn [cfg_model] in HMc, HWc.
      exists tr, (mkCfg ms m), evs. split.
      * right. exact Hr'.
      * exact (step_up segs env Lbig Lsmall HLE ms m evs SError HMc (MV_OK_wf _ HWc) Hb He).
  - intros tr. split.
    + intros (tr' & c & Hr & Hpre). cbn [canon_trace].
      rewrite (init_config_relim segs pc ph sp brk0 mbase rnd Lbig Lsmall inp) in Hr.
      unfold canon_run in Hr. rewrite stack_low_relim in Hr.
      destruct (canon_up segs env Lbig Lsmall HLE _ _ _ _ _ _ _ Hr _ eq_refl HM0 HW0 Hsafe)
        as (c' & _ & _ & _ & Hr').
      exists tr', c'. split; [exact Hr' | exact Hpre].
    + intros (tr' & c & Hr & Hpre).
      destruct (canon_down segs env Lbig Lsmall HLE _ _ _ _ _ _ _ Hr HM0 HW0 Hsafe) as (_ & _ & Hr').
      cbn [canon_trace]. rewrite (init_config_relim segs pc ph sp brk0 mbase rnd Lbig Lsmall inp).
      exists tr', (relim_cfg Lsmall c). split; [|exact Hpre].
      unfold canon_run. rewrite stack_low_relim. exact Hr'.
Qed.

Theorem agrees_in_room_relim_source : forall (env : SpuriousCfg) (Lsmall Lbig Lt : Z) (pl sn : Image),
  Lsmall <= Lbig ->
  RoomShapesDraft.agrees_in_room env Lbig Lt pl sn ->
  RoomShapesDraft.agrees_in_room env Lsmall Lt pl sn.
Proof.
  intros env Lsmall Lbig Lt pl sn HLE HA p en_plain en_san inp Hp Hvp Hvs Hvi Hnr.
  destruct (HA p en_plain en_san inp Hp Hvp Hvs Hvi (canon_relim_nr env p pl Lsmall Lbig en_plain inp HLE Hnr))
    as (NEp & NEs & Htr).
  destruct (canon_relim_pt env p pl Lsmall Lbig en_plain inp Hp Hvp Hvi HLE Hnr) as (Herr & Htr').
  split; [intros E; exact (NEp (Herr E))|]. split; [exact NEs|].
  intros tr. split; intros H.
  - exact (proj1 (Htr tr) (proj1 (Htr' tr) H)).
  - exact (proj2 (Htr' tr) (proj2 (Htr tr) H)).
Qed.
