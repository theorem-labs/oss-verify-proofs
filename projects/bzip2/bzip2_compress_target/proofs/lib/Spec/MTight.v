(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc MallocCtrl MI_Inv MI_Kit MI_Arith.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require MI_Bits.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require MI_WCreate2 MI_WSlot2.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Inv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Kit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Arith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Bits.MI_Cnt OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WCreate2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WSlot2.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition full1 (st : mstate) (g : aptr) : Prop :=
  m_avail (MR st g) = 0 /\ m_freed (MR st g) = 0 /\ m_next (MR st g) = Some g.

(* [comment removed for export] *)
Definition in_pool (st : mstate) (x : aptr) : Prop :=
  c_free_meta_head (s_ctx st) = Some x
  \/ exists am i, c_avail_meta (s_ctx st) = Some am /\ 0 <= i /\ x = aadd am (META_SIZE * i).

Record TT (c : Z) (st : mstate) : Prop := mkTT {
  tt_init : c_init_done (s_ctx st) <> 0;
  tt_act : forall sc, active st sc = None \/ exists g, active st sc = Some g /\ full1 st g /\ ~ in_pool st g;
  tt_bnc : c_bounces (s_ctx st) = ∅;
  tt_useq : c_unmap_seq (s_ctx st) = ∅;
  tt_free : forall m, c_free_meta_head (s_ctx st) = Some m ->
             m_next (MR st m) = Some m /\ forall am i, c_avail_meta (s_ctx st) = Some am -> 0 <= i -> m <> aadd am (META_SIZE * i);
  tt_avail : c_avail_meta (s_ctx st) <> None;
  tt_cnt : c <= c_avail_meta_count (s_ctx st)
}.

Lemma aadd_aadd p a b : aadd (aadd p a) b = aadd p (a + b).
Proof. unfold aadd. cbn. f_equal. lia. Qed.
Lemma aadd_0 p : aadd p 0 = p.
Proof. unfold aadd. destruct p; cbn; f_equal; lia. Qed.
Lemma aadd_inj p a b : aadd p a = aadd p b -> a = b.
Proof. unfold aadd. destruct p; cbn. intros H. injection H. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma live_ranges_ext st st' : s_regions st' = s_regions st -> s_reserved st' = s_reserved st -> live_ranges st' = live_ranges st.
Proof. intros A B. unfold live_ranges. rewrite A, B. reflexivity. Qed.

Lemma is_bouncing_tt c st sc : TT c st -> is_bouncing sc st = false.
Proof.
  intros HT. unfold is_bouncing. destruct (sc_in_seq_range sc); [|reflexivity]. cbn [andb].
  unfold bounces. rewrite (tt_bnc _ _ HT). rewrite lookup_empty. reflexivity.
Qed.

Lemma account_bounce_tt c st sc : TT c st -> account_bounce sc st = st.
Proof.
  intros HT. unfold account_bounce. destruct (sc_in_seq_range sc); [|reflexivity].
  unfold unmap_seq. rewrite (tt_useq _ _ HT). rewrite lookup_empty. cbn. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_seq_facts st :
  s_regions (step_seq st) = s_regions st /\ s_reserved (step_seq st) = s_reserved st /\ s_metas (step_seq st) = s_metas st
  /\ s_groups (step_seq st) = s_groups st /\ s_slots (step_seq st) = s_slots st /\ s_next_rid (step_seq st) = s_next_rid st
  /\ c_active (s_ctx (step_seq st)) = c_active (s_ctx st) /\ c_usage (s_ctx (step_seq st)) = c_usage (s_ctx st)
  /\ c_bounces (s_ctx (step_seq st)) = c_bounces (s_ctx st)
  /\ c_free_meta_head (s_ctx (step_seq st)) = c_free_meta_head (s_ctx st)
  /\ c_avail_meta (s_ctx (step_seq st)) = c_avail_meta (s_ctx st)
  /\ c_avail_meta_count (s_ctx (step_seq st)) = c_avail_meta_count (s_ctx st)
  /\ c_init_done (s_ctx (step_seq st)) = c_init_done (s_ctx st)
  /\ c_mmap_counter (s_ctx (step_seq st)) = c_mmap_counter (s_ctx st)
  /\ (c_unmap_seq (s_ctx st) = ∅ -> c_unmap_seq (s_ctx (step_seq st)) = ∅).
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); cbn; repeat split; try reflexivity; intros ->; reflexivity. Qed.

Lemma TT_step_seq c st : TT c st -> TT c (step_seq st).
Proof.
  intros HT. cps_pose (step_seq_facts st) as (_ & _ & M & _ & _ & _ & A & _ & B & F & AV & CN & I & _ & U).
  assert (MRe : forall x, MR (step_seq st) x = MR st x) by (intros x; unfold MR, get_meta_rec; rewrite M; reflexivity).
  assert (ACe : forall sc, active (step_seq st) sc = active st sc) by (intros sc; unfold active; rewrite A; reflexivity).
  assert (PL : forall x, in_pool (step_seq st) x <-> in_pool st x) by (intros x; unfold in_pool; rewrite F, AV; tauto).
  constructor.
  - rewrite I. apply (tt_init _ _ HT).
  - intros sc. rewrite ACe. destruct (tt_act _ _ HT sc) as [H|(g & H & [F1 [F2 F3]] & NP)]; [left; exact H| right].
    exists g. split; [exact H|]. unfold full1. rewrite !MRe. split; [split; [exact F1| split; [exact F2| exact F3]]|]. rewrite PL. exact NP.
  - rewrite B. apply (tt_bnc _ _ HT).
  - apply U. apply (tt_useq _ _ HT).
  - intros m Hm. rewrite F in Hm. rewrite MRe, AV. exact (tt_free _ _ HT m Hm).
  - rewrite AV. apply (tt_avail _ _ HT).
  - rewrite CN. apply (tt_cnt _ _ HT).
Qed.

(* [comment removed for export] *)
Lemma queue_empty_eq {T} h m st (k : mstate -> M T) bail :
  m_next (MR st m) = None -> m_prev (MR st m) = None -> get_head st h = None ->
  queue h m st k bail = k (set_head h (Some m) (upd_meta m (fun r => m_set_prev (Some m) (m_set_next (Some m) r)) st)).
Proof.
  intros N P H. unfold queue. fold (MR st m). rewrite N, P. cbn [optr_eqb guard]. rewrite H. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma queue_nonempty_eq {T} h m hd st (k : mstate -> M T) bail :
  m_next (MR st m) = None -> m_prev (MR st m) = None -> get_head st h = Some hd ->
  queue h m st k bail =
    k (upd_meta hd (m_set_prev (Some m))
         (match m_prev (MR st hd) with
          | Some pv => upd_meta pv (m_set_next (Some m)) (upd_meta m (fun r => m_set_prev (m_prev (MR st hd)) (m_set_next (Some hd) r)) st)
          | None => upd_meta m (fun r => m_set_prev (m_prev (MR st hd)) (m_set_next (Some hd) r)) st
          end)).
Proof.
  intros N P H. unfold queue. fold (MR st m). rewrite N, P. cbn [optr_eqb guard]. rewrite H. fold (MR st hd). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma free_meta_eq {T} m st (k : mstate -> M T) bail :
  exists st', free_meta m st k bail = k st'
    /\ s_regions st' = s_regions st /\ s_reserved st' = s_reserved st /\ s_next_rid st' = s_next_rid st
    /\ s_groups st' = s_groups st /\ s_slots st' = s_slots st
    /\ (forall sc, active st' sc = active st sc) /\ (forall sc, usage st' sc = usage st sc)
    /\ c_bounces (s_ctx st') = c_bounces (s_ctx st) /\ c_unmap_seq (s_ctx st') = c_unmap_seq (s_ctx st)
    /\ c_init_done (s_ctx st') = c_init_done (s_ctx st) /\ c_avail_meta (s_ctx st') = c_avail_meta (s_ctx st)
    /\ c_avail_meta_count (s_ctx st') = c_avail_meta_count (s_ctx st) /\ c_mmap_counter (s_ctx st') = c_mmap_counter (s_ctx st)
    /\ (c_free_meta_head (s_ctx st) = None ->
        c_free_meta_head (s_ctx st') = Some m /\ MR st' m = mkMeta (Some m) (Some m) None 0 0 0 0 0 0)
    /\ (forall hd, c_free_meta_head (s_ctx st) = Some hd -> c_free_meta_head (s_ctx st') = Some hd)
    /\ (forall x, x <> m -> c_free_meta_head (s_ctx st) <> Some x ->
          (forall hd, c_free_meta_head (s_ctx st) = Some hd -> m_prev (MR st hd) <> Some x) -> MR st' x = MR st x).
Proof.
  unfold free_meta.
  set (st0 := put_meta m meta0 st).
  assert (M0 : MR st0 m = meta0) by (unfold st0, MR; apply get_meta_rec_put_same).
  assert (Mo : forall x, x <> m -> MR st0 x = MR st x) by (intros x NE; unfold st0, MR; apply get_meta_rec_put_other; exact NE).
  destruct (c_free_meta_head (s_ctx st)) as [hd|] eqn:FH.
  - rewrite (queue_nonempty_eq LFree m hd st0 k bail); [| rewrite M0; reflexivity| rewrite M0; reflexivity| unfold get_head; cbn; exact FH].
    destruct (m_prev (MR st0 hd)) as [pv|] eqn:PV.
    + eexists. split; [reflexivity|]. repeat (split; [intros; reflexivity|]). split; [intros E; discriminate|].
      split; [intros hd' E; injection E as <-; unfold st0; cbn; exact FH|].
      intros x NX NH NP. unfold MR.
      assert (x <> hd) by (intros ->; apply NH; reflexivity).
      assert (x <> pv).
      { intros ->. destruct (aptr_eqb_spec hd m) as [->|NE'].
        - rewrite M0 in PV. discriminate.
        - rewrite (Mo hd NE') in PV. exact (NP hd eq_refl PV). }
      rewrite !get_meta_rec_upd_other by congruence. apply Mo. exact NX.
    + eexists. split; [reflexivity|]. repeat (split; [intros; reflexivity|]). split; [intros E; discriminate|].
      split; [intros hd' E; injection E as <-; unfold st0; cbn; exact FH|].
      intros x NX NH NP. unfold MR.
      assert (x <> hd) by (intros ->; apply NH; reflexivity).
      rewrite !get_meta_rec_upd_other by congruence. apply Mo. exact NX.
  - rewrite (queue_empty_eq LFree m st0 k bail); [| rewrite M0; reflexivity| rewrite M0; reflexivity| unfold get_head; cbn; exact FH].
    eexists. split; [reflexivity|]. repeat (split; [intros; reflexivity|]).
    split; [intros _; split; [reflexivity| unfold MR; rewrite get_meta_rec_set_head, get_meta_rec_upd_same; fold (MR st0 m); rewrite M0; reflexivity]|].
    split; [intros hd E; discriminate|].
    intros x NX _ _. unfold MR. rewrite get_meta_rec_set_head, get_meta_rec_upd_other by congruence. apply Mo. exact NX.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition agtn (st : mstate) (sc : Z) (m p : aptr) (cnt ai : Z) : mstate :=
  let st1 := set_usage sc (usage st sc + cnt) st in
  let st2 := upd_meta m (agG sc p cnt ai) st1 in
  let st3 := put_group p (Some m) ai st2 in
  add_slots m p (get_stride (get_meta_rec st3 m)) cnt st3.

Lemma ag_tail_none_eq {T} st sc m p cnt ai (k : mstate -> optr -> M T) :
  ag_tail lay_none st sc m p cnt ai k = k (agtn st sc m p cnt ai) (Some m).
Proof. reflexivity. Qed.

Section AGTN.
Variables (st : mstate) (sc : Z) (m p : aptr) (cnt ai : Z).
Let st' := agtn st sc m p cnt ai.
Lemma agtn_MR_m : MR st' m = agG sc p cnt ai (MR st m).
Proof. unfold MR, get_meta_rec, st', agtn. cbn -[agG get_meta_rec]. rewrite lookup_insert_eq. reflexivity. Qed.
Lemma agtn_MR_other x : x <> m -> MR st' x = MR st x.
Proof. intros NE. unfold MR, get_meta_rec, st', agtn. cbn -[agG get_meta_rec]. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
Lemma agtn_active sc0 : active st' sc0 = active st sc0. Proof. reflexivity. Qed.
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
End AGTN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record CF (st st' : mstate) : Prop := mkCF {
  cf_regions : s_regions st' = s_regions st;
  cf_reserved : s_reserved st' = s_reserved st;
  cf_init : c_init_done (s_ctx st') = c_init_done (s_ctx st);
  cf_bnc : c_bounces (s_ctx st') = ∅;
  cf_useq : c_unmap_seq (s_ctx st') = ∅
}.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma try_avail_tight {T} c st sc (k : mstate -> Z -> M T) bail :
  TT c st ->
  (forall a b g, active st a = Some g -> active st b = Some g -> a = b) ->
  exists st1,
    try_avail sc st k bail = k st1 0
    /\ active st1 sc = None
    /\ (forall sc', sc' <> sc -> active st1 sc' = active st sc')
    /\ (forall a b g, active st1 a = Some g -> active st1 b = Some g -> a = b)
    /\ TT c st1
    /\ CF st st1
    /\ (s_ctx st1 = s_ctx (set_active sc None st) \/ st1 = st)
    /\ s_groups st1 = s_groups st /\ s_slots st1 = s_slots st /\ s_next_rid st1 = s_next_rid st
    /\ (forall x, in_pool st1 x <-> in_pool st x)
    /\ (forall x, active st sc <> Some x -> MR st1 x = MR st x).
Proof.
  intros HT INJ. unfold try_avail.
  destruct (tt_act _ _ HT sc) as [HA|(g & HA & (F1 & F2 & F3) & NP)].
  - rewrite HA. exists st. split; [reflexivity|]. split; [exact HA|]. split; [auto|]. split; [exact INJ|]. split; [exact HT|].
    split; [constructor; try reflexivity; [apply (tt_bnc _ _ HT)| apply (tt_useq _ _ HT)]|].
    split; [right; reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [tauto|]. auto.
  - rewrite HA. fold (MR st g). rewrite F1. cbn [Z.eqb negb]. rewrite F2. cbn [Z.eqb].
    set (st1 := dequeue (LActive sc) g st).
    assert (E1 : st1 = upd_meta g (fun r => m_set_prev None (m_set_next None r)) (set_active sc None st)).
    { unfold st1, dequeue. fold (MR st g). rewrite F3, optr_eqb_refl. cbn [negb]. reflexivity. }
    assert (A1 : forall sc', active st1 sc' = if sc' =? sc then None else active st sc').
    { intros sc'. rewrite E1, active_upd_meta, active_set_active. reflexivity. }
    rewrite (A1 sc), Z.eqb_refl.
    exists st1. split; [reflexivity|]. split; [rewrite A1, Z.eqb_refl; reflexivity|].
    assert (A2 : forall sc', sc' <> sc -> active st1 sc' = active st sc') by (intros sc' NE; rewrite A1; destruct (Z.eqb_spec sc' sc); [lia| reflexivity]).
    split; [exact A2|].
    assert (MRo : forall x, x <> g -> MR st1 x = MR st x).
    { intros x NE. rewrite E1. unfold MR. rewrite get_meta_rec_upd_other by exact NE. reflexivity. }
    assert (PL : forall x, in_pool st1 x <-> in_pool st x) by (intros x; rewrite E1; unfold in_pool; cbn; tauto).
    split.
    { intros a b g' Ha Hb. rewrite A1 in Ha, Hb. destruct (Z.eqb_spec a sc); [discriminate|]. destruct (Z.eqb_spec b sc); [discriminate|]. eauto. }
    split.
    { constructor.
      - rewrite E1. cbn. apply (tt_init _ _ HT).
      - intros sc'. rewrite A1. destruct (Z.eqb_spec sc' sc) as [->|NE]; [left; reflexivity|].
        destruct (tt_act _ _ HT sc') as [H|(g' & H & (G1 & G2 & G3) & NP')]; [left; exact H| right].
        assert (NE' : g' <> g) by (intros ->; apply NE; eapply INJ; eauto).
        exists g'. split; [exact H|]. unfold full1. rewrite !MRo by exact NE'. split; [split; [exact G1| split; [exact G2| exact G3]]|]. rewrite PL. exact NP'.
      - rewrite E1. cbn. apply (tt_bnc _ _ HT).
      - rewrite E1. cbn. apply (tt_useq _ _ HT).
      - intros m Hm. rewrite E1 in Hm. cbn in Hm. destruct (tt_free _ _ HT m Hm) as [N1 N2].
        assert (NE : m <> g) by (intros ->; apply NP; left; exact Hm).
        rewrite MRo by exact NE. split; [exact N1|]. rewrite E1. cbn. exact N2.
      - rewrite E1. cbn. apply (tt_avail _ _ HT).
      - rewrite E1. cbn. apply (tt_cnt _ _ HT). }
    split; [rewrite E1; constructor; cbn; try reflexivity; [apply (tt_bnc _ _ HT)| apply (tt_useq _ _ HT)]|].
    split; [left; rewrite E1; reflexivity|]. split; [rewrite E1; reflexivity|]. split; [rewrite E1; reflexivity|]. split; [rewrite E1; reflexivity|].
    split; [exact PL|]. intros x NX. apply MRo. congruence.
Qed.

(* [comment removed for export] *)
Definition cursor_sub (st st' : mstate) : Prop :=
  forall am' i, c_avail_meta (s_ctx st') = Some am' -> 0 <= i ->
    exists am j, c_avail_meta (s_ctx st) = Some am /\ 0 <= j /\ aadd am' (META_SIZE * i) = aadd am (META_SIZE * j).

Lemma cursor_sub_refl st : cursor_sub st st.
Proof. intros am i H Hi. exists am, i. auto. Qed.
Lemma cursor_sub_adv st st' am : c_avail_meta (s_ctx st) = Some am -> c_avail_meta (s_ctx st') = Some (aadd am META_SIZE) -> cursor_sub st st'.
Proof.
  intros H H' am' i E Hi. rewrite H' in E. injection E as <-. exists am, (1 + i). split; [exact H|]. split; [lia|].
  rewrite aadd_aadd. f_equal. lia.
Qed.
(* [comment removed for export] *)


Lemma cursor_sub_eq st st' : c_avail_meta (s_ctx st') = c_avail_meta (s_ctx st) -> cursor_sub st st'.
Proof. intros E am i H Hi. rewrite E in H. exists am, i. auto. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma alloc_meta_tight {T} c st (k : mstate -> optr -> M T) bail :
  TT c st -> 1 <= c ->
  exists st1 m,
    alloc_meta st k bail = k st1 (Some m)
    /\ in_pool st m /\ ~ in_pool st1 m /\ (forall x, in_pool st1 x -> in_pool st x /\ x <> m)
    /\ TT (c - 1) st1
    /\ m_next (MR st1 m) = None /\ m_prev (MR st1 m) = None
    /\ (forall x, x <> m -> MR st1 x = MR st x)
    /\ (forall sc, active st1 sc = active st sc) /\ (forall sc, usage st1 sc = usage st sc)
    /\ c_free_meta_head (s_ctx st1) = None
    /\ CF st st1 /\ s_groups st1 = s_groups st /\ s_slots st1 = s_slots st /\ s_next_rid st1 = s_next_rid st
    /\ c_mmap_counter (s_ctx st1) = c_mmap_counter (s_ctx st)
    /\ c_avail_meta_count (s_ctx st1) = c_avail_meta_count (s_ctx st) - match c_free_meta_head (s_ctx st) with Some _ => 0 | None => 1 end
    /\ cursor_sub st st1.
Proof.
  intros HT Hc. unfold alloc_meta.
  replace (c_init_done (ctx st) =? 0) with false by (symmetry; apply Z.eqb_neq; apply (tt_init _ _ HT)).
  destruct (c_free_meta_head (ctx st)) as [m|] eqn:FH.
  - (* [comment removed for export] *)
    destruct (tt_free _ _ HT m FH) as [NX NC].
    set (st1 := dequeue LFree m st).
    assert (E1 : st1 = upd_meta m (fun r => m_set_prev None (m_set_next None r)) (upd_ctx (set_free_meta_head None) st)).
    { unfold st1, dequeue. fold (MR st m). rewrite NX, optr_eqb_refl. cbn [negb]. reflexivity. }
    exists st1, m. split; [reflexivity|].
    assert (MRm : MR st1 m = m_set_prev None (m_set_next None (MR st m))) by (rewrite E1; unfold MR; rewrite get_meta_rec_upd_same; reflexivity).
    assert (MRo : forall x, x <> m -> MR st1 x = MR st x) by (intros x NE; rewrite E1; unfold MR; rewrite get_meta_rec_upd_other by exact NE; reflexivity).
    assert (PL : forall x, in_pool st1 x -> in_pool st x /\ x <> m).
    { intros x [H|(am & i & H & Hi & ->)]; rewrite E1 in H; cbn in H; [discriminate|].
      split; [right; exists am, i; auto| apply not_eq_sym; exact (NC am i H Hi)]. }
    split; [left; exact FH|]. split; [intros H; exact (proj2 (PL _ H) eq_refl)|]. split; [exact PL|].
    split.
    { constructor.
      - rewrite E1; cbn. apply (tt_init _ _ HT).
      - intros sc. replace (active st1 sc) with (active st sc) by (rewrite E1; reflexivity).
        destruct (tt_act _ _ HT sc) as [H|(g & H & (G1 & G2 & G3) & NP)]; [left; exact H| right].
        assert (NE : g <> m) by (intros ->; apply NP; left; exact FH).
        exists g. split; [exact H|]. unfold full1. rewrite !MRo by exact NE. split; [auto|]. intros P. apply NP. exact (proj1 (PL _ P)).
      - rewrite E1; cbn. apply (tt_bnc _ _ HT).
      - rewrite E1; cbn. apply (tt_useq _ _ HT).
      - intros m' Hm'. rewrite E1 in Hm'; cbn in Hm'. discriminate.
      - rewrite E1; cbn. apply (tt_avail _ _ HT).
      - rewrite E1; cbn. pose proof (tt_cnt _ _ HT). lia. }
    split; [rewrite MRm; destruct (MR st m); reflexivity|]. split; [rewrite MRm; destruct (MR st m); reflexivity|].
    split; [exact MRo|]. split; [intros; rewrite E1; reflexivity|]. split; [intros; rewrite E1; reflexivity|].
    split; [rewrite E1; reflexivity|].
    split; [rewrite E1; constructor; cbn; try reflexivity; [apply (tt_bnc _ _ HT)| apply (tt_useq _ _ HT)]|].
    rewrite E1. cbn. unfold ctx in FH. rewrite FH. repeat split; try reflexivity; try lia. apply cursor_sub_eq. reflexivity.
  - (* [comment removed for export] *)
    match goal with |- context [if ?c then am_take _ _ _ else _] => replace c with true end.
    2:{ symmetry. rewrite negb_true_iff. apply Z.eqb_neq. pose proof (tt_cnt _ _ HT). unfold ctx in *. lia. }
    unfold am_take. destruct (c_avail_meta (ctx st)) as [am|] eqn:AV; [| exfalso; exact (tt_avail _ _ HT AV)].
    set (st1 := upd_meta am _ _).
    exists st1, am. split; [reflexivity|].
    assert (MRm : MR st1 am = m_set_prev None (m_set_next None (MR st am))) by (unfold st1, MR; rewrite get_meta_rec_upd_same; reflexivity).
    assert (MRo : forall x, x <> am -> MR st1 x = MR st x) by (intros x NE; unfold st1, MR; rewrite get_meta_rec_upd_other by exact NE; reflexivity).
    assert (PL : forall x, in_pool st1 x -> in_pool st x /\ x <> am).
    { intros x [H|(am' & i & H & Hi & ->)]; unfold st1 in H; cbn in H; [rewrite FH in H; discriminate|].
      injection H as <-. rewrite aadd_aadd. split; [right; exists am, (1 + i); split; [exact AV| split; [lia| f_equal; lia]]|].
      intros E. rewrite <- (aadd_0 am) in E at 2. apply aadd_inj in E. unfold META_SIZE in E. lia. }
    split; [right; exists am, 0; split; [exact AV| split; [lia| rewrite Z.mul_0_r, aadd_0; reflexivity]]|].
    split; [intros H; exact (proj2 (PL _ H) eq_refl)|]. split; [exact PL|].
    split.
    { constructor.
      - unfold st1; cbn. apply (tt_init _ _ HT).
      - intros sc. change (active st1 sc) with (active st sc).
        destruct (tt_act _ _ HT sc) as [H|(g & H & (G1 & G2 & G3) & NP)]; [left; exact H| right].
        assert (NE : g <> am) by (intros ->; apply NP; right; exists am, 0; rewrite Z.mul_0_r, aadd_0; auto with zarith).
        exists g. split; [exact H|]. unfold full1. rewrite !MRo by exact NE. split; [auto|]. intros P. apply NP. exact (proj1 (PL _ P)).
      - unfold st1; cbn. apply (tt_bnc _ _ HT).
      - unfold st1; cbn. apply (tt_useq _ _ HT).
      - intros m' Hm'. unfold st1 in Hm'; cbn in Hm'. rewrite FH in Hm'. discriminate.
      - unfold st1; cbn. discriminate.
      - unfold st1; cbn. pose proof (tt_cnt _ _ HT). lia. }
    split; [rewrite MRm; destruct (MR st am); reflexivity|]. split; [rewrite MRm; destruct (MR st am); reflexivity|].
    split; [exact MRo|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
    split; [unfold st1; cbn; exact FH|].
    split; [unfold st1; constructor; cbn; try reflexivity; [apply (tt_bnc _ _ HT)| apply (tt_useq _ _ HT)]|].
    unfold st1. cbn. unfold ctx in FH. rewrite FH. repeat split; try reflexivity; try lia.
    all: try (apply (cursor_sub_adv st _ am); [exact AV| reflexivity]).

Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition MMAP1 {T} (LR : list (Z * Z)) (t : M T) (QF : M T -> Prop) (QS : Z -> M T -> Prop) : Prop :=
  exists len K, t = SVis (EMmap 0 len PROT_RW (MAP_PRIVATE + MAP_ANON)) K
    /\ 0 < len <= 2^30
    /\ (forall r, mmap_answer_ok LR len r = true -> is_err r = true -> QF (K r))
    /\ (forall r, mmap_answer_ok LR len r = true -> is_err r = false -> QS r (K r)).

Lemma MMAP1_mono {T} LR (t : M T) (QF QF' : M T -> Prop) (QS QS' : Z -> M T -> Prop) :
  MMAP1 LR t QF QS -> (forall u, QF u -> QF' u) -> (forall r u, QS r u -> QS' r u) -> MMAP1 LR t QF' QS'.
Proof.
  (cps_intros (len & K & E & B & HF & HS); intros MF MS). exists len, K. split; [exact E|]. split; [exact B|]. split; intros; auto.
Qed.

(* [comment removed for export] *)
Definition INJ (st : mstate) : Prop := forall a b g, active st a = Some g -> active st b = Some g -> a = b.

(* [comment removed for export] *)
Definition SQS {T} (st : mstate) (sc : Z) (k : mstate -> Z -> M T) (r : Z) (t : M T) : Prop :=
  exists stS g, t = k stS 0 /\ active stS sc = Some g
    /\ (forall sc', sc' < sc -> active stS sc' = active st sc')
    /\ (forall x, ~ in_pool st x -> (forall a, active st a <> Some x) -> MR stS x = MR st x).
Definition SQF {T} (k : mstate -> Z -> M T) (t : M T) : Prop := exists stF, t = k stF (-1).

(* [comment removed for export] *)
Definition REC_T (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T) (sc cR : Z) : Prop :=
  forall j c st req (k : mstate -> Z -> M T) bail,
    sc < j -> 0 <= j < 48 -> cR <= c -> TT c st -> INJ st -> 0 <= req -> req + IB <= UNIT * size_class j ->
    MMAP1 (live_ranges st) (rec st j req k bail) (SQF k) (SQS st j k).

Section AG.
Variables (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T) (sc cR : Z).
Hypothesis REC : REC_T T rec sc cR.
Hypothesis HcR : 0 <= cR.

Theorem alloc_group_tight c st req (k : mstate -> optr -> M T) bail :
  TT c st -> INJ st -> cR + 1 <= c -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  active st sc = None ->
  MMAP1 (live_ranges st) (alloc_group T lay_none rec st sc req k bail)
    (fun t => exists stF, t = k stF None)
    (fun r t => exists stS m, t = k stS (Some m) /\ m_next (MR stS m) = None /\ m_prev (MR stS m) = None
                /\ in_pool st m /\ active stS sc = None
                /\ (forall sc', sc' < sc -> active stS sc' = active st sc')
                /\ (forall x, ~ in_pool st x -> (forall a, active st a <> Some x) -> MR stS x = MR st x)).
Proof.
  intros HT HI Hc Hsc Hreq Hfit HA. unfold alloc_group.
  lazymatch goal with |- MMAP1 _ (alloc_meta st ?K ?B) _ _ =>
    destruct (alloc_meta_tight c st K B HT ltac:(lia))
      as (st1 & m & EQ & PM & NPM & PL1 & HT1 & MN & MP & MRo & ACT1 & USG1 & FH1 & CF1 & GR1 & SL1 & NR1 & MC1 & CNT1 & CS1) end.
  rewrite EQ. clear EQ. cbn beta iota zeta.
  change (if sc <? 9 then small_cnt_pick sc (usage st1 sc) else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st1 sc)) (UNIT * size_class sc))
    with (cnt0_of sc (usage st1 sc)).
  change (if (cnt0_of sc (usage st1 sc) =? 1) && (UNIT * size_class sc * cnt0_of sc (usage st1 sc) + UNIT <=? PGSZ / 2) then 2 else cnt0_of sc (usage st1 sc))
    with (ag_cnt1 sc (usage st1 sc)).
  pose proof (ag_arith sc req (usage st1 sc)) as AR.
  set (c1 := ag_cnt1 sc (usage st1 sc)) in *.
  assert (LR1 : live_ranges st1 = live_ranges st) by (apply live_ranges_ext; [apply (cf_regions _ _ CF1)| apply (cf_reserved _ _ CF1)]).
  destruct (Z.ltb_spec (PGSZ / 2) (UNIT * size_class sc * c1 + UNIT)) as [HB|HB].
  - (* [comment removed for export] *)
    rewrite (is_bouncing_tt _ _ sc HT1), (account_bounce_tt _ _ sc HT1).
    set (st1' := step_seq st1).
    set (u1 := if Z.even sc && (sc <? 32) then usage st1 sc + usage st1' (sc + 1) else usage st1 sc).
    change (if (u1 <? 4 * c1) && negb false
            then if (Z.land sc 3 =? 1) && (8 * PGSZ <? UNIT * size_class sc * c1) then 2
                 else if (Z.land sc 3 =? 2) && (4 * PGSZ <? UNIT * size_class sc * c1) then 3
                 else if (Z.land sc 3 =? 0) && (8 * PGSZ <? UNIT * size_class sc * c1) then 3
                 else if (Z.land sc 3 =? 0) && (2 * PGSZ <? UNIT * size_class sc * c1) then 5
                 else c1
            else c1) with (ag_cnt2 sc c1 u1 false).
    set (c2 := ag_cnt2 sc c1 u1 false).
    specialize (AR u1 false).
    assert (LR1' : live_ranges st1' = live_ranges st).
    { unfold st1'. rewrite <- LR1. apply live_ranges_ext; apply step_seq_facts. }
    assert (MR1' : forall x, MR st1' x = MR st1 x).
    { intros x. unfold st1', MR, get_meta_rec. rewrite (proj1 (proj2 (proj2 (step_seq_facts st1)))). reflexivity. }
    assert (GO : forall c3 n3, ag_cn3 sc req c2 u1 false = (c3, n3) ->
      MMAP1 (live_ranges st) (SVis (EMmap 0 n3 PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
          if negb (mmap_answer_ok (live_ranges st1') n3 r) then bad_answer bail
          else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
          else let '(st2, rid) := new_region RKGroup r n3 st1' in
               ag_tail lay_none (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) (upd_meta m (m_set_maplen (Z.shiftr n3 12)) st2)) sc m (rid, 0) c3
                 (let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if c3 - 1 <? ai then c3 - 1 else ai in if ai <? 0 then 0 else ai) k))
        (fun t => exists stF, t = k stF None)
        (fun r t => exists stS m, t = k stS (Some m) /\ m_next (MR stS m) = None /\ m_prev (MR stS m) = None
                /\ in_pool st m /\ active stS sc = None
                /\ (forall sc', sc' < sc -> active stS sc' = active st sc')
                /\ (forall x, ~ in_pool st x -> (forall a, active st a <> Some x) -> MR stS x = MR st x))).
    { intros c3 n3 E3. destruct (proj1 (AR c3 n3 Hsc Hreq Hfit) HB E3) as [GRP RED].
      pose proof (grp_ok_sound _ _ _ GRP) as GS. cbn zeta in GS.
      exists n3. eexists. split; [reflexivity|]. split; [clear -GS; lia|]. split.
      - intros r OK ER. rewrite LR1', OK. cbn [negb]. rewrite ER.
        cps_destruct (free_meta_eq m st1' (fun st2 => k st2 None) bail) as (st' & E' & _). rewrite E'. exists st'. reflexivity.
      - intros r OK ER. rewrite LR1', OK. cbn [negb]. rewrite ER. unfold new_region. rewrite ag_tail_none_eq.
        set (stS := agtn _ _ _ _ _ _). exists stS, m. split; [reflexivity|].
        assert (MRS : MR stS m = agG sc (s_next_rid st1', 0) c3
                  (let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if c3 - 1 <? ai then c3 - 1 else ai in if ai <? 0 then 0 else ai)
                  (m_set_maplen (Z.shiftr n3 12) (MR st1 m))).
        { unfold stS. rewrite agtn_MR_m. f_equal. unfold MR. rewrite get_meta_rec_upd_ctx. cbn -[get_meta_rec m_set_maplen].
          rewrite get_meta_rec_upd_same. f_equal. apply MR1'. }
        split; [rewrite MRS; unfold agG; destruct (MR st1 m); cbn; exact MN|].
        split; [rewrite MRS; unfold agG; destruct (MR st1 m); cbn; exact MP|].
        split; [exact PM|].
        assert (AS : forall sc0, active stS sc0 = active st sc0).
        { intros sc0. rewrite <- (ACT1 sc0). unfold stS. rewrite agtn_active.
          change (active st1' sc0 = active st1 sc0). unfold active, ctx, st1'.
          rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (step_seq_facts st1)))))))). reflexivity. }
        split; [rewrite AS; exact HA|]. split; [intros; apply AS|].
        intros x NX NAx. assert (NE : x <> m) by (intros ->; exact (NX PM)).
        unfold stS. rewrite agtn_MR_other by exact NE.
        transitivity (MR st1' x); [| rewrite MR1'; apply MRo; exact NE].
        unfold MR. rewrite get_meta_rec_upd_ctx. etransitivity; [apply get_meta_rec_upd_other; exact NE|]. reflexivity. }
    unfold ag_cn3 in GO. cbn zeta in GO.
    destruct (negb false && (c2 <=? 7)).
    + destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
      * cbn beta iota. exact (GO _ _ eq_refl).
      * cbn beta iota. exact (GO _ _ eq_refl).
    + cbn beta iota. exact (GO _ _ eq_refl).
  - (* [comment removed for export] *)
    pose proof (proj2 (AR 0 false 0 0 Hsc Hreq Hfit) HB) as NEST.
    pose proof (nest_ok_sound _ _ NEST) as NS. cbn zeta in NS. cps_destruct NS as (Hc1 & Hj & FITj & _ & Hn' & _).
    set (size := UNIT * size_class sc) in *.
    set (j := size_to_class (UNIT + c1 * size - IB)) in *.
    assert (HI1 : INJ st1) by (intros a b g Ha Hb; rewrite ACT1 in Ha, Hb; exact (HI a b g Ha Hb)).
    pose proof (REC j (c - 1) st1 (UNIT + c1 * size - IB) 
      (fun st2 idx =>
         if idx <? 0 then free_meta m st2 (fun st3 => k st3 None) bail
         else match active st2 j with
              | Some g =>
                ag_tail lay_none (upd_meta m (m_set_maplen 0) ((lh_nest lay_none) st2 g idx j size c1)) sc m (slot_of st2 g idx) c1 (c1 - 1) k
              | None => SVis (EUndef UBadPtr) (fun _ => bail)
              end) bail ltac:(lia) ltac:(lia) ltac:(lia) HT1 HI1 ltac:(lia) ltac:(unfold size in FITj; lia)) as RR.
    rewrite LR1 in RR.
    eapply MMAP1_mono; [exact RR| |].
    + intros u (stF & ->). change (-1 <? 0) with true. cbn iota.
      cps_destruct (free_meta_eq m stF (fun st3 => k st3 None) bail) as (st' & E' & _). rewrite E'. exists st'. reflexivity.
    + (intros r u; cps_intros (stS & g & -> & HAS & ACTS & MRS)). change (0 <? 0) with false. cbn iota. rewrite HAS.
      cbn [lh_nest lay_none]. rewrite ag_tail_none_eq.
      set (stS' := agtn _ _ _ _ _ _). exists stS', m. split; [reflexivity|].
      assert (NAm : forall a, active st1 a <> Some m).
      { intros a Ha. rewrite ACT1 in Ha. destruct (tt_act _ _ HT a) as [H|(g' & H & _ & NP)]; [congruence|].
        rewrite Ha in H. injection H as <-. exact (NP PM). }
      assert (MRm : MR stS' m = agG sc (slot_of stS g 0) c1 (c1 - 1) (m_set_maplen 0 (MR st1 m))).
      { unfold stS'. rewrite agtn_MR_m. f_equal. unfold MR. rewrite get_meta_rec_upd_same. f_equal. apply MRS; [exact NPM| exact NAm]. }
      split; [rewrite MRm; unfold agG; destruct (MR st1 m); cbn; exact MN|].
      split; [rewrite MRm; unfold agG; destruct (MR st1 m); cbn; exact MP|].
      split; [exact PM|].
      assert (AS : forall sc0, sc0 < j -> active stS' sc0 = active st sc0).
      { intros sc0 Hs0. unfold stS'. rewrite agtn_active, active_upd_meta, ACTS by exact Hs0. apply ACT1. }
      split; [rewrite AS by lia; exact HA|]. split; [intros sc' Hs'; apply AS; lia|].
      intros x NX NAx. assert (NE : x <> m) by (intros ->; exact (NX PM)).
      unfold stS'. rewrite agtn_MR_other by exact NE. unfold MR at 1. rewrite get_meta_rec_upd_other by exact NE. fold (MR stS x).
      rewrite MRS; [apply MRo; exact NE| intros P; exact (NX (proj1 (PL1 _ P)))| intros a; rewrite ACT1; apply NAx].
Qed.
End AG.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SLOT.
Variable T : Type.

Theorem alloc_slot_tight (f : nat) : forall c st sc req (k : mstate -> Z -> M T) bail,
  Z.of_nat f <= c -> 49 - sc <= Z.of_nat f ->
  TT c st -> INJ st -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  MMAP1 (live_ranges st) (alloc_slot lay_none f st sc req k bail) (SQF k) (SQS st sc k).
Proof.
  induction f as [|f IH]; intros c st sc req k bail Hf Hf2 HT HI Hsc Hreq Hfit.
  { exfalso. cbn in Hf2. lia. }
  change (alloc_slot lay_none (S f) st sc req k bail) with
    (try_avail sc st (fun st1 first =>
       if negb (first =? 0) then k st1 (ctz32 first)
       else alloc_group T lay_none (alloc_slot lay_none f) st1 sc req (fun st2 go =>
              match go with
              | None => k st2 (-1)
              | Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
                          queue (LActive sc) g st3 (fun st4 => k st4 0) bail
              end) bail) bail).
  lazymatch goal with |- MMAP1 _ (try_avail sc st ?K bail) _ _ =>
    destruct (try_avail_tight c st sc K bail HT HI) as (st1 & E & HA1 & ACT1 & HI1 & HT1 & CF1 & _ & GR1 & SL1 & NR1 & PL1 & MR1) end.
  rewrite E. clear E. change (negb (0 =? 0)) with false. cbn iota.
  assert (REC : REC_T T (alloc_slot lay_none f) sc (Z.of_nat f)).
  { intros j c' st' req' k' bail' Hj Hj48 Hc' HT' HI' Hreq' Hfit'. apply (IH c' st' j req' k' bail'); try assumption. rewrite Nat2Z.inj_succ in Hf2. lia. }
  lazymatch goal with |- MMAP1 _ (alloc_group _ _ _ st1 sc req ?K bail) _ _ =>
    pose proof (alloc_group_tight T (alloc_slot lay_none f) sc (Z.of_nat f) REC (Nat2Z.is_nonneg f) c st1 req K bail HT1 HI1
                  ltac:(rewrite Nat2Z.inj_succ in Hf; lia) Hsc Hreq Hfit HA1) as AG end.
  rewrite (live_ranges_ext st st1 (cf_regions _ _ CF1) (cf_reserved _ _ CF1)) in AG.
  eapply MMAP1_mono; [exact AG| |].
  - intros u (stF & ->). exists stF. reflexivity.
  - (intros r u; cps_intros (stS & m & -> & MN & MP & PM & HAS & ACTS & MRS)). cbn zeta.
    rewrite (queue_empty_eq (LActive sc) m _ (fun st4 => k st4 0) bail).
    2:{ unfold MR. rewrite get_meta_rec_upd_same. fold (MR stS m). destruct (MR stS m); cbn in *; exact MN. }
    2:{ unfold MR. rewrite get_meta_rec_upd_same. fold (MR stS m). destruct (MR stS m); cbn in *; exact MP. }
    2:{ rewrite get_head_upd_meta. exact HAS. }
    eexists. exists m. split; [reflexivity|].
    split; [cbn [set_head]; rewrite active_set_active, Z.eqb_refl; reflexivity|].
    split.
    + intros sc' Hs'. cbn [set_head]. rewrite active_set_active. destruct (Z.eqb_spec sc' sc); [lia|].
      rewrite !active_upd_meta. rewrite ACTS by exact Hs'. apply ACT1. lia.
    + intros x NX NAx.
      assert (PMst : in_pool st m) by (apply PL1; exact PM).
      assert (NE : x <> m) by (intros ->; exact (NX PMst)).
      transitivity (MR stS x).
      * unfold MR. rewrite get_meta_rec_set_head, !get_meta_rec_upd_other by exact NE. reflexivity.
      * rewrite MRS; [apply MR1; apply NAx| rewrite PL1; exact NX|].
        intros a. destruct (Z.eqb_spec a sc) as [->|NEa]; [rewrite HA1; discriminate| rewrite ACT1 by exact NEa; apply NAx].
Qed.
End SLOT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma MMAP1_bind {R S} LR (t : M R) (F : R -> M S) QF QS (QF' : M S -> Prop) (QS' : Z -> M S -> Prop) :
  MMAP1 LR t QF QS -> (forall u, QF u -> QF' (sbind u F)) -> (forall r u, QS r u -> QS' r (sbind u F)) ->
  MMAP1 LR (sbind t F) QF' QS'.
Proof.
  (cps_intros (len & K & -> & B & HF & HS); intros MF MS). exists len, (fun a => sbind (K a) F).
  split; [rewrite sbind_vis; reflexivity|]. split; [exact B|]. split; intros; auto.
Qed.

Definition CQF (t : M (mstate * option cptr)) : Prop := exists cs', t = SRet (cs', @None cptr).
Definition CQS (r : Z) (t : M (mstate * option cptr)) : Prop := exists cs' p, t = SRet (cs', Some p).

Theorem cmalloc_small_tight c cs n :
  TT c cs -> INJ cs -> Z.of_nat FUEL <= c -> 0 <= n < MMAP_THRESHOLD ->
  MMAP1 (live_ranges cs) (cmalloc cs n) CQF CQS.
Proof.
  intros HT HI Hc Hn. unfold cmalloc, malloc_core.
  replace (size_overflows n) with false by (symmetry; unfold size_overflows, MMAP_THRESHOLD in *; apply Z.leb_gt; lia).
  replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
  assert (CORE : MMAP1 (live_ranges cs) (malloc_small_ctrl lay_none cs n (fun st1 r => ret (st1, r)) (ret (cs, @None (aptr * Z))))
                   (fun t => exists stF, t = SRet (stF, @None (aptr * Z))) (fun r t => exists stS g idx, t = SRet (stS, Some (g, idx)))).
  2:{ eapply MMAP1_bind; [exact CORE| |].
      - intros u (stF & ->). rewrite sbind_ret_l. eexists. reflexivity.
      - (intros r u; cps_intros (stS & g & idx & ->)). rewrite sbind_ret_l. eexists. eexists. reflexivity. }
  (* [comment removed for export] *)
  pose proof (size_to_class_ok n ltac:(lia)) as [SC FIT].
  unfold malloc_small_ctrl.
  set (sc0 := size_to_class n) in *.
  set (sc := match active cs sc0 with Some _ => sc0 | None => _ end).
  assert (SC' : 0 <= sc < 48 /\ n + IB <= UNIT * size_class sc).
  { subst sc. destruct (active cs sc0); [auto|].
    destruct ((4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage cs sc0 =? 0)) eqn:E; [| auto].
    match goal with |- context [if ?c then Z.lor sc0 1 else sc0] => destruct c end; [| auto].
    apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E EV]. apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E1 E2].
    apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    rewrite (lor1_even sc0 ltac:(lia) EV). split; [lia|].
    pose proof (size_class_lt sc0 (sc0 + 1) ltac:(lia) ltac:(lia) ltac:(lia)). unfold UNIT in *. lia. }
  clearbody sc. destruct SC' as [SC' FIT'].
  assert (MASK : match active cs sc with Some gp => m_avail (get_meta_rec cs gp) | None => 0 end = 0).
  { destruct (tt_act _ _ HT sc) as [->|(g & -> & (F1 & _) & _)]; [reflexivity| exact F1]. }
  rewrite MASK. change (lowbit 0) with 0. cbn [Z.eqb negb].
  lazymatch goal with |- MMAP1 ?LR (match active cs sc with Some _ => _ | None => ?B end) ?QF ?QS =>
    enough (G : MMAP1 LR B QF QS) by (destruct (active cs sc); exact G) end.
  lazymatch goal with |- MMAP1 _ (alloc_slot _ _ cs sc n ?K ?B) _ _ =>
    pose proof (alloc_slot_tight _ FUEL c cs sc n K B Hc ltac:(unfold FUEL; cbn; lia) HT HI ltac:(lia) ltac:(lia) FIT') as AS end.
  eapply MMAP1_mono; [exact AS| |].
  - intros u (stF & ->). change (-1 <? 0) with true. cbn iota. exists stF. reflexivity.
  - (intros r u; cps_intros (stS & g & -> & HAS & _ & _)). change (0 <? 0) with false. cbn iota. rewrite HAS. exists stS, g, 0. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record BIGPOST (cs : mstate) (n r : Z) (cs' : mstate) (g : aptr) (c : cptr) : Prop := mkBP {
  bp_rid : fst c = s_next_rid cs /\ snd c = UNIT;
  bp_slot : s_slots cs' !! c = Some (g, 0);
  bp_slots_other : forall x, x <> c -> s_slots cs' !! x = s_slots cs !! x;
  bp_meta : MR cs' g = mkMeta None None (Some (s_next_rid cs, 0)) 0 0 0 1 63 ((n + IB + UNIT + 4095) / 4096);
  bp_metas_other : forall x, x <> g -> MR cs' x = MR cs x;
  bp_pool : in_pool cs g /\ ~ in_pool cs' g /\ (forall x, in_pool cs' x -> in_pool cs x /\ x <> g);
  bp_groups : exists ai, s_groups cs' = <[(s_next_rid cs, 0) := mkGhdr (Some g) ai]> (s_groups cs);
  bp_regions : s_regions cs' = <[s_next_rid cs := mkRegion RKGroup r (n + IB + UNIT)]> (s_regions cs);
  bp_next_rid : s_next_rid cs' = N.succ (s_next_rid cs);
  bp_reserved : s_reserved cs' = s_reserved cs;
  bp_active : forall sc, active cs' sc = active cs sc;
  bp_free_head : c_free_meta_head (s_ctx cs') = None;
  bp_init : c_init_done (s_ctx cs') = c_init_done (s_ctx cs);
  bp_bnc : c_bounces (s_ctx cs') = ∅;
  bp_useq : c_unmap_seq (s_ctx cs') = ∅;
  bp_avail : c_avail_meta (s_ctx cs') <> None;
  bp_cnt : c_avail_meta_count (s_ctx cs') = c_avail_meta_count (s_ctx cs) - match c_free_meta_head (s_ctx cs) with Some _ => 0 | None => 1 end
}.

Lemma in_pool_sub st st' x :
  cursor_sub st st' -> (c_free_meta_head (s_ctx st') = c_free_meta_head (s_ctx st) \/ c_free_meta_head (s_ctx st') = None) ->
  in_pool st' x -> in_pool st x.
Proof.
  intros CS F [H|(am' & i & E & Hi & ->)].
  - left. destruct F as [F|F]; congruence.
  - cps_destruct (CS am' i E Hi) as (am & j & E1 & Hj & ->). right. exists am, j. auto.
Qed.

Lemma TT_frame c c' st st' :
  TT c st ->
  c_init_done (s_ctx st') = c_init_done (s_ctx st) ->
  (forall sc, active st' sc = active st sc) ->
  c_bounces (s_ctx st') = ∅ -> c_unmap_seq (s_ctx st') = ∅ ->
  (c_free_meta_head (s_ctx st') = c_free_meta_head (s_ctx st) \/ c_free_meta_head (s_ctx st') = None) ->
  c_avail_meta (s_ctx st') <> None -> cursor_sub st st' ->
  c' <= c_avail_meta_count (s_ctx st') ->
  (forall x, ((exists a, active st a = Some x) \/ c_free_meta_head (s_ctx st) = Some x) -> MR st' x = MR st x) ->
  TT c' st'.
Proof.
  intros HT I A B U F AV CS CN M. constructor.
  - rewrite I. apply (tt_init _ _ HT).
  - intros sc. rewrite A. destruct (tt_act _ _ HT sc) as [H|(g & H & (F1 & F2 & F3) & NP)]; [left; exact H| right].
    exists g. split; [exact H|]. unfold full1. rewrite !M by (left; exists sc; exact H). split; [auto|].
    intros P. apply NP. exact (in_pool_sub st st' g CS F P).
  - exact B.
  - exact U.
  - intros m Hm. destruct F as [F|F]; [| rewrite F in Hm; discriminate]. rewrite F in Hm.
    destruct (tt_free _ _ HT m Hm) as [N1 N2]. rewrite M by (right; exact Hm). split; [exact N1|].
    intros am' i E Hi EQ. cps_destruct (CS am' i E Hi) as (am & j & E1 & Hj & E2). apply (N2 am j E1 Hj). rewrite <- E2. exact EQ.
  - exact AV.
  - exact CN.
Qed.

Lemma TT_only_ctx_metas c st st' : s_ctx st' = s_ctx st -> s_metas st' = s_metas st -> TT c st -> TT c st'.
Proof.
  intros EC EM HT.
  assert (MRe : forall x, MR st' x = MR st x) by (intros x; unfold MR, get_meta_rec; rewrite EM; reflexivity).
  apply (TT_frame c c st st' HT).
  - rewrite EC. reflexivity.
  - intros sc. unfold active, ctx. rewrite EC. reflexivity.
  - rewrite EC. apply (tt_bnc _ _ HT).
  - rewrite EC. apply (tt_useq _ _ HT).
  - left. rewrite EC. reflexivity.
  - rewrite EC. apply (tt_avail _ _ HT).
  - apply cursor_sub_eq. rewrite EC. reflexivity.
  - rewrite EC. apply (tt_cnt _ _ HT).
  - intros x _. apply MRe.
Qed.

Lemma INJ_ext st st' : (forall sc, active st' sc = active st sc) -> INJ st -> INJ st'.
Proof. intros A HI a b g Ha Hb. rewrite A in Ha, Hb. exact (HI a b g Ha Hb). Qed.

Lemma slot_key_single p stride x : 0 < stride ->
  ((fst x =? fst p)%N && (0 <=? snd x - snd p - UNIT) && ((snd x - snd p - UNIT) mod stride =? 0) && ((snd x - snd p - UNIT) / stride <? 1))
  = aptr_eqb x (aadd p UNIT).
Proof.
  intros Hs. destruct (aptr_eqb_spec x (aadd p UNIT)) as [->|NE].
  - apply (proj2 (slot_key_test p stride 1 _ Hs)). exists 0. split; [lia|]. f_equal. lia.
  - match goal with |- ?b = false => destruct b eqn:E; [|reflexivity] end.
    exfalso. apply (proj1 (slot_key_test p stride 1 _ Hs)) in E as (i & Hi & ->). apply NE. f_equal. assert (i = 0) by lia. subst. lia.
Qed.

Lemma big_meta_eq p q a b c0 d e f g0 mm ml :
  m_set_freed 0 (m_set_avail 0 (m_set_maplen ml (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0
    (m_set_mem mm (mkMeta p q a b c0 d e f g0))))))) = mkMeta p q mm 0 0 0 1 63 (Z.land ml (2^52 - 1)).
Proof. reflexivity. Qed.

Lemma land_52 x : 0 <= x < 2^52 -> Z.land x (2^52 - 1) = x.
Proof. intros H. change (2^52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. apply Z.mod_small. exact H. Qed.

Theorem cmalloc_big_tight c cs n :
  TT c cs -> INJ cs -> 1 <= c -> MMAP_THRESHOLD <= n -> n + IB + UNIT <= 2^30 -> strip cs = cs ->
  MMAP1 (live_ranges cs) (cmalloc cs n)
    (fun t => t = SRet (cs, @None cptr))
    (fun r t => exists cs' g c', t = SRet (cs', Some c') /\ BIGPOST cs n r cs' g c' /\ TT (c - 1) cs' /\ INJ cs' /\ strip cs' = cs').
Proof.
  intros HT HI Hc Hn Hn2 Hcs. unfold cmalloc, malloc_core.
  replace (size_overflows n) with false by (symmetry; unfold size_overflows, MMAP_THRESHOLD, IB, UNIT in *; apply Z.leb_gt; lia).
  replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; lia).
  rewrite sbind_vis. eexists. eexists. split; [reflexivity|]. split; [unfold IB, UNIT, MMAP_THRESHOLD in *; lia|]. split.
  - intros r OK ER. rewrite OK. cbn [negb]. rewrite ER. rewrite sbind_ret_l. rewrite Hcs. reflexivity.
  - intros r OK ER. rewrite OK. cbn [negb]. rewrite ER. unfold new_region.
    set (st1 := set_next_rid _ _).
    assert (HT1 : TT c st1) by (apply (TT_only_ctx_metas c cs st1); [reflexivity| reflexivity| exact HT]).
    assert (HT2 : TT c (step_seq st1)) by (apply TT_step_seq; exact HT1).
    assert (HI2 : INJ (step_seq st1)).
    { apply (INJ_ext cs); [| exact HI]. intros sc. unfold active, ctx. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (step_seq_facts st1)))))))). reflexivity. }
    lazymatch goal with |- context [alloc_meta (step_seq st1) ?K ?B] =>
      destruct (alloc_meta_tight c (step_seq st1) K B HT2 Hc)
        as (st3 & g & EQ & PM & NPM & PL3 & HT3 & MN & MP & MRo & ACT3 & USG3 & FH3 & CF3 & GR3 & SL3 & NR3 & MC3 & CNT3 & CS3) end.
    rewrite EQ. clear EQ. cbn beta iota. rewrite sbind_ret_l. cbn [lh_hdr lay_none].
    set (F := fun mr : meta => m_set_freed 0 (m_set_avail 0 (m_set_maplen ((n + IB + UNIT + 4095) / 4096)
                 (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (s_next_rid cs, 0)) mr))))))).
    set (st4 := upd_meta g F st3). set (st5 := put_group _ _ _ st4). set (st6 := add_slots _ _ _ _ st5). set (st7 := upd_ctx _ st6).
    cps_pose (step_seq_facts st1) as (Srg & Srs & Smt & Sgr & Ssl & Snr & Sac & Sus & Sbn & Sfh & Sav & Scn & Sin & Smc & Suq).
    assert (ML : 32 <= (n + IB + UNIT + 4095) / 4096).
    { apply Z.div_le_lower_bound; [lia|]. unfold MMAP_THRESHOLD, IB, UNIT in *. lia. }
    assert (MR7 : MR st7 g = mkMeta None None (Some (s_next_rid cs, 0)) 0 0 0 1 63 ((n + IB + UNIT + 4095) / 4096)).
    { unfold MR. rewrite (get_meta_rec_ext st4 st7 g) by reflexivity. unfold st4.
      rewrite get_meta_rec_upd_same. fold (MR st3 g). destruct (MR st3 g) as [q1 q2 q3 q4 q5 q6 q7 q8 q9] eqn:EM. cbn in MN, MP. subst. unfold F.
      rewrite big_meta_eq, land_52; [reflexivity|].
      split; [lia|]. apply Z.div_lt_upper_bound; [lia|]. unfold IB, UNIT in *. lia. }
    assert (MR7o : forall x, x <> g -> MR st7 x = MR cs x).
    { intros x NE. unfold MR. rewrite (get_meta_rec_ext st4 st7 x) by reflexivity. unfold st4.
      rewrite get_meta_rec_upd_other by exact NE. fold (MR st3 x). rewrite MRo by exact NE. unfold MR, get_meta_rec. rewrite Smt. reflexivity. }
    assert (ST7 : get_stride (MR st7 g) = (n + IB + UNIT + 4095) / 4096 * 4096 - UNIT).
    { rewrite MR7. unfold get_stride. cbn [m_last_idx m_maplen]. rewrite Z.eqb_refl.
      replace ((n + IB + UNIT + 4095) / 4096 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
    assert (MR5 : get_meta_rec st5 g = MR st7 g) by reflexivity.
    assert (SL7 : forall x, s_slots st7 !! x = if aptr_eqb x (s_next_rid cs, UNIT) then Some (g, 0) else s_slots cs !! x).
    { intros x. unfold st7. rewrite s_slots_upd_ctx. unfold st6. rewrite MR5, ST7. rewrite lookup_add_slots by (unfold UNIT in *; lia).
      replace (s_slots st5 !! x) with (s_slots cs !! x) by (unfold st5, st4; cbn; rewrite SL3, Ssl; reflexivity).
      cbn [fst snd]. unfold aptr_eqb. cbn [fst snd].
      destruct (N.eqb_spec (fst x) (s_next_rid cs)) as [E1|NE1]; cbn [andb]; [|reflexivity].
      destruct (Z.eqb_spec (snd x) UNIT) as [E2|NE2].
      - rewrite E2. replace (UNIT - 0 - UNIT) with 0 by lia. rewrite Z.mod_0_l, Z.div_0_l by (unfold UNIT; lia). cbn. reflexivity.
      - destruct (Z.leb_spec 0 (snd x - 0 - UNIT)); cbn [andb]; [|reflexivity].
        destruct (Z.eqb_spec ((snd x - 0 - UNIT) mod ((n + IB + UNIT + 4095) / 4096 * 4096 - UNIT)) 0); cbn [andb]; [|reflexivity].
        destruct (Z.ltb_spec ((snd x - 0 - UNIT) / ((n + IB + UNIT + 4095) / 4096 * 4096 - UNIT)) 1); [|reflexivity].
        exfalso. apply NE2.
        set (sd := (n + IB + UNIT + 4095) / 4096 * 4096 - UNIT) in *.
        assert (DZ : (snd x - 0 - UNIT) / sd = 0) by (pose proof (Z.div_pos (snd x - 0 - UNIT) sd); unfold UNIT in *; lia).
        pose proof (Z.div_mod (snd x - 0 - UNIT) sd ltac:(unfold UNIT in *; lia)) as DM. rewrite DZ, e in DM. unfold UNIT in *. lia. }
    exists (strip st7), g, (slot_of st7 g 0).
    assert (SO : slot_of st7 g 0 = (s_next_rid cs, UNIT)).
    { unfold slot_of. fold (MR st7 g). rewrite MR7. unfold slot_start'. cbn -[Z.add Z.mul]. unfold aadd. cbn. f_equal. lia. }
    rewrite SO. split; [reflexivity|].
    assert (A7 : forall sc, active (strip st7) sc = active cs sc).
    { intros sc. rewrite active_strip. unfold st7, st6, st5, st4. unfold active, ctx. cbn. fold (ctx st3). fold (active st3 sc). rewrite ACT3. unfold active, ctx. rewrite Sac. reflexivity. }
    assert (P7 : forall x, in_pool (strip st7) x <-> in_pool st3 x) by (intros x; unfold in_pool, st7, st6, st5, st4; cbn; tauto).
    assert (P1 : forall x, in_pool (step_seq st1) x <-> in_pool cs x) by (intros x; unfold in_pool; rewrite Sfh, Sav; cbn; tauto).
    split; [| split; [| split]].
    + constructor.
      * cbn. lia.
      * rewrite s_slots_strip. rewrite SL7, aptr_eqb_refl. reflexivity.
      * intros x NE. rewrite s_slots_strip, SL7. destruct (aptr_eqb_spec x (s_next_rid cs, UNIT)); [congruence| reflexivity].
      * unfold MR. rewrite get_meta_rec_strip. exact MR7.
      * intros x NE. unfold MR at 1. rewrite get_meta_rec_strip. exact (MR7o x NE).
      * split; [apply P1; exact PM|]. split; [rewrite P7; exact NPM|]. intros x Hx. apply P7 in Hx. destruct (PL3 x Hx) as [H1 H2]. split; [apply P1; exact H1| exact H2].
      * eexists. rewrite s_groups_strip. unfold st7, st6, st5, st4. cbn. rewrite GR3, Sgr. reflexivity.
      * rewrite s_regions_strip. unfold st7, st6, st5, st4. cbn. rewrite (cf_regions _ _ CF3), Srg. reflexivity.
      * rewrite s_next_rid_strip. unfold st7, st6, st5, st4. cbn. rewrite NR3, Snr. reflexivity.
      * rewrite s_reserved_strip. unfold st7, st6, st5, st4. cbn. rewrite (cf_reserved _ _ CF3), Srs. reflexivity.
      * exact A7.
      * cbn. exact FH3.
      * cbn. rewrite (cf_init _ _ CF3), Sin. reflexivity.
      * cbn. apply (cf_bnc _ _ CF3).
      * cbn. apply (cf_useq _ _ CF3).
      * cbn. apply (tt_avail _ _ HT3).
      * cbn. rewrite CNT3, Scn, Sfh. reflexivity.
    + apply (TT_frame (c - 1) (c - 1) st3 (strip st7) HT3).
      * reflexivity.
      * intros sc. rewrite A7, ACT3. unfold active, ctx. rewrite Sac. reflexivity.
      * cbn. apply (cf_bnc _ _ CF3).
      * cbn. apply (cf_useq _ _ CF3).
      * left. reflexivity.
      * cbn. apply (tt_avail _ _ HT3).
      * apply cursor_sub_eq. reflexivity.
      * cbn. apply (tt_cnt _ _ HT3).
      * intros x Hx. assert (NE : x <> g).
        { intros ->. destruct Hx as [(a & Ha)|Hh]; [| rewrite FH3 in Hh; discriminate].
          rewrite ACT3 in Ha. destruct (tt_act _ _ HT2 a) as [H|(g' & H & _ & NP)]; [congruence|]. rewrite Ha in H. injection H as <-. exact (NP PM). }
        unfold MR at 1. rewrite get_meta_rec_strip. fold (MR st7 x). rewrite MR7o by exact NE. symmetry. rewrite (MRo x NE). unfold MR, get_meta_rec. rewrite Smt. reflexivity.
    + apply (INJ_ext cs); [exact A7| exact HI].
    + apply strip_strip.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record FREEPRE (cs : mstate) (c : cptr) (g : aptr) (p : aptr) (sc ml : Z) : Prop := mkFP {
  fp_slot : s_slots cs !! c = Some (g, 0);
  fp_meta : exists pv nx, MR cs g = mkMeta pv nx (Some p) 0 0 0 1 sc ml
              /\ ((sc = 63 /\ nx = None) \/ (39 <= sc < 48 /\ nx = Some g /\ active cs sc = Some g /\ ml * 4096 - UNIT < UNIT * size_class sc));
  fp_ml : 0 < ml;
  fp_pool : ~ in_pool cs g;
  fp_head : c_free_meta_head (s_ctx cs) = None;
  fp_act : forall a, active cs a = Some g -> a = sc /\ sc < 48;
  fp_c : c = aadd p UNIT
}.

Record FREEPOST (cs : mstate) (c : cptr) (g : aptr) (p : aptr) (sc : Z) (cs' : mstate) : Prop := mkFQ {
  fq_slots : forall x, s_slots cs' !! x = if aptr_eqb x c then None else s_slots cs !! x;
  fq_groups : forall x, s_groups cs' !! x = if aptr_eqb x p then None else s_groups cs !! x;
  fq_regions : forall rid, s_regions cs' !! rid = if (rid =? fst p)%N then None else s_regions cs !! rid;
  fq_reserved : s_reserved cs' = s_reserved cs;
  fq_next_rid : s_next_rid cs' = s_next_rid cs;
  fq_meta : MR cs' g = mkMeta (Some g) (Some g) None 0 0 0 0 0 0;
  fq_metas_other : forall x, x <> g -> MR cs' x = MR cs x;
  fq_active : forall sc', active cs' sc' = if (sc' =? sc) && (sc <? 48) then None else active cs sc';
  fq_free_head : c_free_meta_head (s_ctx cs') = Some g;
  fq_init : c_init_done (s_ctx cs') = c_init_done (s_ctx cs);
  fq_bnc : c_bounces (s_ctx cs') = ∅;
  fq_useq : c_unmap_seq (s_ctx cs') = ∅;
  fq_avail : c_avail_meta (s_ctx cs') = c_avail_meta (s_ctx cs);
  fq_cnt : c_avail_meta_count (s_ctx cs') = c_avail_meta_count (s_ctx cs)
}.

Lemma nontrivial_free_S {R} (dec : decoder R) f st g i (k : mstate -> mapinfo -> M R) bail :
  nontrivial_free dec (S f) st g i k bail =
    (let mr := get_meta_rec st g in
     let self := bit i in
     let sc := m_sizeclass mr in
     let mask := Z.lor (m_freed mr) (m_avail mr) in
     if (mask + self =? mask_upto (m_last_idx mr)) && okay_to_free st g then
       match m_next mr with
       | Some _ =>
         guard 50 (sc <? 48) (
           let activate_new := optr_eqb (active st sc) (Some g) in
           let st1 := dequeue (LActive sc) g st in
           match activate_new, active st1 sc with
           | true, Some a => activate_group a st1 (fun st2 _ => free_group R dec (nontrivial_free dec f) st2 g k bail) bail
           | _, _ => free_group R dec (nontrivial_free dec f) st1 g k bail
           end) bail
       | None => free_group R dec (nontrivial_free dec f) st g k bail
       end
     else if mask =? 0 then
       guard 51 (sc <? 48) (
         let aor (st : mstate) := k (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) self) r) st) None in
         if negb (optr_eqb (active st sc) (Some g)) then queue (LActive sc) g st aor bail
         else aor st) bail
     else k (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) self) r) st) None).
Proof. reflexivity. Qed.

Theorem cfree_single_tight cnt cs c g p sc ml :
  TT cnt cs -> INJ cs -> strip cs = cs -> FREEPRE cs c g p sc ml ->
  exists K, cfree cs (Some c) = SVis (EMunmap (conc cs p) (ml * 4096)) K
    /\ forall ru, munmap_answer_ok ru = true ->
         exists cs', K ru = SRet cs' /\ FREEPOST cs c g p sc cs' /\ TT cnt cs' /\ INJ cs' /\ strip cs' = cs'.
Proof.
  intros HT HI Hcs [SL (pv & nx & MRg & CASES) ML NP FH HAg Hc].
  unfold cfree. rewrite SL. unfold free_tail. fold (MR cs g). rewrite MRg. cbn [m_freed m_avail m_last_idx].
  change (guard 60 (negb (testbit (Z.lor 0 0) 0)) ?A ?B) with A.
  change (negb ((0 =? 0) || (Z.lor 0 0 + bit 0 =? mask_upto 0))) with false. cbn iota.
  unfold FUEL. rewrite nontrivial_free_S. cbv zeta. fold (MR cs g). rewrite MRg. cbn [m_freed m_avail m_last_idx m_sizeclass m_next].
  change (Z.lor 0 0 + bit 0 =? mask_upto 0) with true. cbn [andb].
  assert (OK : okay_to_free cs g = true).
  { unfold okay_to_free. fold (MR cs g). rewrite MRg. cbn [m_freeable m_sizeclass m_last_idx m_maplen m_next].
    change (1 =? 0) with false. cbv iota.
    destruct CASES as [(-> & _)|(Hsc & _ & _ & STR)]; [reflexivity|].
    unfold get_stride. cbn [m_last_idx m_maplen m_sizeclass]. change (0 =? 0) with true.
    replace (ml =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb].
    destruct (Z.leb_spec 48 sc); [lia|]. cbn [orb]. rewrite (proj2 (Z.ltb_lt _ _) STR). reflexivity. }
  rewrite OK.
  assert (SR : sc_in_seq_range sc = false).
  { unfold sc_in_seq_range. destruct CASES as [(-> & _)|(Hsc & _)]; [reflexivity|]. apply andb_false_iff. right. apply Z.ltb_ge. lia. }
  set (K := fun (st2 : mstate) (mi : mapinfo) => match mi with
         | Some (base, len) => if negb (len =? 0) then SVis (EMunmap (conc st2 base) len) (fun ru => if munmap_answer_ok ru then ret (drop_region (fst base) st2) else bad_answer (ret cs)) else ret st2
         | None => ret st2 end).
  assert (GF : forall stX pv' nx',
    MR stX g = mkMeta pv' nx' (Some p) 0 0 0 1 sc ml -> (forall x, x <> g -> MR stX x = MR cs x) ->
    s_regions stX = s_regions cs -> s_slots stX = s_slots cs -> s_groups stX = s_groups cs -> s_reserved stX = s_reserved cs -> s_next_rid stX = s_next_rid cs ->
    c_free_meta_head (s_ctx stX) = None -> c_init_done (s_ctx stX) = c_init_done (s_ctx cs) -> c_bounces (s_ctx stX) = ∅ -> c_unmap_seq (s_ctx stX) = ∅ ->
    c_avail_meta (s_ctx stX) = c_avail_meta (s_ctx cs) -> c_avail_meta_count (s_ctx stX) = c_avail_meta_count (s_ctx cs) ->
    (forall sc', active stX sc' = if (sc' =? sc) && (sc <? 48) then None else active cs sc') ->
    exists K0, sbind (free_group mstate dec_slots (nontrivial_free dec_slots 63) stX g K (ret cs)) (fun x => ret (strip x)) = SVis (EMunmap (conc cs p) (ml * 4096)) K0
      /\ forall ru, munmap_answer_ok ru = true ->
           exists cs', K0 ru = SRet cs' /\ FREEPOST cs c g p sc cs' /\ TT cnt cs' /\ INJ cs' /\ strip cs' = cs').
  { intros stX pv' nx' MRX MRXo RGX SLX GRX RSX NRX FHX INX BNX UQX AVX CNX ACX.
    unfold free_group. fold (MR stX g). rewrite MRX. cbn [m_sizeclass m_mem m_last_idx m_maplen].
    replace (negb (ml =? 0)) with true by (symmetry; rewrite negb_true_iff; apply Z.eqb_neq; lia). cbv iota.
    set (st1 := if sc <? 48 then _ else _). set (st1' := del_slots _ _ _ _). set (st2 := record_seq _ _).
    assert (RS2 : record_seq sc (step_seq st1') = step_seq st1') by (unfold record_seq; rewrite SR; reflexivity).
    assert (C1 : s_ctx st1 = s_ctx stX \/ s_ctx st1 = s_ctx (set_usage sc (usage stX sc - (0 + 1)) stX))
      by (unfold st1; destruct (sc <? 48); [right| left]; reflexivity).
    assert (F1 : s_metas st1 = s_metas stX /\ s_regions st1 = s_regions stX /\ s_slots st1 = s_slots stX /\ s_groups st1 = s_groups stX
                 /\ s_reserved st1 = s_reserved stX /\ s_next_rid st1 = s_next_rid stX)
      by (unfold st1; destruct (sc <? 48); repeat split; reflexivity).
    cps_destruct F1 as (M1 & R1 & S1 & G1 & V1 & N1).
    cps_pose (step_seq_facts st1') as (Srg & Srs & Smt & Sgr & Ssl & Snr & Sac & Sus & Sbn & Sfh & Sav & Scn & Sin & Smc & Suq).
    assert (CX : forall P : mctx -> Prop,
              (forall cx v, P (set_usage_map v cx) <-> P cx) -> P (s_ctx stX) -> P (s_ctx st1)).
    { intros P HP H. destruct C1 as [E|E]; rewrite E; [exact H|]. cbn. apply HP. exact H. }
    assert (IN1 : c_init_done (s_ctx st1) = c_init_done (s_ctx stX)) by (apply (CX (fun cx => c_init_done cx = c_init_done (s_ctx stX))); [intros; cbn; tauto| reflexivity]).
    assert (BN1 : c_bounces (s_ctx st1) = ∅) by (apply (CX (fun cx => c_bounces cx = ∅)); [intros; cbn; tauto| exact BNX]).
    assert (UQ1 : c_unmap_seq (s_ctx st1) = ∅) by (apply (CX (fun cx => c_unmap_seq cx = ∅)); [intros; cbn; tauto| exact UQX]).
    assert (AV1 : c_avail_meta (s_ctx st1) = c_avail_meta (s_ctx stX)) by (apply (CX (fun cx => c_avail_meta cx = c_avail_meta (s_ctx stX))); [intros; cbn; tauto| reflexivity]).
    assert (CN1 : c_avail_meta_count (s_ctx st1) = c_avail_meta_count (s_ctx stX)) by (apply (CX (fun cx => c_avail_meta_count cx = c_avail_meta_count (s_ctx stX))); [intros; cbn; tauto| reflexivity]).
    assert (HD1 : c_free_meta_head (s_ctx st1) = c_free_meta_head (s_ctx stX)) by (apply (CX (fun cx => c_free_meta_head cx = c_free_meta_head (s_ctx stX))); [intros; cbn; tauto| reflexivity]).
    cps_destruct (free_meta_eq g st2 (fun st3 => K st3 (Some (p, ml * 4096))) (ret cs))
      as (st3 & E3 & Qrg & Qrs & Qnr & Qgr & Qsl & Qac & Qus & Qbn & Quq & Qin & Qav & Qcn & Qmc & Qhd & _ & Qmr).
    rewrite E3. unfold K at 1. replace (negb (ml * 4096 =? 0)) with true by (symmetry; rewrite negb_true_iff; apply Z.eqb_neq; lia).
    cbv iota beta. rewrite sbind_vis.
    assert (RG3 : s_regions st3 = s_regions cs) by (rewrite Qrg; unfold st2; rewrite RS2, Srg; unfold st1'; cbn; rewrite R1; exact RGX).
    assert (CC : conc st3 p = conc cs p) by (unfold conc, get_region; rewrite RG3; reflexivity).
    rewrite CC. eexists. split; [reflexivity|].
    intros ru RU. cbn beta. rewrite RU, sbind_ret_l. eexists. split; [reflexivity|].
    (* [comment removed for export] *)
    assert (FH2 : c_free_meta_head (s_ctx st2) = None).
    { unfold st2. rewrite RS2, Sfh. unfold st1'. cbn. rewrite HD1. exact FHX. }
    destruct (Qhd FH2) as [HD3 MR3].
    assert (MT2 : s_metas st2 = s_metas stX) by (unfold st2; rewrite RS2, Smt; unfold st1'; cbn; exact M1).
    assert (AC2 : forall sc', active st2 sc' = active stX sc').
    { intros sc'. unfold active, ctx, st2. rewrite RS2, Sac. unfold st1'. cbn.
      destruct C1 as [E|E]; rewrite E; reflexivity. }
    set (cs' := strip (drop_region (fst p) st3)).
    assert (MRo' : forall x, x <> g -> MR cs' x = MR cs x).
    { intros x NE. unfold cs', MR. rewrite get_meta_rec_strip. unfold get_meta_rec. rewrite s_metas_drop_region.
      fold (get_meta_rec st3 x). fold (MR st3 x). rewrite Qmr; [| exact NE| rewrite FH2; discriminate| intros hd Hh; rewrite FH2 in Hh; discriminate].
      unfold MR, get_meta_rec. rewrite MT2. fold (get_meta_rec stX x) (MR stX x). apply MRXo. exact NE. }
    assert (ACT' : forall sc', active cs' sc' = if (sc' =? sc) && (sc <? 48) then None else active cs sc').
    { intros sc'. unfold cs'. rewrite active_strip. unfold active, ctx. cbn. fold (ctx st3) (active st3 sc'). rewrite Qac, AC2. apply ACX. }
    assert (PL' : forall x, in_pool cs' x <-> x = g \/ in_pool cs x).
    { intros x. unfold in_pool, cs'. cbn. rewrite HD3, Qav. unfold st2. rewrite RS2, Sav. unfold st1'. cbn.
      rewrite AV1, AVX, FH. split; [intros [H|H]; [left; congruence| right; right; exact H]| intros [->|[H|H]]; [left; reflexivity| discriminate| right; exact H]]. }
    split; [| split; [| split]].
    - constructor.
      + intros x. unfold cs'. rewrite s_slots_strip, s_slots_drop_region, Qsl. unfold st2. rewrite RS2, Ssl. unfold st1'.
        rewrite lookup_del_slots by (unfold get_stride; cbn; rewrite ?Z.eqb_refl; destruct (ml =? 0) eqn:E; [apply Z.eqb_eq in E; lia|]; cbn; unfold UNIT; lia).
        replace (get_stride _) with (ml * 4096 - UNIT).
        2:{ unfold get_stride. cbn [m_last_idx m_maplen m_sizeclass]. rewrite Z.eqb_refl. replace (ml =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
        rewrite slot_key_single by (unfold UNIT; lia). rewrite <- Hc. cbn [s_slots del_group set_groups]. rewrite S1, SLX. reflexivity.
      + intros x. unfold cs'. rewrite s_groups_strip, s_groups_drop_region, Qgr. unfold st2. rewrite RS2, Sgr. unfold st1'. cbn. rewrite lookup_del_group, G1, GRX. reflexivity.
      + intros rid. unfold cs'. rewrite s_regions_strip, lookup_drop_region, RG3. reflexivity.
      + unfold cs'. rewrite s_reserved_strip. cbn. rewrite Qrs. unfold st2. rewrite RS2, Srs. unfold st1'. cbn. rewrite V1. exact RSX.
      + unfold cs'. rewrite s_next_rid_strip. cbn. rewrite Qnr. unfold st2. rewrite RS2, Snr. unfold st1'. cbn. rewrite N1. exact NRX.
      + unfold cs', MR. rewrite get_meta_rec_strip. unfold get_meta_rec. rewrite s_metas_drop_region. exact MR3.
      + exact MRo'.
      + exact ACT'.
      + unfold cs'. cbn. exact HD3.
      + unfold cs'. cbn. rewrite Qin. unfold st2. rewrite RS2, Sin. unfold st1'. cbn. rewrite IN1. exact INX.
      + unfold cs'. cbn. rewrite Qbn. unfold st2. rewrite RS2, Sbn. unfold st1'. cbn. exact BN1.
      + unfold cs'. cbn. rewrite Quq. unfold st2. rewrite RS2. apply Suq. unfold st1'. cbn. exact UQ1.
      + unfold cs'. cbn. rewrite Qav. unfold st2. rewrite RS2, Sav. unfold st1'. cbn. rewrite AV1. exact AVX.
      + unfold cs'. cbn. rewrite Qcn. unfold st2. rewrite RS2, Scn. unfold st1'. cbn. rewrite CN1. exact CNX.
    - constructor.
      + unfold cs'. cbn. rewrite Qin. unfold st2. rewrite RS2, Sin. unfold st1'. cbn. rewrite IN1, INX. apply (tt_init _ _ HT).
      + intros sc'. rewrite ACT'. destruct ((sc' =? sc) && (sc <? 48)) eqn:EB; [left; reflexivity|].
        destruct (tt_act _ _ HT sc') as [H|(g' & H & (F1 & F2 & F3) & NP')]; [left; exact H| right].
        assert (NE : g' <> g).
        { intros ->. destruct (HAg sc' H) as [-> L]. rewrite Z.eqb_refl, (proj2 (Z.ltb_lt _ _) L) in EB. discriminate. }
        exists g'. split; [exact H|]. unfold full1. rewrite !MRo' by exact NE. split; [auto|]. rewrite PL'. intros [E|P]; [exact (NE E)| exact (NP' P)].
      + unfold cs'. cbn. rewrite Qbn. unfold st2. rewrite RS2, Sbn. unfold st1'. cbn. exact BN1.
      + unfold cs'. cbn. rewrite Quq. unfold st2. rewrite RS2. apply Suq. unfold st1'. cbn. exact UQ1.
      + intros m Hm. unfold cs' in Hm. cbn in Hm. rewrite HD3 in Hm. injection Hm as <-.
        split; [unfold cs', MR; rewrite get_meta_rec_strip; unfold get_meta_rec; rewrite s_metas_drop_region; fold (get_meta_rec st3 g) (MR st3 g); rewrite MR3; reflexivity|].
        intros am i Ham Hi E. apply NP. right. exists am, i. split; [| auto].
        revert Ham. unfold cs'. cbn. rewrite Qav. unfold st2. rewrite RS2, Sav. unfold st1'. cbn. rewrite AV1, AVX. intros X; exact X.
      + unfold cs'. cbn. rewrite Qav. unfold st2. rewrite RS2, Sav. unfold st1'. cbn. rewrite AV1, AVX. apply (tt_avail _ _ HT).
      + unfold cs'. cbn. rewrite Qcn. unfold st2. rewrite RS2, Scn. unfold st1'. cbn. rewrite CN1, CNX. apply (tt_cnt _ _ HT).
    - intros a b g0 Ha Hb. rewrite ACT' in Ha, Hb. destruct ((a =? sc) && (sc <? 48)); [discriminate|]. destruct ((b =? sc) && (sc <? 48)); [discriminate|]. exact (HI a b g0 Ha Hb).
    - apply strip_strip. }
  destruct CASES as [(Hsc & ->)|(Hsc & -> & HA & STR)].
  - eapply (GF cs pv None MRg); try reflexivity; try (intros; reflexivity).
    + exact FH. + apply (tt_bnc _ _ HT). + apply (tt_useq _ _ HT).
    + intros sc'. rewrite Hsc. destruct (sc' =? 63); reflexivity.
  - cbn [guard]. rewrite (proj2 (Z.ltb_lt sc 48)) by lia. rewrite HA, optr_eqb_refl.
    set (st1 := dequeue (LActive sc) g cs).
    assert (E1 : st1 = upd_meta g (fun r => m_set_prev None (m_set_next None r)) (set_active sc None cs)).
    { unfold st1, dequeue. fold (MR cs g). rewrite MRg. cbn [m_next m_prev]. rewrite optr_eqb_refl. cbn [negb]. reflexivity. }
    assert (A1 : forall sc', active st1 sc' = if sc' =? sc then None else active cs sc').
    { intros sc'. rewrite E1, active_upd_meta, active_set_active. reflexivity. }
    rewrite (A1 sc), Z.eqb_refl.
    eapply (GF st1 None None); try (rewrite E1; reflexivity).
    + rewrite E1. unfold MR. rewrite get_meta_rec_upd_same. rewrite (get_meta_rec_ext cs (set_active sc None cs)) by reflexivity.
      fold (MR cs g). rewrite MRg. reflexivity.
    + intros x NE. rewrite E1. unfold MR. rewrite get_meta_rec_upd_other by exact NE. reflexivity.
    + rewrite E1. cbn. exact FH.
    + rewrite E1. cbn. apply (tt_bnc _ _ HT).
    + rewrite E1. cbn. apply (tt_useq _ _ HT).
    + intros sc'. rewrite A1. rewrite (proj2 (Z.ltb_lt sc 48)) by lia. rewrite andb_true_r. reflexivity.
Qed.

Lemma cmalloc_big_event cs n :
  MMAP_THRESHOLD <= n -> n + IB + UNIT <= 2^30 ->
  exists K, cmalloc cs n = SVis (EMmap 0 (n + IB + UNIT) PROT_RW (MAP_PRIVATE + MAP_ANON)) K.
Proof.
  intros Hn Hn2. unfold cmalloc, malloc_core.
  replace (size_overflows n) with false by (symmetry; unfold size_overflows, MMAP_THRESHOLD, IB, UNIT in *; apply Z.leb_gt; lia).
  replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; lia).
  rewrite sbind_vis. eexists. reflexivity.
Qed.

End ACeilS1.
