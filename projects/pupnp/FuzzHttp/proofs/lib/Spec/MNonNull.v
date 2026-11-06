(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import LiaTuning.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc.
Import ListNotations.
Local Open Scope Z_scope.

Definition good (e : ev) (z : Z) : bool :=
  match e with
  | EMmap _ _ _ _ => negb (is_err z)
  | EMprotect _ _ _ => z =? 0
  | EBrk _ => true
  | EMunmap _ _ => true
  | EPeek _ _ _ => false
  | EUndef _ => false
  end.

Inductive gpath {R} : M R -> R -> Prop :=
| gp_ret : forall r, gpath (SRet r) r
| gp_vis : forall e k z r, good e z = true -> gpath (k z) r -> gpath (SVis e k) r.

Lemma gpath_ret_inv {R} (x r : R) : gpath (SRet x) r -> r = x.
Proof. intros H. inversion H. reflexivity. Qed.

Lemma gpath_vis_inv {R} e (k : Z -> M R) r : gpath (SVis e k) r -> exists z, good e z = true /\ gpath (k z) r.
Proof. intros H. inversion H; subst. eauto. Qed.

Lemma gpath_undef {R} u (k : Z -> M R) r : gpath (SVis (EUndef u) k) r -> False.
Proof. intros H. apply gpath_vis_inv in H as (z & Hg & _). discriminate. Qed.

Lemma gpath_bad_answer {R} (bail : M R) r : gpath (bad_answer bail) r -> False.
Proof. unfold bad_answer. apply gpath_undef. Qed.

Lemma gpath_guard {R} tag c (k bail : M R) r : gpath (guard tag c k bail) r -> c = true /\ gpath k r.
Proof. unfold guard. destruct c; [auto| intros H; exfalso; exact (gpath_undef _ _ _ H)]. Qed.

Lemma gpath_sbind {A B} (t : M A) (f : A -> M B) r : gpath (sbind t f) r -> exists x, gpath t x /\ gpath (f x) r.
Proof.
  revert r. induction t as [x|e k IH]; intros r H; cbn in H.
  - exists x. split; [constructor| exact H].
  - apply gpath_vis_inv in H as (z & Hg & H). destruct (IH z r H) as (x & H1 & H2).
    exists x. split; [econstructor; eauto| exact H2].
Qed.

Ltac gp H :=
  repeat first
    [ apply gpath_ret_inv in H
    | exfalso; exact (gpath_undef _ _ _ H)
    | exfalso; exact (gpath_bad_answer _ _ H)
    | apply gpath_guard in H as [? H]
    | let z := fresh "z" in let Hg := fresh "Hg" in apply gpath_vis_inv in H as (z & Hg & H); cbn [good] in Hg ].

Lemma gpath_queue {R} h m st (k : mstate -> M R) bail r :
  gpath (queue h m st k bail) r -> exists st', gpath (k st') r.
Proof.
  unfold queue. intros H. gp H. destruct (get_head st h); eexists; exact H.
Qed.

Lemma gpath_free_meta {R} m st (k : mstate -> M R) bail r :
  gpath (free_meta m st k bail) r -> exists st', gpath (k st') r.
Proof. unfold free_meta. apply gpath_queue. Qed.

Lemma gpath_activate_group {R} m st (k : mstate -> Z -> M R) bail r :
  gpath (activate_group m st k bail) r -> exists st' mask, gpath (k st' mask) r.
Proof. unfold activate_group. intros H. gp H. eexists _, _. exact H. Qed.

Lemma gpath_am_take {R} st (k : mstate -> optr -> M R) bail r :
  gpath (am_take st k bail) r -> exists st' m, gpath (k st' (Some m)) r.
Proof. unfold am_take. intros H. destruct (c_avail_meta (ctx st)); gp H. eexists _, _. exact H. Qed.

Lemma gpath_am_carve {R} st p (k : mstate -> optr -> M R) bail r :
  gpath (am_carve st p k bail) r -> exists st' m, gpath (k st' (Some m)) r.
Proof. unfold am_carve. intros H. eapply gpath_am_take. exact H. Qed.

Lemma gpath_am_finish {R} st nu (k : mstate -> optr -> M R) bail r :
  gpath (am_finish st nu k bail) r -> exists st' m, gpath (k st' (Some m)) r.
Proof.
  unfold am_finish. intros H. destruct (c_avail_meta_areas (ctx st)) as [p|]; [| gp H].
  destruct (if negb (snd p mod PGSZ =? 0) then false else nu).
  - gp H. destruct (negb (mprotect_answer_ok z)); [gp H|]. apply Z.eqb_eq in Hg. subst z. cbn [Z.eqb orb] in H.
    eapply gpath_am_carve. exact H.
  - eapply gpath_am_carve. exact H.
Qed.

Lemma gpath_am_after_brk {R} st nu (k : mstate -> optr -> M R) bail r :
  gpath (am_after_brk st nu k bail) r -> exists st' m, gpath (k st' (Some m)) r.
Proof.
  unfold am_after_brk. intros H. destruct (c_avail_meta_area_count (ctx st) =? 0).
  - gp H. destruct (negb (mmap_answer_ok _ _ _ z)); [gp H|]. apply negb_true_iff in Hg. rewrite Hg in H.
    destruct (new_region RKMeta z _ st) as [st1 rid]. eapply gpath_am_finish. exact H.
  - eapply gpath_am_finish. exact H.
Qed.

Lemma gpath_alloc_meta {R} st (k : mstate -> optr -> M R) bail r :
  gpath (alloc_meta st k bail) r -> exists st' m, gpath (k st' (Some m)) r.
Proof.
  unfold alloc_meta. intros H.
  set (st0 := if c_init_done (ctx st) =? 0 then _ else st) in H.
  destruct (c_free_meta_head (ctx st0)) as [m|]; [eexists _, _; exact H|].
  destruct (negb (c_avail_meta_count (ctx st0) =? 0)); [eapply gpath_am_take; exact H|].
  destruct ((c_avail_meta_area_count (ctx st0) =? 0) && negb match c_brk (ctx st0) with BrkDead => true | _ => false end);
    [| eapply gpath_am_after_brk; exact H].
  destruct (c_brk (ctx st0)) as [| |rid off].
  - gp H. destruct (negb (brk0_answer_ok z)); [gp H|]. gp H. destruct (negb (brk_answer_ok z _ z0)); [gp H|].
    destruct (negb (z0 =? _)); [eapply gpath_am_after_brk; exact H|].
    destruct (negb (brk_pages_ok st0 _ _)); [gp H|]. gp H. destruct (negb (mmap_fixed_answer_ok _ z1)); [gp H|].
    destruct (new_region RKBrk _ _ st0) as [st1 rid]. eapply gpath_am_after_brk. exact H.
  - eapply gpath_am_after_brk. exact H.
  - gp H. destruct (negb (brk_answer_ok _ _ z)); [gp H|]. destruct (negb (z =? _)); [eapply gpath_am_after_brk; exact H|].
    destruct (negb (brk_pages_ok st0 _ _)); [gp H|]. eapply gpath_am_after_brk. exact H.
Qed.

Lemma gpath_try_avail {R} sc st (k : mstate -> Z -> M R) bail r :
  gpath (try_avail sc st k bail) r -> exists st' first, gpath (k st' first) r.
Proof.
  unfold try_avail. intros H. destruct (active st sc) as [m|]; [| eexists _, _; exact H].
  destruct (negb (m_avail (get_meta_rec st m) =? 0)). { unfold ta_fin in H. eexists _, _; exact H. }
  match type of H with gpath (match ?s with _ => _ end) _ => destruct s as [[st1 m1]|] end.
  - match type of H with gpath (match ?x with _ => _ end) _ => destruct x as [[st2 m2] mask] end.
    match type of H with gpath (match ?x with _ => _ end) _ => destruct x as [st3 m3] end.
    apply gpath_activate_group in H as (st4 & mask4 & H). gp H. unfold ta_fin in H. eexists _, _; exact H.
  - destruct (m_freed (get_meta_rec st m) =? 0); [eexists _, _; exact H| gp H].
Qed.

Lemma gpath_alloc_group {R} lay aslot st sc req (k : mstate -> optr -> M R) bail r :
  (forall st1 j req1 k1 bail1, gpath (aslot st1 j req1 k1 bail1) r -> exists st2 idx, 0 <= idx /\ gpath (k1 st2 idx) r) ->
  gpath (alloc_group R lay aslot st sc req k bail) r -> exists st' g, gpath (k st' (Some g)) r.
Proof.
  intros HREC H. unfold alloc_group in H. apply gpath_alloc_meta in H as (st1 & m & H). cbn beta iota in H.
  match type of H with gpath (if ?c then _ else _) _ => destruct c end.
  -
    match type of H with gpath (match ?x with _ => _ end) _ => destruct x as [cnt needed] end.
    gp H. destruct (negb (mmap_answer_ok _ _ _ z)); [gp H|]. apply negb_true_iff in Hg. rewrite Hg in H.
    destruct (new_region RKGroup z needed st1) as [st2 rid]. unfold ag_tail in H. eexists _, _; exact H.
  -
    apply HREC in H as (st2 & idx & Hidx & H). rewrite (proj2 (Z.ltb_ge idx 0)) in H by lia.
    destruct (active st2 _) as [g|]; [| gp H]. unfold ag_tail in H. eexists _, _; exact H.
Qed.

Lemma ctz32_nonneg m : 0 <= ctz32 m.
Proof. unfold ctz32. apply Z.log2_nonneg. Qed.

Lemma gpath_alloc_slot {R} lay fuel : forall st sc req (k : mstate -> Z -> M R) bail r,
  gpath (alloc_slot lay fuel st sc req k bail) r -> exists st' idx, 0 <= idx /\ gpath (k st' idx) r.
Proof.
  induction fuel as [|f IH]; intros st sc req k bail r H; cbn [alloc_slot] in H; [gp H|].
  apply gpath_try_avail in H as (st1 & first & H).
  destruct (negb (first =? 0)).
  - eexists _, _. split; [apply ctz32_nonneg| exact H].
  - apply (gpath_alloc_group lay (alloc_slot lay f)) in H as (st2 & g & H); [| intros; eapply IH; eauto].
    cbn iota in H. apply gpath_queue in H as (st4 & H). eexists _, 0. split; [lia| exact H].
Qed.

Lemma gpath_malloc_small_ctrl {R} lay st n (k : mstate -> option (aptr * Z) -> M R) bail r :
  gpath (malloc_small_ctrl lay st n k bail) r -> exists st' g idx, gpath (k st' (Some (g, idx))) r.
Proof.
  unfold malloc_small_ctrl. intros H.
  match type of H with gpath (match active st ?sc with _ => _ end) _ => set (SC := sc) in H; destruct (active st SC) as [gp0|] end.
  - destruct (negb (lowbit (m_avail (get_meta_rec st gp0)) =? 0)).
    + eexists _, _, _; exact H.
    + apply gpath_alloc_slot in H as (st1 & idx & Hidx & H). rewrite (proj2 (Z.ltb_ge idx 0)) in H by lia.
      destruct (active st1 SC) as [g|]; [| gp H]. eexists _, _, _; exact H.
  - apply gpath_alloc_slot in H as (st1 & idx & Hidx & H). rewrite (proj2 (Z.ltb_ge idx 0)) in H by lia.
    destruct (active st1 SC) as [g|]; [| gp H]. eexists _, _, _; exact H.
Qed.

Theorem gpath_malloc_core lay st n r :
  size_overflows n = false -> gpath (malloc_core lay st n) r -> exists st' x, r = (st', Some x).
Proof.
  intros Hov H. unfold malloc_core in H. rewrite Hov in H.
  destruct (MMAP_THRESHOLD <=? n).
  - gp H. destruct (negb (mmap_answer_ok _ _ _ z)); [gp H|]. apply negb_true_iff in Hg. rewrite Hg in H.
    destruct (new_region RKGroup z _ st) as [st1 rid]. apply gpath_alloc_meta in H as (st3 & g & H). cbn iota in H.
    gp H. eexists _, _; exact H.
  - apply gpath_malloc_small_ctrl in H as (st1 & g & idx & H). gp H. eexists _, _; exact H.
Qed.

Theorem gpath_cmalloc cs n r :
  size_overflows n = false -> gpath (cmalloc cs n) r -> exists c, snd r = Some c.
Proof.
  intros Hov H. unfold cmalloc in H. apply gpath_sbind in H as ([st1 x] & H1 & H2).
  apply (gpath_malloc_core lay_none cs n) in H1 as (st' & [g idx] & E); [| exact Hov]. injection E as -> ->.
  gp H2. subst r. eexists. reflexivity.
Qed.

Lemma size_overflows_small n : n < 2^62 -> size_overflows n = false.
Proof. intros Hn. unfold size_overflows. apply Z.leb_gt. lia. Qed.
