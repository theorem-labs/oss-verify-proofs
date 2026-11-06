(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import STree Malloc.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition okz (e : ev) (z : Z) : Prop :=
  match e with
  | EMmap _ _ _ flags => (Z.land flags MAP_FIXED =? 0) = false \/ is_err z = false
  | EMprotect _ _ _ => z = 0
  | EUndef _ => False
  | _ => True
  end.

Fixpoint nn {R} (P : R -> Prop) (t : M R) {struct t} : Prop :=
  match t with
  | SRet r => P r
  | SVis e k => forall z, okz e z -> nn P (k z)
  end.

Lemma nn_ret {R} (P : R -> Prop) r : P r -> nn P (ret r).
Proof. intros H. exact H. Qed.

Lemma nn_sbind {R S} (P1 : R -> Prop) (P : S -> Prop) (t : M R) (f : R -> M S) :
  nn P1 t -> (forall r, P1 r -> nn P (f r)) -> nn P (sbind t f).
Proof.
  revert t. fix IH 1. intros [r|e k]; cbn; intros H Hf.
  - apply Hf. exact H.
  - intros z Hz. apply IH; [apply H; exact Hz| exact Hf].
Qed.

Lemma nn_mono {R} (P P' : R -> Prop) (t : M R) : nn P t -> (forall r, P r -> P' r) -> nn P' t.
Proof.
  revert t. fix IH 1. intros [r|e k]; cbn; intros H HP.
  - apply HP. exact H.
  - intros z Hz. apply IH; [apply H; exact Hz| exact HP].
Qed.

Lemma nn_undef {R} (P : R -> Prop) w (k : Z -> M R) : nn P (SVis (EUndef w) k).
Proof. intros z []. Qed.

Lemma nn_bad_answer {R} (P : R -> Prop) (bail : M R) : nn P (bad_answer bail).
Proof. apply nn_undef. Qed.

Lemma nn_guard {R} (P : R -> Prop) tag c (k bail : M R) : nn P k -> nn P (guard tag c k bail).
Proof. intros H. unfold guard. destruct c; [exact H| apply nn_undef]. Qed.

(* [comment removed for export] *)
Lemma nn_vis_any {R} (P : R -> Prop) e (k : Z -> M R) : (forall z, nn P (k z)) -> nn P (SVis e k).
Proof. intros H z _. apply H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Walk.
Context {R : Type} (P : R -> Prop).

Lemma nn_queue h m st (k : mstate -> M R) bail : (forall st', nn P (k st')) -> nn P (queue h m st k bail).
Proof.
  intros Hk. unfold queue. apply nn_guard. apply nn_guard. destruct (get_head st h); apply Hk.
Qed.

Lemma nn_free_meta m st (k : mstate -> M R) bail : (forall st', nn P (k st')) -> nn P (free_meta m st k bail).
Proof. intros Hk. unfold free_meta. apply nn_queue. exact Hk. Qed.

Lemma nn_activate_group m st (k : mstate -> Z -> M R) bail :
  (forall st' z, nn P (k st' z)) -> nn P (activate_group m st k bail).
Proof. intros Hk. unfold activate_group. apply nn_guard. apply Hk. Qed.

Lemma nn_am_take st (k : mstate -> optr -> M R) bail :
  (forall st' m, nn P (k st' (Some m))) -> nn P (am_take st k bail).
Proof. intros Hk. unfold am_take. destruct (c_avail_meta (ctx st)); [apply Hk| apply nn_undef]. Qed.

Lemma nn_am_carve st p (k : mstate -> optr -> M R) bail :
  (forall st' m, nn P (k st' (Some m))) -> nn P (am_carve st p k bail).
Proof. intros Hk. unfold am_carve. apply nn_am_take. exact Hk. Qed.

Lemma nn_am_finish st nu (k : mstate -> optr -> M R) bail :
  (forall st' m, nn P (k st' (Some m))) -> nn P (am_finish st nu k bail).
Proof.
  intros Hk. unfold am_finish. destruct (c_avail_meta_areas (ctx st)) as [p|]; [| apply nn_undef].
  match goal with |- nn P (if ?c then _ else _) => destruct c end; [| apply nn_am_carve; exact Hk].
  intros z Hz. cbn in Hz. subst z.
  replace (negb (mprotect_answer_ok 0)) with false by reflexivity.
  replace ((0 =? 0) || (0 =? TWO64 - ENOSYS)) with true by reflexivity. cbn iota. apply nn_am_carve. exact Hk.
Qed.

Lemma land_mapf : (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) = true.
Proof. reflexivity. Qed.

Lemma nn_am_after_brk st nu (k : mstate -> optr -> M R) bail :
  (forall st' m, nn P (k st' (Some m))) -> nn P (am_after_brk st nu k bail).
Proof.
  intros Hk. unfold am_after_brk. destruct (c_avail_meta_area_count (ctx st) =? 0); [| apply nn_am_finish; exact Hk].
  intros z Hz. cbn [okz] in Hz. rewrite land_mapf in Hz. destruct Hz as [Hz|Hz]; [discriminate|].
  destruct (negb _); [apply nn_bad_answer|]. rewrite Hz.
  destruct (new_region _ _ _ _) as [st1 rid]. apply nn_am_finish. exact Hk.
Qed.

Lemma nn_alloc_meta st (k : mstate -> optr -> M R) bail :
  (forall st' m, nn P (k st' (Some m))) -> nn P (alloc_meta st k bail).
Proof.
  intros Hk. unfold alloc_meta.
  set (st0 := if c_init_done (ctx st) =? 0 then _ else _). clearbody st0.
  destruct (c_free_meta_head (ctx st0)); [apply Hk|].
  destruct (negb (c_avail_meta_count (ctx st0) =? 0)); [apply nn_am_take; exact Hk|].
  match goal with |- nn P (if ?c then _ else _) => destruct c end; [| apply nn_am_after_brk; exact Hk].
  destruct (c_brk (ctx st0)) as [| |rid off].
  - apply nn_vis_any. intros cur. destruct (negb (brk0_answer_ok cur)); [apply nn_bad_answer|].
    apply nn_vis_any. intros r. destruct (negb (brk_answer_ok _ _ r)); [apply nn_bad_answer|].
    destruct (negb (r =? _)); [apply nn_am_after_brk; exact Hk|].
    destruct (negb (brk_pages_ok _ _ _)); [apply nn_bad_answer|].
    apply nn_vis_any. intros rg. destruct (negb (mmap_fixed_answer_ok _ rg)); [apply nn_bad_answer|].
    destruct (new_region _ _ _ _) as [st1 rid]. apply nn_am_after_brk; exact Hk.
  - apply nn_am_after_brk; exact Hk.
  - apply nn_vis_any. intros r. destruct (negb (brk_answer_ok _ _ r)); [apply nn_bad_answer|].
    destruct (negb (r =? _)); [apply nn_am_after_brk; exact Hk|].
    destruct (negb (brk_pages_ok _ _ _)); [apply nn_bad_answer|].
    apply nn_am_after_brk; exact Hk.
Qed.

Lemma nn_ta_fin st m mask (k : mstate -> Z -> M R) : (forall st' z, nn P (k st' z)) -> nn P (ta_fin st m mask k).
Proof. intros Hk. unfold ta_fin. apply Hk. Qed.

Lemma nn_try_avail sc st (k : mstate -> Z -> M R) bail :
  (forall st' z, nn P (k st' z)) -> nn P (try_avail sc st k bail).
Proof.
  intros Hk. unfold try_avail. destruct (active st sc) as [m|]; [| apply Hk].
  destruct (negb (m_avail (get_meta_rec st m) =? 0)); [apply nn_ta_fin; exact Hk|].
  match goal with |- nn P (match ?s with Some _ => _ | None => _ end) => destruct s as [[st1 m1]|] end.
  2:{ destruct (m_freed _ =? 0); [apply Hk| apply nn_undef]. }
  match goal with |- nn P (let (a, b) := ?x in _) => destruct x as [[st2 m2] mask] end.
  match goal with |- nn P (let (a, b) := ?x in _) => destruct x as [st3 m3] end.
  apply nn_activate_group. intros st4 z. apply nn_guard. apply nn_ta_fin. exact Hk.
Qed.

Lemma nn_ag_tail lay st sc m p cnt ai (k : mstate -> optr -> M R) :
  (forall st', nn P (k st' (Some m))) -> nn P (ag_tail lay st sc m p cnt ai k).
Proof. intros Hk. unfold ag_tail. apply Hk. Qed.

Lemma nn_alloc_group lay (asr : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R) st sc req (k : mstate -> optr -> M R) bail :
  (forall st1 sc1 req1 (k1 : mstate -> Z -> M R) bail1, (forall st' idx, 0 <= idx -> nn P (k1 st' idx)) -> nn P (asr st1 sc1 req1 k1 bail1)) ->
  (forall st' m, nn P (k st' (Some m))) -> nn P (alloc_group R lay asr st sc req k bail).
Proof.
  intros Hasr Hk. unfold alloc_group. apply nn_alloc_meta. intros st1 m. cbv beta iota.
  match goal with |- nn P (if ?c then _ else _) => destruct c end.
  - (* [comment removed for export] *)
    match goal with |- nn P (let (a, b) := ?x in _) => destruct x as [cnt needed] end.
    intros z Hz. cbn [okz] in Hz. rewrite land_mapf in Hz. destruct Hz as [Hz|Hz]; [discriminate|].
    destruct (negb _); [apply nn_bad_answer|]. rewrite Hz.
    destruct (new_region _ _ _ _) as [st2 rid]. apply nn_ag_tail. intros st'. apply Hk.
  - (* [comment removed for export] *)
    apply Hasr. intros st' idx Hidx. replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (active st' _) as [g|]; [| apply nn_undef]. apply nn_ag_tail. intros st''. apply Hk.
Qed.

Lemma ctz32_nonneg first : 0 <= ctz32 first.
Proof. unfold ctz32. apply Z.log2_nonneg. Qed.

Lemma nn_alloc_slot lay fuel : forall st sc req (k : mstate -> Z -> M R) bail,
  (forall st' idx, 0 <= idx -> nn P (k st' idx)) -> nn P (alloc_slot lay fuel st sc req k bail).
Proof.
  induction fuel as [|f IH]; intros st sc req k bail Hk; cbn [alloc_slot]; [apply nn_undef|].
  apply nn_try_avail. intros st1 first. destruct (negb (first =? 0)); [apply Hk; apply ctz32_nonneg|].
  apply nn_alloc_group; [exact IH|]. intros st2 g. cbv beta iota. apply nn_queue. intros st4. apply Hk. lia.
Qed.

Lemma nn_malloc_small_ctrl lay st n (k : mstate -> option (aptr * Z) -> M R) bail :
  (forall st' g idx, nn P (k st' (Some (g, idx)))) -> nn P (malloc_small_ctrl lay st n k bail).
Proof.
  intros Hk. unfold malloc_small_ctrl.
  match goal with |- nn P (match ?g with Some _ => _ | None => _ end) => destruct g as [gp|] end.
  - destruct (negb _); [apply Hk|].
    apply nn_alloc_slot. intros st' idx Hidx. replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (active st' _); [apply Hk| apply nn_undef].
  - cbn iota. apply nn_alloc_slot. intros st' idx Hidx. replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (active st' _); [apply Hk| apply nn_undef].
Qed.

End Walk.

Lemma nn_malloc_core lay st n : size_overflows n = false ->
  nn (fun r => exists g idx, snd r = Some (g, idx)) (malloc_core lay st n).
Proof.
  intros Hn. unfold malloc_core. rewrite Hn.
  destruct (MMAP_THRESHOLD <=? n).
  - intros z Hz. cbn [okz] in Hz. rewrite land_mapf in Hz. destruct Hz as [Hz|Hz]; [discriminate|].
    destruct (negb _); [apply nn_bad_answer|]. rewrite Hz.
    destruct (new_region _ _ _ _) as [st1 rid]. apply nn_alloc_meta. intros st3 g. cbv beta iota.
    apply nn_ret. cbn. eauto.
  - apply nn_malloc_small_ctrl. intros st' g idx. apply nn_ret. cbn. eauto.
Qed.

Theorem cmalloc_nn cs n : size_overflows n = false -> nn (fun r => snd r <> None) (cmalloc cs n).
Proof.
  intros Hn. unfold cmalloc. eapply nn_sbind; [apply nn_malloc_core; exact Hn|].
  intros [st1 r] (g & idx & E). cbn in E. subst r. apply nn_ret. cbn. discriminate.
Qed.
