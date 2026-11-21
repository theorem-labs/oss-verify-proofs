(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Malloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint gsome {R} (P : R -> Prop) (t : M R) {struct t} : Prop :=
  match t with
  | SRet r => P r
  | SVis e k =>
      match e with
      | EBrk req => forall z, (req = 0 \/ z <> req) -> gsome P (k z)
      | EMmap _ _ _ flags => (Z.land flags MAP_FIXED =? 0) = true /\ forall z, is_err z = false -> gsome P (k z)
      | EMprotect _ _ _ => gsome P (k 0)
      | EUndef _ => True
      | EMunmap _ _ => False
      | EPeek _ _ _ => False
      end
  end.

Lemma gsome_sbind {R S} (P1 : R -> Prop) (P : S -> Prop) (t : M R) (f : R -> M S) :
  gsome P1 t -> (forall r, P1 r -> gsome P (f r)) -> gsome P (sbind t f).
Proof.
  revert t. fix IH 1. intros [r|e k]; cbn; intros H Hf.
  - apply Hf. exact H.
  - destruct e; try exact H; try exact I.
    + intros z Hz. apply IH; [apply H; exact Hz | exact Hf].
    + destruct H as [H1 H2]. split; [exact H1|]. intros z Hz. apply IH; [apply H2; exact Hz | exact Hf].
    + apply IH; [exact H | exact Hf].
Qed.

Section Walk.
Context {R : Type} (P : R -> Prop).

Lemma gs_guard tag c (k bail : M R) : gsome P k -> gsome P (guard tag c k bail).
Proof. intros H. unfold guard. destruct c; [exact H | exact I]. Qed.

Lemma gs_queue h m st (k : mstate -> M R) bail : (forall st', gsome P (k st')) -> gsome P (queue h m st k bail).
Proof. intros Hk. unfold queue. apply gs_guard. apply gs_guard. destruct (get_head st h); apply Hk. Qed.

Lemma gs_activate_group m st (k : mstate -> Z -> M R) bail :
  (forall st' z, gsome P (k st' z)) -> gsome P (activate_group m st k bail).
Proof. intros Hk. unfold activate_group. apply gs_guard. apply Hk. Qed.

Lemma gs_am_take st (k : mstate -> optr -> M R) bail :
  (forall st' m, gsome P (k st' (Some m))) -> gsome P (am_take st k bail).
Proof. intros Hk. unfold am_take. destruct (c_avail_meta (ctx st)); [apply Hk | exact I]. Qed.

Lemma gs_am_carve st p (k : mstate -> optr -> M R) bail :
  (forall st' m, gsome P (k st' (Some m))) -> gsome P (am_carve st p k bail).
Proof. intros Hk. unfold am_carve. apply gs_am_take. exact Hk. Qed.

Lemma gs_am_finish st nu (k : mstate -> optr -> M R) bail :
  (forall st' m, gsome P (k st' (Some m))) -> gsome P (am_finish st nu k bail).
Proof.
  intros Hk. unfold am_finish. destruct (c_avail_meta_areas (ctx st)) as [p|]; [|exact I].
  match goal with |- gsome P (if ?c then _ else _) => destruct c end; [|apply gs_am_carve; exact Hk].
  cbn [gsome].
  replace (negb (mprotect_answer_ok 0)) with false by reflexivity.
  replace ((0 =? 0) || (0 =? TWO64 - ENOSYS)) with true by reflexivity. cbn iota. apply gs_am_carve. exact Hk.
Qed.

Lemma gs_am_after_brk st nu (k : mstate -> optr -> M R) bail :
  (forall st' m, gsome P (k st' (Some m))) -> gsome P (am_after_brk st nu k bail).
Proof.
  intros Hk. unfold am_after_brk. destruct (c_avail_meta_area_count (ctx st) =? 0); [|apply gs_am_finish; exact Hk].
  cbn [gsome]. split; [reflexivity|]. intros z Hz.
  destruct (negb _); [exact I|]. rewrite Hz.
  destruct (new_region _ _ _ _) as [st1 rid]. apply gs_am_finish. exact Hk.
Qed.

Lemma gs_alloc_meta st (k : mstate -> optr -> M R) bail :
  (forall st' m, gsome P (k st' (Some m))) -> gsome P (alloc_meta st k bail).
Proof.
  intros Hk. unfold alloc_meta.
  set (st0 := if c_init_done (ctx st) =? 0 then _ else _). clearbody st0.
  destruct (c_free_meta_head (ctx st0)); [apply Hk|].
  destruct (negb (c_avail_meta_count (ctx st0) =? 0)); [apply gs_am_take; exact Hk|].
  match goal with |- gsome P (if ?c then _ else _) => destruct c end; [|apply gs_am_after_brk; exact Hk].
  destruct (c_brk (ctx st0)) as [| |rid off].
  - cbn [gsome]. intros cur _. destruct (brk0_answer_ok cur) eqn:E0; cbn [negb]; [|exact I].
    assert (Hnew : round_up_pg cur + 2 * PGSZ <> 0).
    { unfold brk0_answer_ok in E0. apply andb_prop in E0 as [E0 _]. apply andb_prop in E0 as [E0 _]. apply Z.ltb_lt in E0.
      unfold round_up_pg, PGSZ. assert (0 <= Z.land (- cur) (4096 - 1)) by (apply Z.land_nonneg; right; lia). lia. }
    cbn [gsome]. intros r [Hr|Hr]; [contradiction|].
    destruct (negb (brk_answer_ok cur _ r)); [exact I|].
    replace (r =? round_up_pg cur + 2 * PGSZ) with false by (symmetry; apply Z.eqb_neq; exact Hr).
    cbn [negb]. apply gs_am_after_brk. exact Hk.
  - apply gs_am_after_brk; exact Hk.
  - cbn [gsome]. intros r Hr. destruct (negb (brk_answer_ok _ _ r)); [exact I|].
    destruct (negb (r =? _)); [apply gs_am_after_brk; exact Hk|].
    destruct (negb (brk_pages_ok _ _ _)); [exact I|].
    apply gs_am_after_brk; exact Hk.
Qed.

Lemma gs_ta_fin st m mask (k : mstate -> Z -> M R) : (forall st' z, gsome P (k st' z)) -> gsome P (ta_fin st m mask k).
Proof. intros Hk. unfold ta_fin. apply Hk. Qed.

Lemma gs_try_avail sc st (k : mstate -> Z -> M R) bail :
  (forall st' z, gsome P (k st' z)) -> gsome P (try_avail sc st k bail).
Proof.
  intros Hk. unfold try_avail. destruct (active st sc) as [m|]; [|apply Hk].
  destruct (negb (m_avail (get_meta_rec st m) =? 0)); [apply gs_ta_fin; exact Hk|].
  match goal with |- gsome P (match ?s with Some _ => _ | None => _ end) => destruct s as [[st1 m1]|] end.
  2:{ destruct (m_freed _ =? 0); [apply Hk | exact I]. }
  match goal with |- gsome P (let (a, b) := ?x in _) => destruct x as [[st2 m2] mask] end.
  match goal with |- gsome P (let (a, b) := ?x in _) => destruct x as [st3 m3] end.
  apply gs_activate_group. intros st4 z. apply gs_guard. apply gs_ta_fin. exact Hk.
Qed.

Lemma gs_ag_tail lay st sc m p cnt ai (k : mstate -> optr -> M R) :
  (forall st', gsome P (k st' (Some m))) -> gsome P (ag_tail lay st sc m p cnt ai k).
Proof. intros Hk. unfold ag_tail. apply Hk. Qed.

Lemma gs_alloc_group lay (asr : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R) st sc req (k : mstate -> optr -> M R) bail :
  (forall st1 sc1 req1 (k1 : mstate -> Z -> M R) bail1, (forall st' idx, 0 <= idx -> gsome P (k1 st' idx)) -> gsome P (asr st1 sc1 req1 k1 bail1)) ->
  (forall st' m, gsome P (k st' (Some m))) -> gsome P (alloc_group R lay asr st sc req k bail).
Proof.
  intros Hasr Hk. unfold alloc_group. apply gs_alloc_meta. intros st1 m. cbv beta iota.
  match goal with |- gsome P (if ?c then _ else _) => destruct c end.
  - match goal with |- gsome P (let (a, b) := ?x in _) => destruct x as [cnt needed] end.
    cbn [gsome]. split; [reflexivity|]. intros z Hz.
    destruct (negb _); [exact I|]. rewrite Hz.
    destruct (new_region _ _ _ _) as [st2 rid]. apply gs_ag_tail. intros st'. apply Hk.
  - apply Hasr. intros st' idx Hidx. replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (active st' _) as [g|]; [|exact I]. apply gs_ag_tail. intros st''. apply Hk.
Qed.

Lemma ctz32_nonneg first : 0 <= ctz32 first.
Proof. unfold ctz32. apply Z.log2_nonneg. Qed.

Lemma gs_alloc_slot lay fuel : forall st sc req (k : mstate -> Z -> M R) bail,
  (forall st' idx, 0 <= idx -> gsome P (k st' idx)) -> gsome P (alloc_slot lay fuel st sc req k bail).
Proof.
  induction fuel as [|f IH]; intros st sc req k bail Hk; cbn [alloc_slot]; [exact I|].
  apply gs_try_avail. intros st1 first. destruct (negb (first =? 0)); [apply Hk; apply ctz32_nonneg|].
  apply gs_alloc_group; [exact IH|]. intros st2 g. cbv beta iota. apply gs_queue. intros st4. apply Hk. lia.
Qed.

Lemma gs_malloc_small_ctrl lay st n (k : mstate -> option (aptr * Z) -> M R) bail :
  (forall st' g idx, gsome P (k st' (Some (g, idx)))) -> gsome P (malloc_small_ctrl lay st n k bail).
Proof.
  intros Hk. unfold malloc_small_ctrl.
  match goal with |- gsome P (match ?g with Some _ => _ | None => _ end) => destruct g as [gp|] end.
  - destruct (negb _); [apply Hk|].
    apply gs_alloc_slot. intros st' idx Hidx. replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (active st' _); [apply Hk | exact I].
  - cbn iota. apply gs_alloc_slot. intros st' idx Hidx. replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (active st' _); [apply Hk | exact I].
Qed.

End Walk.

Lemma gs_malloc_core lay st n : size_overflows n = false ->
  gsome (fun r => exists g idx, snd r = Some (g, idx)) (malloc_core lay st n).
Proof.
  intros Hn. unfold malloc_core. rewrite Hn.
  destruct (MMAP_THRESHOLD <=? n).
  - cbn [gsome]. split; [reflexivity|]. intros z Hz.
    destruct (negb _); [exact I|]. rewrite Hz.
    destruct (new_region _ _ _ _) as [st1 rid]. apply gs_alloc_meta. intros st3 g. cbv beta iota.
    cbn. eauto.
  - apply gs_malloc_small_ctrl. intros st' g idx. cbn. eauto.
Qed.

Theorem cmalloc_gsome cs n : size_overflows n = false -> gsome (fun r => snd r <> None) (cmalloc cs n).
Proof.
  intros Hn. unfold cmalloc. eapply gsome_sbind; [apply gs_malloc_core; exact Hn|].
  intros [st1 r] (g & idx & E). cbn in E. subst r. cbn. discriminate.
Qed.
