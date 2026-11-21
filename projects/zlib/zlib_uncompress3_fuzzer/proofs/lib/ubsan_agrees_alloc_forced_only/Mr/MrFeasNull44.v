(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Mr Require Import MrFeasNull MrFeasSome1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition none44 (st : mstate) : Prop := forall sc, sc <> 44 -> active st sc = None.
Definition full44 (st : mstate) : Prop :=
  match active st 44 with
  | None => True
  | Some m => m_avail (get_meta_rec st m) = 0 /\ m_freed (get_meta_rec st m) = 0 /\ m_next (get_meta_rec st m) = Some m
  end.

Lemma keeps_none44 st st' : keeps_active st st' -> none44 st -> none44 st'.
Proof. intros H A sc Hsc. rewrite H. apply A. exact Hsc. Qed.

Lemma small_class_not44 : forall x, 0 <= x <= 2044 -> size_to_class x <> 44.
Proof.
  assert (H : forallb (fun i => negb (size_to_class (Z.of_nat i) =? 44)) (seq 0 2045) = true) by (vm_compute; reflexivity).
  intros x Hx. rewrite forallb_forall in H. specialize (H (Z.to_nat x)).
  rewrite Z2Nat.id in H by lia. intros E. rewrite E in H. 
  assert (Hin : In (Z.to_nat x) (seq 0 2045)) by (apply in_seq; lia).
  specialize (H Hin). discriminate.
Qed.

Section RN44.
Context {R : Type} (P : R -> Prop).

Lemma rnull44_try_avail sc st (k : mstate -> Z -> M R) bail :
  none44 st -> sc <> 44 -> rnull P (k st 0) -> rnull P (try_avail sc st k bail).
Proof. intros A Hsc Hk. unfold try_avail. rewrite (A sc Hsc). exact Hk. Qed.

Lemma rnull44_alloc_group lay (asr : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R) st sc req
    (k : mstate -> optr -> M R) bail :
  (forall st1 j rq (k1 : mstate -> Z -> M R) bl, none44 st1 -> j <> 44 ->
     (forall st2, none44 st2 -> rnull P (k1 st2 (-1))) -> rnull P (asr st1 j rq k1 bl)) ->
  none44 st ->
  (forall st', none44 st' -> rnull P (k st' None)) ->
  rnull P (alloc_group R lay asr st sc req k bail).
Proof.
  intros Hasr A Hk. unfold alloc_group. apply rnull_alloc_meta. intros st1 mo K1.
  pose proof (keeps_none44 _ _ K1 A) as A1.
  destruct mo as [m|]; [|apply Hk; exact A1]. cbv beta iota.
  set (size := UNIT * size_class sc) in *.
  assert (Hsz : 0 <= size <= 131056) by (subst size; pose proof (size_class_bounds sc); unfold UNIT; lia).
  set (c0 := if sc <? 9 then small_cnt_pick sc (usage st1 sc)
             else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st1 sc)) size) in *.
  assert (Hc0 : 0 <= c0 <= 32).
  { subst c0. destruct (sc <? 9); [apply small_cnt_pick_bounds | apply halve_big_bounds, halve_even_bounds, med_cnt_bounds]. }
  set (c1 := if (c0 =? 1) && (size * c0 + UNIT <=? PGSZ / 2) then 2 else c0) in *.
  assert (Hc1 : 0 <= c1 <= 32) by (subst c1; destruct ((c0 =? 1) && (size * c0 + UNIT <=? PGSZ / 2)); lia).
  clearbody c1. clear Hc0. clearbody c0 size.
  destruct (PGSZ / 2 <? size * c1 + UNIT) eqn:Ebr.
  - set (st2 := step_seq (account_bounce sc st1)).
    assert (A2 : none44 st2).
    { eapply keeps_none44; [|exact A1]. eapply ka_trans; [apply ka_account_bounce | apply ka_step_seq]. }
    match goal with |- rnull P (let '(c, nd) := ?X in _) => destruct X as [cnt needed] end.
    cbn [rnull]. split; [reflexivity|]. intros z Hz.
    destruct (negb (mmap_answer_ok _ _ needed z)); [exact I|]. rewrite Hz.
    apply rnull_free_meta. intros st3 K3. apply Hk. eapply keeps_none44; [exact K3 | exact A2].
  - apply Z.ltb_ge in Ebr. change (PGSZ / 2) with 2048 in Ebr.
    apply Hasr; [exact A1 | apply small_class_not44; unfold UNIT, IB in *; nia |].
    intros st2 A2. replace (-1 <? 0) with true by reflexivity.
    apply rnull_free_meta. intros st3 K3. apply Hk. eapply keeps_none44; [exact K3 | exact A2].
Qed.

Lemma rnull44_alloc_slot lay fuel : forall st sc req (k : mstate -> Z -> M R) bail,
  none44 st -> sc <> 44 -> (forall st', none44 st' -> rnull P (k st' (-1))) -> rnull P (alloc_slot lay fuel st sc req k bail).
Proof.
  induction fuel as [|f IH]; intros st sc req k bail A Hsc Hk; cbn [alloc_slot]; [exact I|].
  apply rnull44_try_avail; [exact A | exact Hsc|]. cbn [Z.eqb negb].
  apply rnull44_alloc_group; [|exact A|].
  - intros st1 j rq k1 bl A1 Hj Hk1. apply IH; assumption.
  - intros st' A'. apply Hk. exact A'.
Qed.

End RN44.

Lemma aptr_eqb_refl (a : aptr) : aptr_eqb a a = true.
Proof. unfold aptr_eqb. rewrite N.eqb_refl, Z.eqb_refl. reflexivity. Qed.

Lemma active_dequeue_singleton sc m st sc' :
  m_next (get_meta_rec st m) = Some m ->
  active (dequeue (LActive sc) m st) sc' = if sc' =? sc then None else active st sc'.
Proof.
  intros Hn. unfold dequeue. rewrite Hn. cbn [optr_eqb]. rewrite aptr_eqb_refl. cbn [negb].
  change (active (upd_meta m (fun r => m_set_prev None (m_set_next None r)) (set_head (LActive sc) None st)) sc')
    with ((delete sc (c_active (ctx st))) !! sc').
  destruct (Z.eqb_spec sc' sc) as [->|NE].
  - apply lookup_delete_eq.
  - rewrite lookup_delete_ne by congruence. reflexivity.
Qed.

Lemma lor1_not44 x : Z.lor x 1 <> 44.
Proof. intros E. assert (H : Z.testbit (Z.lor x 1) 0 = true) by (rewrite Z.lor_spec; cbn; apply orb_true_r). rewrite E in H. discriminate. Qed.

Section Top44.
Context {R : Type} (P : R -> Prop).

Lemma rnull44_alloc_slot44 lay fuel : forall st req (k : mstate -> Z -> M R) bail,
  none44 st -> full44 st -> (forall st', rnull P (k st' (-1))) -> rnull P (alloc_slot lay fuel st 44 req k bail).
Proof.
  destruct fuel as [|f]; intros st req k bail A F Hk; cbn [alloc_slot]; [exact I|].
  unfold full44 in F. unfold try_avail. destruct (active st 44) as [m|] eqn:E44.
  - destruct F as (Hav & Hfr & Hnx). rewrite Hav. cbn [Z.eqb negb]. rewrite Hfr. cbn [Z.eqb].
    rewrite (active_dequeue_singleton 44 m st 44 Hnx). rewrite Z.eqb_refl. cbn [Z.eqb negb].
    assert (AN : allnone (dequeue (LActive 44) m st)).
    { intros sc. rewrite (active_dequeue_singleton 44 m st sc Hnx). destruct (Z.eqb_spec sc 44); [reflexivity | apply A; assumption]. }
    apply (rnull_alloc_group P lay (alloc_slot lay f)); [|exact AN|].
    + intros st1 j rq k1 bl A1 Hk1. apply rnull_alloc_slot; assumption.
    + intros st' _. apply Hk.
  - cbn [Z.eqb negb].
    assert (AN : allnone st) by (intros sc; destruct (Z.eq_dec sc 44) as [->|NE]; [exact E44 | apply A; exact NE]).
    apply (rnull_alloc_group P lay (alloc_slot lay f)); [|exact AN|].
    + intros st1 j rq k1 bl A1 Hk1. apply rnull_alloc_slot; assumption.
    + intros st' _. apply Hk.
Qed.

Lemma rnull44_malloc_small_ctrl lay st n (k : mstate -> option (aptr * Z) -> M R) bail :
  none44 st -> full44 st -> (forall st', rnull P (k st' None)) -> rnull P (malloc_small_ctrl lay st n k bail).
Proof.
  intros A F Hk. unfold malloc_small_ctrl.
  destruct (Z.eq_dec (size_to_class n) 44) as [E|NE].
  - rewrite E.
    assert (Hgo : forall sc', sc' = 44 ->
              rnull P (alloc_slot lay FUEL st sc' n
                    (fun st1 idx => if idx <? 0 then k st1 None
                                    else match active st1 sc' with Some gp => k st1 (Some (gp, idx)) | None => SVis (EUndef UBadPtr) (fun _ => bail) end) bail)).
    { intros sc' ->. apply rnull44_alloc_slot44; [exact A | exact F|]. intros st'. replace (-1 <? 0) with true by reflexivity. apply Hk. }
    unfold full44 in F. destruct (active st 44) as [m|] eqn:E44.
    + cbv beta iota. rewrite E44. destruct F as (Hav & _). rewrite Hav. cbn [lowbit Z.land Z.eqb negb Z.opp].
      change (negb (lowbit 0 =? 0)) with false. cbv iota. apply Hgo. reflexivity.
    + change ((4 <=? 44) && (44 <? 32) && negb (44 =? 6) && Z.even 44 && (usage st 44 =? 0)) with false. cbv iota.
      rewrite E44. change (negb (lowbit 0 =? 0)) with false. cbv iota. apply Hgo. reflexivity.
  - rewrite (A _ NE). cbv beta iota.
    match goal with |- context [alloc_slot lay FUEL st ?x n] => remember x as sc eqn:Esc end.
    assert (Hsc : sc <> 44).
    { subst sc. match goal with |- (if ?c then _ else _) <> 44 => destruct c end; [|exact NE].
      cbv zeta. match goal with |- (if ?c then _ else _) <> 44 => destruct c end; [apply lor1_not44 | exact NE]. }
    clear Esc. rewrite (A _ Hsc). change (negb (lowbit 0 =? 0)) with false. cbv iota.
    apply rnull44_alloc_slot; [exact A | exact Hsc|]. intros st' _. replace (-1 <? 0) with true by reflexivity. apply Hk.
Qed.

End Top44.

Lemma rnull44_malloc_core lay st n : none44 st -> full44 st -> rnull (fun r => snd r = None) (malloc_core lay st n).
Proof.
  intros A F. unfold malloc_core. destruct (size_overflows n); [reflexivity|].
  destruct (MMAP_THRESHOLD <=? n).
  - cbn [rnull]. split; [reflexivity|]. intros z Hz.
    destruct (negb (mmap_answer_ok _ _ _ z)); [exact I|]. rewrite Hz. reflexivity.
  - apply rnull44_malloc_small_ctrl; [exact A | exact F|]. intros st'. reflexivity.
Qed.

Theorem cmalloc_rnull44 cs n : none44 cs -> full44 cs -> rnull (fun r => snd r = None) (cmalloc cs n).
Proof.
  intros A F. unfold cmalloc. eapply rnull_sbind; [apply (rnull44_malloc_core lay_none cs n A F)|].
  intros [st1 r] Hr. cbn in Hr. subst r. reflexivity.
Qed.
