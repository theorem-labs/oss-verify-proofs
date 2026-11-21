(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint rnull {R} (P : R -> Prop) (t : M R) {struct t} : Prop :=
  match t with
  | SRet r => P r
  | SVis e k =>
      match e with
      | EBrk req => forall z, (req = 0 \/ z <> req) -> rnull P (k z)
      | EMmap _ _ _ flags => (Z.land flags MAP_FIXED =? 0) = true /\ forall z, is_err z = true -> rnull P (k z)
      | EMprotect _ _ _ => forall z, ((z =? 0) || (z =? TWO64 - ENOSYS)) = false -> rnull P (k z)
      | EUndef _ => True
      | EMunmap _ _ => False
      | EPeek _ _ _ => False
      end
  end.

Definition allnone (st : mstate) : Prop := forall sc, active st sc = None.

Section RN.
Context {R : Type} (P : R -> Prop).

Lemma rnull_guard tag c (k bail : M R) : rnull P k -> rnull P (guard tag c k bail).
Proof. intros H. unfold guard. destruct c; [exact H | exact I]. Qed.

Lemma rnull_bad_answer (bail : M R) : rnull P (bad_answer bail).
Proof. exact I. Qed.

Definition keeps_active (st st' : mstate) : Prop := forall sc, active st' sc = active st sc.
Lemma keeps_allnone st st' : keeps_active st st' -> allnone st -> allnone st'.
Proof. intros H A sc. rewrite H. apply A. Qed.
Lemma ka_refl st : keeps_active st st. Proof. intros sc; reflexivity. Qed.
Lemma ka_trans a b c : keeps_active a b -> keeps_active b c -> keeps_active a c.
Proof. intros H1 H2 sc. rewrite H2. apply H1. Qed.
Lemma ka_put_meta m r st : keeps_active st (put_meta m r st). Proof. intros sc; reflexivity. Qed.
Lemma ka_upd_meta m f st : keeps_active st (upd_meta m f st). Proof. intros sc; reflexivity. Qed.
Lemma ka_upd_region rid f st : keeps_active st (upd_region rid f st).
Proof. intros sc. unfold upd_region. destruct (get_region st rid); reflexivity. Qed.

Lemma ka_queue_free m st (k : mstate -> M R) bail :
  (forall st', keeps_active st st' -> rnull P (k st')) -> rnull P (queue LFree m st k bail).
Proof.
  intros Hk. unfold queue. apply rnull_guard, rnull_guard.
  destruct (get_head st LFree) as [head|].
  - apply Hk. intros sc. destruct (m_prev (get_meta_rec st head)); reflexivity.
  - apply Hk. intros sc. reflexivity.
Qed.

Lemma rnull_free_meta m st (k : mstate -> M R) bail :
  (forall st', keeps_active st st' -> rnull P (k st')) -> rnull P (free_meta m st k bail).
Proof.
  intros Hk. unfold free_meta. apply ka_queue_free. intros st' H. apply Hk.
  eapply ka_trans; [apply ka_put_meta | exact H].
Qed.

Lemma ka_dequeue_free m st : keeps_active st (dequeue LFree m st).
Proof.
  intros sc. unfold dequeue.
  destruct (negb (optr_eqb (m_next (get_meta_rec st m)) (Some m))).
  - destruct (m_prev (get_meta_rec st m)); destruct (m_next (get_meta_rec st m));
      match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
  - reflexivity.
Qed.

Lemma rnull_am_take st (k : mstate -> optr -> M R) bail :
  (forall st' mo, keeps_active st st' -> rnull P (k st' mo)) -> rnull P (am_take st k bail).
Proof.
  intros Hk. unfold am_take. destruct (c_avail_meta (ctx st)); [|exact I]. apply Hk. intros sc; reflexivity.
Qed.

Lemma rnull_am_carve st p (k : mstate -> optr -> M R) bail :
  (forall st' mo, keeps_active st st' -> rnull P (k st' mo)) -> rnull P (am_carve st p k bail).
Proof.
  intros Hk. unfold am_carve. apply rnull_am_take. intros st' mo H. apply Hk.
  eapply ka_trans; [|exact H]. intros sc.
  destruct (c_meta_area_tail (ctx (upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096))
             (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st))); reflexivity.
Qed.

Lemma rnull_am_finish st nu (k : mstate -> optr -> M R) bail :
  (forall st' mo, keeps_active st st' -> rnull P (k st' mo)) -> rnull P (am_finish st nu k bail).
Proof.
  intros Hk. unfold am_finish. destruct (c_avail_meta_areas (ctx st)) as [p|]; [|exact I].
  destruct (if negb (snd p mod PGSZ =? 0) then false else nu).
  - cbn [rnull]. intros z Hz. destruct (negb (mprotect_answer_ok z)); [exact I|].
    rewrite Hz. apply Hk. apply ka_refl.
  - apply rnull_am_carve. exact Hk.
Qed.

Lemma rnull_am_after_brk st nu (k : mstate -> optr -> M R) bail :
  (forall st' mo, keeps_active st st' -> rnull P (k st' mo)) -> rnull P (am_after_brk st nu k bail).
Proof.
  intros Hk. unfold am_after_brk. destruct (c_avail_meta_area_count (ctx st) =? 0).
  - cbn [rnull]. split; [reflexivity|]. intros z Hz.
    destruct (negb (mmap_answer_ok _ _ _ z)); [exact I|]. rewrite Hz. apply Hk. apply ka_refl.
  - apply rnull_am_finish. exact Hk.
Qed.

Lemma rnull_alloc_meta st (k : mstate -> optr -> M R) bail :
  (forall st' mo, keeps_active st st' -> rnull P (k st' mo)) -> rnull P (alloc_meta st k bail).
Proof.
  intros Hk. unfold alloc_meta.
  set (st0 := if c_init_done (ctx st) =? 0 then _ else st).
  assert (K0 : keeps_active st st0) by (subst st0; destruct (c_init_done (ctx st) =? 0); intros sc; reflexivity).
  assert (Hk0 : forall st' mo, keeps_active st0 st' -> rnull P (k st' mo))
    by (intros st' mo H; apply Hk; eapply ka_trans; eauto).
  clearbody st0. clear Hk K0.
  destruct (c_free_meta_head (ctx st0)) as [m|].
  { apply Hk0. apply ka_dequeue_free. }
  destruct (negb (c_avail_meta_count (ctx st0) =? 0)); [apply rnull_am_take; exact Hk0|].
  destruct ((c_avail_meta_area_count (ctx st0) =? 0) && negb match c_brk (ctx st0) with BrkDead => true | _ => false end).
  2:{ apply rnull_am_after_brk. exact Hk0. }
  destruct (c_brk (ctx st0)) as [| |rid off].
  -
    cbn [rnull]. intros cur _. destruct (brk0_answer_ok cur) eqn:E0; cbn [negb]; [|exact I].
    assert (Hnew : round_up_pg cur + 2 * PGSZ <> 0).
    { unfold brk0_answer_ok in E0. apply andb_prop in E0 as [E0 _]. apply andb_prop in E0 as [E0 _]. apply Z.ltb_lt in E0.
      unfold round_up_pg, PGSZ. assert (0 <= Z.land (- cur) (4096 - 1)) by (apply Z.land_nonneg; right; lia). lia. }
    cbn [rnull]. intros r [Hr|Hr]; [contradiction|].
    destruct (negb (brk_answer_ok cur _ r)); [exact I|].
    replace (r =? round_up_pg cur + 2 * PGSZ) with false by (symmetry; apply Z.eqb_neq; exact Hr).
    cbn [negb]. apply rnull_am_after_brk. intros st' mo H. apply Hk0. eapply ka_trans; [|exact H]. intros sc; reflexivity.
  - apply rnull_am_after_brk. exact Hk0.
  - cbn [rnull]. intros r [Hr|Hr].
    +
      destruct (negb (brk_answer_ok _ _ r)); [exact I|].
      destruct (r =? conc st0 (rid, off) + PGSZ) eqn:E.
      * cbn [negb]. destruct (negb (brk_pages_ok st0 _ PGSZ)); [exact I|].
        apply rnull_am_after_brk. intros st' mo H. apply Hk0. eapply ka_trans; [|exact H].
        eapply ka_trans; [apply ka_upd_region|]. intros sc; reflexivity.
      * cbn [negb]. apply rnull_am_after_brk. intros st' mo H. apply Hk0. eapply ka_trans; [|exact H]. intros sc; reflexivity.
    + destruct (negb (brk_answer_ok _ _ r)); [exact I|].
      replace (r =? conc st0 (rid, off) + PGSZ) with false by (symmetry; apply Z.eqb_neq; exact Hr).
      cbn [negb]. apply rnull_am_after_brk. intros st' mo H. apply Hk0. eapply ka_trans; [|exact H]. intros sc; reflexivity.
Qed.

Lemma rnull_try_avail sc st (k : mstate -> Z -> M R) bail :
  allnone st -> rnull P (k st 0) -> rnull P (try_avail sc st k bail).
Proof. intros A Hk. unfold try_avail. rewrite (A sc). exact Hk. Qed.

Lemma ka_step_seq st : keeps_active st (step_seq st).
Proof. intros sc. unfold step_seq. destruct (c_seq (ctx st) =? 255); reflexivity. Qed.
Lemma ka_account_bounce sc0 st : keeps_active st (account_bounce sc0 st).
Proof.
  intros sc. unfold account_bounce. destruct (sc_in_seq_range sc0); [|reflexivity].
  destruct (negb (unmap_seq st (sc0 - 7) =? 0) && (c_seq (ctx st) - unmap_seq st (sc0 - 7) <? 10)); [|reflexivity].
  destruct (bounces st (sc0 - 7) + 1 <? 100); reflexivity.
Qed.

Lemma rnull_alloc_group lay (asr : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R) st sc req
    (k : mstate -> optr -> M R) bail :
  (forall st1 j rq (k1 : mstate -> Z -> M R) bl, allnone st1 ->
     (forall st2, allnone st2 -> rnull P (k1 st2 (-1))) -> rnull P (asr st1 j rq k1 bl)) ->
  allnone st ->
  (forall st', allnone st' -> rnull P (k st' None)) ->
  rnull P (alloc_group R lay asr st sc req k bail).
Proof.
  intros Hasr A Hk. unfold alloc_group. apply rnull_alloc_meta. intros st1 mo K1.
  pose proof (keeps_allnone _ _ K1 A) as A1.
  destruct mo as [m|]; [|apply Hk; exact A1].
  match goal with |- context [if ?c then _ else _] => idtac end.
  set (cnt0 := if sc <? 9 then _ else _).
  set (cnt1 := if (cnt0 =? 1) && _ then 2 else cnt0).
  destruct (PGSZ / 2 <? UNIT * size_class sc * cnt1 + UNIT).
  -
    set (st2 := step_seq (account_bounce sc st1)).
    assert (A2 : allnone st2).
    { eapply keeps_allnone; [|exact A1]. eapply ka_trans; [apply ka_account_bounce | apply ka_step_seq]. }
    match goal with |- rnull P (let '(c, nd) := ?X in _) => destruct X as [cnt needed] end.
    cbn [rnull]. split; [reflexivity|]. intros z Hz.
    destruct (negb (mmap_answer_ok _ _ needed z)); [exact I|]. rewrite Hz.
    apply rnull_free_meta. intros st3 K3. apply Hk. eapply keeps_allnone; [exact K3 | exact A2].
  -
    apply Hasr; [exact A1|]. intros st2 A2.
    replace (-1 <? 0) with true by reflexivity.
    apply rnull_free_meta. intros st3 K3. apply Hk. eapply keeps_allnone; [exact K3 | exact A2].
Qed.

Lemma rnull_alloc_slot lay fuel : forall st sc req (k : mstate -> Z -> M R) bail,
  allnone st -> (forall st', allnone st' -> rnull P (k st' (-1))) -> rnull P (alloc_slot lay fuel st sc req k bail).
Proof.
  induction fuel as [|f IH]; intros st sc req k bail A Hk; cbn [alloc_slot]; [exact I|].
  apply rnull_try_avail; [exact A|]. cbn [Z.eqb negb].
  apply rnull_alloc_group; [|exact A|].
  - intros st1 j rq k1 bl A1 Hk1. apply IH; assumption.
  - intros st' A'. apply Hk. exact A'.
Qed.

Lemma rnull_malloc_small_ctrl lay st n (k : mstate -> option (aptr * Z) -> M R) bail :
  allnone st -> (forall st', rnull P (k st' None)) -> rnull P (malloc_small_ctrl lay st n k bail).
Proof.
  intros A Hk. unfold malloc_small_ctrl. unfold allnone in A. rewrite !A. cbv beta iota zeta.
  change (negb (lowbit 0 =? 0)) with false. cbv beta iota.
  apply rnull_alloc_slot; [exact A|]. intros st' _. replace (-1 <? 0) with true by reflexivity. apply Hk.
Qed.

End RN.

Lemma rnull_sbind {R S} (P1 : R -> Prop) (P : S -> Prop) (t : M R) (f : R -> M S) :
  rnull P1 t -> (forall r, P1 r -> rnull P (f r)) -> rnull P (sbind t f).
Proof.
  revert t. fix IH 1. intros [r|e k]; cbn; intros H Hf.
  - apply Hf. exact H.
  - destruct e; try exact H; try exact I.
    + intros z Hz. apply IH; [apply H; exact Hz | exact Hf].
    + destruct H as [H1 H2]. split; [exact H1|]. intros z Hz. apply IH; [apply H2; exact Hz | exact Hf].
    + intros z Hz. apply IH; [apply H; exact Hz | exact Hf].
Qed.

Lemma rnull_malloc_core lay st n : allnone st -> rnull (fun r => snd r = None) (malloc_core lay st n).
Proof.
  intros A. unfold malloc_core. destruct (size_overflows n); [reflexivity|].
  destruct (MMAP_THRESHOLD <=? n).
  - cbn [rnull]. split; [reflexivity|]. intros z Hz.
    destruct (negb (mmap_answer_ok _ _ _ z)); [exact I|]. rewrite Hz. reflexivity.
  - apply rnull_malloc_small_ctrl; [exact A|]. intros st'. reflexivity.
Qed.

Theorem cmalloc_rnull cs n : allnone cs -> rnull (fun r => snd r = None) (cmalloc cs n).
Proof.
  intros A. unfold cmalloc. eapply rnull_sbind; [apply (rnull_malloc_core lay_none cs n A)|].
  intros [st1 r] Hr. cbn in Hr. subst r. reflexivity.
Qed.
