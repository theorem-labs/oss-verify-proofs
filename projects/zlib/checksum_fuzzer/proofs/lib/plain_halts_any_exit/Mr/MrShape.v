(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Mr Require Import MrFeasNull MrFeasSome1 MrTall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Theorem cmalloc_rnull_big cs n : MMAP_THRESHOLD <= n -> rnull (fun r => snd r = None) (cmalloc cs n).
Proof.
  intros Hn. unfold cmalloc. eapply rnull_sbind with (P1 := fun r => snd r = None).
  - unfold malloc_core. destruct (size_overflows n); [reflexivity|].
    replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; exact Hn).
    cbn [rnull]. split; [reflexivity|]. intros z Hz.
    destruct (negb (mmap_answer_ok _ _ _ z)); [exact I|]. rewrite Hz. reflexivity.
  - intros [st1 r] Hr. cbn in Hr. subst r. reflexivity.
Qed.

Definition cnt (st : mstate) : Z := c_avail_meta_count (ctx st).
Definition REL (st st' : mstate) : Prop := keeps_active st st' /\ (1 <= cnt st -> cnt st - 1 <= cnt st').

Lemma REL_refl st : REL st st. Proof. split; [apply ka_refl | lia]. Qed.
Lemma REL_kc a b c : REL a b -> keeps_active b c -> cnt c = cnt b -> REL a c.
Proof. intros [H1 H2] H3 H4. split; [eapply ka_trans; eauto | rewrite H4; exact H2]. Qed.
Lemma kc_REL a b c : keeps_active a b -> cnt b = cnt a -> REL b c -> REL a c.
Proof. intros H1 H2 [H3 H4]. split; [eapply ka_trans; eauto | rewrite <- H2; exact H4]. Qed.

Section U.
Context {R : Type} (phi : R -> Prop).

Lemma uall_guard tag c (k bail : M R) : uall phi k -> uall phi bail -> uall phi (guard tag c k bail).
Proof. intros H Hb. unfold guard. destruct c; [exact H | exact I]. Qed.

Lemma uall_bad_answer (bail : M R) : uall phi bail -> uall phi (bad_answer bail).
Proof. intros _. exact I. Qed.

Lemma uall_am_take st (k : mstate -> optr -> M R) bail :
  (forall st' go, keeps_active st st' -> cnt st' = cnt st - 1 -> uall phi (k st' go)) -> uall phi bail ->
  uall phi (am_take st k bail).
Proof.
  intros Hk Hb. unfold am_take. destruct (c_avail_meta (ctx st)); [|exact I].
  apply Hk; [intros sc; reflexivity | reflexivity].
Qed.

Lemma uall_am_carve st p (k : mstate -> optr -> M R) bail :
  (forall st' go, keeps_active st st' -> uall phi (k st' go)) -> uall phi bail -> uall phi (am_carve st p k bail).
Proof.
  intros Hk Hb. unfold am_carve. apply uall_am_take; [|exact Hb]. intros st' go H _. apply Hk.
  eapply ka_trans; [|exact H]. intros sc.
  destruct (c_meta_area_tail (ctx (upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096))
             (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st))); reflexivity.
Qed.

Lemma uall_am_finish st nu (k : mstate -> optr -> M R) bail :
  (forall st' go, keeps_active st st' -> uall phi (k st' go)) -> uall phi bail -> uall phi (am_finish st nu k bail).
Proof.
  intros Hk Hb. unfold am_finish. destruct (c_avail_meta_areas (ctx st)) as [p|]; [|exact I].
  destruct (if negb (snd p mod PGSZ =? 0) then false else nu).
  - cbn [uall]. intros z. destruct (negb (mprotect_answer_ok z)); [apply uall_bad_answer; exact Hb|].
    destruct ((z =? 0) || (z =? TWO64 - ENOSYS)); [apply uall_am_carve; assumption | apply Hk; apply ka_refl].
  - apply uall_am_carve; assumption.
Qed.

Lemma ka_new_region kd base len st : keeps_active st (fst (new_region kd base len st)).
Proof. intros sc. reflexivity. Qed.

Lemma uall_am_after_brk st nu (k : mstate -> optr -> M R) bail :
  (forall st' go, keeps_active st st' -> uall phi (k st' go)) -> uall phi bail -> uall phi (am_after_brk st nu k bail).
Proof.
  intros Hk Hb. unfold am_after_brk. destruct (c_avail_meta_area_count (ctx st) =? 0).
  - cbn [uall]. intros z. destruct (negb (mmap_answer_ok _ _ _ z)); [apply uall_bad_answer; exact Hb|].
    destruct (is_err z); [apply Hk; apply ka_refl|].
    destruct (new_region RKMeta z _ st) as [st1 rid] eqn:E.
    apply uall_am_finish; [|exact Hb]. intros st' go H. apply Hk. eapply ka_trans; [|exact H].
    pose proof (ka_new_region RKMeta z (Z.shiftl 2 (c_meta_alloc_shift (ctx st)) * PGSZ) st) as K. rewrite E in K. cbn [fst] in K.
    eapply ka_trans; [exact K|]. intros sc; reflexivity.
  - apply uall_am_finish; assumption.
Qed.

Lemma uall_alloc_meta st (k : mstate -> optr -> M R) bail :
  (forall st' go, REL st st' -> uall phi (k st' go)) -> uall phi bail -> uall phi (alloc_meta st k bail).
Proof.
  intros Hk Hb. unfold alloc_meta.
  set (st0 := if c_init_done (ctx st) =? 0 then _ else st).
  assert (K0 : keeps_active st st0) by (subst st0; destruct (c_init_done (ctx st) =? 0); intros sc; reflexivity).
  assert (C0 : cnt st0 = cnt st) by (subst st0; destruct (c_init_done (ctx st) =? 0); reflexivity).
  assert (Hk0 : forall st' go, REL st0 st' -> uall phi (k st' go)).
  { intros st' go H. apply Hk. eapply kc_REL; eauto. }
  clearbody st0. clear Hk K0 C0.
  destruct (c_free_meta_head (ctx st0)) as [m|].
  { apply Hk0. split; [apply ka_dequeue_free|]. intros _. unfold cnt. rewrite (kc_dequeue LFree m st0). lia. }
  destruct (c_avail_meta_count (ctx st0) =? 0) eqn:EC; cbn [negb].
  2:{ apply uall_am_take; [|exact Hb]. intros st' go H C. apply Hk0. split; [exact H | intros _; lia]. }
  apply Z.eqb_eq in EC.
  assert (HkA : forall st' go, keeps_active st0 st' -> uall phi (k st' go)).
  { intros st' go H. apply Hk0. split; [exact H | unfold cnt; lia]. }
  clear Hk0.
  destruct ((c_avail_meta_area_count (ctx st0) =? 0) && negb match c_brk (ctx st0) with BrkDead => true | _ => false end).
  2:{ apply uall_am_after_brk; assumption. }
  destruct (c_brk (ctx st0)) as [| |rid off].
  - cbn [uall]. intros cur. destruct (negb (brk0_answer_ok cur)); [apply uall_bad_answer; exact Hb|].
    cbn [uall]. intros r. destruct (negb (brk_answer_ok cur _ r)); [apply uall_bad_answer; exact Hb|].
    destruct (negb (r =? round_up_pg cur + 2 * PGSZ)).
    { apply uall_am_after_brk; [|exact Hb]. intros st' go H. apply HkA. eapply ka_trans; [|exact H]. intros sc; reflexivity. }
    destruct (negb (brk_pages_ok st0 _ _)); [apply uall_bad_answer; exact Hb|].
    cbn [uall]. intros rg. destruct (negb (mmap_fixed_answer_ok _ rg)); [apply uall_bad_answer; exact Hb|].
    destruct (new_region RKBrk _ _ st0) as [st1 rid] eqn:E.
    apply uall_am_after_brk; [|exact Hb]. intros st' go H. apply HkA. eapply ka_trans; [|exact H].
    pose proof (ka_new_region RKBrk (round_up_pg cur) (2 * PGSZ) st0) as K. rewrite E in K. cbn [fst] in K.
    eapply ka_trans; [exact K|]. intros sc; reflexivity.
  - apply uall_am_after_brk; assumption.
  - cbn [uall]. intros r. destruct (negb (brk_answer_ok _ _ r)); [apply uall_bad_answer; exact Hb|].
    destruct (negb (r =? conc st0 (rid, off) + PGSZ)).
    { apply uall_am_after_brk; [|exact Hb]. intros st' go H. apply HkA. eapply ka_trans; [|exact H]. intros sc; reflexivity. }
    destruct (negb (brk_pages_ok st0 _ _)); [apply uall_bad_answer; exact Hb|].
    apply uall_am_after_brk; [|exact Hb]. intros st' go H. apply HkA. eapply ka_trans; [|exact H].
    eapply ka_trans; [apply ka_upd_region|]. intros sc; reflexivity.
Qed.

End U.

Lemma uall_sbind {R S} (P1 : R -> Prop) (P : S -> Prop) (t : M R) (f : R -> M S) :
  uall P1 t -> (forall r, P1 r -> uall P (f r)) -> uall P (sbind t f).
Proof.
  induction t as [r | e k IH]; cbn; intros H Hf; [apply Hf; exact H|].
  destruct e; try exact I; intros z; (apply IH; [apply H | exact Hf]).
Qed.

Lemma cnt_step_seq st : cnt (step_seq st) = cnt st.
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); reflexivity. Qed.

Lemma uall_malloc_core_big st n : MMAP_THRESHOLD <= n -> uall (fun r => REL st (fst r)) (malloc_core lay_none st n).
Proof.
  intros Hn. unfold malloc_core. destruct (size_overflows n); [apply REL_refl|].
  replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; exact Hn).
  cbn [uall]. intros z. destruct (negb (mmap_answer_ok _ _ _ z)); [apply uall_bad_answer; apply REL_refl|].
  destruct (is_err z); [apply REL_refl|].
  destruct (new_region RKGroup z (n + IB + UNIT) st) as [st1 rid] eqn:E.
  pose proof (ka_new_region RKGroup z (n + IB + UNIT) st) as K1. rewrite E in K1. cbn [fst] in K1.
  assert (C1 : cnt st1 = cnt st) by (pose proof (f_equal fst E) as E1; cbn [fst] in E1; rewrite <- E1; reflexivity).
  apply uall_alloc_meta; [|apply REL_refl].
  intros st3 go H3.
  assert (H03 : REL st st3).
  { eapply kc_REL; [ | | exact H3].
    - eapply ka_trans; [exact K1 | apply ka_step_seq].
    - rewrite cnt_step_seq. exact C1. }
  destruct go as [g|].
  - cbn [uall fst]. eapply REL_kc; [exact H03 | | reflexivity]. intros sc; reflexivity.
  - cbn [uall]. intros ru. destruct (munmap_answer_ok ru); [|apply uall_bad_answer; apply REL_refl].
    cbn [uall fst]. eapply REL_kc; [exact H03 | | reflexivity]. intros sc; reflexivity.
Qed.

Theorem cmalloc_big_shape cs n : MMAP_THRESHOLD <= n -> uall (fun r => REL cs (fst r)) (cmalloc cs n).
Proof.
  intros Hn. unfold cmalloc. eapply uall_sbind; [apply (uall_malloc_core_big cs n Hn)|].
  intros [st1 r] H. cbn [fst] in H. cbn [uall fst]. eapply REL_kc; [exact H | | reflexivity]. intros sc; reflexivity.
Qed.

Section UF.
Context {R : Type} (phi : R -> Prop).

Lemma uall_queue_kc h m st (k : mstate -> M R) bail :
  (forall st', keeps_count st st' -> uall phi (k st')) -> uall phi bail -> uall phi (queue h m st k bail).
Proof.
  intros Hk Hb. unfold queue. apply uall_guard; [|exact Hb]. apply uall_guard; [|exact Hb].
  destruct (get_head st h) as [head|].
  - apply Hk. destruct (m_prev (get_meta_rec st head)); reflexivity.
  - apply Hk. destruct h; reflexivity.
Qed.

Lemma uall_free_meta_kc m st (k : mstate -> M R) bail :
  (forall st', keeps_count st st' -> uall phi (k st')) -> uall phi bail -> uall phi (free_meta m st k bail).
Proof. intros Hk Hb. unfold free_meta. apply uall_queue_kc; [|exact Hb]. intros st' H. apply Hk. exact H. Qed.

Lemma uall_activate_group_kc m st (k : mstate -> Z -> M R) bail :
  (forall st' z, keeps_count st st' -> uall phi (k st' z)) -> uall phi bail -> uall phi (activate_group m st k bail).
Proof. intros Hk Hb. unfold activate_group. apply uall_guard; [|exact Hb]. apply Hk. reflexivity. Qed.

Lemma kc_record_seq sc st : keeps_count st (record_seq sc st).
Proof. unfold record_seq. destruct (sc_in_seq_range sc); reflexivity. Qed.

Lemma kc_step_seq' st : keeps_count st (step_seq st).
Proof. unfold keeps_count, step_seq. destruct (c_seq (ctx st) =? 255); reflexivity. Qed.

Lemma uall_dec_slots st p (k : aptr -> Z -> M R) bail :
  (forall m idx, uall phi (k m idx)) -> uall phi bail -> uall phi (dec_slots st p k bail).
Proof. intros Hk Hb. unfold dec_slots. destruct (s_slots st !! p) as [[m idx]|]; [apply Hk | exact I]. Qed.

Lemma uall_free_group_kc (rec : mstate -> aptr -> Z -> (mstate -> mapinfo -> M R) -> M R -> M R) st g
    (k : mstate -> mapinfo -> M R) bail :
  (forall st1 m i k', (forall st' mi, keeps_count st1 st' -> uall phi (k' st' mi)) -> uall phi (rec st1 m i k' bail)) ->
  (forall st' mi, keeps_count st st' -> uall phi (k st' mi)) -> uall phi bail ->
  uall phi (free_group R dec_slots rec st g k bail).
Proof.
  intros Hrec Hk Hb. unfold free_group.
  set (st1 := if m_sizeclass (get_meta_rec st g) <? 48 then _ else st).
  assert (K1 : keeps_count st st1) by (subst st1; destruct (m_sizeclass (get_meta_rec st g) <? 48); reflexivity).
  clearbody st1.
  destruct (m_mem (get_meta_rec st g)) as [p|]; [|exact I].
  set (st2 := del_slots p _ _ (del_group p st1)).
  assert (K2 : keeps_count st st2) by (subst st2; exact K1).
  clearbody st2. clear K1 st1.
  destruct (negb (m_maplen (get_meta_rec st g) =? 0)).
  - apply uall_free_meta_kc; [|exact Hb]. intros st' H. apply Hk.
    eapply kc_trans; [exact K2|]. eapply kc_trans; [|exact H].
    eapply kc_trans; [apply kc_step_seq' | apply kc_record_seq].
  - apply uall_dec_slots; [|exact Hb]. intros m idx. apply Hrec. intros st3 mi H3.
    apply uall_free_meta_kc; [|exact Hb]. intros st4 H4. apply Hk.
    eapply kc_trans; [exact K2|]. eapply kc_trans; [exact H3 | exact H4].
Qed.

Lemma uall_nontrivial_free_kc fuel : forall st g i (k : mstate -> mapinfo -> M R) bail,
  (forall st' mi, keeps_count st st' -> uall phi (k st' mi)) -> uall phi bail ->
  uall phi (nontrivial_free dec_slots fuel st g i k bail).
Proof.
  induction fuel as [|f IH]; intros st g i k bail Hk Hb; cbn [nontrivial_free]; [exact I|].
  assert (HFG : forall st0, keeps_count st st0 -> uall phi (free_group R dec_slots (nontrivial_free dec_slots f) st0 g k bail)).
  { intros st0 K0. apply uall_free_group_kc; [| |exact Hb].
    - intros st1 m j k' Hk'. apply IH; [exact Hk' | exact Hb].
    - intros st' mi H. apply Hk. eapply kc_trans; eauto. }
  destruct ((Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) + bit i =? mask_upto (m_last_idx (get_meta_rec st g)))
            && okay_to_free st g).
  - destruct (m_next (get_meta_rec st g)) as [nx|]; [|apply HFG; reflexivity].
    apply uall_guard; [|exact Hb].
    destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)).
    + destruct (active (dequeue (LActive (m_sizeclass (get_meta_rec st g))) g st) (m_sizeclass (get_meta_rec st g))) as [a|].
      * apply uall_activate_group_kc; [|exact Hb]. intros st2 z K2. apply HFG. eapply kc_trans; [apply kc_dequeue | exact K2].
      * apply HFG. apply kc_dequeue.
    + apply HFG. apply kc_dequeue.
  - destruct (Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) =? 0).
    + apply uall_guard; [|exact Hb].
      destruct (negb (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g))).
      * apply uall_queue_kc; [|exact Hb]. intros st' H. apply Hk. eapply kc_trans; [exact H | reflexivity].
      * apply Hk. reflexivity.
    + apply Hk. reflexivity.
Qed.

End UF.

Theorem cfree_keeps_cnt cs p : uall (fun cs' => cnt cs' = cnt cs) (cfree cs p).
Proof.
  unfold cfree. destruct p as [s|]; [|reflexivity].
  destruct (s_slots cs !! s) as [[g idx]|]; [|exact I].
  eapply uall_sbind with (P1 := fun st1 => cnt st1 = cnt cs); [|intros st1 H; exact H].
  unfold free_tail. apply uall_guard; [|reflexivity].
  destruct (negb ((m_freed (get_meta_rec cs g) =? 0) || _)); [reflexivity|].
  apply uall_nontrivial_free_kc; [|reflexivity].
  intros st2 mi K2. destruct mi as [[base len]|]; [|exact K2].
  destruct (negb (len =? 0)); [|exact K2].
  cbn [uall]. intros ru. destruct (munmap_answer_ok ru); [exact K2 | apply uall_bad_answer; reflexivity].
Qed.

Lemma REL_metaok : forall d st st', REL st st' -> 1 <= d -> metaok d st -> metaok (d - 1) st'.
Proof. intros d st st' [_ H] Hd Hm. unfold metaok in *. unfold cnt in H. lia. Qed.
Lemma REL_allnone : forall st st', REL st st' -> allnone st -> allnone st'.
Proof. intros st st' [H _] A. eapply keeps_allnone; eauto. Qed.
Lemma cnt_metaok : forall d st st', cnt st' = cnt st -> metaok d st -> metaok d st'.
Proof. intros d st st' E Hm. unfold metaok, cnt in *. lia. Qed.
