(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/PixChk.v; 76 of its 102 lines of code are new or changed and 45 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YGcfRecStep.v at commit 33db28e0c9a (the core dead_shadow_new change 269a783f7a5..33db28e0c9a, reviewed), module paths changed. *)
(* One recycle step in the model keeps every dead real slot dead with the same length, and revives no slot: every
   entry live after the step is the same entry before it. recycle_chunk only removes the chunk and, for a secondary,
   marks the SAME st_secs entry dead with the same length and size (sec_dealloc); cache_dealloc touches neither
   st_secs nor st_chunks. A walk that makes several such calls composes them by rec_step's reflexivity and
   transitivity, so each call's dead set (YGcfRehidePost.dead_shadow_new, keyed by slot index) fits inside the walk's. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0f YG0k YG04 YG06 YG0n YGcfRehidePost.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. st_secs and st_chunks fixed, through the steps cache_dealloc makes.          *)
Definition SCx (X : list secmap) (Y : list chunk) (s : astate) : Prop := st_secs s = X /\ st_chunks s = Y.

Lemma apost_bind_P {A B} : forall (m : M B) (k : B -> M A) s (P : astate -> Prop),
  apost (m s) (fun r => P (snd r)) -> (forall b s1, P s1 -> apost (k b s1) (fun r => P (snd r))) ->
  apost (bind m k s) (fun r => P (snd r)).
Proof.
intros m k s P H1 H2. apply apost_bind. eapply apost_mono; [|exact H1]. intros [b s1] H. exact (H2 b s1 H).
Qed.

(* One step of a proof that P holds of every returned state, for an M term built from the model's primitives
   whose state updates P cannot see. *)
Ltac sc_step :=
  cbn [fst snd] in *;
  first
  [ match goal with |- apost (bind get _ _) _ => apply apost_bind; apply apost_get end
  | match goal with H : ?P ?s |- apost (bind _ _ ?s) (fun r => ?P (snd r)) =>
      apply (apost_bind_P _ _ s P); [|let b := fresh "b" in let s1 := fresh "s" in let H1 := fresh "HP" in
                                       intros b s1 H1] end
  | apply apost_fail | apply apost_spin
  | apply apost_mcheck; intros _
  | apply apost_askz; intros ? _
  | apply apost_if; intros _
  | apply apost_get_region | apply apost_get_pc | apply apost_set_region | apply apost_set_pc
  | apply apost_get | apply apost_put | apply apost_modify | apply apost_ret
  | match goal with H : ?P ?s |- ?P _ => exact H end ].

Lemma ensure_free_array_sc : forall X Y c need b s, SCx X Y s ->
  apost (ensure_free_array c need b s) (fun r => SCx X Y (snd r)).
Proof. intros X Y c need b s H. unfold ensure_free_array. repeat sc_step. Qed.

Lemma return_to_allocator_sc : forall X Y c offs s, SCx X Y s ->
  apost (return_to_allocator c offs s) (fun r => SCx X Y (snd r)).
Proof.
intros X Y c offs s H. unfold return_to_allocator.
apply (apost_bind_P _ _ s (SCx X Y)); [repeat sc_step|]. intros r0 s1 H1. cbn [fst snd].
apply (apost_bind_P _ _ s1 (SCx X Y)); [exact (ensure_free_array_sc X Y c _ true s1 H1)|]. intros b0 s2 H2.
repeat sc_step.
Qed.

Lemma cache_dealloc_sc : forall X Y c z s, SCx X Y s -> apost (cache_dealloc c z s) (fun r => SCx X Y (snd r)).
Proof.
intros X Y c z s H. unfold cache_dealloc, init_cache_if_needed.
repeat (sc_step || match goal with H : SCx ?X ?Y ?s |- apost (return_to_allocator ?c ?o ?s) _ =>
                     exact (return_to_allocator_sc X Y c o s H) end).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. rec_step and the two step lemmas.                                            *)
Section r. Context {rc : YM05.RunCeil}.

Definition rec_step (ly : alayout) (S S' : astate) : Prop :=
  (forall r sm, YGcfRehidePost.dead_sec ly S r sm -> exists sm', YGcfRehidePost.dead_sec ly S' r sm' /\ sm_len sm' = sm_len sm) /\
  (forall r sm0, nth_error (st_secs S') r = Some sm0 -> sm_live sm0 = true -> nth_error (st_secs S) r = Some sm0).

Lemma rec_step_of_sc : forall ly S S', st_secs S' = st_secs S -> rec_step ly S S'.
Proof.
intros ly S S' Es. split.
- intros r sm (H1 & H2 & H3 & H4 & H5). exists sm. split; [|reflexivity].
  unfold dead_sec. rewrite Es. exact (conj H1 (conj H2 (conj H3 (conj H4 H5)))).
- intros r sm0 Hn _. rewrite Es in Hn. exact Hn.
Qed.

Lemma del_chunk_sub : forall l b k, In k (del_chunk l b) -> In k l.
Proof.
induction l as [|k0 t IH]; intros b k H; cbn [del_chunk] in H; [destruct H|].
destruct (sptr_eqb (ck_beg k0) b); [right; exact H|].
destruct H as [<-|H]; [left; reflexivity | right; exact (IH b k H)].
Qed.

Lemma cache_dealloc_rec_step : forall ly z X, apost (cache_dealloc kBatchClass z X) (fun r => rec_step ly X (snd r)).
Proof.
intros ly z X. eapply apost_mono; [|apply (cache_dealloc_sc (st_secs X) (st_chunks X)); split; reflexivity].
intros r [E1 _]. exact (rec_step_of_sc ly X (snd r) E1).
Qed.

Lemma recycle_chunk_rec_step : forall ly k X, apost (recycle_chunk k X) (fun r => rec_step ly X (snd r)).
Proof.
intros ly k X. unfold recycle_chunk.
apply apost_bind. apply apost_get. cbn [fst snd].
apply apost_bind. apply apost_mcheck. intros _. cbn [fst snd].
apply apost_bind. apply apost_put. cbn [fst snd].
set (X1 := set_chunks (del_chunk (st_chunks X) (ck_beg k)) X).
destruct (ck_beg k) as [|off|r o|cid pos] eqn:Eb; [apply apost_fail | | | apply apost_fail].
- (* a primary chunk: the cache keeps st_secs *)
  eapply apost_mono; [|apply (cache_dealloc_sc (st_secs X1) (st_chunks X1)); split; reflexivity].
  intros r0 [E1 _]. exact (rec_step_of_sc ly X (snd r0) E1).
- (* a secondary chunk: sec_dealloc marks the same entry dead *)
  unfold sec_dealloc. apply apost_bind. apply apost_get. cbn [fst snd].
  change (st_secs X1) with (st_secs X). change (st_sec_arr X1) with (st_sec_arr X).
  destruct (nth_error (st_secs X) r) as [sm|] eqn:En; [|apply apost_fail].
  destruct (index_of (st_sec_arr X) r 0) as [i|]; [|apply apost_fail].
  apply apost_bind. apply (apost_mono _ (fun r0 => snd r0 = X1)).
  2:{ apply apost_if; intros _; [|apply apost_ret; reflexivity].
      apply apost_bind. apply apost_askz. intros z0 _. cbn [fst snd].
      apply apost_if; intros _; [apply apost_ret; reflexivity | apply apost_spin]. }
  intros [u1 s1] Hs. cbn [fst snd] in Hs |- *. subst s1.
  apply apost_bind. apply apost_askz. intros z1 _. cbn [fst snd].
  apply apost_modify. cbn [snd]. unfold X1 in *.
  unfold rec_step, dead_sec, sec_real in *.
  cbn [st_secs st_chunks st_sec_arr set_chunks set_sec_arr set_secs] in *.
  assert (Lt : (r < length (st_secs X))%nat) by (apply nth_error_Some; rewrite En; discriminate). split.
  + intros r' sm' (H1 & H2 & H3 & H4 & H5).
    destruct (Nat.eq_dec r' r) as [->|Ne].
    * rewrite En in H1. injection H1 as <-. exists (mkSec (sm_len sm) (sm_size sm) false). split; [|reflexivity].
      cbn [sm_len sm_size sm_live]. rewrite (nth_error_lupd_same _ _ _ Lt).
      exact (conj eq_refl (conj eq_refl (conj H3 (conj H4 H5)))).
    * exists sm'. split; [|reflexivity].
      rewrite (nth_error_lupd_other _ _ _ _ (not_eq_sym Ne)). exact (conj H1 (conj H2 (conj H3 (conj H4 H5)))).
  + intros r' sm0 Hn Hl. destruct (Nat.eq_dec r' r) as [->|Ne].
    * rewrite (nth_error_lupd_same _ _ _ Lt) in Hn. injection Hn as <-. cbn [sm_live] in Hl. discriminate.
    * rewrite (nth_error_lupd_other _ _ _ _ (not_eq_sym Ne)) in Hn. exact Hn.
Qed.
End r.
