(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0n.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Definition qtightB (s : astate) : Prop := qtight s /\ BigInv s.
Definition jbud (s s' : astate) (k : Z) : Prop := vev s' <= vev s + k /\ bud_le s s' k k (2 ^ 17 * k) (HULL_UNIT * k).
Lemma jbud_refl : forall s, jbud s s 0.
Proof. intros s. split; [lia|]. unfold bud_le. lia. Qed.
Lemma jbud_mono : forall s s' k k', jbud s s' k -> k <= k' -> jbud s s' k'.
Proof. intros s s' k k' (V & B) H. split; [lia|]. eapply bud_le_mono; [exact B | lia | lia | lia | unfold HULL_UNIT; lia]. Qed.
Lemma jbud_step : forall s s1 s2 k j e c w h, 0 <= k -> 0 <= j ->
jbud s s1 k -> bud_le s1 s2 e c w h -> e <= j -> c <= j -> w <= 2 ^ 17 * j -> h <= HULL_UNIT * j -> jbud s s2 (k + j).
Proof.
intros s s1 s2 k j e c w h Hk Hj (V & B) D He Hc Hw Hh.
assert (B2 : bud_le s s2 (k + j) (k + j) (2 ^ 17 * (k + j)) (HULL_UNIT * (k + j))).
{ pose proof (bud_le_trans _ _ _ _ _ _ _ _ _ _ _ B D) as T. eapply bud_le_mono; [exact T | lia | lia | lia | lia]. }
split; [|exact B2]. exact (vev_le s s2 (k + j) ltac:(lia) B2).
Qed.
Lemma jbud_trans : forall s s1 s2 k k1, 0 <= k -> 0 <= k1 -> jbud s s1 k -> jbud s1 s2 k1 -> jbud s s2 (k + k1).
Proof. intros s s1 s2 k k1 Hk Hk1 J (_ & D). apply (jbud_step s s1 s2 k k1 _ _ _ _ Hk Hk1 J D); lia. Qed.
Lemma bud_le_same : forall s s', st_nev s' = st_nev s -> st_chunks s' = st_chunks s -> st_secs s' = st_secs s -> bud_le s s' 0 0 0 0.
Proof. intros s s' E1 E2 E3. unfold bud_le, nrec, wpot, sec_hulls. rewrite E1, E2, E3. lia. Qed.
Lemma jbud_same : forall s s1 s2 k, 0 <= k -> jbud s s1 k -> st_nev s2 = st_nev s1 -> st_chunks s2 = st_chunks s1 -> st_secs s2 = st_secs s1 -> jbud s s2 k.
Proof.
intros s s1 s2 k Hk J E1 E2 E3. replace k with (k + 0) by lia.
apply (jbud_step s s1 s2 k 0 _ _ _ _ Hk (Z.le_refl 0) J (bud_le_same s1 s2 E1 E2 E3)); lia.
Qed.
Lemma qtightB_same : forall s s', st_chunks s' = st_chunks s -> st_qthread s' = st_qthread s -> st_qglobal s' = st_qglobal s ->
st_regions s' = st_regions s -> st_cache s' = st_cache s -> qtightB s -> qtightB s'.
Proof.
intros s s' E1 E2 E3 E4 E5 (Q & CP & BP). split; [exact (qtight_ext s s' E1 E2 E3 Q)|]. split.
- intros c Hc. rewrite <- (CP c Hc). apply cdef_ext; [unfold reg; rewrite E4; reflexivity|].
unfold class_elems, reg, cache, chunk_offs, batch_offs, all_batches. rewrite E1, E2, E3, E4, E5. reflexivity.
- intros c Hc. unfold reg. rewrite E4. exact (BP c Hc).
Qed.
Lemma malloc_cost_coarse : forall n, 0 <= n < MALLOC_MAX -> 1 <= 1 /\ wcost n <= 2 ^ 17 * 1 /\ hcost n <= HULL_UNIT * 1.
Proof. intros n Hn. pose proof (wcost_range n ltac:(lia)). pose proof (hcost_range n Hn). lia. Qed.
Theorem regime_big_vev : forall U s, Wf U s -> qtightB s -> vev s < VEV_MAX -> regime_big s /\ aregime s.
Proof.
intros U s W (QT & BI) H. pose proof (vev_bud s 1 ltac:(lia)) as (E & C & Wt & Hh).
assert (RB : regime_big s).
{ unfold nrec, wpot, NREC_MAX, WPOT_MAX in *. pose proof (crw_nonneg (st_chunks s)) as C0.
apply (regime_big_intro2 U s W BI QT); unfold kUserMapSize, EV_MAX, kPtrArrayEntriesPerCommit; lia. }
split; [exact RB|]. right. split; [exact RB|]. unfold EV_BIG, HULL_UNIT in *. split; lia.
Qed.

Lemma jbud_step0 : forall s s1 s2 k, 0 <= k -> jbud s s1 k -> bud_le s1 s2 0 0 0 0 -> jbud s s2 k.
Proof. intros s s1 s2 k Hk J D. replace k with (k + 0) by lia. apply (jbud_step s s1 s2 k 0 _ _ _ _ Hk (Z.le_refl 0) J D); lia. Qed.
Lemma jbud_of_bud : forall s s' e c w h j, 0 <= j -> bud_le s s' e c w h -> e <= j -> c <= j -> w <= 2 ^ 17 * j -> h <= HULL_UNIT * j -> jbud s s' j.
Proof.
intros s s' e c w h j Hj D He Hc Hw Hh. replace j with (0 + j) by lia.
apply (jbud_step s s s' 0 j e c w h (Z.le_refl 0) Hj (jbud_refl s) D); assumption.
Qed.
Lemma jbud_malloc1 : forall s n s', 0 <= n < MALLOC_MAX -> mgrow s n s' -> st_nev s' = st_nev s + 1 -> jbud s s' 1.
Proof.
intros s n s' Hn G NE. pose proof (bud_malloc s n s' ltac:(lia) G NE) as D. destruct (malloc_cost_coarse n Hn) as (_ & Cw & Ch).
apply (jbud_of_bud s s' 1 1 (wcost n) (hcost n) 1); try lia. exact D.
Qed.
Lemma jbud_free1 : forall U s p n ns r, fgrow s (snd r) -> free_post U s p n ns r -> jbud s (snd r) 1.
Proof.
intros U s p n ns r G P. pose proof (bud_free U s p n ns r G P) as D.
apply (jbud_of_bud s (snd r) 1 0 0 0 1); try lia; [exact D | unfold HULL_UNIT; lia].
Qed.

