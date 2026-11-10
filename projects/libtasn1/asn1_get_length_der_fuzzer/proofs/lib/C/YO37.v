(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Trevor Hansen, 2026-11: module names. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import
YP0j YP0g YP0h YP0q YP0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition span_ok (A : astate) : Prop :=
forall g am, MT A g = Some (MUsed am) -> am_aidx am < am_last am -> am_sc am <> 0.
Lemma span_ok_init : span_ok init_state.
Proof. intros g am H. unfold MT, init_state in H. cbn in H. discriminate. Qed.
Lemma span_ok_same_metas A A' : span_ok A -> st_metas A' = st_metas A -> span_ok A'.
Proof. intros H Em g am Hg. unfold MT in *. rewrite Em in Hg. exact (H g am Hg). Qed.
Lemma span_ok_set_active A l : span_ok A -> span_ok (set_active l A).
Proof. intros H. apply (span_ok_same_metas A); [exact H | reflexivity]. Qed.
Lemma span_ok_set_bounces A l : span_ok A -> span_ok (set_bounces l A).
Proof. intros H. apply (span_ok_same_metas A); [exact H | reflexivity]. Qed.



Lemma span_ok_set_mmap_counter A v : span_ok A -> span_ok (set_mmap_counter v A).
Proof. intros H. apply (span_ok_same_metas A); [exact H | reflexivity]. Qed.












Lemma span_ok_transfer A A' : span_ok A ->
(forall g am', MT A' g = Some (MUsed am') ->
exists g0 am, MT A g0 = Some (MUsed am) /\ am_aidx am' = am_aidx am /\ am_last am' = am_last am /\ am_sc am' = am_sc am) ->
span_ok A'.
Proof.
intros H HT g am' Hg Hlt. destruct (HT g am' Hg) as (g0 & am & Hg0 & Ea & El & Es). rewrite Es. apply (H g0 am Hg0). lia.
Qed.

Definition am_span_ok (am : ameta) : Prop := am_aidx am < am_last am -> am_sc am <> 0.




Lemma span_ok_upd_used A g am' : span_ok A -> am_span_ok am' -> span_ok (upd_meta g (MUsed am') A).
Proof.
intros H Ham p am Hp. rewrite MT_upd in Hp. destruct (sptr_eqb p g).
- injection Hp as <-. exact Ham.
- exact (H p am Hp).
Qed.
Lemma span_ok_upd_same3 A g am am' : span_ok A -> MT A g = Some (MUsed am) ->
am_aidx am' = am_aidx am -> am_last am' = am_last am -> am_sc am' = am_sc am ->
span_ok (upd_meta g (MUsed am') A).
Proof.
intros H Hg Ea El Es. apply span_ok_upd_used; [exact H|]. intros Hlt. rewrite Es. apply (H g am Hg). lia.
Qed.
Lemma span_ok_upd_set_avail A g am v : span_ok A -> MT A g = Some (MUsed am) -> span_ok (upd_meta g (MUsed (am_set_avail v am)) A).
Proof. intros H Hg. apply (span_ok_upd_same3 A g am); [exact H | exact Hg | reflexivity | reflexivity | reflexivity]. Qed.

Lemma span_ok_upd_set_prev A g am v : span_ok A -> MT A g = Some (MUsed am) -> span_ok (upd_meta g (MUsed (am_set_prev v am)) A).
Proof. intros H Hg. apply (span_ok_upd_same3 A g am); [exact H | exact Hg | reflexivity | reflexivity | reflexivity]. Qed.
Lemma span_ok_upd_set_next A g am v : span_ok A -> MT A g = Some (MUsed am) -> span_ok (upd_meta g (MUsed (am_set_next v am)) A).
Proof. intros H Hg. apply (span_ok_upd_same3 A g am); [exact H | exact Hg | reflexivity | reflexivity | reflexivity]. Qed.
Lemma span_ok_upd_set_links A g am pr nx : span_ok A -> MT A g = Some (MUsed am) -> span_ok (upd_meta g (MUsed (am_set_links pr nx am)) A).
Proof. intros H Hg. apply (span_ok_upd_same3 A g am); [exact H | exact Hg | reflexivity | reflexivity | reflexivity]. Qed.

Lemma span_ok_upd_set_avail_freed A g am v w : span_ok A -> MT A g = Some (MUsed am) ->
span_ok (upd_meta g (MUsed (am_set_avail v (am_set_freed w am))) A).
Proof. intros H Hg. apply (span_ok_upd_same3 A g am); [exact H | exact Hg | reflexivity | reflexivity | reflexivity]. Qed.
Lemma span_ok_upd_set_aidx A g am v : span_ok A -> MT A g = Some (MUsed am) ->
(v < am_last am -> am_aidx am < am_last am) ->
span_ok (upd_meta g (MUsed (am_set_aidx v am)) A).
Proof.
intros H Hg Hv. apply span_ok_upd_used; [exact H|]. intros Hlt. cbn in Hlt |- *. apply (H g am Hg). exact (Hv Hlt).
Qed.

Lemma am_span_ok_sc am : am_sc am <> 0 -> am_span_ok am.
Proof. intros E _. exact E. Qed.
Lemma mapped_aidx_class (size cnt : Z) :
0 < size -> 1 <= cnt <= 32 ->
(let a0 := (4096 - UNIT) / size - 1 in
let a1 := if cnt - 1 <? a0 then cnt - 1 else a0 in
let aidx := if a1 <? 0 then 0 else a1 in
aidx < cnt - 1 -> 127 < size).
Proof.
intros Hs Hc. unfold UNIT. change (4096 - 16) with 4080. cbn zeta.
set (q := 4080 / size). intros Hlt.
assert (Hq : q < 32).
{ destruct (Z.ltb_spec (cnt - 1) (q - 1)); [destruct (Z.ltb_spec (cnt - 1) 0); lia|]. destruct (Z.ltb_spec (q - 1) 0); lia. }
destruct (Z_lt_dec 127 size) as [|Hge]; [assumption|]. exfalso.
assert (32 <= q); [|lia]. unfold q. apply Z.div_le_lower_bound; lia.
Qed.
Lemma class_size_0 : class_size 0 = 16.
Proof. reflexivity. Qed.
Lemma class_size_pos_ge32 sc : 0 <= sc < 48 -> sc <> 0 -> 32 <= class_size sc.
Proof.
intros Hsc Hne. unfold class_size, UNIT, znth.
assert (H : forall k, (k < 48)%nat -> k <> 0%nat -> 2 <= nth k size_classes 0).
{ intros k Hk Hk0. do 48 (destruct k as [|k]; [first [exfalso; exact (Hk0 eq_refl) | cbn; lia] |]). lia. }
specialize (H (Z.to_nat sc) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma class_size_big_not0 sc : 0 <= sc < 48 -> 127 < class_size sc -> sc <> 0.
Proof. intros Hsc Hb ->. rewrite class_size_0 in Hb. lia. Qed.
