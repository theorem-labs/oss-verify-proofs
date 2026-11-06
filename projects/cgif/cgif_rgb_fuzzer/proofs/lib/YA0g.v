(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith Lia.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section c.
Variable OFF : Z.
Variables BAND_LO LSH_HI HSH_LO BAND_HI : Z.
Variable MEM_END : Z.
Definition shadow (a : Z) : Z := a / 8 + OFF.
Hypothesis band_lo_le_off : BAND_LO <= OFF.
Hypothesis low_fits : shadow BAND_LO <= LSH_HI.
Hypothesis high_lo : shadow BAND_HI = HSH_LO.
Hypothesis high_hi : shadow MEM_END <= BAND_HI.
Hypothesis band_order : 0 <= BAND_LO /\ BAND_LO <= LSH_HI /\ LSH_HI <= HSH_LO /\ HSH_LO <= BAND_HI /\ BAND_HI <= MEM_END.
Lemma shadow_mono : forall a b, a <= b -> shadow a <= shadow b.
Proof. intros a b H. unfold shadow. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. Qed.

Lemma shadow_lt_of : forall a b, 0 <= a -> a < b -> b mod 8 = 0 -> shadow a < shadow b.
Proof.
intros a b Ha Hab Hb. unfold shadow.
assert (a / 8 < b / 8).
{ apply Z.div_lt_upper_bound; [lia|].
pose proof (Z.div_mod b 8 ltac:(lia)) as E. rewrite Hb, Z.add_0_r in E. lia. }
lia.
Qed.

Lemma shadow_low' : forall a n,
0 <= a -> 0 < n -> a + n <= BAND_LO -> BAND_LO mod 8 = 0 ->
BAND_LO <= shadow a /\ shadow (a + n - 1) < shadow BAND_LO /\ shadow BAND_LO <= LSH_HI.
Proof.
intros a n Ha Hn Hend Hal. split; [|split; [|exact low_fits]].
- unfold shadow. assert (0 <= a / 8) by (apply Z.div_pos; lia). lia.
- apply shadow_lt_of; lia.
Qed.
Lemma shadow_high : forall a n,
BAND_HI <= a -> 0 < n -> a + n <= MEM_END -> MEM_END mod 8 = 0 ->
HSH_LO <= shadow a /\ shadow (a + n - 1) < BAND_HI.
Proof.
intros a n Ha Hn Hend Hal. split.
- rewrite <- high_lo. apply shadow_mono. lia.
- apply (Z.lt_le_trans _ (shadow MEM_END)); [|exact high_hi].
pose proof band_order. apply shadow_lt_of; lia.
Qed.
Theorem shadow_of_grant : forall a n,
0 <= a -> 0 < n -> a + n <= MEM_END -> BAND_LO mod 8 = 0 -> MEM_END mod 8 = 0 ->
(a + n <= BAND_LO \/ BAND_HI <= a) ->
(BAND_LO <= shadow a /\ shadow (a + n - 1) < LSH_HI)
\/ (HSH_LO <= shadow a /\ shadow (a + n - 1) < BAND_HI).
Proof.
intros a n Ha Hn Hend Hal Hme [Hl|Hh].
- left. destruct (shadow_low' a n Ha Hn Hl Hal) as (H1 & H2 & H3). lia.
- right. apply shadow_high; assumption.
Qed.
Corollary shadow_in_band : forall a n,
0 <= a -> 0 < n -> a + n <= MEM_END -> BAND_LO mod 8 = 0 -> MEM_END mod 8 = 0 ->
(a + n <= BAND_LO \/ BAND_HI <= a) ->
forall i, 0 <= i < n -> BAND_LO <= shadow (a + i) < BAND_HI.
Proof.
intros a n Ha Hn Hend Hal Hme Hout i Hi.
pose proof (shadow_mono a (a + i) ltac:(lia)). pose proof (shadow_mono (a + i) (a + n - 1) ltac:(lia)).
destruct (shadow_of_grant a n Ha Hn Hend Hal Hme Hout) as [[H1 H2]|[H1 H2]]; lia.
Qed.

End c.
Module L47.
Definition OFF : Z := 0x7fff8000.
Definition BAND_LO : Z := 0x7fff7000.
Definition LSH_HI : Z := 0x8fff7000.
Definition HSH_LO : Z := 0x2008fff7000.
Definition BAND_HI : Z := 0x10007fff8000.
Definition MEM_END : Z := 0x800000000000.
Lemma laws : BAND_LO <= OFF /\ shadow OFF BAND_LO <= LSH_HI /\ shadow OFF BAND_HI = HSH_LO /\ shadow OFF MEM_END <= BAND_HI
/\ (0 <= BAND_LO /\ BAND_LO <= LSH_HI /\ LSH_HI <= HSH_LO /\ HSH_LO <= BAND_HI /\ BAND_HI <= MEM_END) /\ BAND_LO mod 8 = 0 /\ MEM_END mod 8 = 0.
Proof. unfold shadow, OFF, BAND_LO, LSH_HI, HSH_LO, BAND_HI, MEM_END. repeat split; cbv; first [reflexivity | discriminate | lia]. Qed.
Lemma alloc_top_lt_mem_end : forall sp, 0x7fff80000000 <= sp < 0x800000000000 -> sp - 0x800000 <= MEM_END.
Proof. intros sp H. unfold MEM_END. lia. Qed.
Theorem shadow_of_grant47 : forall a n,
0 <= a -> 0 < n -> a + n <= MEM_END -> (a + n <= BAND_LO \/ BAND_HI <= a) ->
(BAND_LO <= shadow OFF a /\ shadow OFF (a + n - 1) < LSH_HI) \/ (HSH_LO <= shadow OFF a /\ shadow OFF (a + n - 1) < BAND_HI).
Proof.
pose proof laws as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
intros a n Ha Hn He Ho. eapply shadow_of_grant; eauto.
Qed.
Theorem shadow_in_band47 : forall a n,
0 <= a -> 0 < n -> a + n <= MEM_END -> (a + n <= BAND_LO \/ BAND_HI <= a) ->
forall i, 0 <= i < n -> BAND_LO <= shadow OFF (a + i) < BAND_HI.
Proof.
pose proof laws as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
intros a n Ha Hn He Ho. eapply shadow_in_band; eauto.
Qed.
End L47.
