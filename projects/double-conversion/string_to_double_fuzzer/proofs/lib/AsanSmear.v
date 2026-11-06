(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec AgentLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition sm (t : Z) (k : Z) : Z := Z.lor t (Z.shiftr t k).
Definition smear5 (x : Z) : Z := sm (sm (sm (sm (sm x 1) 2) 4) 8) 16.
Definition smear6 (x : Z) : Z := sm (smear5 x) 32.
(* [comment removed for export] *)
Lemma sm_range : forall t k, 0 <= t < 2 ^ 47 -> 0 <= k -> 0 <= sm t k < 2 ^ 47.
Proof.
  intros t k Ht Hk. unfold sm.
  assert (H0 : 0 <= Z.shiftr t k) by (apply Z.shiftr_nonneg; lia).
  assert (HL : 0 <= Z.lor t (Z.shiftr t k)) by (apply Z.lor_nonneg; lia).
  split; [exact HL|].
  destruct (Z.eq_dec t 0) as [->|Ht0]; [rewrite Z.shiftr_0_l, Z.lor_0_l; lia|].
  destruct (Z.eq_dec (Z.lor t (Z.shiftr t k)) 0) as [E|NE]; [rewrite E; lia|].
  apply Z.log2_lt_pow2; [lia|]. rewrite Z.log2_lor by lia.
  assert (Z.log2 t < 47) by (apply Z.log2_lt_pow2; lia).
  destruct (Z.eq_dec (Z.shiftr t k) 0) as [E0|N0]; [rewrite E0; change (Z.log2 0) with 0; lia|].
  rewrite Z.log2_shiftr by lia. lia.
Qed.

(* [comment removed for export] *)
Definition lowrun (t : Z) (w : Z) : Prop := forall i, 0 <= i -> 46 - w <= i <= 46 -> Z.testbit t i = true.

Lemma sm_run : forall t k w, 0 <= k <= w + 1 -> 0 <= w -> lowrun t w -> lowrun (sm t k) (w + k).
Proof.
  intros t k w Hk Hw H i Hi0 Hi. unfold sm. rewrite Z.lor_spec.
  destruct (Z.le_gt_cases (46 - w) i) as [L|G].
  - rewrite (H i Hi0) by lia. reflexivity.
  - rewrite Z.shiftr_spec by lia. rewrite (H (i + k)) by lia. apply orb_true_r.
Qed.

Lemma bit46 : forall x, 2 ^ 46 <= x < 2 ^ 47 -> lowrun x 0.
Proof.
  intros x Hx i Hi0 Hi. assert (i = 46) as -> by lia.
  apply Z.testbit_true; [lia|]. replace (x / 2 ^ 46) with 1; [reflexivity|].
  apply (Z.div_unique x (2 ^ 46) 1 (x - 2 ^ 46)); lia.
Qed.

Lemma smear5_run : forall x, 2 ^ 46 <= x < 2 ^ 47 -> lowrun (smear5 x) 31 /\ 0 <= smear5 x < 2 ^ 47.
Proof.
  intros x Hx. unfold smear5.
  pose proof (bit46 x Hx) as R0.
  pose proof (sm_run x 1 0 ltac:(lia) ltac:(lia) R0) as R1.
  pose proof (sm_run _ 2 1 ltac:(lia) ltac:(lia) R1) as R2.
  pose proof (sm_run _ 4 3 ltac:(lia) ltac:(lia) R2) as R3.
  pose proof (sm_run _ 8 7 ltac:(lia) ltac:(lia) R3) as R4.
  pose proof (sm_run _ 16 15 ltac:(lia) ltac:(lia) R4) as R5.
  split; [exact R5|].
  repeat (apply sm_range; [|lia]). lia.
Qed.

Theorem smear6_val : forall x, 2 ^ 46 <= x < 2 ^ 47 -> smear6 x = 2 ^ 47 - 1.
Proof.
  intros x Hx. destruct (smear5_run x Hx) as [R5 B5].
  pose proof (sm_run _ 32 31 ltac:(lia) ltac:(lia) R5) as R6. change (sm (smear5 x) 32) with (smear6 x) in R6.
  pose proof (sm_range (smear5 x) 32 B5 ltac:(lia)) as B6. change (sm (smear5 x) 32) with (smear6 x) in B6.
  change (2 ^ 47 - 1) with (Z.ones 47).
  apply Z.bits_inj'. intros n Hn. rewrite Z.testbit_ones_nonneg by lia.
  destruct (Z.lt_ge_cases n 47) as [L|G].
  - rewrite (R6 n Hn) by lia. symmetry. apply Z.ltb_lt. exact L.
  - rewrite Z.bits_above_log2; [| lia | ].
    + symmetry. apply Z.ltb_ge. lia.
    + destruct (Z.eq_dec (smear6 x) 0) as [E|NE]; [rewrite E; change (Z.log2 0) with 0; lia|]. apply Z.log2_lt_pow2; [lia|]. eapply Z.lt_le_trans; [apply (proj2 B6)|]. apply Z.pow_le_mono_r; lia.
Qed.

Theorem smear5_hi : forall x, 2 ^ 46 <= x < 2 ^ 47 -> Z.shiftr (smear5 x) 32 = 32767.
Proof.
  intros x Hx. destruct (smear5_run x Hx) as [R5 B5].
  change 32767 with (Z.ones 15).
  apply Z.bits_inj'. intros n Hn. rewrite Z.testbit_ones_nonneg by lia. rewrite Z.shiftr_spec by lia.
  destruct (Z.lt_ge_cases n 15) as [L|G].
  - rewrite (R5 (n + 32)) by lia. symmetry. apply Z.ltb_lt. exact L.
  - rewrite Z.bits_above_log2; [| lia | ].
    + symmetry. apply Z.ltb_ge. lia.
    + destruct (Z.eq_dec (smear5 x) 0) as [E|NE]; [rewrite E; change (Z.log2 0) with 0; lia|]. apply Z.log2_lt_pow2; [lia|]. eapply Z.lt_le_trans; [apply (proj2 B5)|]. apply Z.pow_le_mono_r; lia.
Qed.

(* [comment removed for export] *)
Definition smw (t : word) (k : Z) : word := v_or t (v_srli t k).
(* [comment removed for export] *)
Definition mv_smear (x : word) : word * word :=
  let t5 := smw (smw (smw (smw (smw x 1) 2) 4) 8) 16 in
  (smw t5 32, v_srli t5 32).

Lemma smw_Z : forall (t : word) k, 0 <= bv_unsigned t < 2 ^ 47 -> 0 <= k ->
  bv_unsigned (smw t k) = sm (bv_unsigned t) k.
Proof.
  intros t k Ht Hk. unfold smw, v_or, v_srli, sm.
  pose proof (sm_range (bv_unsigned t) k Ht Hk) as R. unfold sm in R.
  assert (Hs : 0 <= Z.shiftr (bv_unsigned t) k < 2 ^ 47).
  { split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by lia.
    apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|]. pose proof (Z.pow_pos_nonneg 2 k). nia. }
  rewrite (u64_lit (Z.shiftr (bv_unsigned t) k)) by lia. apply u64_lit. lia.
Qed.

Theorem mv_smear_val : forall x : word, 2 ^ 46 <= bv_unsigned x <= 2 ^ 47 - 1 ->
  fst (mv_smear x) = Z_to_bv 64 (2 ^ 47 - 1) /\ snd (mv_smear x) = Z_to_bv 64 32767.
Proof.
  intros x Hx. unfold mv_smear. cbn [fst snd].
  assert (H0 : 0 <= bv_unsigned x < 2 ^ 47) by lia.
  assert (H1 := sm_range _ 1 H0 ltac:(lia)). rewrite <- (smw_Z x 1 H0) in H1 by lia.
  assert (H2 := sm_range _ 2 H1 ltac:(lia)). rewrite <- (smw_Z _ 2 H1) in H2 by lia.
  assert (H3 := sm_range _ 4 H2 ltac:(lia)). rewrite <- (smw_Z _ 4 H2) in H3 by lia.
  assert (H4 := sm_range _ 8 H3 ltac:(lia)). rewrite <- (smw_Z _ 8 H3) in H4 by lia.
  assert (H5 := sm_range _ 16 H4 ltac:(lia)). rewrite <- (smw_Z _ 16 H4) in H5 by lia.
  assert (E5 : bv_unsigned (smw (smw (smw (smw (smw x 1) 2) 4) 8) 16) = smear5 (bv_unsigned x)).
  { unfold smear5. rewrite !smw_Z by (first [assumption | lia]). reflexivity. }
  split.
  - apply bv_eq. rewrite (smw_Z _ 32 H5) by lia. rewrite E5. change (sm (smear5 (bv_unsigned x)) 32) with (smear6 (bv_unsigned x)).
    rewrite smear6_val by lia. rewrite u64_lit by lia. reflexivity.
  - apply bv_eq. unfold v_srli. rewrite E5, smear5_hi by lia. rewrite !u64_lit by lia. reflexivity.
Qed.
