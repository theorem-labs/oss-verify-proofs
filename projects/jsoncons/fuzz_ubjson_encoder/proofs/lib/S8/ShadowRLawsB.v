(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import HeapIface HeapIfaceA HeapIfaceAEx.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma div8_up (m : Z) : 0 <= m -> (m mod 8 = 0 -> (m + 7) / 8 = m / 8) /\ (m mod 8 <> 0 -> (m + 7) / 8 = m / 8 + 1).
Proof.
  intros Hm. pose proof (Z.div_mod m 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound m 8 ltac:(lia)) as R.
  set (q := m / 8) in *. set (r := m mod 8) in *.
  assert (E : m + 7 = q * 8 + (r + 7)) by lia. rewrite E, (Z.div_add_l q 8 (r + 7)) by lia.
  split; intros Hr.
  - rewrite (Z.div_small (r + 7) 8) by lia. lia.
  - rewrite <- (Z.div_unique_pos (r + 7) 8 1 (r - 1)); lia.
Qed.

Section Laws.
Variables M M' : word -> option byte.

Definition shadow_tby (u n : Z) : Prop :=
  forall j, 0 <= j -> (j < n / 8 \/ (j = n / 8 /\ n mod 8 <> 0)) -> forall v, byte_at M (HeapIfaceA.S u + j) v -> byte_at M' (HeapIfaceA.S u + j) v.

Lemma shadow_blk_tby u n : 0 < n -> shadow_tby u n -> shadow_blk M u n -> shadow_blk M' u n.
Proof.
  intros Hn TBY (Z0 & P0). split.
  - intros j Hj. apply TBY; [lia|left; lia|exact (Z0 j Hj)].
  - intros Hm. apply TBY; [apply Z.div_pos; lia|right; split; [reflexivity|exact Hm]|exact (P0 Hm)].
Qed.

Lemma shadow_blkR_tby u n : 0 < n -> shadow_tby u n -> HAJ.shadow_blkR M u n -> HAJ.shadow_blkR M' u n.
Proof.
  intros Hn TBY [SB|(m & Hm & Z0 & P0 & F0)].
  - left. exact (shadow_blk_tby u n Hn TBY SB).
  - right. exists m. split; [exact Hm|].
    pose proof (Z.div_mod m 8 ltac:(lia)) as Dm. pose proof (Z.mod_pos_bound m 8 ltac:(lia)) as Rm.
    pose proof (Z.div_mod n 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Rn.
    pose proof (div8_up n ltac:(lia)) as (Un0 & Un1).
    assert (MN : m / 8 <= n / 8) by (apply Z.div_le_mono; lia).
    assert (M0 : 0 <= m / 8) by (apply Z.div_pos; lia).
    split; [|split].
    + intros j Hj. apply TBY; [lia|left; lia|exact (Z0 j Hj)].
    + intros Hm8. apply TBY; [lia| |exact (P0 Hm8)].
      destruct (Z_lt_ge_dec (m / 8) (n / 8)) as [Lo|Hi]; [left; exact Lo|right]. split; [lia|]. lia.
    + intros j Hj. pose proof (div8_up m ltac:(lia)) as (Um0 & Um1).
      apply TBY; [destruct (Z.eq_dec (m mod 8) 0); lia| |exact (F0 j Hj)].
      destruct (Z.eq_dec (n mod 8) 0) as [E|E]; [left; rewrite (Un0 E) in Hj; lia|].
      rewrite (Un1 E) in Hj. destruct (Z_lt_ge_dec j (n / 8)) as [Lo|Hi]; [left; exact Lo|right; split; [lia|exact E]].
Qed.

Lemma shadow_tby_in u n j : 0 <= u -> u mod 8 = 0 -> 0 < n -> 0 <= j -> (j < n / 8 \/ (j = n / 8 /\ n mod 8 <> 0)) ->
  in_shadow_of u n (HeapIfaceA.S u + j).
Proof.
  intros Hu H8 Hn Hj0 Hj. unfold in_shadow_of, HeapIfaceA.S.
  pose proof (Z.div_mod u 8 ltac:(lia)) as DU. rewrite H8, Z.add_0_r in DU.
  pose proof (Z.div_mod n 8 ltac:(lia)) as DN. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as RN.
  assert (HI : u / 8 + j <= (u + n - 1) / 8) by (apply Z.div_le_lower_bound; lia).
  lia.
Qed.

Lemma shadow_blkR_frame u n : 0 <= u -> u mod 8 = 0 -> 0 < n ->
  (forall a, in_shadow_of u n a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> HAJ.shadow_blkR M u n -> HAJ.shadow_blkR M' u n.
Proof.
  intros Hu H8 Hn AG. apply shadow_blkR_tby; [exact Hn|]. intros j Hj0 Hj v Bt. unfold byte_at in *. rewrite AG; [exact Bt|].
  exact (shadow_tby_in u n j Hu H8 Hn Hj0 Hj).
Qed.

Lemma shadow_blk_frame u n : 0 <= u -> u mod 8 = 0 -> 0 < n ->
  (forall a, in_shadow_of u n a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> shadow_blk M u n -> shadow_blk M' u n.
Proof.
  intros Hu H8 Hn AG. apply shadow_blk_tby; [exact Hn|]. intros j Hj0 Hj v Bt. unfold byte_at in *. rewrite AG; [exact Bt|].
  exact (shadow_tby_in u n j Hu H8 Hn Hj0 Hj).
Qed.
End Laws.

Lemma shadow_blkR_bytes (M : word -> option byte) u n : 0 < n -> HAJ.shadow_blkR M u n ->
  forall i, 0 <= i -> (i < n / 8 \/ (i = n / 8 /\ n mod 8 <> 0)) -> exists v, byte_at M (HeapIfaceA.S u + i) v.
Proof.
  intros Hn [(Z0 & P0)|(m & Hm & Z0 & P0 & F0)] i Hi0 Hi.
  - destruct Hi as [Hi|(Ei & Hm')]; [eexists; exact (Z0 i ltac:(lia))|]. rewrite Ei. eexists. exact (P0 Hm').
  - pose proof (Z.div_mod m 8 ltac:(lia)) as Dm. pose proof (Z.mod_pos_bound m 8 ltac:(lia)) as Rm.
    pose proof (Z.div_mod n 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Rn.
    pose proof (div8_up m ltac:(lia)) as (Um0 & Um1). pose proof (div8_up n ltac:(lia)) as (Un0 & Un1).
    assert (MN : m / 8 <= n / 8) by (apply Z.div_le_mono; lia).
    destruct (Z_lt_ge_dec i (m / 8)) as [Lo|Hi']; [eexists; exact (Z0 i ltac:(lia))|].
    destruct (Z.eq_dec i (m / 8)) as [Ei|Ni].
    + destruct (Z.eq_dec (m mod 8) 0) as [E|E].
      * eexists. apply F0. rewrite (Um0 E). split; [lia|]. destruct (Z.eq_dec (n mod 8) 0) as [En|En]; [rewrite (Un0 En)|rewrite (Un1 En)]; lia.
      * rewrite Ei. eexists. exact (P0 E).
    + eexists. apply F0. split; [destruct (Z.eq_dec (m mod 8) 0) as [E|E]; [rewrite (Um0 E)|rewrite (Um1 E)]; lia|].
      destruct (Z.eq_dec (n mod 8) 0) as [En|En]; [rewrite (Un0 En)|rewrite (Un1 En)]; lia.
Qed.
