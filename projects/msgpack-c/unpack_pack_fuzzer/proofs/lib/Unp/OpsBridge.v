(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem State MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem St MemP.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module UB.
Section WithSegs.
Variable segs : list Segment.

Definition bmem_of (m : word -> option byte) : bmem :=
  fun a => if (0 <=? a) && (a <? two64) then option_map (fun b : byte => bv_unsigned b) (rb segs m a) else None.

Lemma bmem_of_in : forall m a, 0 <= a < two64 ->
  bmem_of m a = option_map (fun b : byte => bv_unsigned b) (rb segs m a).
Proof.
  intros m a Ha. unfold bmem_of. destruct (Z.leb_spec 0 a); destruct (Z.ltb_spec a two64); cbn [andb]; try reflexivity; lia.
Qed.

Lemma bmem_of_some : forall m a (b : byte), 0 <= a < two64 -> rb segs m a = Some b -> bmem_of m a = Some (bv_unsigned b).
Proof. intros m a b Ha Hb. rewrite (bmem_of_in m a Ha), Hb. reflexivity. Qed.

Lemma bmem_of_range : forall m a v, bmem_of m a = Some v -> 0 <= a < two64 /\ 0 <= v < 256.
Proof.
  intros m a v H. unfold bmem_of in H.
  destruct (Z.leb_spec 0 a); destruct (Z.ltb_spec a two64); cbn [andb] in H; try discriminate.
  destruct (rb segs m a) as [b|]; cbn [option_map] in H; [|discriminate]. injection H as <-.
  pose proof (bv_unsigned_in_range _ b) as R. change (bv_modulus 8) with 256 in R. lia.
Qed.

Lemma rdZ_of_zbytes : forall (bm : bmem) n a w k,
  0 <= k -> 0 <= w ->
  (forall i, 0 <= i < Z.of_nat n -> bm (a + i) = Some (zbyte w (k + i))) ->
  rdZ bm a n = Some ((w / 2 ^ (8 * k)) mod 2 ^ (8 * Z.of_nat n)).
Proof.
  intros bm n. induction n as [|n IH]; intros a w k Hk Hw H.
  - cbn [rdZ]. rewrite Z.mul_0_r, Z.pow_0_r, Z.mod_1_r. reflexivity.
  - cbn [rdZ]. rewrite <- (Z.add_0_r a) at 1. rewrite (H 0) by lia. rewrite Z.add_0_r.
    rewrite (IH (a + 1) w (k + 1)); [| lia | lia |].
    2:{ intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. replace (k + 1 + i) with (k + (1 + i)) by lia.
        apply H. rewrite Nat2Z.inj_succ. lia. }
    f_equal. unfold zbyte.
    set (u := w / 2 ^ (8 * k)).
    assert (Hu : 0 <= u) by (subst u; apply Z.div_pos; [lia| apply Z.pow_pos_nonneg; lia]).
    replace (w / 2 ^ (8 * (k + 1))) with (u / 256).
    2:{ subst u. replace (8 * (k + 1)) with (8 * k + 8) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
        assert (P : 0 < 2 ^ (8 * k)) by (apply Z.pow_pos_nonneg; lia).
        rewrite Z.div_div; [reflexivity| lia| lia]. }
    rewrite Nat2Z.inj_succ. replace (8 * Z.succ (Z.of_nat n)) with (8 + 8 * Z.of_nat n) by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
    rewrite Z.rem_mul_r by (try apply Z.pow_nonneg; lia).
    rewrite (Z.mul_comm 256 ((u / 256) mod 2 ^ (8 * Z.of_nat n))). reflexivity.
Qed.

Lemma rdZ_of_cell_bytes : forall m (v : word) (n : nat) a,
  0 <= a -> a + Z.of_nat n <= two64 ->
  (forall i, 0 <= i < Z.of_nat n -> rb segs m (a + i) = Some (byte_of v i)) ->
  rdZ (bmem_of m) a n = Some (bv_unsigned v mod 2 ^ (8 * Z.of_nat n)).
Proof.
  intros m v n a Ha Han H.
  pose proof (bv_unsigned_in_range _ v) as Rv.
  rewrite (rdZ_of_zbytes (bmem_of m) n a (bv_unsigned v) 0); [| lia | lia |].
  - rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r. reflexivity.
  - intros i Hi. rewrite Z.add_0_l.
    rewrite (bmem_of_some m (a + i) (byte_of v i)); [| lia | apply H; lia].
    f_equal. apply byte_of_zbyte. lia.
Qed.

Lemma u64_at_of_bytes : forall m a (v : word),
  0 <= a -> a + 8 <= two64 ->
  (forall i, 0 <= i < 8 -> rb segs m (a + i) = Some (byte_of v i)) ->
  u64_at (bmem_of m) a (bv_unsigned v).
Proof.
  intros m a v Ha H8 H. unfold u64_at.
  rewrite (rdZ_of_cell_bytes m v 8 a Ha ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ltac:(intros i Hi; apply H; cbn in Hi; lia)).
  f_equal. apply Z.mod_small. pose proof (bv_unsigned_in_range _ v) as R. rewrite bv_modulus_64, two64_eq in R.
  change (8 * Z.of_nat 8) with 64. lia.
Qed.

Lemma u32_at_of_bytes : forall m a (v : word),
  0 <= a -> a + 4 <= two64 ->
  (forall i, 0 <= i < 4 -> rb segs m (a + i) = Some (byte_of v i)) ->
  u32_at (bmem_of m) a (bv_unsigned v mod 2 ^ 32).
Proof.
  intros m a v Ha H4 H. unfold u32_at.
  rewrite (rdZ_of_cell_bytes m v 4 a Ha ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ltac:(intros i Hi; apply H; cbn in Hi; lia)).
  reflexivity.
Qed.

Lemma u8_at_of_bytes : forall m a (v : word),
  0 <= a -> a + 1 <= two64 ->
  (forall i, 0 <= i < 1 -> rb segs m (a + i) = Some (byte_of v i)) ->
  u8_at (bmem_of m) a (bv_unsigned v mod 2 ^ 8).
Proof.
  intros m a v Ha H1 H. unfold u8_at.
  rewrite (rdZ_of_cell_bytes m v 1 a Ha ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ltac:(intros i Hi; apply H; cbn in Hi; lia)).
  reflexivity.
Qed.

Lemma u64_at_of_cell : forall E m B c,
  cell_ok segs E m B c -> to_Z (c_w c) = 8 ->
  0 <= B + to_Z (c_idx c) -> B + to_Z (c_idx c) + 8 <= two64 ->
  u64_at (bmem_of m) (B + to_Z (c_idx c)) (bv_unsigned (den E (c_v c))).
Proof.
  intros E m B c (C1 & C2 & C3 & C4) Hw Hlo Hhi. apply u64_at_of_bytes; [exact Hlo| exact Hhi|].
  intros i Hi. apply C4. lia.
Qed.

Lemma u32_at_of_cell : forall E m B c,
  cell_ok segs E m B c -> to_Z (c_w c) = 4 ->
  0 <= B + to_Z (c_idx c) -> B + to_Z (c_idx c) + 4 <= two64 ->
  u32_at (bmem_of m) (B + to_Z (c_idx c)) (bv_unsigned (den E (c_v c)) mod 2 ^ 32).
Proof.
  intros E m B c (C1 & C2 & C3 & C4) Hw Hlo Hhi. apply u32_at_of_bytes; [exact Hlo| exact Hhi|].
  intros i Hi. apply C4. lia.
Qed.

Lemma u8_at_of_cell : forall E m B c,
  cell_ok segs E m B c -> to_Z (c_w c) = 1 ->
  0 <= B + to_Z (c_idx c) -> B + to_Z (c_idx c) + 1 <= two64 ->
  u8_at (bmem_of m) (B + to_Z (c_idx c)) (bv_unsigned (den E (c_v c)) mod 2 ^ 8).
Proof.
  intros E m B c (C1 & C2 & C3 & C4) Hw Hlo Hhi. apply u8_at_of_bytes; [exact Hlo| exact Hhi|].
  intros i Hi. apply C4. lia.
Qed.

Lemma readable_of_rb : forall m a n,
  0 <= a -> a + Z.of_nat n <= two64 ->
  (forall x, a <= x < a + Z.of_nat n -> rb segs m x <> None) ->
  readable (bmem_of m) a n.
Proof.
  intros m a n Ha Hn H. unfold readable. apply (proj2 (rdZ_some_iff (bmem_of m) a n)).
  intros i Hi. rewrite (bmem_of_in m (a + i)) by lia.
  destruct (rb segs m (a + i)) as [b|] eqn:R; cbn [option_map]; [discriminate|]. exfalso. apply (H (a + i)); [lia| exact R].
Qed.

Lemma readable_of_region : forall priv E m k r a n,
  region_ok segs priv E m k r -> PrimInt63.eqb k 0%uint63 = false ->
  bv_unsigned (ev E k) + loZ r <= a -> a + Z.of_nat n <= bv_unsigned (ev E k) + hiZ E r ->
  readable (bmem_of m) a n.
Proof.
  intros priv E m k r a n RO K Hlo Hhi.
  pose proof (ro_range _ _ _ _ _ _ RO K) as [R1 R2].
  apply readable_of_rb; [lia| lia|].
  intros x Hx. exact (proj1 (ro_valid _ _ _ _ _ _ RO K x ltac:(lia))).
Qed.

Lemma agree_on_of_overlay : forall m m' a n,
  (forall x, a <= x < a + n -> 0 <= x < two64 -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  agree_on (bmem_of m) (bmem_of m') a n.
Proof.
  intros m m' a n H x Hx. unfold bmem_of.
  destruct (Z.leb_spec 0 x); destruct (Z.ltb_spec x two64); cbn [andb]; try reflexivity.
  rewrite (rb_ext segs m m' x); [reflexivity|]. apply H; lia.
Qed.

Lemma readable_mono_of_overlay : forall m m',
  (forall x : word, m x <> None -> m' x <> None) ->
  readable_mono (bmem_of m) (bmem_of m').
Proof.
  intros m m' H. apply readable_mono_of_bytes. intros x. unfold bmem_of.
  destruct (Z.leb_spec 0 x); destruct (Z.ltb_spec x two64); cbn [andb]; try (intros C; exact C).
  rewrite !rb_unfold. specialize (H (Z_to_bv 64 x)).
  destruct (m (Z_to_bv 64 x)) as [b|]; destruct (m' (Z_to_bv 64 x)) as [b'|]; cbn [option_map];
    first [ intros _; discriminate
          | exfalso; apply H; [discriminate| reflexivity]
          | intros C; exact C ].
Qed.

Lemma outside_writes_agree : forall m m' (ws : list (Z * Z)),
  (forall x, 0 <= x < two64 -> Forall (fun w => x < fst w \/ fst w + snd w <= x) ws -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  forall x, Forall (outside x) ws -> bmem_of m' x = bmem_of m x.
Proof.
  intros m m' ws H x Hx. unfold bmem_of.
  destruct (Z.leb_spec 0 x); destruct (Z.ltb_spec x two64); cbn [andb]; try reflexivity.
  rewrite (rb_ext segs m m' x); [reflexivity|]. apply H; [lia|].
  eapply Forall_impl; [|exact Hx]. intros [lo k] Ho. unfold outside in Ho. cbn [fst snd] in *. lia.
Qed.

End WithSegs.
End UB.
