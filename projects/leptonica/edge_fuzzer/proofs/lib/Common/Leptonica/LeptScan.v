(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptArith2.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition pbit (W x : Z) : Z := (W / 2 ^ (31 - x mod 32)) mod 2.

Lemma pbit_range : forall W x, 0 <= pbit W x <= 1.
Proof. intros W x. unfold pbit. pose proof (Z.mod_pos_bound (W / 2 ^ (31 - x mod 32)) 2 ltac:(lia)). lia. Qed.

Lemma pbit_cases : forall W x, pbit W x = 0 \/ pbit W x = 1.
Proof. intros W x. pose proof (pbit_range W x). lia. Qed.

(* [comment removed for export] *)
Lemma not_mod32 : forall x, 0 <= x < 2 ^ 64 -> (2 ^ 64 - 1 - x) mod 32 = 31 - x mod 32.
Proof.
  intros x Hx. pose proof (Z.div_mod x 32 ltac:(lia)) as E. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as R.
  symmetry. apply (Z.mod_unique _ _ (2 ^ 59 - 1 - x / 32)); [left; lia|]. change (2 ^ 64) with (32 * 2 ^ 59). lia.
Qed.

(* [comment removed for export] *)
Lemma zx_sw32_mod32 : forall t, 0 <= t < 2 ^ 32 -> zx (sw32 t) mod 2 ^ 32 = t.
Proof.
  intros t Ht. destruct (Z_lt_ge_dec t (2 ^ 31)) as [Lo|Hi].
  - rewrite sw32_small by lia. rewrite zx_small by lia. apply Z.mod_small. lia.
  - assert (E : sw32 t = t - 2 ^ 32).
    { unfold sw32. replace (t + 2 ^ 31) with ((t + 2 ^ 31 - 2 ^ 32) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia. }
    rewrite E. rewrite zx_neg by lia. replace (t - 2 ^ 32 + 2 ^ 64) with (t + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma zx_sw32_mod2 : forall t, 0 <= t < 2 ^ 32 -> zx (sw32 t) mod 2 = t mod 2.
Proof.
  intros t Ht. pose proof (zx_sw32_mod32 t Ht) as E. rewrite <- E at 2.
  change (2 ^ 32) with (2 * 2 ^ 31). rewrite Z.rem_mul_r by lia.
  replace (zx (sw32 t) mod 2 + 2 * (zx (sw32 t) / 2 mod 2 ^ 31)) with (zx (sw32 t) mod 2 + (zx (sw32 t) / 2 mod 2 ^ 31) * 2) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pbit_val : forall W x, 0 <= W < 2 ^ 32 -> 0 <= x < 2 ^ 31 ->
  v_andi (v_srlw (v_lw (Z_to_bv 64 W)) (v_xori (Z_to_bv 64 x) (-1))) 1 = Z_to_bv 64 (pbit W x).
Proof.
  intros W x HW Hx. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as R.
  unfold v_andi, v_srlw, v_xori. rewrite v_lw_Z. rewrite !u_zbv.
  change (bv_wrap 64 (-1)) with (2 ^ 64 - 1). change (bv_wrap 64 1) with 1.
  rewrite (zx_small x) by lia.
  assert (EX : Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x).
  { change (2 ^ 64 - 1) with (Z.ones 64). rewrite (Z.sub_nocarry_ldiff (Z.ones 64) x).
    - apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec, Z.ldiff_spec.
      destruct (Z_lt_ge_dec n 64) as [Hlt|Hge].
      + rewrite Z.ones_spec_low by lia. destruct (Z.testbit x n); reflexivity.
      + rewrite Z.ones_spec_high by lia.
        assert (Hb : Z.testbit x n = false).
        { destruct (Z.eq_dec x 0) as [->|Hne]; [apply Z.bits_0|].
          apply Z.bits_above_log2; [lia|]. assert (Z.log2 x < 64) by (apply Z.log2_lt_pow2; lia). lia. }
        rewrite Hb. reflexivity.
    - destruct (Z.eq_dec x 0) as [->|Hne]; [apply Z.ldiff_0_l|].
      apply Z.ldiff_ones_r_low; [lia|]. apply Z.log2_lt_pow2; lia. }
  rewrite EX. rewrite (zx_small (2 ^ 64 - 1 - x)) by lia. rewrite (not_mod32 x) by lia.
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). rewrite (zx_sw32_mod32 W HW).
  rewrite Z.shiftr_div_pow2 by lia. rewrite sw32_eq.
  set (t := W / 2 ^ (31 - x mod 32)).
  assert (Ht : 0 <= t < 2 ^ 32).
  { subst t. assert (0 < 2 ^ (31 - x mod 32)) by (apply Z.pow_pos_nonneg; lia). split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; [lia|]. assert (1 <= 2 ^ (31 - x mod 32)) by lia. nia. }
  change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
  rewrite (zx_sw32_mod2 t Ht). unfold pbit. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mbyte (m : word -> option byte) (a : Z) : Z := match m (Z_to_bv 64 a) with Some b => bv_unsigned b | None => 0 end.
Definition mword (m : word -> option byte) (a : Z) : Z :=
  mbyte m a + 256 * (mbyte m (a + 1) + 256 * (mbyte m (a + 2) + 256 * mbyte m (a + 3))).

Lemma mbyte_range : forall m a, 0 <= mbyte m a < 256.
Proof. intros m a. unfold mbyte. destruct (m (Z_to_bv 64 a)) as [b|]; [| lia]. pose proof (bv_unsigned_in_range _ b) as R. change (bv_modulus 8) with 256 in R. lia. Qed.

Lemma mword_range : forall m a, 0 <= mword m a < 2 ^ 32.
Proof.
  intros m a. unfold mword. pose proof (mbyte_range m a). pose proof (mbyte_range m (a + 1)). pose proof (mbyte_range m (a + 2)). pose proof (mbyte_range m (a + 3)). lia.
Qed.

Lemma mword_ext : forall m m' a, (forall i, 0 <= i < 4 -> m' (Z_to_bv 64 (a + i)) = m (Z_to_bv 64 (a + i))) -> mword m' a = mword m a.
Proof.
  intros m m' a E. unfold mword, mbyte.
  pose proof (E 0 ltac:(lia)) as E0. rewrite Z.add_0_r in E0. rewrite E0, (E 1), (E 2), (E 3) by lia. reflexivity.
Qed.

Lemma byte_of_mbyte : forall m a b, m (Z_to_bv 64 a) = Some b -> Z_to_bv 8 (mbyte m a) = b.
Proof. intros m a b E. unfold mbyte. rewrite E. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma zbv8_low : forall x y, 0 <= x < 256 -> Z_to_bv 8 (x + 256 * y) = Z_to_bv 8 x.
Proof.
  intros x y Hx. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  replace (x + 256 * y) with (x + y * 256) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma shr8_low : forall x y, 0 <= x < 256 -> Z.shiftr (x + 256 * y) 8 = y.
Proof.
  intros x y Hx. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  replace (x + 256 * y) with (x + y * 256) by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma mword_bytes_at : forall m a, (forall i, 0 <= i < 4 -> m (Z_to_bv 64 (a + i)) <> None) -> bytes_at m a (Z_to_le_bytes 4 (mword m a)).
Proof.
  intros m a D.
  assert (G : forall k, 0 <= k < 4 -> exists b, m (Z_to_bv 64 (a + k)) = Some b).
  { intros k Hk. destruct (m (Z_to_bv 64 (a + k))) as [b|] eqn:E; [exists b; reflexivity | exfalso; exact (D k Hk E)]. }
  destruct (G 0 ltac:(lia)) as [b0 E0]. destruct (G 1 ltac:(lia)) as [b1 E1]. destruct (G 2 ltac:(lia)) as [b2 E2]. destruct (G 3 ltac:(lia)) as [b3 E3].
  rewrite Z.add_0_r in E0.
  pose proof (mbyte_range m a) as R0. pose proof (mbyte_range m (a + 1)) as R1. pose proof (mbyte_range m (a + 2)) as R2. pose proof (mbyte_range m (a + 3)) as R3.
  assert (EB : Z_to_le_bytes 4 (mword m a) = [b0; b1; b2; b3]).
  { unfold mword. cbn [Z_to_le_bytes]. repeat (rewrite ?zbv8_low, ?shr8_low by assumption).
    rewrite (byte_of_mbyte m a b0 E0), (byte_of_mbyte m (a + 1) b1 E1), (byte_of_mbyte m (a + 2) b2 E2), (byte_of_mbyte m (a + 3) b3 E3). reflexivity. }
  rewrite EB. intros i Hi. cbn [length] in Hi.
  assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
  destruct C as [->|[->|[->| ->]]]; [rewrite Z.add_0_r; exact E0 | exact E1 | exact E2 | exact E3].
Qed.
