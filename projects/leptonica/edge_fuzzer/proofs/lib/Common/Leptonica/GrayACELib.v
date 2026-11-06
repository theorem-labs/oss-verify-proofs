(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics MemImageType.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec StepTac MemSplit.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptArith.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma lor_small : forall a b n, 0 <= n -> 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= Z.lor a b < 2 ^ n.
Proof.
  intros a b n Hn Ha Hb. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lor a b) 0) as [E|NE]; [rewrite E; apply Z.pow_pos_nonneg; lia|].
  assert (P : 0 < Z.lor a b) by (pose proof (proj2 (Z.lor_nonneg a b) (conj (proj1 Ha) (proj1 Hb))); lia).
  apply Z.log2_lt_pow2; [exact P|]. rewrite Z.log2_lor by lia.
  destruct (Z.eq_dec a 0) as [->|Na]; [rewrite Z.lor_0_l in *; cbn [Z.log2]; rewrite Z.max_r by apply Z.log2_nonneg; apply Z.log2_lt_pow2; lia|].
  destruct (Z.eq_dec b 0) as [->|Nb]; [cbn [Z.log2]; rewrite Z.max_l by apply Z.log2_nonneg; apply Z.log2_lt_pow2; lia|].
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma v_or_Z : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> v_or (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.lor a b).
Proof. intros a b Ha Hb. unfold v_or. rewrite !u_Z2bv by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma wbytes_out_Z : forall (m : word -> option byte) (a n : Z) bs (x : word),
  Z.of_nat (length bs) = n -> 0 <= a < 2 ^ 64 -> a + n <= 2 ^ 64 -> ~ (a <= bv_unsigned x < a + n) -> wbytes m (Z_to_bv 64 a) bs x = m x.
Proof.
  intros m a n bs x Hl Ha Hn Hx. pose proof (bv_unsigned_in_range _ x) as Rx. unfold bv_modulus in Rx.
  apply MemSplit.wbytes_outside; rewrite u_Z2bv by lia; lia.
Qed.
