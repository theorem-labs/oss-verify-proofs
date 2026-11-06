(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk MemSplit.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib GrayLib LeptExec DitherLib.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma dl_mulc : forall c x, 0 <= c -> 0 <= x -> c * x < 2 ^ 64 -> c < 2 ^ 64 -> x < 2 ^ 64 ->
  mul_div M_MUL (Z_to_bv 64 c) (Z_to_bv 64 x) = Z_to_bv 64 (c * x).
Proof. intros c x Hc Hx Hcx Hc2 Hx2. rewrite m_mul. unfold v_mul. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma dl_mulw : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= a * b < 2 ^ 31 ->
  sext 64 (mul_div M_MUL (low32 (Z_to_bv 64 a)) (low32 (Z_to_bv 64 b))) = Z_to_bv 64 (a * b).
Proof. intros a b Ha Hb Hab. rewrite w_mulw. apply zbv_mulw_small; assumption. Qed.

Lemma dl_sllw : forall a k, 0 <= a -> 0 <= k < 32 -> a * 2 ^ k < 2 ^ 31 ->
  sext 64 (alu32 ALU_SLL (low32 (Z_to_bv 64 a)) (low32 (Z_to_bv 64 k))) = Z_to_bv 64 (a * 2 ^ k).
Proof. intros a k Ha Hk Hs. rewrite w_sllw. apply ex_sllw_small; assumption. Qed.

(* [comment removed for export] *)
Lemma dl_srl32_eq : forall z q, z = 4294967296 * q -> 0 <= q < 2 ^ 32 ->
  alu64 ALU_SRL (Z_to_bv 64 z) (Z_to_bv 64 32) = Z_to_bv 64 q.
Proof.
  intros z q -> Hq. rewrite alu_srl. unfold v_srl. rewrite (u_Z2bv (4294967296 * q)) by lia. rewrite (u_Z2bv 32) by lia.
  change (32 mod 64) with 32. rewrite Z.shiftr_div_pow2 by lia. f_equal. change (2 ^ 32) with 4294967296.
  rewrite Z.mul_comm. apply Z.div_mul. lia.
Qed.

(* [comment removed for export] *)
Section WithSegs2.
Context {fx : FPState}.
Variable segs : list Segment.
Lemma mframe_wword0 : forall cells m m' (z : Z) (w : nat) (v : word),
  mframe cells m m' -> (0 <= z < 2 ^ 64 /\ z + Z.of_nat w <= 2 ^ 64) -> In (z, Z.of_nat w) cells ->
  mframe cells m (wbytes m' (Z_to_bv 64 z) (word_to_le_bytes w v)).
Proof. intros cells m m' z w v F [Hz Hw] I. exact (mframe_wword cells m m' z _ w v F eq_refl Hz Hw I). Qed.
Lemma dl_rdn_hit0 : forall m (z : Z) (w : nat) (v : word), (0 <= z < 2 ^ 64 /\ z + Z.of_nat w <= 2 ^ 64) ->
  rdn segs (wbytes m (Z_to_bv 64 z) (word_to_le_bytes w v)) (Z_to_bv 64 z) w = Some (word_to_le_bytes w v).
Proof. intros m z w v [Hz Hw]. exact (dl_rdn_hit segs m _ z w v eq_refl Hz Hw). Qed.
Lemma dl_rdn_skip0 : forall m (za z : Z) (w n : nat) (v : word) r,
  (0 <= za < 2 ^ 64 /\ za + Z.of_nat w <= 2 ^ 64 /\ 0 <= z < 2 ^ 64 /\ z + Z.of_nat n <= 2 ^ 64 /\ (z + Z.of_nat n <= za \/ za + Z.of_nat w <= z)) ->
  rdn segs m (Z_to_bv 64 z) n = r -> rdn segs (wbytes m (Z_to_bv 64 za) (word_to_le_bytes w v)) (Z_to_bv 64 z) n = r.
Proof. intros m za z w n v r (A & B & C & D & E) H. exact (dl_rdn_skip segs m _ za z w n v r eq_refl A B C D E H). Qed.
End WithSegs2.

(* [comment removed for export] *)
Lemma dl_slt_true : forall a b, 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 -> a < b -> alu64 ALU_SLT (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 1.
Proof.
  intros a b Ha Hb Hab. rewrite alu_slt. unfold v_slt, c_lts, bv_lts. rewrite !bv_signed_Zs by lia.
  destruct (Z.ltb_spec a b); [reflexivity | lia].
Qed.
Lemma dl_slt_false : forall a b, 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 -> b <= a -> alu64 ALU_SLT (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 0.
Proof.
  intros a b Ha Hb Hab. rewrite alu_slt. unfold v_slt, c_lts, bv_lts. rewrite !bv_signed_Zs by lia.
  destruct (Z.ltb_spec a b); [lia | reflexivity].
Qed.
Lemma dl_sltu0 : forall x, 0 < x < 2 ^ 64 -> alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 x) = Z_to_bv 64 1.
Proof.
  intros x Hx. rewrite alu_sltu. unfold v_sltu, c_ltu, bv_ltu. rewrite !u_Z2bv by lia. destruct (Z.ltb_spec 0 x); [reflexivity | lia].
Qed.
Lemma dl_xor11 : alu64 ALU_XOR (Z_to_bv 64 1) (Z_to_bv 64 1) = Z_to_bv 64 0.
Proof. apply bv_eq. reflexivity. Qed.
Lemma dl_xor01 : alu64 ALU_XOR (Z_to_bv 64 0) (Z_to_bv 64 1) = Z_to_bv 64 1.
Proof. apply bv_eq. reflexivity. Qed.
Lemma dl_negone : mul_div M_MUL (Z_to_bv 64 (-1)) (Z_to_bv 64 1) = Z_to_bv 64 (-1).
Proof. apply bv_eq. reflexivity. Qed.
Lemma dl_max0 : forall x, 0 < x < 2 ^ 63 ->
  alu64 ALU_AND (mul_div M_MUL (Z_to_bv 64 (-1)) (alu64 ALU_SLT (Z_to_bv 64 0) (Z_to_bv 64 x))) (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. rewrite dl_slt_true by lia. rewrite dl_negone, alu_and. unfold v_and. f_equal.
  rewrite (u_Z2bv x) by lia. change (bv_unsigned (Z_to_bv 64 (-1))) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma dl_seqz : forall x, 0 < x < 2 ^ 64 -> alu64 ALU_SLTU (Z_to_bv 64 x) (Z_to_bv 64 1) = Z_to_bv 64 0.
Proof.
  intros x Hx. rewrite alu_sltu. unfold v_sltu, c_ltu, bv_ltu. rewrite !u_Z2bv by lia. destruct (Z.ltb_spec x 1); [lia | reflexivity].
Qed.
Lemma dl_xor10 : alu64 ALU_XOR (Z_to_bv 64 1) (Z_to_bv 64 0) = Z_to_bv 64 1.
Proof. apply bv_eq. reflexivity. Qed.
Lemma dl_and3 : forall z, 0 <= z < 2 ^ 64 -> z mod 4 = 0 -> alu64 ALU_AND (Z_to_bv 64 z) (Z_to_bv 64 3) = Z_to_bv 64 0.
Proof.
  intros z Hz Hm. rewrite alu_and. unfold v_and. rewrite !u_Z2bv by lia. f_equal.
  change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact Hm.
Qed.
Lemma dl_al4 : forall a k, a mod 4 = 0 -> (a + 4 * k) mod 4 = 0.
Proof. intros a k H. rewrite Z.add_mod by lia. rewrite H. rewrite Z.mul_comm, Z_mod_mult. reflexivity. Qed.
