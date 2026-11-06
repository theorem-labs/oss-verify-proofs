(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdSeqTable ZdSeqBuildThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun WStr STRW_tac FseWalkKit FseWalkMem ZdSeqBuildW ZdWalkKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition smear32 (x : Z) : Z :=
  let a := Z.lor x (x ≫ 1) in let b := Z.lor a (a ≫ 2) in let c := Z.lor b (b ≫ 4) in
  let d := Z.lor c (c ≫ 8) in Z.lor d (d ≫ 16).

Lemma smear32_ok : forall x, 1 <= x < 524288 -> smear32 x = 2^(Z.log2 x + 1) - 1.
Proof.
  assert (B : forallb (fun x => smear32 x =? 2^(Z.log2 x + 1) - 1) (ZdSeqTable.zseq (Z.to_nat 524287) 1) = true) by (vm_compute; reflexivity).
  intros x Hx. rewrite forallb_forall in B. apply Z.eqb_eq. apply B. apply zseq_In_iff. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma lor_shr_lt : forall a j k, 0 <= a < 2^k -> 0 <= j -> 0 <= k -> 0 <= Z.lor a (a ≫ j) < 2^k.
Proof.
  intros a j k Ha Hj Hk.
  assert (S0 : 0 <= a ≫ j) by (apply Z.shiftr_nonneg; lia).
  assert (S1 : a ≫ j <= a) by (rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) Hj); Z.div_mod_to_equations; nia).
  split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lor a (a ≫ j)) 0) as [E|NE]; [rewrite E; apply Z.pow_pos_nonneg; lia|].
  apply Z.log2_lt_pow2; [pose proof (proj2 (Z.lor_nonneg a (a ≫ j)) (conj (proj1 Ha) S0)); lia|].
  rewrite Z.log2_lor by lia.
  destruct (Z.eq_dec a 0) as [->|NA]; [exfalso; apply NE; rewrite Z.shiftr_0_l; reflexivity|].
  assert (L1 : Z.log2 a < k) by (apply Z.log2_lt_pow2; lia).
  assert (L2 : Z.log2 (a ≫ j) <= Z.log2 a) by (apply Z.log2_le_mono; lia).
  lia.
Qed.

Lemma le4_cong : forall x v, x mod 2^32 = v mod 2^32 -> le4 (Z_to_bv 64 x) = le4 (Z_to_bv 64 v).
Proof. intros x v E. rewrite (le4_Z x v E), (le4_Z v v eq_refl). reflexivity. Qed.

Lemma u32s_upd_Z : forall (l : list Z) (i : nat) x v, x mod 2^32 = v mod 2^32 ->
  u32s (upd (map (Z_to_bv 64) l) i (Z_to_bv 64 x)) = u32s (map (Z_to_bv 64) (upd_nat i v l)).
Proof.
  induction l as [|a l IH]; intros [|i] x v E; cbn -[le4]; try reflexivity.
  - rewrite (le4_cong x v E). reflexivity.
  - rewrite (IH i x v E). reflexivity.
Qed.

Section Mem.
Variable segs : list Segment.

Lemma u32_znth : forall m A (l : list Z) i a,
  u32arr segs m A (map (Z_to_bv 64) l) -> 0 <= i < Z.of_nat (length l) -> a = wa (A + 4 * i) ->
  ov_read_bytes segs m a 4 = Some (le4 (Z_to_bv 64 (Znth i l))).
Proof.
  intros m A l i a ARR Hi ->. eapply (u32arr_read segs m A _ i); [exact ARR| | lia | reflexivity].
  apply nth_error_map_Znth. exact Hi.
Qed.

Lemma u32arr_upd_Z : forall m A (l : list Z) (i : nat) x v, x mod 2^32 = v mod 2^32 ->
  u32arr segs m A (upd (map (Z_to_bv 64) l) i (Z_to_bv 64 x)) -> u32arr segs m A (map (Z_to_bv 64) (upd_nat i v l)).
Proof.
  intros m A l i x v E [Hb Hw]. split.
  - rewrite <- (u32s_upd_Z l i x v E). exact Hb.
  - rewrite upd_length in Hw. rewrite length_map in *. rewrite upd_nat_length. exact Hw.
Qed.
End Mem.
