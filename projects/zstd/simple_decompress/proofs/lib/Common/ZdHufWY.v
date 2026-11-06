(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdSeqTable ZdSeqBuildThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun WStr STRW_tac FseWalkKit FseWalkMem ZdSeqBuildW ZdWalkKit ZdCellKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma u16s_nth_lo : forall (l : list Z) (k : nat), (k < length l)%nat ->
  nth_error (u16s (map (Z_to_bv 64) l)) (2 * k) = Some (Z_to_bv 8 (nth k l 0 mod 256)).
Proof.
  induction l as [|a l IH]; intros [|k] H; cbn [length] in H; try lia.
  - cbn [map u16s]. rewrite (le2_Z a a eq_refl). reflexivity.
  - cbn [map u16s]. rewrite (le2_Z a a eq_refl). replace (2 * S k)%nat with (S (S (2 * k))) by lia. cbn [zle2 map app nth_error nth].
    apply IH. lia.
Qed.
Lemma u16s_nth_hi : forall (l : list Z) (k : nat), (k < length l)%nat ->
  nth_error (u16s (map (Z_to_bv 64) l)) (2 * k + 1) = Some (Z_to_bv 8 ((nth k l 0 / 256) mod 256)).
Proof.
  induction l as [|a l IH]; intros [|k] H; cbn [length] in H; try lia.
  - cbn [map u16s]. rewrite (le2_Z a a eq_refl). reflexivity.
  - cbn [map u16s]. rewrite (le2_Z a a eq_refl). replace (2 * S k + 1)%nat with (S (S (2 * k + 1))) by lia. cbn [zle2 map app nth_error nth].
    apply IH. lia.
Qed.

(* [comment removed for export] *)
Lemma lor_disj_add : forall a b k, 0 <= k -> 0 <= b < 2^k -> 0 <= a -> Z.lor (a * 2^k) b = a * 2^k + b.
Proof.
  intros a b k Hk Hb Ha. rewrite <- Z.shiftl_mul_pow2 by lia.
  assert (L0 : Z.land (a ≪ k) b = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases n k) as [L|G]; [rewrite Z.shiftl_spec_low by lia; reflexivity|].
    destruct (Z.eq_dec b 0) as [->|NZ]; [rewrite Z.bits_0; apply andb_false_r|].
    rewrite (Z.bits_above_log2 b n); [apply andb_false_r | lia |].
    apply Z.lt_le_trans with k; [apply Z.log2_lt_pow2; lia | lia]. }
  rewrite <- Z.lxor_lor by exact L0. symmetry. apply Z.add_nocarry_lxor. exact L0.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma x2_t0_word : forall X B, 0 <= X -> 0 <= B < 4294967296 ->
  (Z.lor ((X ≪ 32) mod 18446744073709551616) B ≫ 16) mod 2^16 = (B / 65536) mod 2^16.
Proof.
  intros X B HX HB. rewrite Z.shiftl_mul_pow2 by lia.
  replace ((X * 2^32) mod 18446744073709551616) with ((X mod 4294967296) * 2^32)
    by (change 18446744073709551616 with (4294967296 * 2^32); rewrite Z.mul_mod_distr_r by lia; reflexivity).
  pose proof (Z.mod_pos_bound X 4294967296 ltac:(lia)) as HQ. remember (X mod 4294967296) as q eqn:EQ. clear EQ.
  rewrite lor_disj_add by (try lia; change (2^32) with 4294967296; lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2^32) with 4294967296. change (2^16) with 65536.
  Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Lemma x2_D_words : forall X, 0 <= X < 4294967296 ->
  let D := Z.lor ((X ≪ 32) mod 18446744073709551616) X in
  0 <= D < 18446744073709551616 /\ (D ≫ 16) mod 2^16 = X / 65536 /\ (D ≫ 48) mod 2^16 = X / 65536.
Proof.
  intros X HX D. subst D. rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (X * 2^32)) by (change (2^32) with 4294967296; lia).
  rewrite lor_disj_add by (try lia; change (2^32) with 4294967296; lia).
  rewrite !Z.shiftr_div_pow2 by lia. change (2^32) with 4294967296. change (2^16) with 65536. change (2^48) with 281474976710656.
  split; [lia|]. split; Z.div_mod_to_equations; lia.
Qed.
(* [comment removed for export] *)
Lemma x2_X_val : forall hi sy, 0 <= hi < 65536 -> 0 <= sy < 65536 ->
  Z.lor (hi * 65536) sy = hi * 65536 + sy /\ (hi * 65536 + sy) / 65536 = hi /\ 0 <= hi * 65536 + sy < 4294967296.
Proof.
  intros hi sy Hh Hs. change 65536 with (2^16) at 1. rewrite lor_disj_add by (try lia; change (2^16) with 65536; lia).
  change (2^16) with 65536. split; [reflexivity|]. split; [Z.div_mod_to_equations; lia | lia].
Qed.

(* [comment removed for export] *)
Lemma x2_X2_val : forall sv bsym tb, 0 <= sv < 256 -> 0 <= bsym < 256 -> 0 <= tb <= 12 ->
  Z.lor (sv ≪ 8) (tb * 65536 + bsym + 33554432) = (tb + 512) * 65536 + (sv * 256 + bsym).
Proof.
  intros sv bsym tb Hs Hb Ht. rewrite Z.shiftl_mul_pow2 by lia.
  replace (tb * 65536 + bsym + 33554432) with ((tb + 512) * 2^16 + bsym) by (change (2^16) with 65536; lia).
  rewrite <- (lor_disj_add (tb + 512) bsym 16) by (try lia; change (2^16) with 65536; lia).
  rewrite Z.lor_assoc, (Z.lor_comm (sv * 2^8)), <- Z.lor_assoc.
  rewrite (lor_disj_add sv bsym 8) by (try lia; change (2^8) with 256; lia).
  rewrite lor_disj_add by (try lia; change (2^8) with 256; change (2^16) with 65536; lia).
  change (2^16) with 65536. change (2^8) with 256. reflexivity.
Qed.

(* [comment removed for export] *)
Section Mem.
Variable segs : list Segment.

Lemma u16w_store_ok : forall m A (l : list Z) i a,
  u8arr segs m A (u16s (map (Z_to_bv 64) l)) -> 0 <= i < Z.of_nat (length l) -> a = wa (A + 2 * i) -> store_ok segs m a 2 = true.
Proof. intros m A l i a ARR Hi E. eapply (u16arr_store_ok segs m A _ i a ARR); [rewrite length_map; exact Hi | exact E]. Qed.

Lemma u16w_write : forall m A (l : list Z) i x v,
  u8arr segs m A (u16s (map (Z_to_bv 64) l)) -> 0 <= i < Z.of_nat (length l) -> x mod 2^16 = v mod 2^16 ->
  u8arr segs (write_to_mem m (wa (A + 2 * i)) (le2 (Z_to_bv 64 x))) A (u16s (map (Z_to_bv 64) (Zupd i v l))).
Proof.
  intros m A l i x v ARR Hi E.
  pose proof (u16arr_write segs m A _ i (Z_to_bv 64 x) ARR ltac:(rewrite length_map; exact Hi)) as H.
  rewrite (u16s_upd_Z l (Z.to_nat i) x v E) in H. exact H.
Qed.
End Mem.

(* [comment removed for export] *)
Ltac u16st ARR i v :=
  lazymatch type of ARR with u8arr ?segs ?mx ?A (u16s (map (Z_to_bv 64) ?l)) =>
    let a := cur_mem_addr in
    let SOK := fresh "SOK" in
    pose proof (u16w_store_ok segs mx A l i a ARR ltac:(rewrite ?Zupd_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK;
    zstep;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mx ?a2 (le2 (Z_to_bv 64 ?x))) _) =>
      replace (write_to_mem mx a2 (le2 (Z_to_bv 64 x))) with (write_to_mem mx (wa (A + 2 * i)) (le2 (Z_to_bv 64 x)))
        by (f_equal; unfold wa; f_equal; lia);
      let S2 := fresh "ARR" in
      assert (S2 : u8arr segs (write_to_mem mx (wa (A + 2 * i)) (le2 (Z_to_bv 64 x))) A (u16s (map (Z_to_bv 64) (Zupd i v l))));
      [ apply (u16w_write segs mx A l i x v ARR); [rewrite ?Zupd_length; lia | ]
      | clear ARR; store_done; rename S2 into ARR ]
    end
  end.
