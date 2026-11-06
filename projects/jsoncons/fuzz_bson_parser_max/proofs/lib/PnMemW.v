(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec SeqExec L5Defs L5Core L5CoreKit.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNMW.

Lemma rdn_split segs M : forall n1 n2 (a : word) bs, rdn segs M a (n1 + n2) = Some bs ->
  rdn segs M a n1 = Some (take n1 bs) /\ rdn segs M (a + nat_to_word n1) n2 = Some (drop n1 bs).
Proof.
  induction n1 as [|n1 IH]; intros n2 a bs H.
  - cbn [Nat.add take drop rdn] in *. split; [reflexivity|].
    replace (a + nat_to_word 0)%bv with a; [exact H|]. apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, Z_to_bv_unsigned.
    unfold bv_wrap. cbn [Z.of_nat]. rewrite Zmod_0_l, Z.add_0_r. symmetry. apply Z.mod_small. apply bv_unsigned_in_range.
  - cbn [Nat.add rdn] in H |- *.
    destruct (match M a with Some b => Some b | None => seg_rom segs a end) as [b|]; [|discriminate].
    destruct (rdn segs M (a + 1) (n1 + n2)) as [rest|] eqn:E; [|discriminate]. injection H as <-.
    destruct (IH n2 (a + 1)%bv rest E) as (H1 & H2). rewrite H1. cbn [take drop]. split; [reflexivity|].
    replace (a + nat_to_word (S n1))%bv with (a + 1 + nat_to_word n1)%bv; [exact H2|].
    apply bv_eq. unfold nat_to_word. rewrite !bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
    rewrite Nat2Z.inj_succ. change (bv_unsigned (1 : bv 64)) with 1.
    change (bv_modulus 64) with (2 ^ 64). rewrite <- Zplus_mod. rewrite Zplus_mod_idemp_r. f_equal. lia.
Qed.

Lemma to_bv8_shiftr8 w k : 0 <= k -> Z_to_bv 8 (Z.shiftr w k) = Z_to_bv 8 (w / 2 ^ k).
Proof. intros Hk. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma le4_eq w : Z_to_le_bytes 4 w = [Z_to_bv 8 w; Z_to_bv 8 (w / 2 ^ 8); Z_to_bv 8 (w / 2 ^ 16); Z_to_bv 8 (w / 2 ^ 24)].
Proof.
  cbn [Z_to_le_bytes]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ]. rewrite !Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma le8_eq w : Z_to_le_bytes 8 w = [Z_to_bv 8 w; Z_to_bv 8 (w / 2 ^ 8); Z_to_bv 8 (w / 2 ^ 16); Z_to_bv 8 (w / 2 ^ 24);
                                     Z_to_bv 8 (w / 2 ^ 32); Z_to_bv 8 (w / 2 ^ 40); Z_to_bv 8 (w / 2 ^ 48); Z_to_bv 8 (w / 2 ^ 56)].
Proof.
  cbn [Z_to_le_bytes]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ]. rewrite !Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma to_bv8_mod w m k : 0 <= k -> 8 <= m - k -> Z_to_bv 8 ((w mod 2 ^ m) / 2 ^ k) = Z_to_bv 8 (w / 2 ^ k).
Proof.
  intros Hk Hm. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
  rewrite <- !Z.shiftr_div_pow2 by lia. rewrite <- !Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
  rewrite !Z.land_spec, !Z.shiftr_spec, Z.land_spec by lia.
  destruct (Z.ltb_spec i 8).
  - rewrite (Z.ones_spec_low m) by lia. rewrite andb_true_r. reflexivity.
  - rewrite (Z.ones_spec_high 8) by lia. rewrite !andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma le8_split w : 0 <= w < 2 ^ 64 ->
  word_to_le_bytes 8 (Z_to_bv 64 w) = word_to_le_bytes 4 (Z_to_bv 64 (w mod 2 ^ 32)) ++ word_to_le_bytes 4 (Z_to_bv 64 (w / 2 ^ 32)).
Proof.
  intros Hw. unfold word_to_le_bytes.
  assert (B1 : 0 <= w mod 2 ^ 32 < 2 ^ 64) by (pose proof (Z.mod_pos_bound w (2 ^ 32)); lia).
  assert (B2 : 0 <= w / 2 ^ 32 < 2 ^ 64) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  rewrite !L5.unsigned_lit by lia.
  rewrite le8_eq, !le4_eq. cbn [app].
  rewrite !(Z.div_div _ (2 ^ 32)) by lia.
  change (2 ^ 32 * 2 ^ 8) with (2 ^ 40). change (2 ^ 32 * 2 ^ 16) with (2 ^ 48). change (2 ^ 32 * 2 ^ 24) with (2 ^ 56).
  replace (w mod 2 ^ 32) with ((w mod 2 ^ 32) / 2 ^ 0) at 1 by (rewrite Z.pow_0_r, Z.div_1_r; reflexivity).
  rewrite !(to_bv8_mod w 32) by lia. rewrite Z.pow_0_r, Z.div_1_r. reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)

Lemma add4_lit p : 0 <= p -> p + 4 <= 2 ^ 64 -> (Z_to_bv 64 p + nat_to_word 4)%bv = Z_to_bv 64 (p + 4).
Proof.
  intros H0 H1. apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  change (Z.of_nat 4 mod 2 ^ 64) with 4. rewrite !(Z.mod_small p (2 ^ 64)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma u32_at_mod M a v : L5.u32_at segs M a (v mod 2 ^ 32) <-> L5.u32_at segs M a v.
Proof.
  unfold L5.u32_at, word_to_le_bytes. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite !le4_eq.
  replace ((v mod 2 ^ 32) mod 2 ^ 64) with ((v mod 2 ^ 64) mod 2 ^ 32).
  2:{ rewrite <- !Z.land_ones by lia. rewrite <- !Z.land_assoc. f_equal. }
  replace ((v mod 2 ^ 64) mod 2 ^ 32) with (((v mod 2 ^ 64) mod 2 ^ 32) / 2 ^ 0) at 1 by (rewrite Z.pow_0_r, Z.div_1_r; reflexivity).
  rewrite !(to_bv8_mod (v mod 2 ^ 64) 32) by lia. rewrite Z.pow_0_r, Z.div_1_r. reflexivity.
Qed.

Lemma u32_of_u64_lo M a w : 0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= w < 2 ^ 64 -> L5.u64_at segs M a w -> L5.u32_at segs M a (w mod 2 ^ 32).
Proof.
  intros Ha Ha8 Hw H. unfold L5.u64_at, L5.u32_at in *. rewrite (le8_split w Hw) in H.
  destruct (rdn_split segs M 4 4 (Z_to_bv 64 a) _ H) as (H1 & _). rewrite H1. f_equal.
Qed.

Lemma u32_of_u64_hi M a w : 0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= w < 2 ^ 64 -> L5.u64_at segs M a w -> L5.u32_at segs M (a + 4) (w / 2 ^ 32).
Proof.
  intros Ha Ha8 Hw H. unfold L5.u64_at, L5.u32_at in *. rewrite (le8_split w Hw) in H.
  destruct (rdn_split segs M 4 4 (Z_to_bv 64 a) _ H) as (_ & H2). rewrite add4_lit in H2 by lia. rewrite H2. f_equal.
Qed.

Lemma u64_of_u32x2 M a lo hi : 0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= lo < 2 ^ 32 -> 0 <= hi < 2 ^ 32 ->
  L5.u32_at segs M a lo -> L5.u32_at segs M (a + 4) hi -> L5.u64_at segs M a (lo + 4294967296 * hi).
Proof.
  intros Ha Ha8 Hlo Hhi H1 H2. unfold L5.u64_at, L5.u32_at in *.
  rewrite (le8_split (lo + 4294967296 * hi)) by lia.
  replace ((lo + 4294967296 * hi) mod 2 ^ 32) with lo.
  2:{ change (2 ^ 32) with 4294967296. replace (lo + 4294967296 * hi) with (lo + hi * 4294967296) by lia. rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
  replace ((lo + 4294967296 * hi) / 2 ^ 32) with hi.
  2:{ change (2 ^ 32) with 4294967296. replace (lo + 4294967296 * hi) with (hi * 4294967296 + lo) by lia. rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
  change 8%nat with (4 + 4)%nat. apply (SeqExec.rdn_app segs M 4 4); [exact H1|]. rewrite add4_lit by lia. exact H2.
Qed.

(* [comment removed for export] *)
Lemma u32_of_zeros M p n a : (forall i, 0 <= i < n -> M (Z_to_bv 64 (p + i)) = Some (Z_to_bv 8 0)) ->
  p <= a -> a + 4 <= p + n -> 0 <= p -> p + n <= 2 ^ 64 -> L5.u32_at segs M a 0.
Proof.
  intros Z0 H1 H2 H3 H4. unfold L5.u32_at.
  change (word_to_le_bytes 4 (Z_to_bv 64 0)) with (map (fun z => Z_to_bv 8 z) [0; 0; 0; 0]).
  change 4%nat with (length [0; 0; 0; 0]). apply (L5C.bytes_at_rdn segs M); [lia| cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi.
  replace (nth i [0; 0; 0; 0] 0) with 0 by (destruct i as [|[|[|[|i]]]]; [reflexivity..| cbn [length] in Hi; lia]).
  unfold L5.u8_at. cbn [rdn]. replace (a + Z.of_nat i) with (p + (a - p + Z.of_nat i)) by lia. rewrite Z0 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma u32_at_agree M M' a v : L5C.agree_on M M' a 4 -> 0 <= a -> a + 4 <= 2 ^ 64 -> L5.u32_at segs M a v -> L5.u32_at segs M' a v.
Proof. intros AG Ha H4 H. unfold L5.u32_at in *. rewrite (L5C.rdn_agree segs M M' 4 a Ha H4 AG). exact H. Qed.

End WithSegs.
End PNMW.
