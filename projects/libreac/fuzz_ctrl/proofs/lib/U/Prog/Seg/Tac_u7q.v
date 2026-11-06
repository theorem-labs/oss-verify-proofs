(* Helpers for segment Q05 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, batch u7): the 32-bit wrap of a small count
   (sext.w / addw of T57-T59), the room value of AF9 for blk + 8 (T56), a check over every byte value and the one-turn
   form of a code count. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem PropExec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLeaf.
Import ListNotations.
Open Scope Z_scope.

(* A value of int range is its own 32-bit signed wrap. *)
Lemma u7q_swrap : forall z, -2147483648 <= z < 2147483648 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_half_modulus, bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. Z.div_mod_to_equations. lia.
Qed.

(* sext.w of a small count. *)
Lemma u7q_sx : forall x, 0 <= x < 2147483648 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) + 0) = x.
Proof. intros x Hx. rewrite (MState.unsigned_lit x) by lia. rewrite Z.add_0_r. apply u7q_swrap. lia. Qed.

(* addw of a small count and a small increment. *)
Lemma u7q_addw : forall x y, 0 <= x -> 0 <= y -> x + y < 2147483648 ->
  bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) + y) = x + y.
Proof. intros x y H1 H2 H3. rewrite (MState.unsigned_lit x) by lia. apply u7q_swrap. lia. Qed.

(* AF9 for blk + 8: `li a4,-8; sub a5,a4,s7; sltiu a6,a5,-7; neg a6,a6; and a5,a6,a5` gives 2^64 - 8 - blk. *)
Lemma u7q_room : forall blk, 0 <= blk -> blk + 8 <= 2 ^ 64 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (v_sltiu (Z_to_bv 64 (18446744073709551608 -
      bv_unsigned (Z_to_bv 64 blk))) (-7))))) (bv_unsigned (Z_to_bv 64 (18446744073709551608 -
      bv_unsigned (Z_to_bv 64 blk))))) = Z_to_bv 64 (18446744073709551608 - blk).
Proof.
  intros blk H0 H1.
  unfold v_sltiu.
  rewrite (MState.unsigned_lit blk) by lia.
  rewrite (MState.unsigned_lit (18446744073709551608 - blk)) by lia.
  replace (bv_wrap 64 (-7)) with 18446744073709551609 by (vm_compute; reflexivity).
  rewrite (proj2 (Z.ltb_lt (18446744073709551608 - blk) 18446744073709551609)) by lia.
  cbv beta iota.
  rewrite (MState.unsigned_lit 1) by lia.
  replace (bv_unsigned (Z_to_bv 64 (0 - 1))) with (Z.ones 64) by (vm_compute; reflexivity).
  rewrite Z.land_comm, Z.land_ones by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.

(* A boolean fact checked for every byte value. *)
Lemma u7q_all : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall u, 0 <= u < 256 -> P u = true.
Proof.
  intros P H u Hu. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat u).
  split; [apply Z2Nat.id; lia | apply in_seq; lia].
Qed.

Lemma u7q_uzxb : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof.
  intros b. unfold zxb. apply MState.unsigned_lit. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

(* One more code of blk[8 ..) in a count. *)
Lemma u7q_cnt_S : forall f bs k,
  RcLeaf.cnt f bs (S k) =
  RcLeaf.cnt f bs k + (if f (bv_unsigned (nth (8 + k) bs (Z_to_bv 8 0))) then 1 else 0).
Proof. intros f bs k. reflexivity. Qed.
