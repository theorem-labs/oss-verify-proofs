(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import OblsLib InitClf.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP PlanS OL.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module OblsClf.

Lemma nth_last_word : forall (l : list word) w, nth (length l) (l ++ [w]) (Z_to_bv 64 0) = w.
Proof. intros l w. rewrite app_nth2, Nat.sub_diag by lia. reflexivity. Qed.
Lemma nth_last_byte : forall (l : list byte) b, nth (length l) (l ++ [b]) (Z_to_bv 8 0) = b.
Proof. intros l b. rewrite app_nth2, Nat.sub_diag by lia. reflexivity. Qed.

Section WithE.
  Variables (E : env).
  Hypothesis HPB : InitClf.PB_CLF (eb E).

  Lemma envp_word : forall (eptrs : list word) (q : Z),
    eb E 2%uint63 = flat_map word_le8 eptrs ++ word_le8 (Z_to_bv 64 0) ->
    bv_unsigned (ev E 64%uint63) = 8 * q -> 0 <= q <= Z.of_nat (length eptrs) ->
    den E (VBlob false 2%uint63 (VP 64%uint63 (wp 0%uint63)) 8%uint63) = nth (Z.to_nat q) (eptrs ++ [Z_to_bv 64 0]) (Z_to_bv 64 0).
  Proof.
    intros eptrs q Hb2 Hq Hr. apply (den_word_at E 2%uint63 _ (eptrs ++ [Z_to_bv 64 0]) (Z.to_nat q)).
    - rewrite Hb2, flat_map_app. reflexivity.
    - rewrite den_VP. change (to_Z 0%uint63) with 0. pose proof (u64_range (ev E 64%uint63)). rewrite Z.mod_small by lia. lia.
    - rewrite length_app. cbn [length]. lia.
  Qed.

  Lemma argv0_byte : forall (a : list byte),
    eb E 1%uint63 = a ++ [Z_to_bv 8 0] -> bv_unsigned (ev E 64%uint63) <= Z.of_nat (length a) ->
    den E (VExt false 0%uint63 1%uint63 (VBlob false 1%uint63 (VP 64%uint63 (wp 0%uint63)) 1%uint63))
    = Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (bv_unsigned (ev E 64%uint63))) (a ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))).
  Proof.
    intros a Hb1 Hr. pose proof (u64_range (ev E 64%uint63)) as Hu.
    apply den_ext1_byte.
    - apply (den_byte_at E 1%uint63 _ (a ++ [Z_to_bv 8 0]) _ Hb1).
      + rewrite den_VP. change (to_Z 0%uint63) with 0. rewrite Z.mod_small by lia. lia.
      + rewrite length_app. cbn [length]. lia.
    - pose proof (bv_unsigned_in_range _ (nth (Z.to_nat (bv_unsigned (ev E 64%uint63))) (a ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))) as Hb.
      unfold bv_modulus in Hb. exact Hb.
  Qed.
End WithE.

Section LP.
  Variables (E : env).
  Hypothesis HPB : InitClf.PB_CLF (eb E).

  Lemma lp_core : forall a,
    eb E 1%uint63 = a ++ [Z_to_bv 8 0] -> bv_unsigned (ev E 64%uint63) < Z.of_nat (length a) + 1 ->
    den E (VExt false 0%uint63 1%uint63 (VBlob false 1%uint63 (VP 64%uint63 (wp 0%uint63)) 1%uint63)) <> den E (VL (wp 0%uint63)) ->
    bv_unsigned (ev E 64%uint63) < Z.of_nat (length a).
  Proof.
    intros a Hb1 Hlt Hne. pose proof (u64_range (ev E 64%uint63)).
    destruct (Z.eq_dec (bv_unsigned (ev E 64%uint63)) (Z.of_nat (length a))) as [Heq|]; [exfalso|lia].
    apply Hne. rewrite (argv0_byte E a Hb1) by lia. rewrite Heq, Nat2Z.id, nth_last_byte.
    apply bv_eq. rewrite den_lit. reflexivity.
  Qed.

End LP.

End OblsClf.
