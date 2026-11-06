(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC1b YC2u
YC4u YC4z YC52 YC53 YC51.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YC05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j YCbj YCas YCat YCau YCbh YCbk YC7e YC7j YCbl YC6e YCav YC7f YCaw YCax YCay YCaz YC7g YCbm YCb0 YCb1 YCbn YCbi YCbo YC1c YCbe YP14 YP16 YI0f YI09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC8i YC8w.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma m_node_fields : forall (m : word -> option byte) a c0 c1 (n : tnode) leaf,
length (tn_mean n) = 3%nat -> obj_at trasegs m a LAY_Node (node_vals c0 c1 n leaf) ->
(forall d, 0 <= d <= 2 -> val_mem trasegs m (a + 16 + 8 * d) 8 (nth (Z.to_nat d) (tn_mean n) 0) /\ 0 <= nth (Z.to_nat d) (tn_mean n) 0 < 2 ^ 64) /\
(val_mem trasegs m (a + 40) 4 (tn_imin n) /\ 0 <= tn_imin n < 2 ^ 32) /\
(val_mem trasegs m (a + 44) 4 (tn_imax n) /\ 0 <= tn_imax n < 2 ^ 32) /\
(val_mem trasegs m (a + 48) 1 (tn_cut n) /\ 0 <= tn_cut n < 2 ^ 8) /\
(val_mem trasegs m (a + 49) 1 (tn_cidx n) /\ 0 <= tn_cidx n < 2 ^ 8) /\
(val_mem trasegs m (a + 50) 1 leaf /\ 0 <= leaf < 2 ^ 8).
Proof.
intros m a c0 c1 n leaf Hlen Ho.
unfold node_vals in Ho.
destruct (tn_mean n) as [|m0 [|m1 [|m2 [|]]]] eqn:Em; try discriminate Hlen. cbn [app] in Ho.
pose proof (obj_at_nth trasegs m a LAY_Node _ 2%nat (16, 8%N) m0 Ho eq_refl eq_refl) as F2.
pose proof (obj_at_nth trasegs m a LAY_Node _ 3%nat (24, 8%N) m1 Ho eq_refl eq_refl) as F3.
pose proof (obj_at_nth trasegs m a LAY_Node _ 4%nat (32, 8%N) m2 Ho eq_refl eq_refl) as F4.
pose proof (obj_at_nth trasegs m a LAY_Node _ 5%nat (40, 4%N) _ Ho eq_refl eq_refl) as F5.
pose proof (obj_at_nth trasegs m a LAY_Node _ 6%nat (44, 4%N) _ Ho eq_refl eq_refl) as F6.
pose proof (obj_at_nth trasegs m a LAY_Node _ 7%nat (48, 1%N) _ Ho eq_refl eq_refl) as F7.
pose proof (obj_at_nth trasegs m a LAY_Node _ 8%nat (49, 1%N) _ Ho eq_refl eq_refl) as F8.
pose proof (obj_at_nth trasegs m a LAY_Node _ 9%nat (50, 1%N) _ Ho eq_refl eq_refl) as F9.
unfold field_ok in *. cbn [fst snd N.to_nat Z.of_N Pos.to_nat Pos.iter_op Nat.add] in *.
split.
- intros d Hd. assert (d = 0 \/ d = 1 \/ d = 2) as [-> | [-> | ->]] by lia; cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add nth].
+ replace (a + 16 + 8 * 0) with (a + 16) by lia. exact F2.
+ replace (a + 16 + 8 * 1) with (a + 24) by lia. exact F3.
+ replace (a + 16 + 8 * 2) with (a + 32) by lia. exact F4.
- repeat split; first [apply F5 | apply F6 | apply F7 | apply F8 | apply F9].
Qed.
Lemma m_U_idx8_16 : forall E a x,
U E a = x -> 0 <= x < 2 ^ 16 -> U E (SAlu ALU_SRL (SAlu ALU_SLL a (SLit 48)) (SLit 45)) = 8 * x.
Proof.
intros E a x Hx Rx. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hx, !U_SLit.
change (Z.land (zcanon 48) 63) with 48. change (Z.land (zcanon 45) 63) with 45. rewrite Z.shiftl_mul_pow2 by lia.
rewrite (zcanon_id (x * 2 ^ 48)) by (unfold M64; change (2 ^ 16) with 65536 in *; change (2 ^ 48) with 281474976710656; lia).
rewrite Z.shiftr_div_pow2 by lia. replace (x * 2 ^ 48) with (8 * x * 2 ^ 45) by (change (2 ^ 48) with (8 * 2 ^ 45); lia).
rewrite Z.div_mul by (clear; lia). apply zcanon_id. unfold M64. change (2 ^ 16) with 65536 in *. lia.
Qed.
End b.
