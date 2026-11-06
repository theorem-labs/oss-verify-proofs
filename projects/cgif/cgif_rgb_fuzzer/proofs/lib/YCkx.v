(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCe9 YCfx YCi1 YCib YCie YCif YCid.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YP14.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YI0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCkr YCku YCkv.
Lemma g_arr8_copy : forall H H' (m m' : word -> option byte) b b' l, arr8 trbsegs (mrestrict H m) b l ->
(forall i, 0 <= i < zlen l -> aview trbsegs H' m' (b' + i) = aview trbsegs H m (b + i)) -> arr8 trbsegs (mrestrict H' m') b' l.
Proof.
intros H H' m m' b b' l Ha K j Hj. destruct (Ha j Hj) as [Hb Hr]. split; [|exact Hr].
apply g_byte_of_av. rewrite (K (Z.of_nat j) ltac:(unfold zlen; lia)). exact (g_av_of_mbyte H m _ _ Hb Hr).
Qed.
Lemma g_val_mem_copy : forall H H' (m m' : word -> option byte) a a' n v, val_mem trbsegs (mrestrict H m) a n v ->
(forall k, 0 <= k < Z.of_nat n -> aview trbsegs H' m' (a' + k) = aview trbsegs H m (a + k)) -> val_mem trbsegs (mrestrict H' m') a' n v.
Proof.
intros H H' m m' a a' n v Hv K k Hk. pose proof (Hv k Hk) as Hb.
assert (Hr : 0 <= bv_unsigned (Z_to_bv 8 (le_byte v n k)) < 256) by (pose proof (bv_unsigned_in_range _ (Z_to_bv 8 (le_byte v n k))) as X; change (bv_modulus 8) with 256 in X; exact X).
assert (Hav : aview trbsegs H m (a + Z.of_nat k) = Some (bv_unsigned (Z_to_bv 8 (le_byte v n k)))) by (unfold aview; rewrite Hb; reflexivity).
pose proof (K (Z.of_nat k) ltac:(lia)) as K1. rewrite Hav in K1.
pose proof (g_byte_of_av H' m' _ _ K1) as Hb'. rewrite Z_to_bv_bv_unsigned in Hb'. exact Hb'.
Qed.
Lemma g_arr32_copy : forall H H' (m m' : word -> option byte) b b' l, arr32 trbsegs (mrestrict H m) b l ->
(forall i, 0 <= i < 4 * zlen l -> aview trbsegs H' m' (b' + i) = aview trbsegs H m (b + i)) -> arr32 trbsegs (mrestrict H' m') b' l.
Proof.
intros H H' m m' b b' l Ha K j Hj. destruct (Ha j Hj) as [Hv Hr]. split; [|exact Hr].
apply (g_val_mem_copy H H' m m' (b + 4 * Z.of_nat j) (b' + 4 * Z.of_nat j) 4 _ Hv). intros k Hk.
rewrite <- !Z.add_assoc. apply K. unfold zlen. cbn in Hk. lia.
Qed.
Lemma g_arrs_move : forall H H' (m m' : word -> option byte) fq hh uu pp xx pp' xx' T lf lk lu lp lx,
g_arrs (mrestrict H m) fq hh uu pp xx lf lk lu lp lx -> g_lens T lf lk lu lp lx ->
(forall i, 0 <= i < 4 * T -> aview trbsegs H' m' (fq + i) = aview trbsegs H m (fq + i)) ->
(forall i, 0 <= i < 3 * T -> aview trbsegs H' m' (hh + i) = aview trbsegs H m (hh + i)) ->
(forall i, 0 <= i < T -> aview trbsegs H' m' (uu + i) = aview trbsegs H m (uu + i)) ->
(forall i, 0 <= i < 3 * T -> aview trbsegs H' m' (pp' + i) = aview trbsegs H m (pp + i)) ->
(forall i, 0 <= i < 4 * T -> aview trbsegs H' m' (xx' + i) = aview trbsegs H m (xx + i)) ->
g_arrs (mrestrict H' m') fq hh uu pp' xx' lf lk lu lp lx.
Proof.
intros H H' m m' fq hh uu pp xx pp' xx' T lf lk lu lp lx (Af & Ak & Au & Ap & Ax) (L1 & L2 & L3 & L4 & L5) Kf Kk Ku Kp Kx.
unfold g_arrs. split; [|split; [|split; [|split]]].
- apply (g_arr32_copy H H' m m' fq fq lf Af). intros i Hi. apply Kf. rewrite L3 in Hi. exact Hi.
- apply (g_arr8_copy H H' m m' hh hh lk Ak). intros i Hi. apply Kk. rewrite L2 in Hi. exact Hi.
- apply (g_arr8_copy H H' m m' uu uu lu Au). intros i Hi. apply Ku. rewrite L1 in Hi. exact Hi.
- apply (g_arr8_copy H H' m m' pp pp' lp Ap). intros i Hi. apply Kp. rewrite L5 in Hi. exact Hi.
- apply (g_arr32_copy H H' m m' xx xx' lx Ax). intros i Hi. apply Kx. rewrite L4 in Hi. exact Hi.
Qed.
Lemma g_lens_of_inv : forall Ht ent, ht_inv Ht ent -> g_lens (ht_T Ht) (ht_frequ Ht) (ht_keys Ht) (ht_used Ht) (ht_pal Ht) (ht_colidx Ht).
Proof. intros Ht ent ((L1 & L2 & L3 & L4 & L5) & _). unfold g_lens. repeat split; assumption. Qed.
