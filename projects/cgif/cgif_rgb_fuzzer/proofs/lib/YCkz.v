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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP14 YP15 YCkr YCku YCkv YCkx.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCky.
Lemma g_U_zext3 : forall E a x, U E a = x -> 0 <= x < 2 ^ 30 -> U E (SAlu ALU_SRL (SMd M_MUL a (SLit 12884901888)) (SLit 32)) = 3 * x.
Proof.
intros Ez a x Ha Hx. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite Ha, !U_SLit.
change (Z.land (zcanon 32) 63) with 32. change (zcanon 12884901888) with (3 * 2 ^ 32).
change (2 ^ 30) with 1073741824 in Hx. change (2 ^ 32) with 4294967296.
rewrite (zcanon_id (x * (3 * 4294967296))) by (unfold M64; lia).
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 32) with 4294967296.
replace (x * (3 * 4294967296)) with ((3 * x) * 4294967296) by lia. rewrite Z.div_mul by lia.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma g_rh_kept_blk : forall Hh (m0 m' : word -> option byte) fq hh uu fn hn un p1 p2 Ht ent K entK Tn,
g_old3 (mrestrict Hh m0) fq hh uu Ht -> ht_inv Ht ent ->
cht_arrays trbsegs (mrestrict Hh m0) fn hn un p1 p2 K -> ht_inv K entK -> ht_T K = Tn ->
(forall b sz, In (b, sz) [(fq, 4 * ht_T Ht); (hh, 3 * ht_T Ht); (uu, ht_T Ht); (p1, 3 * Tn); (p2, 4 * Tn); (hn, 3 * Tn); (un, Tn); (fn, 4 * Tn)] -> rg_blk_kept Hh Hh m0 m' b sz) ->
g_old3 (mrestrict Hh m') fq hh uu Ht /\ cht_arrays trbsegs (mrestrict Hh m') fn hn un p1 p2 K.
Proof.
intros Hh m0 m' fq hh uu fn hn un p1 p2 Ht ent K entK Tn Hold Hinv HKarr HKinv HKT KB.
assert (KA : forall b sz, In (b, sz) [(fq, 4 * ht_T Ht); (hh, 3 * ht_T Ht); (uu, ht_T Ht); (p1, 3 * Tn); (p2, 4 * Tn); (hn, 3 * Tn); (un, Tn); (fn, 4 * Tn)] ->
forall a, b <= a < b + sz -> aview trbsegs Hh m' a = aview trbsegs Hh m0 a).
{ intros b sz Hb a Ha. replace a with (b + (a - b)) by lia. apply (KB b sz Hb). lia. }
split.
- apply (g_old3_kept Hh m0 m' fq hh uu Ht ent Hold Hinv). intros a [Ha | [Ha | Ha]];
[ apply (KA fq (4 * ht_T Ht)) | apply (KA hh (3 * ht_T Ht)) | apply (KA uu (ht_T Ht)) ]; first [exact Ha | cbn [In]; tauto].
- apply g_cht_of_arrs.
apply (g_arrs_kept Hh m0 m' fn hn un p1 p2 Tn _ _ _ _ _ (g_arrs_of_cht _ _ _ _ _ _ _ HKarr) ltac:(rewrite <- HKT; exact (g_lens_of_inv K _ HKinv))).
intros a Ha. unfold g_in5 in Ha. destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]];
[ apply (KA fn (4 * Tn)) | apply (KA hn (3 * Tn)) | apply (KA un Tn) | apply (KA p1 (3 * Tn)) | apply (KA p2 (4 * Tn)) ]; first [exact Ha | cbn [In]; tauto].
Qed.
Lemma g_rh_kept : forall Hh (m0 m' : word -> option byte) (P : Z -> Prop) fq hh uu fn hn un p1 p2 Ht ent K entK Tn,
g_old3 (mrestrict Hh m0) fq hh uu Ht -> ht_inv Ht ent ->
cht_arrays trbsegs (mrestrict Hh m0) fn hn un p1 p2 K -> ht_inv K entK -> ht_T K = Tn ->
(forall b sz, In (b, sz) [(fq, 4 * ht_T Ht); (hh, 3 * ht_T Ht); (uu, ht_T Ht); (p1, 3 * Tn); (p2, 4 * Tn); (hn, 3 * Tn); (un, Tn); (fn, 4 * Tn)] ->
forall a, b <= a < b + sz -> 0 <= a < 2 ^ 64 /\ ~ P a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview trbsegs Hh m' a = aview trbsegs Hh m0 a) ->
g_old3 (mrestrict Hh m') fq hh uu Ht /\ cht_arrays trbsegs (mrestrict Hh m') fn hn un p1 p2 K.
Proof.
intros Hh m0 m' P fq hh uu fn hn un p1 p2 Ht ent K entK Tn Hold Hinv HKarr HKinv HKT KOFF KP.
apply (g_rh_kept_blk Hh m0 m' fq hh uu fn hn un p1 p2 Ht ent K entK Tn Hold Hinv HKarr HKinv HKT).
intros b sz Hb i Hi. destruct (KOFF b sz Hb (b + i) ltac:(lia)) as [Hq1 Hq2]. exact (KP (b + i) Hq1 Hq2).
Qed.
