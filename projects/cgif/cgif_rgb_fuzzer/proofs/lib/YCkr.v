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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YCd0.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP14 YP15 YI0h YCph YCjr YCpj YCpm.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCl9.
Lemma g_denot_off : forall E n p c, ew E n = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 -> sv_denot E (SOff n c) = Z_to_bv 64 (p + c).
Proof. intros E n p c Hn Hp. cbn [sv_denot]. rewrite Hn, unsigned_lit_small by lia. reflexivity. Qed.
Lemma g_denot_off0 : forall E n p, ew E n = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 p.
Proof. intros E n p Hn Hp. rewrite (g_denot_off E n p 0 Hn Hp), Z.add_0_r. reflexivity. Qed.
Lemma g_mbyte_of_apresent : forall H (m : word -> option byte) a, apresent H m a -> exists b, mbyte trbsegs (mrestrict H m) a = Some b.
Proof.
intros H m a HP. destruct (mbyte trbsegs (mrestrict H m) a) as [b|] eqn:Eb; [exists b; reflexivity|].
exfalso. apply (aview_some_of_apresent trbsegs H m a HP). unfold aview. rewrite Eb. reflexivity.
Qed.
Lemma g_byte_of_av : forall H (m : word -> option byte) a v, aview trbsegs H m a = Some v -> mbyte trbsegs (mrestrict H m) a = Some (Z_to_bv 8 v).
Proof.
intros H m a v Hv. unfold aview in Hv. destruct (mbyte trbsegs (mrestrict H m) a) as [b|]; [|discriminate].
cbn [option_map] in Hv. injection Hv as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma g_blk {rc : YN05.RunCeil} : forall (B : asyms), AR_laws trbsegs B -> forall ly3 S3 W3 m3 md3 b n,
AR trbsegs B ly3 S3 W3 m3 md3 -> In (b, n) (ablocks B ly3 S3) -> 0 <= n ->
4096 <= b /\ b + n <= alloc_ceiling /\ b mod 16 = 0 /\ (forall a, b <= a < b + n -> apresent (w_H W3) m3 a).
Proof.
intros B LAWS ly3 S3 W3 m3 md3 b n HAR3 Hb Hn0. destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR3 Hb) as (Hb16 & Hb4096 & Hbceil & _ & Hbpres & _ & _).
pose proof (req_size_pos n Hn0) as [_ Hrq]. split; [exact Hb4096|]. split; [clear - Hbceil Hrq; lia|]. split; [exact Hb16|].
intros a Ha. apply (proj1 (Hbpres a ltac:(clear - Ha Hrq; lia))).
Qed.
Lemma g_empty_table : forall H (m : word -> option byte) fq hh uu pp xx T, 0 < T ->
(forall a, fq <= a < fq + 4 * T -> apresent H m a) -> (forall a, hh <= a < hh + 3 * T -> apresent H m a) ->
(forall a, pp <= a < pp + 3 * T -> apresent H m a) -> (forall a, xx <= a < xx + 4 * T -> apresent H m a) ->
(forall j, 0 <= j < T -> aview trbsegs H m (uu + j) = Some 0) ->
exists K0 : htab, ht_T K0 = T /\ ht_cnt K0 = 0 /\ cht_arrays trbsegs (mrestrict H m) fq hh uu pp xx K0 /\ ht_inv K0 [].
Proof.
intros H m fq hh uu pp xx T HT Pf Ph Pp Px Hz.
destruct (arr32_of_present trbsegs (mrestrict H m) fq (Z.to_nat T)) as (frN & AfrN & LfrN); [intros a Ha; apply g_mbyte_of_apresent; apply Pf; lia|].
destruct (arr8_of_present trbsegs (mrestrict H m) hh (Z.to_nat (3 * T))) as (keysN & AkN & LkN); [intros a Ha; apply g_mbyte_of_apresent; apply Ph; lia|].
destruct (arr8_of_present trbsegs (mrestrict H m) pp (Z.to_nat (3 * T))) as (palN & ApN & LpN); [intros a Ha; apply g_mbyte_of_apresent; apply Pp; lia|].
destruct (arr32_of_present trbsegs (mrestrict H m) xx (Z.to_nat T)) as (cixN & AcN & LcN); [intros a Ha; apply g_mbyte_of_apresent; apply Px; lia|].
assert (AuN : arr8 trbsegs (mrestrict H m) uu (repeat 0 (Z.to_nat T))) by (apply arr8_zero; intros j Hj; apply g_byte_of_av; exact (Hz j Hj)).
exists (mkHT frN keysN (repeat 0 (Z.to_nat T)) palN cixN 0 T). split; [reflexivity|]. split; [reflexivity|].
split; [exact (conj AfrN (conj AkN (conj AuN (conj ApN AcN))))|].
apply ht_empty_inv; [exact HT | unfold zlen; rewrite LfrN; lia | unfold zlen; rewrite LkN; lia | unfold zlen; rewrite LpN; lia | unfold zlen; rewrite LcN; lia
| exact (arr8_Forall _ _ _ _ AkN) | exact (arr8_Forall _ _ _ _ ApN)].
Qed.
Lemma g_pixel_at_kept : forall H (m m' : word -> option byte) p fmt c op,
pixel_at trbsegs (mrestrict H m) p fmt c op -> (fmt = 3 \/ fmt = 4) ->
(forall k, 0 <= k < fmt -> aview trbsegs H m' (p + k) = aview trbsegs H m (p + k)) -> pixel_at trbsegs (mrestrict H m') p fmt c op.
Proof.
intros H m m' p fmt c op ((B0 & B1 & B2 & Hc) & Hop) Hf K.
assert (K0 : aview trbsegs H m' p = aview trbsegs H m p) by (rewrite <- (Z.add_0_r p); apply K; lia).
split.
- split; [rewrite (mbyte_of_aview trbsegs H H m m' p K0); exact B0|].
split; [rewrite (mbyte_of_aview trbsegs H H m m' (p + 1) (K 1 ltac:(lia))); exact B1|].
split; [rewrite (mbyte_of_aview trbsegs H H m m' (p + 2) (K 2 ltac:(lia))); exact B2 | exact Hc].
- destruct Hop as [(E3 & Eo) | (E4 & a & Ba & Ra & Eo)]; [left; split; assumption|].
right. split; [exact E4|]. exists a. split; [rewrite (mbyte_of_aview trbsegs H H m m' (p + 3) (K 3 ltac:(lia))); exact Ba | split; assumption].
Qed.
Lemma g_av_of_mbyte : forall H (m : word -> option byte) a v, mbyte trbsegs (mrestrict H m) a = Some (Z_to_bv 8 v) -> 0 <= v < 256 -> aview trbsegs H m a = Some v.
Proof. intros H m a v Hb Hv. unfold aview. rewrite Hb. cbn [option_map]. f_equal. apply unsigned_lit_small8 || (rewrite Z_to_bv_unsigned; unfold bv_wrap; apply Z.mod_small; change (bv_modulus 8) with 256; lia). Qed.
Lemma g_col3_views : forall H (m : word -> option byte) a c, col3 trbsegs (mrestrict H m) a c ->
aview trbsegs H m (a + 0) = Some (cR c) /\ aview trbsegs H m (a + 1) = Some (cG c) /\ aview trbsegs H m (a + 2) = Some (cB c).
Proof.
intros H m a c (B0 & B1 & B2 & (R0 & R1 & R2)). rewrite Z.add_0_r.
split; [exact (g_av_of_mbyte H m _ _ B0 R0)|]. split; [exact (g_av_of_mbyte H m _ _ B1 R1) | exact (g_av_of_mbyte H m _ _ B2 R2)].
Qed.
Lemma g_bcmp3_iff : forall H (m : word -> option byte) a b c c', col3 trbsegs (mrestrict H m) a c -> col3 trbsegs (mrestrict H m) b c' ->
((forall i, 0 <= i < 3 -> aview trbsegs H m (a + i) = aview trbsegs H m (b + i)) <-> c = c').
Proof.
intros H m a b c c' Ha Hb. destruct (g_col3_views H m a c Ha) as (A0 & A1 & A2). destruct (g_col3_views H m b c' Hb) as (B0 & B1 & B2).
split.
- intros K. pose proof (K 0 ltac:(lia)) as K0. pose proof (K 1 ltac:(lia)) as K1. pose proof (K 2 ltac:(lia)) as K2.
rewrite A0, B0 in K0. rewrite A1, B1 in K1. rewrite A2, B2 in K2. injection K0 as K0. injection K1 as K1. injection K2 as K2.
apply colour_eqb_spec. unfold colour_eqb. rewrite K0, K1, K2, !Z.eqb_refl. reflexivity.
- intros <- i Hi. assert (Hc : i = 0 \/ i = 1 \/ i = 2) by lia. destruct Hc as [-> | [-> | ->]]; [rewrite A0, B0 | rewrite A1, B1 | rewrite A2, B2]; reflexivity.
Qed.
