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
Lemma g_val_mem_kept : forall H (m m' : word -> option byte) a n v,
val_mem trbsegs (mrestrict H m) a n v ->
(forall k, 0 <= k < Z.of_nat n -> aview trbsegs H m' (a + k) = aview trbsegs H m (a + k)) ->
val_mem trbsegs (mrestrict H m') a n v.
Proof. intros H m m' a n v Hv K k Hk. rewrite (mbyte_of_aview trbsegs H H m m' (a + Z.of_nat k) (K (Z.of_nat k) ltac:(lia))). exact (Hv k Hk). Qed.
Lemma g_arr8_setz : forall (m m' : word -> option byte) base l h v,
arr8 trbsegs m base l -> 0 <= h < zlen l -> 0 <= v < 256 ->
mbyte trbsegs m' (base + h) = Some (Z_to_bv 8 v) ->
(forall j, 0 <= j < zlen l -> j <> h -> mbyte trbsegs m' (base + j) = mbyte trbsegs m (base + j)) ->
arr8 trbsegs m' base (setz l h v).
Proof.
intros m m' base l h v Ha Hh Hv Hb Hk j Hjl. rewrite length_setz in Hjl.
assert (Hz : 0 <= Z.of_nat j < zlen l) by (unfold zlen; lia).
destruct (Z.eq_dec (Z.of_nat j) h) as [Ej | Ej].
- subst h. pose proof (getz_setz_same l (Z.of_nat j) v Hh) as G. unfold getz in G. rewrite Nat2Z.id in G. rewrite G. split; [exact Hb | exact Hv].
- pose proof (getz_setz_other l h (Z.of_nat j) v ltac:(lia) ltac:(lia) Ej) as G. unfold getz in G. rewrite Nat2Z.id in G. rewrite G.
rewrite (Hk (Z.of_nat j) Hz Ej). exact (Ha j ltac:(unfold zlen in Hz; lia)).
Qed.
Lemma g_arr32_setz : forall (m m' : word -> option byte) base l h v,
arr32 trbsegs m base l -> 0 <= h < zlen l -> 0 <= v < 2 ^ 32 ->
val_mem trbsegs m' (base + 4 * h) 4 v ->
(forall j, 0 <= j < zlen l -> j <> h -> forall k, 0 <= k < 4 -> mbyte trbsegs m' (base + 4 * j + k) = mbyte trbsegs m (base + 4 * j + k)) ->
arr32 trbsegs m' base (setz l h v).
Proof.
intros m m' base l h v Ha Hh Hv Hb Hk j Hjl. rewrite length_setz in Hjl.
assert (Hz : 0 <= Z.of_nat j < zlen l) by (unfold zlen; lia).
destruct (Z.eq_dec (Z.of_nat j) h) as [Ej | Ej].
- subst h. pose proof (getz_setz_same l (Z.of_nat j) v Hh) as G. unfold getz in G. rewrite Nat2Z.id in G. rewrite G. split; [exact Hb | exact Hv].
- pose proof (getz_setz_other l h (Z.of_nat j) v ltac:(lia) ltac:(lia) Ej) as G. unfold getz in G. rewrite Nat2Z.id in G. rewrite G.
destruct (Ha j ltac:(unfold zlen in Hz; lia)) as [A1 A2]. split; [|exact A2].
intros kk Hkk. rewrite (Hk (Z.of_nat j) Hz Ej (Z.of_nat kk) ltac:(lia)). exact (A1 kk Hkk).
Qed.
Lemma g_arr8_set_col : forall (m m' : word -> option byte) base l h (c : colour),
arr8 trbsegs m base l -> 0 <= h -> 3 * h + 3 <= zlen l -> col3 trbsegs m' (base + 3 * h) c ->
(forall j, 0 <= j < zlen l -> ~ (3 * h <= j < 3 * h + 3) -> mbyte trbsegs m' (base + j) = mbyte trbsegs m (base + j)) ->
arr8 trbsegs m' base (set_col l h c).
Proof.
intros m m' base l h c Ha Hh Hlen (B0 & B1 & B2 & (Rr & Rg & Rb)) Hk j Hjl.
assert (Hjl' : (j < length l)%nat) by (pose proof (zlen_set_col l h c) as X; unfold zlen in X; lia).
assert (Hz : 0 <= Z.of_nat j < zlen l) by (unfold zlen; lia).
pose proof (getz_set_col l h c (Z.of_nat j) Hh ltac:(lia) Hlen) as G. unfold getz in G. rewrite Nat2Z.id in G. rewrite G.
destruct (Z.eqb_spec (Z.of_nat j) (3 * h)) as [E0|N0]; [rewrite E0; split; [exact B0 | exact Rr]|].
destruct (Z.eqb_spec (Z.of_nat j) (3 * h + 1)) as [E1|N1]; [rewrite E1; split; [rewrite Z.add_assoc; exact B1 | exact Rg]|].
destruct (Z.eqb_spec (Z.of_nat j) (3 * h + 2)) as [E2|N2]; [rewrite E2; split; [rewrite Z.add_assoc; exact B2 | exact Rb]|].
rewrite (Hk (Z.of_nat j) Hz ltac:(lia)). exact (Ha j Hjl').
Qed.
Definition g_sep5 (fq hh uu pp xx T : Z) : Prop :=
(fq + 4 * T <= hh \/ hh + 3 * T <= fq) /\ (fq + 4 * T <= uu \/ uu + T <= fq) /\ (fq + 4 * T <= pp \/ pp + 3 * T <= fq) /\ (fq + 4 * T <= xx \/ xx + 4 * T <= fq) /\
(hh + 3 * T <= uu \/ uu + T <= hh) /\ (hh + 3 * T <= pp \/ pp + 3 * T <= hh) /\ (hh + 3 * T <= xx \/ xx + 4 * T <= hh) /\
(uu + T <= pp \/ pp + 3 * T <= uu) /\ (uu + T <= xx \/ xx + 4 * T <= uu) /\ (pp + 3 * T <= xx \/ xx + 4 * T <= pp).
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma g_sep5_of_AR : forall (B : asyms), AR_laws trbsegs B -> forall ly S W m md l0 fq hh uu pp xx T,
AR trbsegs B ly S W m md -> Permutation (ablocks B ly S) (l0 ++ cht_blocks fq hh uu pp xx T) -> 0 < T -> g_sep5 fq hh uu pp xx T.
Proof.
intros B LAWS ly S W m md l0 fq hh uu pp xx T HAR HP HT. unfold cht_blocks in HP.
assert (K : forall x y l, Permutation (l0 ++ [(fq, 4 * T); (hh, 3 * T); (uu, T); (pp, 3 * T); (xx, 4 * T)]) (x :: y :: l) ->
fst x + req_size (snd x) <= fst y \/ fst y + req_size (snd y) <= fst x).
{ intros x y l HP2. pose proof (sep_blocks_perm trbsegs B LAWS ly S W m md x y l HAR (Permutation_trans HP HP2)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. exact D. }
pose proof (req_size_pos (4 * T) ltac:(lia)) as [_ R4]. pose proof (req_size_pos (3 * T) ltac:(lia)) as [_ R3]. pose proof (req_size_pos T ltac:(lia)) as [_ R1].
unfold g_sep5.
repeat match goal with |- _ /\ _ => split end.
- pose proof (K (fq, 4 * T) (hh, 3 * T) (l0 ++ [(uu, T); (pp, 3 * T); (xx, 4 * T)]) ltac:(YI0g.perm_tac)) as D. cbn [fst snd] in D. lia.
- pose proof (K (fq, 4 * T) (uu, T) (l0 ++ [(hh, 3 * T); (pp, 3 * T); (xx, 4 * T)]) ltac:(YI0g.perm_tac)) as D. cbn [fst snd] in D. lia.
- pose proof (K (fq, 4 * T) (pp, 3 * T) (l0 ++ [(hh, 3 * T); (uu, T); (xx, 4 * T)]) ltac:(YI0g.perm_tac)) as D. cbn [fst snd] in D. lia.
- pose proof (K (fq, 4 * T) (xx, 4 * T) (l0 ++ [(hh, 3 * T); (uu, T); (pp, 3 * T)]) ltac:(YI0g.perm_tac)) as D. cbn [fst snd] in D. lia.
- pose proof (K (hh, 3 * T) (uu, T) (l0 ++ [(fq, 4 * T); (pp, 3 * T); (xx, 4 * T)]) ltac:(YI0g.perm_tac)) as D. cbn [fst snd] in D. lia.
- pose proof (K (hh, 3 * T) (pp, 3 * T) (l0 ++ [(fq, 4 * T); (uu, T); (xx, 4 * T)]) ltac:(YI0g.perm_tac)) as D. cbn [fst snd] in D. lia.
- pose proof (K (hh, 3 * T) (xx, 4 * T) (l0 ++ [(fq, 4 * T); (uu, T); (pp, 3 * T)]) ltac:(YI0g.perm_tac)) as D. cbn [fst snd] in D. lia.
- pose proof (K (uu, T) (pp, 3 * T) (l0 ++ [(fq, 4 * T); (hh, 3 * T); (xx, 4 * T)]) ltac:(YI0g.perm_tac)) as D. cbn [fst snd] in D. lia.
- pose proof (K (uu, T) (xx, 4 * T) (l0 ++ [(fq, 4 * T); (hh, 3 * T); (pp, 3 * T)]) ltac:(YI0g.perm_tac)) as D. cbn [fst snd] in D. lia.
- pose proof (K (pp, 3 * T) (xx, 4 * T) (l0 ++ [(fq, 4 * T); (hh, 3 * T); (uu, T)]) ltac:(YI0g.perm_tac)) as D. cbn [fst snd] in D. lia.
Qed.
End b.
Definition g_in5 (fq hh uu pp xx T a : Z) : Prop :=
fq <= a < fq + 4 * T \/ hh <= a < hh + 3 * T \/ uu <= a < uu + T \/ pp <= a < pp + 3 * T \/ xx <= a < xx + 4 * T.
Lemma g_cht_hit : forall H (m m' : word -> option byte) fq hh uu pp xx Ht h,
cht_arrays trbsegs (mrestrict H m) fq hh uu pp xx Ht ->
zlen (ht_used Ht) = ht_T Ht -> zlen (ht_keys Ht) = 3 * ht_T Ht -> zlen (ht_frequ Ht) = ht_T Ht -> zlen (ht_colidx Ht) = ht_T Ht -> zlen (ht_pal Ht) = 3 * ht_T Ht ->
g_sep5 fq hh uu pp xx (ht_T Ht) -> 0 <= h < ht_T Ht -> 0 <= freq Ht h + 1 < 2 ^ 32 ->
val_mem trbsegs (mrestrict H m') (fq + 4 * h) 4 (freq Ht h + 1) ->
(forall a, g_in5 fq hh uu pp xx (ht_T Ht) a -> ~ (fq + 4 * h <= a < fq + 4 * h + 4) -> aview trbsegs H m' a = aview trbsegs H m a) ->
cht_arrays trbsegs (mrestrict H m') fq hh uu pp xx (ht_hit Ht h).
Proof.
intros H m m' fq hh uu pp xx Ht h (Af & Ak & Au & Ap & Ax) L1 L2 L3 L4 L5 SEP Hh Hf Vn K.
unfold g_sep5 in SEP. destruct SEP as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
unfold cht_arrays, ht_hit. cbn [ht_frequ ht_keys ht_used ht_pal ht_colidx].
assert (KB : forall a, g_in5 fq hh uu pp xx (ht_T Ht) a -> ~ (fq + 4 * h <= a < fq + 4 * h + 4) -> mbyte trbsegs (mrestrict H m') a = mbyte trbsegs (mrestrict H m) a)
by (intros a Ha Hn; apply (mbyte_of_aview trbsegs); exact (K a Ha Hn)).
split; [|split; [|split; [|split]]].
- apply (g_arr32_setz _ _ fq (ht_frequ Ht) h _ Af); [rewrite L3; exact Hh | exact Hf | exact Vn |].
intros j Hj Hne k Hk. rewrite L3 in Hj. apply KB; [left; lia | lia].
- apply (arr8_frame trbsegs _ _ hh _ Ak). intros a Ha. rewrite L2 in Ha. apply KB; [right; left; lia | lia].
- apply (arr8_frame trbsegs _ _ uu _ Au). intros a Ha. rewrite L1 in Ha. apply KB; [right; right; left; lia | lia].
- apply (arr8_frame trbsegs _ _ pp _ Ap). intros a Ha. rewrite L5 in Ha. apply KB; [right; right; right; left; lia | lia].
- apply (arr32_frame trbsegs _ _ xx _ Ax). intros a Ha. rewrite L4 in Ha. apply KB; [right; right; right; right; lia | lia].
Qed.
Definition g_insW (fq hh uu pp xx h cnt a : Z) : Prop :=
hh + 3 * h <= a < hh + 3 * h + 3 \/ pp + 3 * cnt <= a < pp + 3 * cnt + 3 \/ a = uu + h \/ xx + 4 * h <= a < xx + 4 * h + 4 \/ fq + 4 * h <= a < fq + 4 * h + 4.

