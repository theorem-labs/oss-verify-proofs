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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCkr YCku.
Definition g_arrs (m : word -> option byte) (fq hh uu pp xx : Z) (lf lk lu lp lx : list Z) : Prop :=
arr32 trbsegs m fq lf /\ arr8 trbsegs m hh lk /\ arr8 trbsegs m uu lu /\ arr8 trbsegs m pp lp /\ arr32 trbsegs m xx lx.
Definition g_lens (T : Z) (lf lk lu lp lx : list Z) : Prop := zlen lu = T /\ zlen lk = 3 * T /\ zlen lf = T /\ zlen lx = T /\ zlen lp = 3 * T.
Lemma g_arrs_of_cht : forall m fq hh uu pp xx H, cht_arrays trbsegs m fq hh uu pp xx H -> g_arrs m fq hh uu pp xx (ht_frequ H) (ht_keys H) (ht_used H) (ht_pal H) (ht_colidx H).
Proof. intros m fq hh uu pp xx H K. exact K. Qed.
Lemma g_cht_of_arrs : forall m fq hh uu pp xx H, g_arrs m fq hh uu pp xx (ht_frequ H) (ht_keys H) (ht_used H) (ht_pal H) (ht_colidx H) -> cht_arrays trbsegs m fq hh uu pp xx H.
Proof. intros m fq hh uu pp xx H K. exact K. Qed.

Lemma g_lens_keys : forall T lf lk lu lp lx h c, g_lens T lf lk lu lp lx -> g_lens T lf (set_col lk h c) lu lp lx.
Proof. intros T lf lk lu lp lx h c (A1 & A2 & A3 & A4 & A5). unfold g_lens. rewrite zlen_set_col. repeat split; assumption. Qed.
Lemma g_lens_pal : forall T lf lk lu lp lx i c, g_lens T lf lk lu lp lx -> g_lens T lf lk lu (set_col lp i c) lx.
Proof. intros T lf lk lu lp lx i c (A1 & A2 & A3 & A4 & A5). unfold g_lens. rewrite zlen_set_col. repeat split; assumption. Qed.
Lemma g_arrs_kept : forall H (m m' : word -> option byte) fq hh uu pp xx T lf lk lu lp lx,
g_arrs (mrestrict H m) fq hh uu pp xx lf lk lu lp lx -> g_lens T lf lk lu lp lx ->
(forall a, g_in5 fq hh uu pp xx T a -> aview trbsegs H m' a = aview trbsegs H m a) ->
g_arrs (mrestrict H m') fq hh uu pp xx lf lk lu lp lx.
Proof.
intros H m m' fq hh uu pp xx T lf lk lu lp lx (Af & Ak & Au & Ap & Ax) (L1 & L2 & L3 & L4 & L5) K.
assert (KB : forall a, g_in5 fq hh uu pp xx T a -> mbyte trbsegs (mrestrict H m') a = mbyte trbsegs (mrestrict H m) a)
by (intros a Ha; apply (mbyte_of_aview trbsegs); exact (K a Ha)).
unfold g_arrs. split; [|split; [|split; [|split]]].
- apply (arr32_frame trbsegs _ _ fq _ Af). intros a Ha. rewrite L3 in Ha. apply KB. left. lia.
- apply (arr8_frame trbsegs _ _ hh _ Ak). intros a Ha. rewrite L2 in Ha. apply KB. right; left. lia.
- apply (arr8_frame trbsegs _ _ uu _ Au). intros a Ha. rewrite L1 in Ha. apply KB. right; right; left. lia.
- apply (arr8_frame trbsegs _ _ pp _ Ap). intros a Ha. rewrite L5 in Ha. apply KB. right; right; right; left. lia.
- apply (arr32_frame trbsegs _ _ xx _ Ax). intros a Ha. rewrite L4 in Ha. apply KB. right; right; right; right. lia.
Qed.
Lemma g_arrs_keys : forall H (m m' : word -> option byte) fq hh uu pp xx T lf lk lu lp lx h c,
g_arrs (mrestrict H m) fq hh uu pp xx lf lk lu lp lx -> g_lens T lf lk lu lp lx -> g_sep5 fq hh uu pp xx T -> 0 <= h < T ->
col3 trbsegs (mrestrict H m') (hh + 3 * h) c ->
(forall a, g_in5 fq hh uu pp xx T a -> ~ (hh + 3 * h <= a < hh + 3 * h + 3) -> aview trbsegs H m' a = aview trbsegs H m a) ->
g_arrs (mrestrict H m') fq hh uu pp xx lf (set_col lk h c) lu lp lx.
Proof.
intros H m m' fq hh uu pp xx T lf lk lu lp lx h c (Af & Ak & Au & Ap & Ax) (L1 & L2 & L3 & L4 & L5) SEP Hh Ck K.
unfold g_sep5 in SEP. destruct SEP as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
assert (KB : forall a, g_in5 fq hh uu pp xx T a -> ~ (hh + 3 * h <= a < hh + 3 * h + 3) -> mbyte trbsegs (mrestrict H m') a = mbyte trbsegs (mrestrict H m) a)
by (intros a Ha Hn; apply (mbyte_of_aview trbsegs); exact (K a Ha Hn)).
unfold g_arrs. split; [|split; [|split; [|split]]].
- apply (arr32_frame trbsegs _ _ fq _ Af). intros a Ha. rewrite L3 in Ha. apply KB; [left; lia | lia].
- apply (g_arr8_set_col _ _ hh lk h c Ak); [lia | rewrite L2; lia | exact Ck |].
intros j Hj Hne. rewrite L2 in Hj. apply KB; [right; left; lia | lia].
- apply (arr8_frame trbsegs _ _ uu _ Au). intros a Ha. rewrite L1 in Ha. apply KB; [right; right; left; lia | lia].
- apply (arr8_frame trbsegs _ _ pp _ Ap). intros a Ha. rewrite L5 in Ha. apply KB; [right; right; right; left; lia | lia].
- apply (arr32_frame trbsegs _ _ xx _ Ax). intros a Ha. rewrite L4 in Ha. apply KB; [right; right; right; right; lia | lia].
Qed.
Lemma g_arrs_pal : forall H (m m' : word -> option byte) fq hh uu pp xx T lf lk lu lp lx i c,
g_arrs (mrestrict H m) fq hh uu pp xx lf lk lu lp lx -> g_lens T lf lk lu lp lx -> g_sep5 fq hh uu pp xx T -> 0 <= i < T ->
col3 trbsegs (mrestrict H m') (pp + 3 * i) c ->
(forall a, g_in5 fq hh uu pp xx T a -> ~ (pp + 3 * i <= a < pp + 3 * i + 3) -> aview trbsegs H m' a = aview trbsegs H m a) ->
g_arrs (mrestrict H m') fq hh uu pp xx lf lk lu (set_col lp i c) lx.
Proof.
intros H m m' fq hh uu pp xx T lf lk lu lp lx i c (Af & Ak & Au & Ap & Ax) (L1 & L2 & L3 & L4 & L5) SEP Hi Ck K.
unfold g_sep5 in SEP. destruct SEP as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
assert (KB : forall a, g_in5 fq hh uu pp xx T a -> ~ (pp + 3 * i <= a < pp + 3 * i + 3) -> mbyte trbsegs (mrestrict H m') a = mbyte trbsegs (mrestrict H m) a)
by (intros a Ha Hn; apply (mbyte_of_aview trbsegs); exact (K a Ha Hn)).
unfold g_arrs. split; [|split; [|split; [|split]]].
- apply (arr32_frame trbsegs _ _ fq _ Af). intros a Ha. rewrite L3 in Ha. apply KB; [left; lia | lia].
- apply (arr8_frame trbsegs _ _ hh _ Ak). intros a Ha. rewrite L2 in Ha. apply KB; [right; left; lia | lia].
- apply (arr8_frame trbsegs _ _ uu _ Au). intros a Ha. rewrite L1 in Ha. apply KB; [right; right; left; lia | lia].
- apply (g_arr8_set_col _ _ pp lp i c Ap); [lia | rewrite L5; lia | exact Ck |].
intros j Hj Hne. rewrite L5 in Hj. apply KB; [right; right; right; left; lia | lia].
- apply (arr32_frame trbsegs _ _ xx _ Ax). intros a Ha. rewrite L4 in Ha. apply KB; [right; right; right; right; lia | lia].
Qed.
Definition g_cells3 (fq uu xx h a : Z) : Prop := a = uu + h \/ xx + 4 * h <= a < xx + 4 * h + 4 \/ fq + 4 * h <= a < fq + 4 * h + 4.
Lemma g_arrs_cells3 : forall H (m m' : word -> option byte) fq hh uu pp xx T lf lk lu lp lx h v f,
g_arrs (mrestrict H m) fq hh uu pp xx lf lk lu lp lx -> g_lens T lf lk lu lp lx -> g_sep5 fq hh uu pp xx T -> 0 <= h < T -> 0 <= v < 2 ^ 32 -> 0 <= f < 2 ^ 32 ->
mbyte trbsegs (mrestrict H m') (uu + h) = Some (Z_to_bv 8 1) ->
val_mem trbsegs (mrestrict H m') (xx + 4 * h) 4 v -> val_mem trbsegs (mrestrict H m') (fq + 4 * h) 4 f ->
(forall a, g_in5 fq hh uu pp xx T a -> ~ g_cells3 fq uu xx h a -> aview trbsegs H m' a = aview trbsegs H m a) ->
g_arrs (mrestrict H m') fq hh uu pp xx (setz lf h f) lk (setz lu h 1) lp (setz lx h v).
Proof.
intros H m m' fq hh uu pp xx T lf lk lu lp lx h v f (Af & Ak & Au & Ap & Ax) (L1 & L2 & L3 & L4 & L5) SEP Hh Hv Hf Bu Vx Vf K.
unfold g_sep5 in SEP. destruct SEP as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
assert (KB : forall a, g_in5 fq hh uu pp xx T a -> ~ g_cells3 fq uu xx h a -> mbyte trbsegs (mrestrict H m') a = mbyte trbsegs (mrestrict H m) a)
by (intros a Ha Hn; apply (mbyte_of_aview trbsegs); exact (K a Ha Hn)).
unfold g_arrs. split; [|split; [|split; [|split]]].
- apply (g_arr32_setz _ _ fq lf h _ Af); [rewrite L3; exact Hh | exact Hf | exact Vf |].
intros j Hj Hne k Hk. rewrite L3 in Hj. apply KB; [left; lia | unfold g_cells3; lia].
- apply (arr8_frame trbsegs _ _ hh _ Ak). intros a Ha. rewrite L2 in Ha. apply KB; [right; left; lia | unfold g_cells3; lia].
- apply (g_arr8_setz _ _ uu lu h 1 Au); [rewrite L1; exact Hh | lia | exact Bu |].
intros j Hj Hne. rewrite L1 in Hj. apply KB; [right; right; left; lia | unfold g_cells3; lia].
- apply (arr8_frame trbsegs _ _ pp _ Ap). intros a Ha. rewrite L5 in Ha. apply KB; [right; right; right; left; lia | unfold g_cells3; lia].
- apply (g_arr32_setz _ _ xx lx h _ Ax); [rewrite L4; exact Hh | exact Hv | exact Vx |].
intros j Hj Hne k Hk. rewrite L4 in Hj. apply KB; [right; right; right; right; lia | unfold g_cells3; lia].
Qed.
Lemma g_col3_kept : forall H (m m' : word -> option byte) a c, col3 trbsegs (mrestrict H m) a c ->
(forall k, 0 <= k < 3 -> aview trbsegs H m' (a + k) = aview trbsegs H m (a + k)) -> col3 trbsegs (mrestrict H m') a c.
Proof.
intros H m m' a c (B0 & B1 & B2 & R) K. unfold col3.
pose proof (mbyte_of_aview trbsegs H H m m' (a + 0) (K 0 ltac:(lia))) as E0. rewrite Z.add_0_r in E0.
rewrite E0, (mbyte_of_aview trbsegs H H m m' (a + 1) (K 1 ltac:(lia))), (mbyte_of_aview trbsegs H H m m' (a + 2) (K 2 ltac:(lia))).
repeat split; try assumption; apply R.
Qed.
Lemma g_col3_copy : forall H (m m' : word -> option byte) x d c, col3 trbsegs (mrestrict H m) x c ->
(forall i, 0 <= i < 3 -> aview trbsegs H m' (d + i) = aview trbsegs H m (x + i)) -> col3 trbsegs (mrestrict H m') d c.
Proof.
intros H m m' x d c Hc K. destruct (g_col3_views H m x c Hc) as (A0 & A1 & A2). pose proof Hc as (_ & _ & _ & R).
pose proof (K 0 ltac:(lia)) as K0. pose proof (K 1 ltac:(lia)) as K1. pose proof (K 2 ltac:(lia)) as K2.
rewrite A0 in K0. rewrite A1 in K1. rewrite A2 in K2. rewrite Z.add_0_r in K0.
unfold col3. split; [exact (g_byte_of_av H m' _ _ K0)|]. split; [exact (g_byte_of_av H m' _ _ K1)|]. split; [exact (g_byte_of_av H m' _ _ K2) | exact R].
Qed.
