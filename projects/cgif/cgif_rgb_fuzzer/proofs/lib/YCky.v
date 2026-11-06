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
Definition g_old3 (m : word -> option byte) (fq hh uu : Z) (Ht : htab) : Prop :=
arr32 trbsegs m fq (ht_frequ Ht) /\ arr8 trbsegs m hh (ht_keys Ht) /\ arr8 trbsegs m uu (ht_used Ht).
Lemma g_old3_of_arrs : forall m fq hh uu pp xx Ht,
g_arrs m fq hh uu pp xx (ht_frequ Ht) (ht_keys Ht) (ht_used Ht) (ht_pal Ht) (ht_colidx Ht) -> g_old3 m fq hh uu Ht.
Proof. intros m fq hh uu pp xx Ht (Af & Ak & Au & _ & _). exact (conj Af (conj Ak Au)). Qed.
Lemma g_old3_kept : forall H (m m' : word -> option byte) fq hh uu Ht ent,
g_old3 (mrestrict H m) fq hh uu Ht -> ht_inv Ht ent ->
(forall a, (fq <= a < fq + 4 * ht_T Ht \/ hh <= a < hh + 3 * ht_T Ht \/ uu <= a < uu + ht_T Ht) -> aview trbsegs H m' a = aview trbsegs H m a) ->
g_old3 (mrestrict H m') fq hh uu Ht.
Proof.
intros H m m' fq hh uu Ht ent (Af & Ak & Au) Hinv K.
destruct (g_lens_of_inv Ht ent Hinv) as (L1 & L2 & L3 & L4 & L5).
assert (KB : forall a, (fq <= a < fq + 4 * ht_T Ht \/ hh <= a < hh + 3 * ht_T Ht \/ uu <= a < uu + ht_T Ht) -> mbyte trbsegs (mrestrict H m') a = mbyte trbsegs (mrestrict H m) a)
by (intros a Ha; apply (mbyte_of_aview trbsegs); exact (K a Ha)).
unfold g_old3. split; [|split].
- apply (YI0c.arr32_frame trbsegs _ _ fq _ Af). intros a Ha. apply KB. rewrite L3 in Ha. left. exact Ha.
- apply (YI0c.arr8_frame trbsegs _ _ hh _ Ak). intros a Ha. apply KB. rewrite L2 in Ha. right. left. exact Ha.
- apply (YI0c.arr8_frame trbsegs _ _ uu _ Au). intros a Ha. apply KB. rewrite L1 in Ha. right. right. exact Ha.
Qed.
Definition g_sepON (fq hh uu T p1 p2 hn un fn Tn : Z) : Prop :=
forall bo so bn sn, In (bo, so) [(fq, 4 * T); (hh, 3 * T); (uu, T)] -> In (bn, sn) [(p1, 3 * Tn); (p2, 4 * Tn); (hn, 3 * Tn); (un, Tn); (fn, 4 * Tn)] ->
bo + so <= bn \/ bn + sn <= bo.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma g_sep8_of_AR : forall (B : asyms), AR_laws trbsegs B -> forall ly S W m md l0 fq hh uu T p1 p2 hn un fn Tn,
AR trbsegs B ly S W m md ->
Permutation (ablocks B ly S) (l0 ++ [(fq, 4 * T); (hh, 3 * T); (uu, T); (p1, 3 * Tn); (p2, 4 * Tn); (hn, 3 * Tn); (un, Tn); (fn, 4 * Tn)]) -> 0 < T -> 0 < Tn ->
g_sepON fq hh uu T p1 p2 hn un fn Tn /\ g_sep5 fn hn un p1 p2 Tn.
Proof.
intros B LAWS ly S W m md l0 fq hh uu T p1 p2 hn un fn Tn HAR HP HT HTn. split.
- intros bo so bn sn Ho Hn.
pose proof (rg_sep_app_in B LAWS ly S W m md (l0 ++ [(fq, 4 * T); (hh, 3 * T); (uu, T)]) [(p1, 3 * Tn); (p2, 4 * Tn); (hn, 3 * Tn); (un, Tn); (fn, 4 * Tn)] (bo, so) (bn, sn) HAR
ltac:(rewrite <- app_assoc; exact HP) ltac:(apply in_or_app; right; exact Ho) Hn) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D.
assert (Hso : 0 < so) by (cbn [In] in Ho; destruct Ho as [Q | [Q | [Q | []]]]; injection Q as _ <-; lia).
assert (Hsn : 0 < sn) by (cbn [In] in Hn; destruct Hn as [Q | [Q | [Q | [Q | [Q | []]]]]]; injection Q as _ <-; lia).
pose proof (req_size_pos so ltac:(lia)) as [_ R1]. pose proof (req_size_pos sn ltac:(lia)) as [_ R2]. lia.
- apply (g_sep5_of_AR B LAWS ly S W m md (l0 ++ [(fq, 4 * T); (hh, 3 * T); (uu, T)]) fn hn un p1 p2 Tn HAR); [|exact HTn].
eapply Permutation_trans; [exact HP|]. unfold cht_blocks. rewrite <- app_assoc. apply Permutation_app_head. YI0g.perm_tac.
Qed.
End b.
