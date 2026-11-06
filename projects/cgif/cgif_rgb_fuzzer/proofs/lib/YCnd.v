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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCm2 YCqc YCjo YCly YClz YCqd YCqe YCqf YCea YP14 YP16 YI0f YI09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCn4.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma m_ent_ok : forall H ent, ht_inv H ent -> ent_ok ent.
Proof.
intros H ent Hinv. unfold ent_ok. apply Forall_forall. intros e He.
split; [exact (proj1 (Forall_forall _ _) (ent_colour_ok H ent Hinv) e He) | exact (proj1 (Forall_forall _ _) (ent_freq_pos H ent Hinv) e He)].
Qed.
Lemma m_ecol_palc : forall H ent, ht_inv H ent -> forall i, 0 <= i < ht_cnt H -> ecol ent i = palc H i.
Proof.
intros H ent Hinv i Hi. destruct (ent_slot H ent Hinv i Hi) as (h & _ & _ & He & Hpc & _).
unfold ecol, znth. rewrite (nth_error_nth _ _ _ He). cbn [fst]. symmetry. exact Hpc.
Qed.
Lemma m_pal_agrees : forall H ent, ht_inv H ent -> pal_agrees (ht_pal H) ent.
Proof.
intros H ent Hinv x Hx. destruct (inv_cnt H ent Hinv) as [Hlen Hc]. rewrite Hlen in Hx.
rewrite getz_pal_bytes_at by (rewrite Hlen; exact Hx).
pose proof (Z.div_mod x 3 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 3 ltac:(lia)) as Hm.
rewrite (m_ecol_palc H ent Hinv) by nia. unfold palc. rewrite comp_col_at by lia. f_equal. lia.
Qed.
Lemma m_pal_split : forall H ent, ht_inv H ent ->
pal_bytes ent ++ skipn (Z.to_nat (3 * ht_cnt H)) (ht_pal H) = ht_pal H.
Proof.
intros H ent Hinv. destruct (inv_cnt H ent Hinv) as [Hlen Hc].
pose proof Hinv as ((_ & _ & _ & _ & L5) & _).
assert (E1 : pal_bytes ent = firstn (Z.to_nat (3 * ht_cnt H)) (ht_pal H)).
{ apply getz_ext.
- rewrite pal_bytes_length, length_firstn. unfold elen in Hlen. unfold zlen in L5. lia.
- intros i Hi. rewrite zlen_pal_bytes, Hlen in Hi.
rewrite <- (m_pal_agrees H ent Hinv i) by (rewrite Hlen; exact Hi).
unfold getz. rewrite nth_firstn. destruct (Nat.ltb_spec (Z.to_nat i) (Z.to_nat (3 * ht_cnt H))); [reflexivity | lia]. }
rewrite E1. apply firstn_skipn.
Qed.
Lemma m_arr32_of_vals : forall segs (m : word -> option byte) b l,
(forall j, 0 <= j < zlen l -> val_mem segs m (b + 4 * j) 4 (getz l j)) ->
(forall j, 0 <= j < zlen l -> 0 <= getz l j < 2 ^ 32) -> arr32 segs m b l.
Proof.
intros segs m b l Hv Hr j Hj. unfold zlen, getz in *.
specialize (Hv (Z.of_nat j) ltac:(lia)). specialize (Hr (Z.of_nat j) ltac:(lia)). rewrite Nat2Z.id in Hv, Hr.
split; [exact Hv | exact Hr].
Qed.
Lemma m_fr_bounds : forall ent N j, ent_ok ent -> zsum (fr_vals ent) <= N -> 0 <= j < elen ent -> 1 <= getz (fr_vals ent) j <= N.
Proof.
intros ent N j Hok Hs Hj. rewrite getz_fr_vals by exact Hj.
pose proof (efreq_le_zsum ent j Hok Hj) as Hle.
assert (H1 : 1 <= efreq ent j).
{ unfold efreq, znth. unfold elen in Hj. pose proof (proj1 (Forall_forall _ _) Hok (nth (Z.to_nat j) ent dentry) ltac:(apply nth_In; lia)) as [_ Hf]. exact Hf. }
lia.
Qed.
End a.
