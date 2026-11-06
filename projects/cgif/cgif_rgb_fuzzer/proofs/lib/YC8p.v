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
Lemma m_CLmem_kept : forall (H H' : word -> bool) (m m' : word -> option byte) pp dn F tail st tns,
m_CLmem H m pp dn F tail st tns ->
rg_blk_kept H H' m m' pp (zlen (pal_bytes (c_E st) ++ tail)) ->
rg_blk_kept H H' m m' dn (4 * zlen (fr_vals (c_E st))) ->
(forall j, 0 <= j < elen tns -> rg_blk_kept H H' m m' (tn_addr (tnth tns j)) NODE_SIZE) ->
rg_blk_kept H H' m m' (F + 32) (8 * elen tns) ->
m_CLmem H' m' pp dn F tail st tns.
Proof.
intros H H' m m' pp dn F tail st tns (A1 & A2 & A3 & A4) Kp Kd Kn Kl. unfold m_CLmem. split; [|split; [|split]].
- apply (arr8_frame trasegs _ _ pp _ A1). intros a Ha. apply (mbyte_of_aview trasegs). replace a with (pp + (a - pp)) by lia. apply Kp. lia.
- apply (arr32_frame trasegs _ _ dn _ A2). intros a Ha. apply (mbyte_of_aview trasegs). replace a with (dn + (a - dn)) by lia. apply Kd. lia.
- intros j Hj. apply (node_mem_frame trasegs _ _ _ _ j (A3 j Hj)). intros i Hi. apply (mbyte_of_aview trasegs). apply (Kn j Hj). exact Hi.
- intros j Hj. apply (rg_val_mem_blk_kept H H' m m' (F + 32) (8 * elen tns) _ 8 _ (A4 j Hj) Kl); [lia | cbn; lia].
Qed.
End b.
