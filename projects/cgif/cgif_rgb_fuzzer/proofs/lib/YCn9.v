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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCm2 YCqc YCjo YCly YClz YCqd YCqe YCqf YCea YP14.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCn4.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma m_mbyte_of_apresent : forall H (m : word -> option byte) a, apresent H m a -> exists b, mbyte trbsegs (mrestrict H m) a = Some b.
Proof.
intros H m a Hp. pose proof (aview_some_of_apresent trbsegs H m a Hp) as Hn. unfold aview in Hn.
destruct (mbyte trbsegs (mrestrict H m) a) as [b|]; [exists b; reflexivity | exfalso; apply Hn; reflexivity].
Qed.
Lemma m_pixel_of_present : forall segs (m : word -> option byte) p fmt,
(forall k, 0 <= k < fmt -> exists b, mbyte segs m (p + k) = Some b) -> (fmt = 3 \/ fmt = 4) ->
exists c op, pixel_at segs m p fmt c op.
Proof.
intros segs m p fmt Hp Hf.
destruct (Hp 0 ltac:(lia)) as [b0 B0]. destruct (Hp 1 ltac:(lia)) as [b1 B1]. destruct (Hp 2 ltac:(lia)) as [b2 B2].
rewrite Z.add_0_r in B0.
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1. pose proof (bv_unsigned_in_range 8 b2) as R2.
change (bv_modulus 8) with 256 in *.
exists (mkcol (bv_unsigned b0) (bv_unsigned b1) (bv_unsigned b2)).
assert (C3 : col3 segs m p (mkcol (bv_unsigned b0) (bv_unsigned b1) (bv_unsigned b2))).
{ unfold col3, colour_ok, cR, cG, cB, mkcol. cbn [fst snd]. rewrite !Z_to_bv_bv_unsigned. repeat split; assumption || lia. }
destruct Hf as [-> | ->].
- exists true. split; [exact C3 | left; split; reflexivity].
- destruct (Hp 3 ltac:(lia)) as [b3 B3]. pose proof (bv_unsigned_in_range 8 b3) as R3. change (bv_modulus 8) with 256 in R3.
exists (128 <=? bv_unsigned b3). split; [exact C3|]. right. split; [reflexivity|].
exists (bv_unsigned b3). rewrite Z_to_bv_bv_unsigned. split; [exact B3|]. split; [lia | reflexivity].
Qed.
Lemma m_s11_nobef : forall E na nb, ew E nb = Z_to_bv 64 0 ->
branch_taken BC_NE (sv_denot E (SAlu ALU_OR (SAlu ALU_SLTU (SLit 0) (SOff na 0)) (SAlu ALU_SLTU (SOff nb 0) (SLit 1)))) (sv_denot E (SLit 0)) = true.
Proof.
intros E na nb Hb. rewrite YO3v.branch_ne_U. apply negb_true_iff, Z.eqb_neq.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_SAlu E ALU_SLTU (SOff nb 0)). cbn [zalu_raw].
rewrite (U_atom E nb 0 Hb) by lia. rewrite !U_SLit. change (zcanon 1) with 1. change (zcanon 0) with 0. change (0 <? 1) with true. cbv iota.
rewrite (U_SAlu E ALU_SLTU (SLit 0)). cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0.
destruct (0 <? U E (SOff na 0)); vm_compute; discriminate.
Qed.
Lemma m_U_add0 : forall E a x, U E a = x -> U E (SAlu ALU_ADD a (SLit 0)) = x.
Proof.
intros E a x Hx. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hx, U_SLit. change (zcanon 0) with 0. rewrite Z.add_0_r. subst x.
apply zcanon_id. exact (U_range E a).
Qed.
End d.
