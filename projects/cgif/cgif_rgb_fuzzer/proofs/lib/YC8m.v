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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j YCbj YCas YCat YCau YCbh YCbk YC7e YC7j YCbl YC6e YCav YC7f YCaw YCax YCay YCaz YC7g YCbm YCb0 YCb1 YCbn YCbi YCbo YC1c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC8i.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma m_U_idx4 : forall E a x,
U E a = x -> 0 <= x < 2 ^ 32 -> U E (SAlu ALU_SRL (SAlu ALU_SLL a (SLit 32)) (SLit 30)) = 4 * x.
Proof.
intros E a x Hx Rx. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hx, !U_SLit.
change (Z.land (zcanon 32) 63) with 32. change (Z.land (zcanon 30) 63) with 30. rewrite Z.shiftl_mul_pow2 by lia.
rewrite (zcanon_id (x * 2 ^ 32)) by (unfold M64; change (2 ^ 32) with 4294967296 in *; lia).
rewrite Z.shiftr_div_pow2 by lia. replace (x * 2 ^ 32) with (4 * x * 2 ^ 30) by (change (2 ^ 32) with (4 * 2 ^ 30); lia).
rewrite Z.div_mul by lia. apply zcanon_id. unfold M64. change (2 ^ 32) with 4294967296 in Rx. lia.
Qed.
Lemma m_U_elem4 : forall E n b a x,
ew E n = Z_to_bv 64 b -> 0 <= b -> b + 4 * x < 2 ^ 64 -> U E a = x -> 0 <= x < 2 ^ 32 ->
U E (SAlu ALU_ADD (SOff n 0) (SAlu ALU_SRL (SAlu ALU_SLL a (SLit 32)) (SLit 30))) = b + 4 * x.
Proof.
intros E n b a x Hn Hb Hs Hx Rx. apply U_add_small_q; [apply (U_atom E n b Hn); lia | apply m_U_idx4; assumption | lia | lia | lia].
Qed.
Section d.
Variable B : asyms.
Lemma m_blk_kept_call0 : forall STK1 sp1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 b m,
ajournal trasegs B STK1 sp1 [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2) ->
rg_blk_kept (w_H W) (w_H W2) memc mem2 b (req_size m).
Proof.
intros STK1 sp1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 b m HJ1 Hin Hin2 i Hi.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
apply (G2 b m i Hin Hin2 Hi). intros Hf. exact (inFP_nil _ Hf).
Qed.
End d.
End c.
