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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCm2 YCqc YCjo YCly YCpm YCpo YCpq YClz YCqd YCqe YCpy YCq3 YCq4 YCq6 YCq5 YP14 YP15 YI0d YI0h YChh YCia YCm1 YCn4 YCn5 YCn6 YCn7 YCn8 YCn9 YCna YCnf YCoi YCoj YCok YCol YCom YCon YCoo YCop.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YCqg.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCps YCq7.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0f YCd3.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCkf YCkg YCkh YCki YCkj YCkk YCjt YCju YCjv YCjw.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCl9 YCla YClu YCle YClf YCl1 YClt YClr YCls YClg YClh YCli YClj YClk YCll YClp YClm YCln YClo YCkr YCks YCkt YCku YCkv YCkw YCkx YClv.
Section a. Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis AMALLOC : forall fx : YK11.FPState, @amalloc_realizes fx rc trbsegs B.
Hypothesis AFREE : forall fx : YK11.FPState, @afree_realizes fx rc trbsegs B.
Hypothesis AREALLOC : forall fx : YK11.FPState, @arealloc_realizes fx rc trbsegs B 0x533cc 0x53904.
Lemma rga_chain_RF : forall n, rga_fromA B ss_X38b (fun _ => INV_X38b B) -> rga_fromA B ss_RF (fun _ => INV_R5 B (S n)).
Proof.
intros n RX.
assert (R3 : rga_fromA B ss_RF3 (fun _ => INV_RF3 B (S n))) by (intros f0; exact (@rga_gF4 f0 rc B TL LAWS ML FFL (AFREE f0) n RX)).
assert (R2 : rga_fromA B ss_RF2 (fun _ => INV_RF2 B (S n))) by (intros f0; exact (@rga_gF3 f0 rc B TL LAWS ML FFL (AFREE f0) n R3)).
assert (R1 : rga_fromA B ss_RF1 (fun _ => INV_RF1 B (S n))) by (intros f0; exact (@rga_gF2 f0 rc B TL LAWS ML FFL (AFREE f0) n R2)).
intros f0. exact (@rga_gF1 f0 rc B TL LAWS FFL n R1).
Qed.
Theorem rga_chain_RS : forall n, rga_fromA B ss_X38b (fun _ => INV_X38b B) -> rga_fromA B ss_RG (fun _ => INV_RG B (S n)) ->
rga_fromA B ss_RS (fun _ => INV_RS B (S n)).
Proof.
intros n RX RG. pose proof (rga_chain_RF n RX) as RF.
assert (R5 : rga_fromA B ss_R5 (fun _ => INV_R5 B (S n))) by (intros f0; exact (@rga_gR6 f0 rc B TL LAWS FFL n RF RG)).
assert (R4 : rga_fromA B ss_R4 (fun _ => INV_R4 B (S n))) by (intros f0; exact (@rga_gR5 f0 rc B TL LAWS ML FFL (AMALLOC f0) n R5)).
assert (R3 : rga_fromA B ss_R3 (fun _ => INV_R3 B (S n))) by (intros f0; exact (@rga_gR4 f0 rc B TL LAWS ML FFL (AMALLOC f0) n R4)).
assert (R2 : rga_fromA B ss_R2 (fun _ => INV_R2 B (S n))) by (intros f0; exact (@rga_gR3 f0 rc B TL LAWS ML FFL (AMALLOC f0) n R3)).
assert (R1 : rga_fromA B ss_R1 (fun _ => INV_R1 B (S n))) by (intros f0; exact (@rga_gR2 f0 rc B TL LAWS ML FFL (AREALLOC f0) n R2)).
intros f0. exact (@rga_gR1 f0 rc B TL LAWS ML FFL (AREALLOC f0) n R1).
Qed.
End a.
