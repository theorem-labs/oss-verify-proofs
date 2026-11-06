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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCk6 YCk7 YCk8 YCk9 YCka YCkb YCkc YCkd YCke.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCl9 YCla YClu YCle YClf YCl1 YClt YClr YCls YClc YCld YCkr YCks YCkt YCku YCkv YClv YClw.
Section a. Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis TGPV : forall fx : YK11.FPState, @tgpv_spec fx rc B.
Hypothesis ABCMP : forall fx : YK11.FPState, @abcmp_realizes fx rc trbsegs B A_bcmp_tra.
Hypothesis AMEMCPY : forall fx : YK11.FPState, @aintrin_realizes fx rc trbsegs B OCpy A_asan_memcpy.
Lemma rga_PB_loop : forall n, rga_fromA B ss_FD (fun _ => INV_FD B (S n)) -> forall m, rga_fromA B ss_PB (fun _ => INV_PB B (S n) m).
Proof.
intros n RFD. induction m as [|m IH]; intros f0; apply (@rga_gP2 f0 rc B TL LAWS FFL (ABCMP f0) n _ RFD); intros m' Hm';
[discriminate Hm' | injection Hm' as <-; exact IH].
Qed.
Lemma rga_HL_step : forall n, rga_fromA B ss_RS (fun _ => INV_RS B (S n)) -> rga_fromA B ss_HD (fun _ => INV_HD B) ->
rga_fromA B ss_HL (fun _ => INV_HL B n) -> rga_fromA B ss_HL (fun _ => INV_HL B (S n)).
Proof.
intros n RRS RHD RHL.
assert (RTL : rga_fromA B ss_TL (fun _ => INV_TL B (S n))) by (intros f0; exact (@rga_gP8 f0 rc B TL LAWS FFL n RHL RHD)).
assert (RRL : rga_fromA B ss_RL (fun _ => INV_RT B (S n))) by (intros f0; exact (@rga_gP7 f0 rc B TL LAWS FFL n RTL RRS)).
assert (RRT : rga_fromA B ss_RT (fun _ => INV_RT B (S n))) by (intros f0; exact (@rga_gP6 f0 rc B TL LAWS FFL n RTL RRL)).
assert (RM2 : rga_fromA B ss_M2 (fun _ => INV_M2 B (S n))) by (intros f0; exact (@rga_gP5 f0 rc B TL LAWS FFL (AMEMCPY f0) n RRT)).
assert (RM1 : rga_fromA B ss_M1 (fun _ => INV_M1 B (S n))) by (intros f0; exact (@rga_gP4 f0 rc B TL LAWS FFL (AMEMCPY f0) n RM2)).
assert (RFD : rga_fromA B ss_FD (fun _ => INV_FD B (S n))) by (intros f0; exact (@rga_gP3 f0 rc B TL LAWS FFL n RRT RM1)).
intros f0. exact (@rga_gP1 f0 rc B TL LAWS FFL (TGPV f0) n RTL (rga_PB_loop n RFD)).
Qed.


End a.
