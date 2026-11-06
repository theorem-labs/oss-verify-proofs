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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP15.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YClu YClp YCl2 YClq YClb YCl6 YCl7 YCl8 YCl3.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCjx YCjy YCjz YCk0 YCk1 YCk2 YCk5 YCkq.
Section a. Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis COLHASH : forall fx : YK11.FPState, @tcolhash_spec fx rc B.
Hypothesis AMEMSET : forall fx : YK11.FPState, @aintrin_realizes fx rc trbsegs B OSet A_asan_memset.
Hypothesis AFREE : forall fx : YK11.FPState, @afree_realizes fx rc trbsegs B.
Hypothesis AMEMCPY : forall fx : YK11.FPState, @aintrin_realizes fx rc trbsegs B OCpy A_asan_memcpy.
Lemma RH34 : forall n m, rga_fromA B ss_HT (fun _ => INV_HT B (S n) m) -> rga_fromA B ss_H2 (fun _ => INV_H2 B (S n) m).
Proof.
intros n m RHT.
assert (RH3 : rga_fromA B ss_H3 (fun _ => INV_H3 B (S n) m)) by (intros f0; exact (@rga_gH4 f0 rc B TL LAWS FFL (AMEMCPY f0) n m RHT)).
intros f0. exact (@rga_gH3 f0 rc B TL LAWS FFL (AMEMCPY f0) n m RH3).
Qed.
Lemma rga_RH_trip : forall n m, rga_fromA B ss_GX (fun _ => INV_GX B (S n)) ->
(forall m' : nat, m = S m' -> rga_fromA B ss_RH (fun _ => INV_RH B (S n) m')) -> rga_fromA B ss_RH (fun _ => INV_RH B (S n) m).
Proof.
intros n m RGX RRH.
assert (RHT : rga_fromA B ss_HT (fun _ => INV_HT B (S n) m)) by (intros f0; exact (@rga_gHT f0 rc B TL LAWS FFL n m RRH RGX)).
pose proof (RH34 n m RHT) as RH2.
assert (RH1 : rga_fromA B ss_H1 (fun _ => INV_H1 B (S n) m)) by (intros f0; exact (@rga_gH2 f0 rc B TL LAWS FFL (COLHASH f0) n m RH2)).
intros f0. exact (@rga_gH1 f0 rc B TL LAWS FFL n m RHT RH1).
Qed.
Lemma rga_RH_loop : forall n, rga_fromA B ss_GX (fun _ => INV_GX B (S n)) -> forall m, rga_fromA B ss_RH (fun _ => INV_RH B (S n) m).
Proof.
intros n RGX. induction m as [|m IH]; apply (rga_RH_trip n _ RGX); intros m' Hm'; [discriminate Hm' | injection Hm' as <-; exact IH].
Qed.
Theorem rga_chain_RG : forall n, rga_fromA B ss_TL (fun _ => INV_TL B (S n)) -> rga_fromA B ss_RG (fun _ => INV_RG B (S n)).
Proof.
intros n RTL.
pose proof (rga_chain_GX B TL LAWS ML FFL AFREE n RTL) as RGX.
assert (RG1 : rga_fromA B ss_G1 (fun _ => INV_G1 B (S n))) by (intros f0; exact (@rga_gG2 f0 rc B TL LAWS FFL (AMEMSET f0) n (rga_RH_loop n RGX))).
intros f0. exact (@rga_gG1 f0 rc B TL LAWS FFL n RG1).
Qed.
End a.
