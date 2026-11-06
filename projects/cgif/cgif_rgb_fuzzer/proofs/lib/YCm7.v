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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCin YCi2 YCpi.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YCd0.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCm2 YCqc YCjo YCly YClz YCqd YCqe YCqf YCea YP14.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCn4 YCn5 YCn6 YCn7 YCn8 YCn9 YCna YCnf YCoi YCoj YCok YCol YCom YCon YCoo YCnd YCni YCnb.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCnk YCob YCm4 YCm5 YCmg YCmu YCmv YCmw YCmx YCmy YCm6.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCnn YCpd.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM02 YCj8.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCil YCim YP16 YI0f YI09 YCji.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YChh.
Section a. Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis AMEMCPY : forall fx : YK11.FPState, @aintrin_realizes fx rc trbsegs B OCpy A_asan_memcpy.
Hypothesis NTN2 : tntn_spec2V B.
Hypothesis RXT : rga_fromA B ss_XT (fun _ => INV_XT B).
Hypothesis RCX : rga_fromA B ss_CX (fun _ => INV_CX B).
Lemma rga_CLn_loop : forall n, rga_fromA B ss_CLn (fun _ => INV_CL B n).
Proof.
induction n as [|n IH].
{
intros f0 cx E k ly3 S3 W3 ms3 md3 _ _ _ _ _ HINV _. exfalso.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & dn & T & cnt & ent & tail & st & tns & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcinv & HL254 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmeas).
pose proof (cinv_counts cnt ent st Hcinv) as Hcc. cbv zeta in Hcc. destruct Hcc as (C1a & C1b & C1c & _).
clear - C1a C1b C1c HL254 Hmeas. lia. }
assert (RST : rga_fromA B ss_ST (fun _ => INV_ST B (S n))).
{ intros f1. apply (rga_ST1 B TL LAWS FFL NTN2 (S n)). intros f2. apply (rga_ST2 B TL LAWS FFL NTN2 (S n)).
intros f3. apply (rga_ST3a B TL LAWS FFL (S n) RXT). apply (rga_ST3b1 B TL LAWS FFL n). exact (rga_ST3b2 B TL LAWS FFL n IH RCX). }
intros f0. apply (rga_CL1a B TL LAWS FFL n). apply (rga_CL1b B TL LAWS FFL n (IH f0)). intros pm.
exact (rga_PL_loop B TL LAWS FFL AMEMCPY (S n) RST pm f0).
Qed.
Theorem rga_CL_loop : forall n, rga_fromA B ss_CL (fun _ => INV_CL B n).
Proof. intros n f0. exact (rga_CL_of_CLn B TL LAWS FFL n (rga_CLn_loop n)). Qed.
End a.
