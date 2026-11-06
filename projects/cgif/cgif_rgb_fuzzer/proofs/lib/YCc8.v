(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC1b YC2u YC4o YC4q YC4h YC27 YC2r YC20 YC16 YC4u YC52 YCaq YCar YCct YCce YCcd YCc6 YCcb YCc9 YCca YCc7 YCc5 YC4z YCcc YCbq YCbr YCbs YCbt YCbu YCbv YCbw YCbx YCby YCbz YCc0 YCc1 YCc2 YCc3 YCc4.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YG0o YG0t YG0r YG0q YC00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : forall fx : YK11.FPState, @afree_realizes fx rc trasegs B.
Hypothesis AMEMSET : forall fx : YK11.FPState, @aintrin_realizes fx rc trasegs B OSet A_asan_memset.
Hypothesis ASM2 : forall fx : YK11.FPState, @astack_malloc_realizes fx rc trasegs B 2.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law trasegs B.
Hypothesis FFL : frame_flag_lawP trasegs B.
Hypothesis TRGBNEWGIF : forall fx : YK11.FPState, @trgb_newgif_spec fx rc B.
Hypothesis TRRFC : forall fx : YK11.FPState, @trrfc_spec fx rc B.
Hypothesis TRGBADD : forall fx : YK11.FPState, @trgb_addframe_specV fx rc B.
Hypothesis TRGBCLOSE : forall fx : YK11.FPState, @trgb_close_spec fx rc B.
Lemma rt_X_all : rt_fromA B ss_X (fun _ => INV_X B).
Proof. intros fx. eapply (@rt_X fx rc B); eassumption. Qed.
Lemma rt_H_all : rt_fromA B ss_H (fun _ => INV_H B).
Proof. intros fx. eapply (@rt_H fx rc B); try eassumption; [apply TRGBCLOSE | apply rt_X_all]. Qed.
Lemma rt_G_all : forall (m : nat) (c : Z), c <= Z.of_nat m -> rt_fromA B ss_G (fun _ => INV_G B c).
Proof.
induction m as [|m IH]; intros c Hcm fx.
- intros cx E k ly3 S3 W3 ms3 md3 _ _ _ _ _ HINV _. unfold INV_G, INV_GX in HINV. destruct HINV as (_ & _ & Hc & _). exfalso. clear - Hc Hcm. cbn in Hcm. lia.
- eapply (@rt_G1 fx rc B); try eassumption; [apply TRGBADD|].
intros fx2. eapply (@rt_G2 fx2 rc B); try eassumption; [apply AFREE|].
eapply (@rt_G3 fx2 rc B); try eassumption; [apply TRRFC | apply rt_H_all |].
apply IH. rewrite Nat2Z.inj_succ in Hcm. clear - Hcm. lia.
Qed.
Theorem tra_rlib : tra_rlibV_contract_all B.
Proof.
intros fx.
assert (RX : rt_from B ss_X (INV_X B)) by (apply rt_X_all).
assert (RH : rt_from B ss_H (INV_H B)) by (apply rt_H_all).
assert (RG : rt_from B ss_G (INV_G B 16)) by (apply (rt_G_all 16%nat 16); cbn; lia).
assert (RF : rt_from B ss_F (INV_F B)) by (eapply (@rt_F fx rc B); try eassumption; apply TRRFC).
assert (RE : rt_from B ss_E (INV_E B)) by (eapply (@rt_E fx rc B); try eassumption; apply TRGBNEWGIF).
assert (RD : rt_from B ss_D (INV_Bn B 14)) by (eapply (@rt_D fx rc B); eassumption).
assert (RB5 : rt_from B ss_B5 (INV_Bn B 12)) by (eapply (@rt_B5 fx rc B); eassumption).
assert (RB4 : rt_from B ss_B4 (INV_Bn B 8)) by (eapply (@rt_B4 fx rc B); eassumption).
assert (RB3 : rt_from B ss_B3 (INV_Bn B 4)) by (eapply (@rt_B3 fx rc B); eassumption).
assert (RB2 : rt_from B ss_B2 (INV_Bn B 2)) by (eapply (@rt_B2 fx rc B); eassumption).
assert (RB1 : rt_from B ss_B (INV_0 B 0)) by (eapply (@rt_B1 fx rc B); eassumption).
assert (RA2 : rt_from B ss_A2 (INV_0 B 0)) by (eapply (@rt_A2 fx rc B); try eassumption; apply AMEMSET).
eapply (@tra_rlib_A fx rc B); try eassumption. apply ASM2.
Qed.
End a.
