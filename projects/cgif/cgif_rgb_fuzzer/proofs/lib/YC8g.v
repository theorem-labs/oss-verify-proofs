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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC5b YC4v YCar.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YC05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCbe YP14.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j YCbj YCas YCat YCau YCbh YCbk YC7e YC7j YCbl YC6e YCav YC7f YCaw YCax YCay YCaz YC7g YCbm YCb0 YCb1 YCbn YCbi YCbo YC1c YC6a.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC8i YC8j YC95 YC96 YC97 YC98 YC7q YC7r YC7s YC7t YC8k YC9t YC9d YC9e YC9f YC80 YC81 YC82 YC9r YC8d YC8e YC8l YC9g YC9c YC92 YC7y YC7z YC8m YC9u YC9v YC93 YC94 YC8z YC7p YC8n YC8o YC9w YC9i YC9j YC9h YC9k YC9l YC87 YC86 YC88 YC83 YC9m YC84 YC85 YC8t YC8r YC9x YC9y YC9z YC8w YC8p YC9s YC7o YC8f.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC59 YC5a.
Section a. Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis FFL : frame_flag_lawP trasegs B.
Hypothesis ASSF8 : forall fx : YK11.FPState, @aset_shadow_realizes fx rc trasegs B A_set_shadow_f8 248.
Hypothesis ASF7 : forall fx : YK11.FPState, @astack_free_realizes fx rc trasegs B A_stack_free_7 7.
Hypothesis AMALLOC : forall fx : YK11.FPState, @amalloc_realizes fx rc trasegs B.
Hypothesis AFREE : forall fx : YK11.FPState, @afree_realizes fx rc trasegs B.
Hypothesis AMEMCPY : forall fx : YK11.FPState, @aintrin_realizes fx rc trasegs B OCpy A_asan_memcpy.
Hypothesis ADDFRAME : forall fx : YK11.FPState, @taddframe_specG fx rc B.
Hypothesis FREETREE : forall fx : YK11.FPState, @tfree_tree_specV fx rc B.
Hypothesis FREECHT : forall fx : YK11.FPState, @tfree_cht_spec fx rc B.
Hypothesis COLHASH : forall fx : YK11.FPState, @tcolhash_spec fx rc B.
Hypothesis ABCMP : forall fx : YK11.FPState, @abcmp_realizes fx rc trasegs B A_bcmp_tra.
Hypothesis NTN2 : tntn_spec2V B.
Hypothesis ASS00 : forall fx : YK11.FPState, @aset_shadow_realizes fx rc trasegs B A_set_shadow_00 0.
Lemma rga_exit_EPI2 : rga_fromFA B ss_EPI2 (fun _ => INV_X B).
Proof. intros fy. eapply rga_EPI2; eauto. Qed.
Theorem rga_chain_FIN : rga_fromA B ss_FIN (fun _ => INV_FIN B).
Proof.
intros f0. eapply rga_FIN0; eauto.
intros f1. eapply rga_FIN1; eauto.
intros f2. eapply rga_FIN2; eauto.
intros f3. eapply rga_FIN3; eauto using rga_exit_EPI2.
Qed.
Theorem rga_chain_QE : rga_fromA B ss_QE (fun _ => INV_QE B).
Proof.
intros f0. eapply rga_QE1; eauto.
intros f1. eapply rga_QE2; eauto.
intros f2. eapply rga_QE3; eauto using rga_chain_FIN.
Qed.
Theorem rga_chain_XC : rga_fromA B ss_XC (fun _ => INV_XC B).
Proof.
intros f0. eapply rga_XC1; eauto.
intros f1. eapply rga_XC2; eauto using rga_exit_EPI2.
Qed.
Theorem rga_chain_SMT : rga_fromA B ss_SMT (fun _ => INV_SMT B).
Proof.
intros f0. eapply rga_SMT1; eauto.
intros f1. eapply rga_SMT2; eauto using rga_chain_FIN.
Qed.
Theorem rga_chain_XD : rga_fromA B ss_XD (fun _ => INV_XD B).
Proof. intros f0. eapply rga_XD; eauto using rga_chain_XC. Qed.
Theorem rga_chain_CR0 : (forall n, rga_fromA B ss_CL (fun _ => INV_CL B n)) -> rga_fromA B ss_CR0 (fun _ => INV_CR0 B).
Proof. intros RCL f0. eapply rga_CR1; eauto using rga_chain_XD. Qed.
Theorem rga_chain_HD : (forall n, rga_fromA B ss_CL (fun _ => INV_CL B n)) -> rga_fromA B ss_HD (fun _ => INV_HD B).
Proof.
intros RCL f0. eapply rga_Q0; eauto.
- intros f1. eapply rga_SM; eauto using rga_chain_SMT.
- intros f1. eapply rga_Q1; eauto using rga_chain_XC.
intros f2. eapply rga_DL; eauto using rga_chain_CR0.
Qed.
End a.
