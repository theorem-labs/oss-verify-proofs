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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCq5 YP14.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCq8 YCqb YClx YCm2 YCqc YCjo YCly YClz YCqd YCqe YCq9 YCqf YCea YCjk.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCni YCm8 YCmt YCn4 YCn5 YCns YCma YCmb YCmc YCmd YCn6 YCoi YCo0 YCog YCmz YCn0 YCn7 YCmi YCmj YCn8 YCoj YCok YCnm YCm9 YCn9 YCna YCol YCo9 YCmr YCmq YCms YCmn YCmo YCmp YCnf YCnd YCom YCon YCoo YCni YCnb YCoh YCn1.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCil YCim.
Section a. Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis ASSF8 : forall fx : YK11.FPState, @aset_shadow_realizes fx rc trbsegs B A_set_shadow_f8 248.
Hypothesis ASF7 : forall fx : YK11.FPState, @astack_free_realizes fx rc trbsegs B A_stack_free_7 7.
Hypothesis AMALLOC : forall fx : YK11.FPState, @amalloc_realizes fx rc trbsegs B.
Hypothesis AFREE : forall fx : YK11.FPState, @afree_realizes fx rc trbsegs B.
Hypothesis AMEMCPY : forall fx : YK11.FPState, @aintrin_realizes fx rc trbsegs B OCpy A_asan_memcpy.
Hypothesis ADDFRAME : forall fx : YK11.FPState, @taddframe_specG fx rc B.
Hypothesis FREETREE : forall fx : YK11.FPState, @tfree_tree_specV fx rc B.
Hypothesis FREECHT : forall fx : YK11.FPState, @tfree_cht_spec fx rc B.
Hypothesis COLHASH : forall fx : YK11.FPState, @tcolhash_spec fx rc B.
Hypothesis ABCMP : forall fx : YK11.FPState, @abcmp_realizes fx rc trbsegs B A_bcmp_tra.
Hypothesis NTN2 : tntn_spec2V B.
Hypothesis ASS00 : forall fx : YK11.FPState, @aset_shadow_realizes fx rc trbsegs B A_set_shadow_00 0.
Lemma rga_exit_EPI2 : rga_fromFA B ss_EPI2 (fun _ => INV_X B).
Proof. intros fy. eapply rga_EPI2; eauto. Qed.
Theorem rga_chain_FIN : rga_fromA B ss_FIN (fun _ => INV_FIN B).
Proof.
intros f0. eapply rga_FIN0; eauto.
intros f1. eapply rga_FIN1; eauto.
intros f2. eapply rga_FIN2; eauto.
intros f3. eapply rga_FIN3; eauto using rga_exit_EPI2.
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
Theorem rga_chain_HD_mod_CR0 : rga_fromA B ss_CR0 (fun _ => INV_CR0 B) -> rga_fromA B ss_HD (fun _ => INV_HD B).
Proof.
intros RCR0 f0. eapply rga_Q0; eauto.
- intros f1. eapply rga_SM; eauto using rga_chain_SMT.
- intros f1. eapply rga_Q1; eauto using rga_chain_XC.
intros f2. eapply rga_DL; eauto.
Qed.
Theorem rga_chain_HD_mod_CL : (forall n, rga_fromA B ss_CL (fun _ => INV_CL B n)) -> rga_fromA B ss_HD (fun _ => INV_HD B).
Proof. intros RCL. apply rga_chain_HD_mod_CR0. intros f0. eapply rga_CR1; eauto using rga_chain_XD. Qed.
End a.
