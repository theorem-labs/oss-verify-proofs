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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP14.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCea.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCil YCim YCi7 YCia YCp4.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCns YCog YCoh YCnn YCo0 YCpd YCpe YCn2.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCmk YCml YCmm.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCor YCos YCot YCou YCov YCow YCox YCoy YCoz YCp0.
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
Hypothesis GETPAL : forall fx : YK11.FPState, @tgetpal_specB fx rc B.
Hypothesis GLNI : forall fx : YK11.FPState, @tglni_spec fx rc B.
Hypothesis ROLC : trb_rol_const B.
Theorem rga_chain_QE : rga_fromA B ss_QE (fun _ => INV_QE B).
Proof.
intros f0. eapply rga_QE1; eauto.
intros f1. eapply rga_QE2; eauto.
intros f2. eapply rga_QE3; eauto using rga_chain_FIN.
Qed.
Theorem rga_chain_XT2 : rga_fromA B ss_XT2 (fun _ => INV_XT2 B).
Proof. intros f0. eapply rga_qXT2; eauto using rga_chain_XC. Qed.
Theorem rga_chain_XT : rga_fromA B ss_XT (fun _ => INV_XT B).
Proof.
intros f0. eapply rga_qXTa; eauto.
intros f1. eapply rga_qXTb; eauto using rga_chain_XD.
Qed.
Theorem rga_chain_CX : rga_fromA B ss_CX (fun _ => INV_CX B).
Proof.
intros f0. eapply rga_q1; eauto.
intros f1. eapply rga_q2; eauto.
intros f2. eapply rga_q3; eauto.
intros f3. eapply rga_q4; eauto using rga_chain_XT2.
intros f4. eapply rga_q5; eauto.
- intros f5. eapply rga_q6; eauto using rga_chain_QE.
- intros f5. eapply rga_q7; eauto using rga_chain_QE.
Qed.
End a.
