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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI03 YI04 YI1i YI20.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC1b YC2q YC2u YC4r YC13 YC2o YC16 YC12 YC20 YC3q YC0u YC0w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC17 YC18 YC0q YC0t YC0n YC0o YC0p
YC0k YC0l YC0m YC0r YC0j YC0i YC0h YC0e YC0b YC0s YC0a.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC1c.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trasegs B.
Hypothesis AFREE : afree_realizes trasegs B.
Hypothesis AMEMCPY : aintrin_realizes trasegs B OCpy A_asan_memcpy.
Hypothesis AMEMCMP : amemcmp_realizes trasegs B A_memcmp_icpt.
Hypothesis ABCMP : abcmp_realizes trasegs B A_bcmp_icpt.
Hypothesis FLUSH : tflush_spec B.
Theorem tra_cgif_addframeG : taddframe_specG B.
Proof.
pose proof (tra_cmpPixelF B TL LAWS AMEMCMP) as CMP.
assert (RET : AF_RET_stmt B) by (eapply af_RET; eassumption).
assert (RETC : AF_RETC_stmt B) by (eapply af_RETC; eassumption).
assert (RET0 : AF_RET0_stmt B) by (eapply af_RET0; eassumption).
assert (PE3 : AF_E3_stmt B) by (eapply af_E3; eassumption).
assert (PE2 : AF_E2_stmt B) by (eapply af_E2; eassumption).
assert (PE : AF_E_stmt B) by (eapply af_E1; eassumption).
assert (PD3 : AF_D3_stmt B) by (eapply af_D3; eassumption).
assert (PD2 : AF_D2_stmt B) by (eapply af_D2; eassumption).
assert (PD : AF_D_stmt B) by (eapply af_D1; eassumption).
assert (PFL : AF_FL_stmt B) by (eapply af_FL; eassumption).
assert (PC : AF_C_stmt B) by (eapply af_C; eassumption).
assert (PSM : AF_SM_stmt B) by (eapply af_SM; eassumption).
assert (PL : AF_L_stmt B) by (eapply af_L; eassumption).
assert (PB : AF_B_stmt B) by (eapply af_B; eassumption).
assert (POK : AF_OK_stmt B) by (eapply af_OK; eassumption).
intros ly S W regs mem md ch g cfp s N lpal img fattr fgen delay nlp tidx rest HPRE Hctx Hfr7 HROD H10 H11 HFO HCF HT HWF HPAL HPerm Hev Hlive.
exact (af_A B TL LAWS POK ly S W regs mem md ch g cfp s N lpal lpal img fattr fgen delay nlp tidx rest
(conj HPRE (conj Hctx (conj Hfr7 (conj HROD (conj H10 (conj H11 (conj HFO (conj HCF (conj HT (conj HWF (conj eq_refl (conj HPerm (conj Hev (conj Hlive HPAL))))))))))))))).
Qed.
End b.
End a.
