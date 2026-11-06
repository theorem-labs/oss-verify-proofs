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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCq8 YCqb YClx YCm2 YCqc YCjo YCly YCpo YCpp YClz YCqd YCqe YCpy YCq2 YCq3 YCir YCjj YCjn YCjl YCis YCit YCiu YCiv YCiw YCix YCiy YCiz YCj0 YCj1 YCj2 YCj3 YCj4 YCj5.
Section a. Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis ASM7 : forall fx : YK11.FPState, @astack_malloc_sz_realizes fx rc trbsegs B A_stack_malloc_7 7.
Hypothesis ASSF8 : forall fx : YK11.FPState, @aset_shadow_realizes fx rc trbsegs B A_set_shadow_f8 248.
Hypothesis ASS00 : forall fx : YK11.FPState, @aset_shadow_realizes fx rc trbsegs B A_set_shadow_00 0.
Hypothesis ASF7 : forall fx : YK11.FPState, @astack_free_realizes fx rc trbsegs B A_stack_free_7 7.
Hypothesis AMALLOC : forall fx : YK11.FPState, @amalloc_realizes fx rc trbsegs B.
Hypothesis AFREE : forall fx : YK11.FPState, @afree_realizes fx rc trbsegs B.
Hypothesis AMEMSET : forall fx : YK11.FPState, @aintrin_realizes fx rc trbsegs B OSet A_asan_memset.
Hypothesis AMEMCPY : forall fx : YK11.FPState, @aintrin_realizes fx rc trbsegs B OCpy A_asan_memcpy.
Hypothesis FREECHT : forall fx : YK11.FPState, @tfree_cht_spec fx rc B.
Lemma rga_exit_EPI : rga_fromFA B ss_EPI (fun _ => INV_X B).
Proof. intros fy. eapply rga_EPI; eauto. Qed.
Lemma rga_exit_XB : rga_fromA B ss_XB (fun _ => INV_XB B).
Proof. intros fy. eapply rga_XBp; eauto using rga_exit_EPI. Qed.
Lemma rga_exit_X38 : rga_fromA B ss_X38 (fun _ => INV_X38 B).
Proof. intros fy. eapply rga_X38p; eauto using rga_exit_XB. Qed.
Theorem rga_chain_to_A10 :
rga_fromA B ss_A10 (fun _ => INV_N B 8 news_A9) -> forall fx : YK11.FPState, @trgb_addframe_specV fx rc B.
Proof.
intros RC fx.
pose proof rga_exit_EPI as RX. pose proof rga_exit_XB as RXB. pose proof rga_exit_X38 as RX38.
eapply rga_A; eauto.
intros f1. eapply rga_B1; eauto.
intros f2. eapply rga_B2a; eauto.
intros f3. eapply rga_B2b; eauto.
intros f4. eapply rga_B3; eauto.
intros f5. eapply rga_E2a; eauto.
intros f6. eapply rga_E2b; eauto.
intros f7. eapply rga_E2c; eauto.
intros f8. eapply rga_E2d; eauto.
intros f9. eapply rga_E2e; eauto.
intros f10. eapply rga_E2f; eauto.
intros f11. eapply rga_E2g; eauto.
intros f12. eapply rga_E2h1; eauto.
intros f12b. eapply rga_E2h2; eauto.
intros f13. eapply rga_E2i; eauto.
Qed.
End a.
