(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YChd.v, with its module paths and module names changed; 56 of its 87 lines of code are new or changed and 514 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q YG0s YC1g YC4b YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SetShadowDef ConstsViewDef StrlenDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import SbCh SbDec.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_box_name_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacBoxName ReacBoxNameCut ReacBoxNameLoops ReacBoxNameAsm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require
  ReacBoxNameSeg1 ReacBoxNameSeg2 ReacBoxNameSeg3 ReacBoxNameSeg4 ReacBoxNameSeg5 ReacBoxNameSeg6 ReacBoxNameSeg7
  ReacBoxNameSeg8 ReacBoxNameSeg9 ReacBoxNameSeg10 ReacBoxNameL1 ReacBoxNameL2 ReacBoxNameL3 ReacBoxNameL4 ReacBoxNameL567.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Context {PX : PAXcalls lib_both3_0_listing}.
Context {PO : PAObjImg lib_both3_0_listing}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA AS___asan_memset).
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Hypothesis ASTRLEN : forall fq : YK11.FPState,
  astrlen_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (SIGMA AS___interceptor_trampoline_strlen).
Hypothesis mc_consts_unowned : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis mc_consts_img : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_img SEGS a.
Hypothesis ASSF5 : forall fq : YK11.FPState,
  aset_shadow_realizes (fx := fq) SEGS B (SIGMA AS___asan_set_shadow_f5) 0xf5.
Hypothesis ASM3 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 3.
Hypothesis TLF : PALibF B.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis HSBDEC : tsb_dec_spec B.
Hypothesis TSB : tsb_ch_spec B.
Hypothesis DRO : tfib_ro_unowned B.
Hypothesis GM : globs_marked SEGS B tfib_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Theorem pb_reac_box_name : treac_box_name_spec B.
Proof.
apply pb_reac_box_name_of_segs.
- apply ReacBoxNameSeg1.rbn_seg1; assumption.
- apply ReacBoxNameSeg2.rbn_seg2; assumption.
- apply ReacBoxNameSeg3.rbn_seg3; assumption.
- apply ReacBoxNameSeg4.rbn_seg4; [assumption | apply ReacBoxNameL1.rbn_l1_fits | apply ReacBoxNameL1.rbn_l1_ovf]; assumption.
- apply ReacBoxNameSeg5.rbn_seg5; try assumption; [apply ReacBoxNameL2.rbn_l2_fits | apply ReacBoxNameL2.rbn_l2_ovf]; assumption.
- apply ReacBoxNameSeg6.rbn_seg6; [assumption | apply ReacBoxNameL3.rbn_l3_fits | apply ReacBoxNameL3.rbn_l3_ovf]; assumption.
- apply ReacBoxNameSeg7.rbn_seg7; try assumption; apply ReacBoxNameL4.rbn_l4_fits; assumption.
- apply ReacBoxNameSeg8.rbn_seg8; try assumption; [apply ReacBoxNameL567.rbn_l5_fits | apply ReacBoxNameL567.rbn_l6_fits]; assumption.
- apply ReacBoxNameSeg9.rbn_seg9; try assumption; apply ReacBoxNameL567.rbn_l7_fits; assumption.
- apply ReacBoxNameSeg10.rbn_seg10; assumption.
Qed.
End h.
End f.
End d.
