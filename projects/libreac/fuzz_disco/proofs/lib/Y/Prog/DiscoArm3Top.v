(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 481 of its 517 lines of code are new or changed and 1242 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntProE.v, with its module paths and module names changed; 57 of its 93 lines of code are new or changed and 481 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoArm3Tail.v; 63 of its 118 lines of code are new or changed and 38 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YRo YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SetShadowDef AcpySameDef SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDefR.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require StrlenDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntryShapes DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3
ReacDiscoTableAge CheckTable TjSpecLift.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require DiscoArm3JsonCallee DiscoArm3JtokSpec.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require
DiscoArm3Age DiscoArm3Json DiscoArm3Field DiscoArm3Tail.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi} {PX : PAXcalls lib_both3_0_listing}
  {PO : PAObjImg lib_both3_0_listing} {POV : PAObjVal lib_both3_0_listing (PI := PI)}
  {PR : PARoPresent lib_both3_0_listing}.
Context {PH : PAHiImg lib_both3_0_listing} {PW : PAWinImg lib_both3_0_listing}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis DUNIV : duniv_ok B.
Hypothesis TRO : tfib_ro_unowned B.
Hypothesis GM : globs_marked SEGS B tfib_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.
Hypothesis AIL : asink_img_laws SEGS B tfib_K.
Hypothesis KCAN : ak_can_got tfib_K = FF_got_canary /\ ak_canary tfib_K = FF_canary.
Hypothesis de_mc_ro : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis de_mc_un : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis SNPRO : forall a, Exists (in_zr a) snp_cr -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis SNPUN : forall a, Exists (in_zr a) snp_cr ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DBKEEP : d_body_keep_stmt B.
Hypothesis DBRT : d_body_rt_stmt B.
Hypothesis DBCK : d_body_call_keep_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DTOBS : d_body_tobs_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DBPC : d_body_pcall_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DBMAL : d_body_malloc_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DBFREE : d_body_free_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis AMALLOC : forall fq : YK11.FPState, amalloc_realizes (fx := fq) SEGS B.
Hypothesis AFREE : forall fq : YK11.FPState, afree_realizes (fx := fq) SEGS B.
Hypothesis ASM3 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 3.
Hypothesis ASM0 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 0.
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).
Hypothesis AMEMCPYEQ : forall fq : YK11.FPState, acpy_same_realizes (fx := fq) SEGS B (SIGMA AS___asan_memcpy).
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA AS___asan_memset).
Hypothesis ASSF8 : forall fq : YK11.FPState, aset_shadow_realizes (fx := fq) SEGS B (SIGMA AS___asan_set_shadow_f8) 0xf8.
Hypothesis ASSF5 : forall fq : YK11.FPState,
  SetShadowDef.aset_shadow_realizes (fx := fq) SEGS B (SIGMA AS___asan_set_shadow_f5) 0xf5.
Hypothesis ASS00 : forall fq : YK11.FPState,
  aset_shadow_realizes (fx := fq) SEGS B (SIGMA AS___asan_set_shadow_00) 0.
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Hypothesis ASTRLEN : forall fq : YK11.FPState,
  StrlenDef.astrlen_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (SIGMA AS___interceptor_trampoline_strlen).
Hypothesis ASNPRINTF : forall fq : YK11.FPState,
  SnprintfDefR.asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi FF_got_canary FF_canary
    YImgTop.IMG_LO YImgTop.IMG_TOP disco_fmt_lo disco_fmt_hi snp_cr (SIGMA AS___interceptor_trampoline_snprintf).
Hypothesis TAGE : treac_disco_table_age_spec B.
Hypothesis TCHKT : tcheck_table_spec B.
Hypothesis TTJ : tj_specPF B TJ_STK 0 dimg_tj.
Hypothesis tjsc_roimg : DiscoArm3JsonCallee.tjson_scalar_roimg.
Hypothesis TJSC : DiscoArm3JsonCallee.tjson_scalar_spec B.
Hypothesis TJTOK : DiscoArm3JtokSpec.tjtok_is_spec B.

Theorem arm3_proved : arm3_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
  assert (GO65 : In (pa_val (A_OBJ 65), 12) tfib_globs).
  { rewrite (pa_obj_val (PI := PI) 65%nat) by (apply Nat.ltb_lt; reflexivity).
    vm_compute. repeat (first [left; reflexivity | right]). }
  assert (DROH : d_ro_hyps B) by exact (conj TRO (conj GM HV)).
  assert (DCAN : d_can_hyps B tfib_K) by exact (conj AIL (proj2 KCAN)).
  assert (TJTOKJ : DiscoArm3JsonCallee.tjtok_is_spec B) by exact TJTOK.
  apply arm3_of_parts.
  - eapply DiscoArm3Age.a3_age; eassumption.
  - eapply DiscoArm3Json.a3_json; eassumption.
  - eapply DiscoArm3Field.a3_field; eassumption.
  - eapply DiscoArm3Tail.a3_tail; eassumption.
Qed.

End h.
End f.
End d.
