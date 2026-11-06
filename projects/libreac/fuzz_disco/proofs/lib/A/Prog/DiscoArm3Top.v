(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_build_grant_sweep on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8c.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8k.v, proofs/cgif/cgif_file_fuzzer/lib/A/AE2d.v, proofs/cgif/cgif_file_fuzzer/lib/UI2d.v. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_build_grant_sweep on image B (fuzz_grant.asan-ubsan, bin fde52226dc48, 0x8363c = BASE + 0x2c00, 367 slots), ported from lib/A/Prog/CtrlBuildGrantSweep.v at a working branch 5aae1e8a0ce (its Require closure: 196 files, 0 Admitted / admit / Axiom / Parameter), with the steps of the class-6 side-stack frame adapted from lib/A/Prog/CtrlStampHeadamp.v at the same commit (whose own cgif sources are proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, ACam.v, ACbf.v, ACf6.v, AChd.v); every address, constant and byte is image B's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/CtrlBuildGrantSweep.v, with its module paths and module names changed; 254 of its 285 lines of code are new or changed and 3979 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntRec2Cc.v, with its module names changed; 64 of its 97 lines of code are new or changed and 252 lines of the source are left out. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YCbp YC5d YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import StrlenDef SetShadowDef SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import McConsts SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AE2k.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntryShapes DiscoRo DiscoEntBodyStmt TjSpec ReacDiscoTableAge CheckTable JtokIs JsonScalar
ReacBoxName ReacHuntStep ReacHuntVerdictName ReacHuntRole ReacHuntHeardAnything DiscoArm3.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require DiscoEntSeat.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require DiscoArm3Tail DiscoArm3Age DiscoArm3Json DiscoArm3Field.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDefR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis de_laws : AR_laws SEGS B.
Hypothesis de_tl : PALib B.
Hypothesis de_ml : model_laws (as_universe B).
Hypothesis de_mt_triv : MT = ameter_triv.
Hypothesis de_ffl : frame_flag_lawP SEGS B.
Hypothesis de_dro : disco_ro_unowned B.
Hypothesis de_gm : globs_marked SEGS B disco_globs.
Hypothesis de_hv : img_shadow_vis SEGS B.
Hypothesis de_dcro : dimg_consts_of_ro_stmt B.
Hypothesis de_mc_ro : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis de_mc_un : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis de_snp_ro : forall a, Exists (in_zr a) snp_cr -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis de_snp_un : forall a, Exists (in_zr a) snp_cr ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis de_ail : asink_img_laws SEGS B tfib_K.
Hypothesis de_kcan : ak_can_got tfib_K = AE2k.FF_got_canary /\ ak_canary tfib_K = AE2k.FF_canary.
Hypothesis de_duniv : duniv_ok B.
Hypothesis de_amalloc : forall fq : YK11.FPState, amalloc_realizes (fx := fq) SEGS B.
Hypothesis de_afree : forall fq : YK11.FPState, afree_realizes (fx := fq) SEGS B.
Hypothesis de_amemcpy : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA DS___asan_memcpy).
Hypothesis de_amemset : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA DS___asan_memset).
Hypothesis de_assf8 : forall fq : YK11.FPState, aset_shadow_realizes (fx := fq) SEGS B (SIGMA DS___asan_set_shadow_f8) 0xf8.
Hypothesis de_ass00 : forall fq : YK11.FPState, aset_shadow_realizes (fx := fq) SEGS B (SIGMA DS___asan_set_shadow_00) 0.
Hypothesis de_astrlen : forall fq : YK11.FPState,
  astrlen_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (SIGMA DS___interceptor_trampoline_strlen).
Hypothesis de_asnprintf : forall fq : YK11.FPState,
  SnprintfDefR.asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi AE2k.FF_got_canary AE2k.FF_canary YImgTop.IMG_LO YImgTop.IMG_TOP
    disco_fmt_lo disco_fmt_hi snp_cr (SIGMA DS___interceptor_trampoline_snprintf).
Hypothesis de_tage : treac_disco_table_age_spec B.
Hypothesis de_tchkt : tcheck_table_spec B.
Hypothesis de_ttjson : tj_specP B TJ_STK 0 dimg_tj.
Hypothesis de_tjsc : tjson_scalar_spec B.
Hypothesis de_tjtok : tjtok_is_spec B.
Hypothesis de_tbox : treac_box_name_spec B.
Hypothesis de_thstep : treac_hunt_step_spec B.
Hypothesis de_tvname : treac_hunt_verdict_name_spec B.
Hypothesis de_throle : treac_hunt_role_spec B.
Hypothesis de_thheard : treac_hunt_heard_anything_spec B.
Hypothesis tjsc_roimg : tjson_scalar_roimg.

Theorem arm3_proved : arm3_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
  pose proof (DiscoEntSeat.d_seat B MT XM_LIB RLO RHI tfib_K) as DSEAT.
  pose proof (DiscoEntSeat.d_facts_ok B MT XM_LIB RLO RHI tfib_K) as DFACTS.
  pose proof (DiscoEntSeat.d_land B MT XM_LIB RLO RHI tfib_K) as DLAND.
  assert (DCAN : d_can_hyps B tfib_K) by exact (conj de_ail (proj2 de_kcan)).
  assert (DROH : d_ro_hyps B) by exact (conj de_dro (conj de_gm de_hv)).
  apply arm3_of_parts.
  - eapply DiscoArm3Age.a3_age; eassumption.
  - eapply DiscoArm3Json.a3_json; eassumption.
  - eapply DiscoArm3Field.a3_field; eassumption.
  - eapply DiscoArm3Tail.a3_tail; eassumption.
Qed.

End h.
End f.
End d.
