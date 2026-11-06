(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 481 of its 517 lines of code are new or changed and 1242 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntProE.v, with its module paths and module names changed; 49 of its 85 lines of code are new or changed and 481 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntryShapes DiscoArm3 DiscoRo DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntBody DiscoEntBodyCall
ReacDiscoTableAge CheckTable TjSpec DiscoArm3AgeSt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require
DiscoArm3AgeEnt DiscoArm3AgeShort DiscoArm3AgeLeft DiscoArm3AgeRes DiscoArm3AgeCall1 DiscoArm3AgeCall2.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import StrlenDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import McConsts.
Import ListNotations.
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
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis DRO : disco_ro_unowned B.
Hypothesis GM : globs_marked SEGS B disco_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis DCAN : d_can_hyps B tfib_K.
Hypothesis DUNIV : duniv_ok B.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.
Hypothesis AMALLOC : forall fq : YK11.FPState, amalloc_realizes (fx := fq) SEGS B.
Hypothesis TAGE : treac_disco_table_age_spec B.
Hypothesis TCHKT : tcheck_table_spec B.
Hypothesis TTJ : tj_specP B TJ_STK 0 dimg_tj.
Hypothesis ASTRLEN : forall fq : YK11.FPState,
  astrlen_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (SIGMA DS___interceptor_trampoline_strlen).
Hypothesis de_mc_ro : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis de_mc_un : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).

Theorem a3_age : a3_age_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
  pose proof (d_seat B MT XM_LIB RLO RHI tfib_K) as DSEAT.
  pose proof (d_facts_ok B MT XM_LIB RLO RHI tfib_K) as DFACTS.
  pose proof (d_land B MT XM_LIB RLO RHI tfib_K) as DLAND.
  pose proof (d_body_keep B) as DBKEEP.
  pose proof (d_body_rt B) as DBRT.
  pose proof (d_body_tobs B MT XM_LIB RLO RHI tfib_K) as DBTOBS.
  pose proof (d_body_pcall B MT XM_LIB RLO RHI tfib_K) as DBPC.
  pose proof (d_body_malloc B MT XM_LIB RLO RHI tfib_K) as DBMAL.
  assert (DROH : d_ro_hyps B) by (split; [exact DRO | split; [exact GM | exact HV]]).
  apply a3_age_of_parts.
  - eapply DiscoArm3AgeEnt.a3_e_ent; eassumption.
  - eapply DiscoArm3AgeCall1.c_age; eassumption.
  - eapply DiscoArm3AgeShort.a3_e_chk; eassumption.
  - eapply DiscoArm3AgeCall1.c_chk; eassumption.
  - eapply DiscoArm3AgeLeft.a3_e_left; eassumption.
  - eapply DiscoArm3AgeCall2.c_mal; eassumption.
  - eapply DiscoArm3AgeShort.a3_e_tj; eassumption.
  - eapply DiscoArm3AgeCall2.c_tj; eassumption.
  - eapply DiscoArm3AgeRes.e_res; eassumption.
  - eapply DiscoArm3AgeCall2.c_sl; eassumption.
  - eapply DiscoArm3AgeRes.e_brk; eassumption.
Qed.

End h.
End f.
End d.
