(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 481 of its 517 lines of code are new or changed and 1242 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntProE.v, with its module paths and module names changed; 57 of its 93 lines of code are new or changed and 481 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SetShadowDef AcpySameDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
ReacHuntStep CheckTable ReacHuntVerdictName ReacHuntRole ReacHuntHeardAnything.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
ReacDiscoTableAge ReacArbitrate ReacSenderKind ReacRivalKindOf ReacMasterOnlyCadenceNs ReacRateSnap.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3 DiscoArm3TailDefs DiscoArm3TailK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoArm3TailTA DiscoArm3TailT1 DiscoArm3TailT2 DiscoArm3TailT3 DiscoArm3TailT4 DiscoArm3TailT5 DiscoArm3TailT6.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PO : PAObjImg lib_both3_0_listing} {PX : PAXcalls lib_both3_0_listing}.
Context {PH : PAHiImg lib_both3_0_listing} {PW : PAWinImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : forall fq : YK11.FPState, afree_realizes (fx := fq) SEGS B.
Hypothesis ASSF8 : forall fq : YK11.FPState, aset_shadow_realizes (fx := fq) SEGS B (SIGMA AS___asan_set_shadow_f8) 0xf8.
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Hypothesis DUNIV : duniv_ok B.
Hypothesis TRO : tfib_ro_unowned B.
Hypothesis GM : globs_marked SEGS B tfib_globs.
Hypothesis GO65 : In (pa_val (A_OBJ 65), 12) tfib_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DBPC : d_body_pcall_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DBFREE : d_body_free_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DBRT : d_body_rt_stmt B.
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).
Hypothesis AMEMCPYEQ : forall fq : YK11.FPState, acpy_same_realizes (fx := fq) SEGS B (SIGMA AS___asan_memcpy).
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA AS___asan_memset).
Hypothesis DCAN : d_can_hyps B tfib_K.

Theorem a3_tail : a3_tail_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
  assert (DROH : d_ro_hyps B) by (split; [exact TRO | split; [exact GM | exact HV]]).
  pose proof (pb_check_table B LAWS PAL ABCMP) as TCHKT.
  pose proof (pb_reac_hunt_verdict_name B LAWS PAL) as TVNAME.
  pose proof (pb_reac_hunt_role B LAWS PAL) as THROLE.
  pose proof (pb_reac_hunt_heard_anything B LAWS PAL) as THHEARD.
  assert (TRIVAL : treac_rival_kind_of_spec B) by (apply (pb_reac_rival_kind_of B); assumption).
  assert (TRATE : treac_rate_snap_spec B) by (apply (pb_reac_rate_snap B); assumption).
  assert (TMOC : treac_master_only_cadence_ns_spec B) by (apply (pb_reac_master_only_cadence_ns B); assumption).
  assert (TSENDER : treac_sender_kind_spec B) by (apply (pb_reac_sender_kind B); assumption).
  assert (TAGE : treac_disco_table_age_spec B) by (apply (pb_reac_disco_table_age B); assumption).
  assert (TARB : treac_arbitrate_spec B) by (apply (pb_reac_arbitrate B); assumption).
  assert (THSTEP : treac_hunt_step_spec B) by (apply (pb_reac_hunt_step B); assumption).
  apply (a3_tail_of_parts B MT XM_LIB RLO RHI tfib_K).
  - apply (a3t_TA B MT XM_LIB RLO RHI tfib_K); assumption.
  - apply (a3t_T1 B MT XM_LIB RLO RHI tfib_K); assumption.
  - apply (a3t_T2 B MT XM_LIB RLO RHI tfib_K); assumption.
  - apply (a3t_T3 B MT XM_LIB RLO RHI tfib_K); assumption.
  - apply (a3t_T4 B MT XM_LIB RLO RHI tfib_K); assumption.
  - apply (a3t_T5 B MT XM_LIB RLO RHI tfib_K); assumption.
  - apply (a3t_T6 B MT XM_LIB RLO RHI tfib_K); assumption.
Qed.

End h.
End f.
End d.
