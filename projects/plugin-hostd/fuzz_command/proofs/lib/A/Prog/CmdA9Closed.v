(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the closing pattern of the re-fit to statement passes 4-5 for the seven
   ASan walks of plugin-hostd/fuzz_command (xstrdup, rec_calls_free, rec_calls_equal, rec_canonical, joined,
   rec_calls_copy, check_round_trip), as lib/A/Prog/SupRemoveAllRefitClosed.v does for the worked example: each walk's
   theorem with the per-binary record hypotheses it names discharged at the pinned image (lib/A/Prog/CmdImg.v's
   instance PB_cmd, whose segments are tfibsegs, and the sink head AE2k.tfib_sink_head) by the kit's helpers: TL is
   CmdRecRest.cmd_palib, TLF cmd_palibf, ML cmd_model_laws, SIGP cmd_sig_prog_PB, PRW cmd_prw_tfib, IMG
   CmdRecImg.cmd_img_facts_tfib, and the listing's object bridge (cmd_val_objs) cmd_val_objs_PB. What remains is HB,
   the meter laws (MTL, and MTFL for check_round_trip), and the statements' own hypotheses: the callees' and the
  runtime entries' contracts at every FP state. check_round_trip's side-stack progress law SMP is discharged by the
  kit's CmdRecRest.cmd_stack_malloc_progress. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m AB1v AB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtStack RtShadow RtAlloc RtAlloc04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib PaLibF CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecBase CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require xstrdup_c rec_calls_free_c rec_calls_equal_c
  rec_canonical_c joined_c rec_calls_copy_c send_message_c check_round_trip_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require xstrdup rec_calls_free rec_calls_equal
  rec_canonical joined rec_calls_copy check_round_trip.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance AE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PB_cmd s).
#[local] Notation SK := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
(* the allocator record and the meter's laws *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.

Theorem txstrdup_closed
  (AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT)
  (AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy))
  (ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen)) :
  xstrdup_c.txstrdup_spec B MT.
Proof.
exact (xstrdup.txstrdup_spec_holds B MT AMALLOC4 AMEMCPY ASTRLEN (CmdRecRest.cmd_palib B HB) HB
  (CmdRecImg.cmd_img_facts_tfib B HB)).
Qed.

Theorem trec_calls_free_closed
  (AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT) :
  rec_calls_free_c.trec_calls_free_spec B MT.
Proof.
exact (rec_calls_free.trec_calls_free_spec_holds B MT AFREE4 HB (CmdRecRest.cmd_palib B HB) MTL
  (CmdRecImg.cmd_img_facts_tfib B HB) (CmdRecRest.cmd_prw_tfib B HB)).
Qed.

Theorem trec_calls_equal_closed
  (ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp)) :
  rec_calls_equal_c.trec_calls_equal_spec B MT.
Proof.
exact (rec_calls_equal.trec_calls_equal_spec_holds B ASTRCMP (CmdRecRest.cmd_palib B HB) HB MT).
Qed.

Theorem trec_canonical_closed
  (AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT) :
  rec_canonical_c.trec_canonical_spec B MT.
Proof.
exact (rec_canonical.trec_canonical_spec_holds B MT AMALLOC4 (CmdRecRest.cmd_palib B HB)).
Qed.

Theorem tjoined_closed
  (AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT)
  (AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy))
  (ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen)) :
  joined_c.tjoined_spec B MT.
Proof.
exact (joined.tjoined_spec_holds B MT AMALLOC4 AMEMCPY ASTRLEN (CmdRecRest.cmd_palib B HB) HB
  (CmdRecImg.cmd_img_facts_tfib B HB)).
Qed.

Theorem trec_calls_copy_closed
  (HXSTRDUP : forall fx0 : YK11.FPState, @xstrdup_c.txstrdup_spec fx0 rc SK PB_cmd B MT) :
  rec_calls_copy_c.trec_calls_copy_spec B MT.
Proof.
exact (rec_calls_copy.trec_calls_copy_spec_holds B MT HXSTRDUP CmdRecRest.cmd_val_objs_PB (CmdRecRest.cmd_palib B HB) HB
  (CmdRecImg.cmd_img_facts_tfib B HB) MTL CmdRecRest.cmd_sig_prog_PB).
Qed.

Theorem tcheck_round_trip_closed
  (HSEND : forall fx0 : YK11.FPState, @send_message_c.tsend_message_spec fx0 rc SK PB_cmd B MT)
  (HJOINED : forall fx0 : YK11.FPState, @joined_c.tjoined_spec fx0 rc SK PB_cmd B MT)
  (HRCC : forall fx0 : YK11.FPState, @rec_calls_copy_c.trec_calls_copy_spec fx0 rc SK PB_cmd B MT)
  (HRCE : forall fx0 : YK11.FPState, @rec_calls_equal_c.trec_calls_equal_spec fx0 rc SK PB_cmd B MT)
  (HRCF : forall fx0 : YK11.FPState, @rec_calls_free_c.trec_calls_free_spec fx0 rc SK PB_cmd B MT)
  (PC_STRDUP_RA0 : Z)
  (AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT)
  (ASTRDUP4 : forall fx0 : YK11.FPState,
     @astrdup04_rule fx0 rc SK SEGS B MT (SIG CS___interceptor_trampoline_strdup) PC_STRDUP_RA0)
  (ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp))
  (ASM5 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 5)
  (ASF5 : forall fx0 : YK11.FPState, @astack_free_cls_realizes fx0 rc SEGS B (SIG CS___asan_stack_free_5) 5)
  (ASH00 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_00) 0)
  (ASHF8 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_f8) 0xf8) :
  check_round_trip_c.tcheck_round_trip_spec B MT.
Proof.
exact (check_round_trip.tcheck_round_trip_spec_holds B MT HSEND HJOINED HRCC HRCE HRCF PC_STRDUP_RA0 AFREE4 ASTRDUP4
  ASTRCMP ASM5 ASF5 ASH00 ASHF8 CmdRecRest.cmd_val_objs_PB HB (CmdRecRest.cmd_palib B HB) (CmdRecRest.cmd_palibf B HB)
  (CmdRecRest.cmd_model_laws B HB) (CmdRecRest.cmd_stack_malloc_progress B) MTL MTFL CmdRecRest.cmd_sig_prog_PB (CmdRecRest.cmd_prw_tfib B HB)
  (CmdRecImg.cmd_img_facts_tfib B HB)).
Qed.
End closed.
Print Assumptions txstrdup_closed.
Print Assumptions trec_calls_free_closed.
Print Assumptions trec_calls_equal_closed.
Print Assumptions trec_canonical_closed.
Print Assumptions tjoined_closed.
Print Assumptions trec_calls_copy_closed.
Print Assumptions tcheck_round_trip_closed.
