(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: tLLVMFuzzerTestOneInput_spec on plugin-hostd/fuzz_command's ASan+UBSan image B (entry 0x86530) from the segment lemmas of its walk (LLVMFuzzerTestOneInput_s02.v's loop induction and assembly), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACfj.v (tfib_lib_x_body: the contract from the walk's segments) and A/ACh6.v (segment statements composed into the contract). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YCfn YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Rt Require Import StrnlenDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdPaLib
  CmdBase CmdRep CmdObj CmdRo CmdGlob CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import rec_clear_c send_message_c check_reply_c
  check_arity_c check_words_c check_refusal_c check_round_trip_c LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import LLVMFuzzerTestOneInput_defs
  LLVMFuzzerTestOneInput_s02.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require
  LLVMFuzzerTestOneInput_s10 LLVMFuzzerTestOneInput_s65 LLVMFuzzerTestOneInput_s15 LLVMFuzzerTestOneInput_s20
  LLVMFuzzerTestOneInput_s30 LLVMFuzzerTestOneInput_s47 LLVMFuzzerTestOneInput_Kall LLVMFuzzerTestOneInput_s60
  LLVMFuzzerTestOneInput_s71 LLVMFuzzerTestOneInput_s90.
Import ListNotations.
Local Open Scope Z_scope.

Module LE := LLVMFuzzerTestOneInput_s10.
Module LRC := LLVMFuzzerTestOneInput_s65.
Module LA := LLVMFuzzerTestOneInput_s15.
Module LLH := LLVMFuzzerTestOneInput_s20.
Module LSM := LLVMFuzzerTestOneInput_s30.
Module LW := LLVMFuzzerTestOneInput_s47.
Module LK := LLVMFuzzerTestOneInput_Kall.
Module LRT := LLVMFuzzerTestOneInput_s60.
Module LF := LLVMFuzzerTestOneInput_s71.
Module LZ2 := LLVMFuzzerTestOneInput_s90.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the statement's callee and runtime-entry hypotheses, word for word (LLVMFuzzerTestOneInput_c.v) *)
Hypothesis HREC_CLEAR : forall fx0 : YK11.FPState, @trec_clear_spec fx0 rc SK PI B MT.
Hypothesis HSEND_MESSAGE : forall fx0 : YK11.FPState, @tsend_message_spec fx0 rc SK PI B MT.
Hypothesis HCHECK_REPLY : forall fx0 : YK11.FPState, @tcheck_reply_spec fx0 rc SK PI B MT.
Hypothesis HCHECK_ARITY : forall fx0 : YK11.FPState, @tcheck_arity_spec fx0 rc SK PI B MT.
Hypothesis HCHECK_WORDS : forall fx0 : YK11.FPState, @tcheck_words_spec fx0 rc SK PI B MT.
Hypothesis HCHECK_REFUSAL : forall fx0 : YK11.FPState, @tcheck_refusal_spec fx0 rc SK PI B MT.
Hypothesis HCHECK_ROUND_TRIP : forall fx0 : YK11.FPState, @tcheck_round_trip_spec fx0 rc SK PI B MT.
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy).
Hypothesis ASTRNLEN : forall fx0 : YK11.FPState,
  @astrnlen_whole_realizesM fx0 rc SEGS B 0x10358 0x10378 (SIG CS___interceptor_trampoline_strnlen).
Hypothesis ASTRSPN : forall fx0 : YK11.FPState,
  @astrspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa6bf8 0x604158.
Hypothesis ASTRCSPN : forall fx0 : YK11.FPState,
  @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa6bf8 0x604158.
(* the walk's hypotheses, with the names of a Theorem Labs lane's RULING-STMT.md section 1; the closing file discharges them at
   the pinned image (PASS4-REFIT.md F) *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis PRW : prog_rw SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
(* segment E's walk-level hypothesis (the A walk's same one, lib/A/Prog/LLVMFuzzerTestOneInput_s10.v): every byte of
   g_rec, record.spill and g_quitting has a ROM byte; the closing file discharges it at tfibsegs *)
Hypothesis cmd_prog_rd : forall a, inFP cmd_PG a -> seg_rom SEGS (Z_to_bv 64 a) <> None.

Theorem tLLVMFuzzerTestOneInput_holds : tLLVMFuzzerTestOneInput_spec B MT.
Proof.
exact (lt_adapter B MT (lt_assemble B MT
  (fun H fx1 => LE.lt_seg_E (fx := fx1) B MT LAWS TL SIGP MTL cmd_prog_rd H)
  (fun H fx1 => LRC.lt_call_RC1 (fx := fx1) B MT HREC_CLEAR HB LAWS MTL IMG H)
  (fun H fx1 => LA.lt_seg_A (fx := fx1) B MT LAWS HB IMG PRW VOBJS H)
  (fun m H1 H2 fx1 => LLH.lt_seg_LH (fx := fx1) B MT LAWS HB IMG PRW VOBJS SIGP m H1 H2)
  (fun m H fx1 => LSM.lt_call_SM (fx := fx1) B MT HSEND_MESSAGE HB LAWS MTL IMG m H)
  (fun m H fx1 => LW.lt_seg_W (fx := fx1) B MT AMALLOC4 AMEMCPY ASTRNLEN ASTRSPN ASTRCSPN HB LAWS TL MTL IMG m H)
  (fun m H fx1 => LK.lt_seg_K (fx := fx1) B MT HCHECK_REPLY HCHECK_ARITY HCHECK_WORDS HCHECK_REFUSAL HB LAWS SIGP IMG
     MTL MTFL m H)
  (fun m H fx1 => LRT.lt_call_RT (fx := fx1) B MT HB LAWS MTL IMG HCHECK_ROUND_TRIP m H)
  (fun m H1 H2 fx1 => LF.lt_seg_F (fx := fx1) B MT HB LAWS TL MTL IMG SIGP AFREE4 m H1 H2)
  (fun H fx1 => LRC.lt_call_RC2 (fx := fx1) B MT HREC_CLEAR HB LAWS MTL IMG H)
  (fun fx1 => LZ2.lt_seg_Z2 (fx := fx1) B MT HB LAWS MTL PRW IMG))).
Qed.

End e.
End f.
End d.
Print Assumptions tLLVMFuzzerTestOneInput_holds.
