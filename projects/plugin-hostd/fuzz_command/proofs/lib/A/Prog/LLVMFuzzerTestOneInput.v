(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x864e4, 395 instructions) assembled from its segments: each segment lemma at every FP state, the top loop by downward induction, the entry statement adapted to the contract; in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACfj.v (tfib_lib_x_body from the segment lemmas) and A/ACh6.v (segment statements composed into the contract). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Rt Require Import StrnlenDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdPaLib
  CmdBase CmdObj CmdGlob CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_clear_c send_message_c check_reply_c
  check_arity_c check_words_c check_refusal_c check_round_trip_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs
  LLVMFuzzerTestOneInput_s02.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require LLVMFuzzerTestOneInput_s10
  LLVMFuzzerTestOneInput_s15 LLVMFuzzerTestOneInput_s20 LLVMFuzzerTestOneInput_s30 LLVMFuzzerTestOneInput_s47
  LLVMFuzzerTestOneInput_Kall LLVMFuzzerTestOneInput_s60 LLVMFuzzerTestOneInput_s65 LLVMFuzzerTestOneInput_s71
  LLVMFuzzerTestOneInput_s90.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Module LE := LLVMFuzzerTestOneInput_s10.
Module LA := LLVMFuzzerTestOneInput_s15.
Module LH := LLVMFuzzerTestOneInput_s20.
Module LS := LLVMFuzzerTestOneInput_s30.
Module LW := LLVMFuzzerTestOneInput_s47.
Module LK := LLVMFuzzerTestOneInput_Kall.
Module LR := LLVMFuzzerTestOneInput_s60.
Module LC := LLVMFuzzerTestOneInput_s65.
Module LF := LLVMFuzzerTestOneInput_s71.
Module LZ := LLVMFuzzerTestOneInput_s90.

(* a segment lemma's premise: a walk hypothesis of this section, a continuation in the context, or a callee or
   runtime contract at the segment's FP state (the statement gives them at every FP state) *)
Ltac lt_close := solve [ assumption | match goal with H : forall fx0 : YK11.FPState, _ |- _ => exact (H _) end ].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the statement's own hypotheses, word for word (LLVMFuzzerTestOneInput_c.v): the callees' contracts and the
   runtime entries, at every FP state *)
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
Hypothesis AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIG CS___asan_memset).
Hypothesis ASTRNLEN : forall fx0 : YK11.FPState,
  @astrnlen_whole_realizesM fx0 rc SEGS B 0x10358 0x10378 (SIG CS___interceptor_trampoline_strnlen).
Hypothesis ASTRSPN : forall fx0 : YK11.FPState,
  @astrspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa7098 0x6045d8.
Hypothesis ASTRCSPN : forall fx0 : YK11.FPState,
  @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8.
(* the walk's hypotheses, with cgif's names; LtoiClosed.v discharges every one of
   them but HB, MTL and MTFL at the pinned image *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis PRW : prog_rw SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
(* every byte of g_rec, record.spill and g_quitting has an image byte (segment E's premise; LtoiClosed.v discharges it
   from lib/A/AB13.v's tfib_rom_all) *)
Hypothesis cmd_prog_rd : forall a, inFP cmd_PG a -> seg_rom SEGS (Z_to_bv 64 a) <> None.

Theorem pb_LLVMFuzzerTestOneInput : tLLVMFuzzerTestOneInput_spec B MT.
Proof.
(* each segment at every FP state, from its lemma at that state *)
assert (HZ2 : LTA_Z2 B MT) by (intros fx1; eapply (@LZ.lt_seg_Z2 fx1); lt_close).
assert (HRC2 : LTA_Z2 B MT -> LTA_Z B MT) by (intros H fx1; eapply (@LC.lt_call_RC2 fx1); lt_close).
assert (HZ : LTA_Z B MT) by exact (HRC2 HZ2).
assert (HRC1 : LTA_A B MT -> LTA_RC1 B MT) by (intros H fx1; eapply (@LC.lt_call_RC1 fx1); lt_close).
assert (HA : LTA_LH B MT 0 -> LTA_Z B MT -> LTA_A B MT) by (intros H1 H2 fx1; eapply (@LA.lt_seg_A fx1); lt_close).
assert (HE : LTA_RC1 B MT -> LTA_ENTRY B MT) by (intros H fx1; eapply (@LE.lt_seg_E fx1); lt_close).
assert (HLH : forall m, LTA_SM B MT m -> LTA_LH B MT m) by (intros m H fx1; eapply (@LH.lt_seg_LH fx1); lt_close).
assert (HSM : forall m, LTA_W B MT m -> LTA_SM B MT m) by (intros m H fx1; eapply (@LS.lt_call_SM fx1); lt_close).
assert (HW : forall m, LTA_K B MT m -> LTA_W B MT m) by (intros m H fx1; eapply (@LW.lt_seg_W fx1); lt_close).
assert (HK : forall m, LTA_RT B MT m -> LTA_K B MT m) by (intros m H fx1; eapply (@LK.lt_seg_K fx1); lt_close).
assert (HRT : forall m, LTA_F B MT m -> LTA_RT B MT m) by (intros m H fx1; eapply (@LR.lt_call_RT fx1); lt_close).
assert (HF : forall m, LTA_LH B MT (Datatypes.S m) -> LTA_Z B MT -> LTA_F B MT m)
  by (intros m H1 H2 fx1; eapply (@LF.lt_seg_F fx1); lt_close).
exact (lt_adapter B MT (lt_assemble B MT HE HRC1 HA HLH HSM HW HK HRT HF HRC2 HZ2)).
Qed.

End e.
End f.
End d.
Print Assumptions pb_LLVMFuzzerTestOneInput.
