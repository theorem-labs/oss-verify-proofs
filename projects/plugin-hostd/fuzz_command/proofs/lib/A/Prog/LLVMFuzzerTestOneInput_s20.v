(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment LH of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x865f4 .. the call of send_message at 0x86714), composed of its head (LLVMFuzzerTestOneInput_s23.v, 0x865f4 .. 0x86694) and its rest (LLVMFuzzerTestOneInput_s24.v, 0x86694 .. 0x86714) through the point LH_M1_stmt (LLVMFuzzerTestOneInput_s22.v), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (segment statements chained into one). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import ACfn AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase
  CmdObj CmdGlob CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c
  LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s22 LLVMFuzzerTestOneInput_s23 LLVMFuzzerTestOneInput_s24.
Import ListNotations.
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the walk's hypotheses, with cgif's names *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HB : CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis PRW : prog_rw SEGS B.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis SIGP : cmd_sig_prog.

(* 0x865f4 .. the call of send_message. The loop's other exit (n = 0 after a pass) is taken at the latch 0x8698c,
   in segment F; every branch of this segment that leaves the straight path is an inline check's report, which the
   shadow entries remove, so the continuation LTA_Z is not reached from here. The continuations are statement pass 4's LTA forms. *)
Theorem lt_seg_LH : forall m, LTA_SM B MT m -> LTA_Z B MT -> LT_LH_stmt B MT m.
Proof.
intros m HSM _.
exact (lh_head B MT LAWS m (fun fx1 => @lh_mid fx1 _ _ _ B MT LAWS HB IMG PRW VOBJS SIGP m HSM)).
Qed.

End e.
End f.
End d.
