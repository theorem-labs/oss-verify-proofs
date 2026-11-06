(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment LH of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86654 .. the call of send_message at 0x8675c, or the second rec_clear at 0x86af0 when no byte is left), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s20.v, composed of the exit with r = 0 (LLVMFuzzerTestOneInput_s25.v), the head (LLVMFuzzerTestOneInput_s23.v, 0x86654 .. 0x866bc) and the rest (LLVMFuzzerTestOneInput_s24.v, 0x866bc .. 0x8675c) through the point LH_M1_stmt (LLVMFuzzerTestOneInput_s22.v), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (segment statements chained into one). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YCfn YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase
  CmdObj CmdGlob CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c
  LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s22 LLVMFuzzerTestOneInput_s23 LLVMFuzzerTestOneInput_s24
  LLVMFuzzerTestOneInput_s25.
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
(* the walk's hypotheses, with the names of a Theorem Labs lane's RULING-STMT.md section 1 *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HB : CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis PRW : prog_rw SEGS B.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis SIGP : cmd_sig_prog.

(* 0x86654 .. the call of send_message, or with no byte left (r = 0, beqz s8) the call of the second rec_clear.
   Every other branch of this segment that leaves the straight path is an inline check's report (the shadow entries
   remove it) or a UBSan trap to 0x86b50 (refuted from the payload block, rec_ncodes = 58 and the index bound). The
   continuations are statement pass 4's LTA forms. *)
Theorem lt_seg_LH : forall m, LTA_SM B MT m -> LTA_Z B MT -> LT_LH_stmt B MT m.
Proof.
intros m HSM HZ cx ly S W regs mem md k acc r R O q HBS HFP HBody Hr R23 R24 R15 HREC HBUD.
destruct (Z.eq_dec r 0) as [Hr0 | Hr0].
- subst r.
  exact (@lh_zero fx rc SK PI B MT LAWS SIGP m HZ cx ly S W regs mem md k acc R O q HBS HFP HBody R24 HREC HBUD).
- exact (@lh_head fx rc SK PI B MT LAWS m (fun fx1 => @lh_mid fx1 rc SK PI B MT LAWS HB IMG PRW VOBJS SIGP m HSM)
    cx ly S W regs mem md k acc r R O q HBS HFP HBody ltac:(lia) R23 R24 R15 HREC HBUD).
Qed.

End e.
End f.
End d.
