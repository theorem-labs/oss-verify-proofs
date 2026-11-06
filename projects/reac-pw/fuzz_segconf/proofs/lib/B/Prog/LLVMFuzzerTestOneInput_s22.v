(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the assembly of the inlined words_of of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x86718 .. 0x8693c) from its segment lemmas, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh5.v (cl_A_okX: a function's statement from the CL_*_stmtX segment statements) and A/ACfj.v (a loop closed by well-founded induction over its segment lemmas). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/LLVMFuzzerTestOneInput_s47.v, with its module paths and module names changed; 21 of its 45 lines of code are new or changed and 61 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the walk of
   segment S14 (0x85b0c .. 0x85d00 with the "continue" join and latch 0x85b58 .. 0x85b94: the head of the inlined
   m_declared loop at turn i) of the test harness's entry function LLVMFuzzerTestOneInput (0x84dc0).

   proves function LLVMFuzzerTestOneInput (reuse search, rule 24: released units, the earlier proof delivery and working
   heads; the result is recorded with the commissioning brief; none: written new)

   The statement proved: lt_seg_S14_stmt of LLVMFuzzerTestOneInput_defs.v,
     forall i, LTA_K85d04 i -> LTA_K85b0c (S i) -> LTA_K85e50 -> LT_K85b0c_stmt i,
   composed by LLVMFuzzerTestOneInput_s22k.s22_compose from the six pieces of the kit's inner cut points:
     a  _s22a.v  s22_p1   V0 (K85b0c i) -> JOIN | VR    v in scope, traps 0x85b24 0x85b30, check 29, strrchr
     b  _s22b.v  s22_p2   VR -> JOIN | VD               NULL / start / dot[1] tests, trap 0x85bc0, check 31
     c  _s22c.v  s22_p3   VD -> JOIN | VP               the digit loop, trap 0x85c00, check 32
     d  _s22d.v  s22_p4   VP -> JOIN | VM               the parent loop, trap 0x85c58, check 33
     e  _s22e.v  s22_p5   VM -> K85d04 i                memcpy, traps 0x85ce4 0x85cf0, parent[pn] := 0, vid
     f  _s22f.v  s22_p6   JOIN -> K85b0c (S i) | K85e50  v out of scope, check 30, the latch
   The Section hypotheses are the listing record SegPaLib.PALib B (piece a's walk hypothesis) and the two runtime rows
   the segment calls, at every FP state: strrchr (row 11, lib/B/Rt/RtSeg.v) and the memory-checking runtime's memcpy
   entry (YG0d.aintrin_realizes OCpy). AR's laws are proved (lib/B/YG0q.v AR_laws_ok), not assumed. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_c SegInstB LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s22k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require
LLVMFuzzerTestOneInput_s22a LLVMFuzzerTestOneInput_s22b LLVMFuzzerTestOneInput_s22c
LLVMFuzzerTestOneInput_s22d LLVMFuzzerTestOneInput_s22e LLVMFuzzerTestOneInput_s22f.
Import ListNotations.
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* piece a's walk hypothesis, the listing record of the runtime cells and wrappers (SegPaLib.PALib: the shadow base's
   GOT word and cell, api_env); the runtime entries S14 calls, at every FP state: row 11 (strrchr, 0x85ba0) and the
   memory-checking runtime's memcpy entry (0x85cdc) *)
Hypothesis TL : PALib B.
Hypothesis ASTRRCHR : forall fx0 : YK11.FPState,
  @RtSeg.astrrchr_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_strrchr).
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (pa_sigma SS___asan_memcpy).

Theorem lt_seg_S14 : lt_seg_S14_stmt B MT.
Proof.
apply (s22_compose B MT).
- eapply LLVMFuzzerTestOneInput_s22a.s22_p1; eassumption.
- eapply LLVMFuzzerTestOneInput_s22b.s22_p2; eassumption.
- eapply LLVMFuzzerTestOneInput_s22c.s22_p3; eassumption.
- eapply LLVMFuzzerTestOneInput_s22d.s22_p4; eassumption.
- eapply LLVMFuzzerTestOneInput_s22e.s22_p5; eassumption.
- eapply LLVMFuzzerTestOneInput_s22f.s22_p6; eassumption.
Qed.

End e.
End f.
End d.
