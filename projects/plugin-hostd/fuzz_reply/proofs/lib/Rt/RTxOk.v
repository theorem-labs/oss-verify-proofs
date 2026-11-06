(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: lib/Rt/RTx.v's rt_laws is SATISFIABLE at the real cf instance, with no premise: rt_laws_ok_cf.
   rt_laws segs B (ARcf segs B) follows from YG0lawscf.AR_laws_ok_cf (the cf instance's laws, proved for every segs and
   B) through RTx.rt_laws_cf. Kept out of RTx.v so the runtime walks that Require RTx do not load the cf law proofs. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG0ncf YG0dcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import RTx.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable segs : list Segment.
Variable B : asyms.
Theorem rt_laws_ok_cf : rt_laws segs B (ARcf segs B).
Proof. exact (rt_laws_cf segs B (AR_laws_ok_cf segs B)). Qed.
End a.
