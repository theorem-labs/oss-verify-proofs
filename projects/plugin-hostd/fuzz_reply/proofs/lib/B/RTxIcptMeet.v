(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/plugin-hostd/fuzz_reply/lib/A/RTxIcpt.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/RTxIcpt.v, with its module paths and module names changed; 1 of its 21 lines of code is new or changed and 60 lines of the source are left out. *)
(* The image-B twin of lib/A/RTxIcpt.v's cf_meet: RTxIcpt.icpt_laws_x_cf_via_rt (icpt_laws_x at ARx := ARcf tfibsegs B,
   from AR_laws_cf through RTx.rt_laws_cf and alc_zshadow) and B/YD2mcf.v's icpt_laws_x_cf (the same AR_laws_cf /
   ARmcf fields cited directly) inhabit one type.
   A separate file, which no file Requires: a Require of YD2mcf loads lib/B/YCbqG.v, and a loaded lib.B.YCbqG takes the
   partial name `YCbqG.` (`Locate YCbqG.alx_zshadow` then names lib.B.YCbqG.alx_zshadow first).  Inside RTxIcpt.v
   that load broke lib/B/TopX_RT3.v:65, which cites `YCbqG.alx_zshadow` for the Reusable law record. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YF0m YE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require RTxIcpt YD2mcf.
Import ListNotations.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c. Context {ci : CfImg} {cp : CfParams}.
Definition cf_meet :=
(RTxIcpt.icpt_laws_x_cf_via_rt, fun B L => YD2mcf.icpt_laws_x_cf B L) :
(forall B, AR_laws_cf tfibsegs B -> icpt_laws_x B (fun ly S Hp W mem md => ARcf tfibsegs B ly S Hp W mem md)) *
(forall B, AR_laws_cf tfibsegs B -> icpt_laws_x B (fun ly S Hp W mem md => ARcf tfibsegs B ly S Hp W mem md)).
End c.
End a.
