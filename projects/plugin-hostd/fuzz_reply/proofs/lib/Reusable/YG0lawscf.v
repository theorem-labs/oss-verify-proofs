(* CARRIED from a working branch 3dd49fa29fa14b99e3c465cacbfe79a09756bb26,
   proofs/omx-clap-core/fuzz_preset/lib/Reusable/YG0lawscf.v, sha256 e3e4ee72f507d3d755c3cce4f9265978f3367b0b7c8ff5e3fb1839bc6346fc49.
   DO NOT EDIT in this tree: change it on that branch and carry it again. The only change
   made here is the module prefix OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf). cgif's AR_laws_ok (YG0q.v),
   the assembly of the AR laws, over ARcf: AR_laws_ok_cf : AR_laws_cf segs B. Each field is the _cf law of the
   lane file that proves it: YG0scf.v (twelve laws), YG0sshcf.v (AR_shadow_law_ok_cf), YG0qcf.v
   (AR_frame_law_ok_cf), YG0tcf.v (AR_head_frame_law_ok_cf, the 15th field, which cgif's record lacks).
   It is a file of its own, not part of YG0qcf.v, because YG0tcf.v Requires YG0qcf.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0scf YG0sshcf YG0qcf YG0tcf.
Import ListNotations.
Local Open Scope Z_scope.
Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable segs : list Segment.
Variable B : asyms.
Theorem AR_laws_ok_cf : AR_laws_cf segs B.
Proof.
constructor.
- exact (AR_blocks_law_ok_cf segs B).
- exact (AR_shadow_law_ok_cf segs B).
- exact (AR_zshadow_law_ok_cf segs B).
- exact (AR_frame_law_ok_cf segs B).
- exact (AR_frames_law_ok_cf segs B).
- exact (AR_flag_law_ok_cf segs B).
- exact (AR_const_law_ok_cf segs B).
- exact (AR_stack_law_ok_cf segs B).
- exact (AR_wle_law_ok_cf segs B).
- exact (AR_layout_law_ok_cf segs B).
- exact (AR_owned_low_law_ok_cf segs B).
- exact (AR_owned_image_law_ok_cf segs B).
- exact (AR_sep_law_ok_cf segs B).
- exact (AR_client_img_law_ok_cf segs B).
- exact (AR_head_frame_law_ok_cf segs B).
Qed.
End j.
