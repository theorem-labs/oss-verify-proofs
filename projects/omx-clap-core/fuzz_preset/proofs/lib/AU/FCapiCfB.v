(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the frame-area API of fuzz_preset's ASan-UBSan image B at the second allocator instance,
   the image-B twin of lib/A/FCapiCf.v (blob e29123ff8116) by the same module-path map that gen_fc_b.py applies to
   lib/A/FCapi.v (lib/AU/FCapi.v:4; A<x> -> Y<x>, FCimg -> FCimgB, lib.A FCapi -> lib.AU FCapi), with both theorems
   renamed with a _B suffix (:23, :30); no other code change. It builds against the head's lib/AU FCimgB and FCapi (:18); as history (of the 10 blobs below only FCm0r, FCm1r and FCm3r are the head's), it was first built against a Theorem Labs lane's image-B frame-class chain, taken by path from
   origin/cold/h-hpreset-7-frameclass 2cca8b644ee7 (lib/AU blobs: FCapi d9cde3c681ba, FCf5 0d2e2435408f,
   FCimgB b4380b440ea5, FCm0r f82124ec3b50, FCm0s 8a5323b82e64, FCm1r 5d44271d1c6a, FCm1s 68fda7b03e80,
   FCm3r ecf9803a2ef1, FCm3s 42a8954d22cd, FCxA 39e380adbd7a).
   FCapi.v's two theorems at ARx := ARcf tfibsegs B, with fs_iface from FCifaceCf.fs_iface_ARcf.
   astack_malloc_realizes_cf (YG0dcf.v) and aset_shadow_realizes_cf (YG0d2cf.v) are FCiface's
   astack_malloc_realizes_x and aset_shadow_realizes_x at ARx := ARcf tfibsegs B, by conversion (ecall_pre_cf is
   ecall_pre_x there). The pc is FCimgB's SET_SHADOW_F5. No image numeral appears in this file. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05 FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG0ncf YG0dcf YG0d2cf FCifaceCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import FCimgB FCapi.
Import ListNotations.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Theorem preset_aa_stack_malloc_cf_B : forall B, AR_laws_cf tfibsegs B -> TfibSyms B ->
  forall cid, In cid [0; 1; 3] -> astack_malloc_realizes_cf tfibsegs B cid.
Proof.
  intros B LAWS TB cid Hc.
  exact (preset_stack_malloc_x B (ARcf tfibsegs B) (fs_iface_ARcf tfibsegs B LAWS) TB cid Hc).
Qed.

Theorem preset_aa_set_shadow_f5_cf_B : forall B, AR_laws_cf tfibsegs B -> TfibSyms B ->
  aset_shadow_realizes_cf tfibsegs B SET_SHADOW_F5 0xf5.
Proof.
  intros B LAWS TB.
  exact (preset_set_shadow_f5_x B (ARcf tfibsegs B) (fs_iface_ARcf tfibsegs B LAWS) TB).
Qed.

End a.
