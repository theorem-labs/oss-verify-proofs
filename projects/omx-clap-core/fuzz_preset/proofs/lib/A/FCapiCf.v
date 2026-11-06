(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the frame-area API of fuzz_preset's ASan image A at the second allocator instance, in
   the forms the instance's API record takes (YGcfNames.v: aa_stack_malloc_cf under `In cid cf_fs_classes`,
   aa_set_shadow_f5_cf at value 0xf5). FCapi.v's two theorems at ARx := ARcf tfibsegs B, with fs_iface from
   FCifaceCf.fs_iface_ARcf. astack_malloc_realizes_cf (YG0dcf.v) and aset_shadow_realizes_cf (YG0d2cf.v) are
   FCiface's astack_malloc_realizes_x and aset_shadow_realizes_x at ARx := ARcf tfibsegs B, by conversion
   (ecall_pre_cf is ecall_pre_x there). The pc is FCimg's SET_SHADOW_F5. No image numeral appears in this file. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05 FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG0ncf YG0dcf YG0d2cf FCifaceCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m AF0x FCimg FCapi.
Import ListNotations.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Theorem preset_aa_stack_malloc_cf : forall B, AR_laws_cf tfibsegs B -> TfibSyms B ->
  forall cid, In cid [0; 1; 3] -> astack_malloc_realizes_cf tfibsegs B cid.
Proof.
  intros B LAWS TB cid Hc.
  exact (preset_stack_malloc_x B (ARcf tfibsegs B) (fs_iface_ARcf tfibsegs B LAWS) TB cid Hc).
Qed.

Theorem preset_aa_set_shadow_f5_cf : forall B, AR_laws_cf tfibsegs B -> TfibSyms B ->
  aset_shadow_realizes_cf tfibsegs B SET_SHADOW_F5 0xf5.
Proof.
  intros B LAWS TB.
  exact (preset_set_shadow_f5_x B (ARcf tfibsegs B) (fs_iface_ARcf tfibsegs B LAWS) TB).
Qed.

End a.
