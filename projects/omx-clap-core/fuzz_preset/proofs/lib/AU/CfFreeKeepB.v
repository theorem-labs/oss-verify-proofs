(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-31: fuzz_preset: preset's free at image B' (#102 pin
   fuzz_preset.asan-ubsan d663f82d7f48, twin c90d4fa54d43) in KEEP form under the re-hide, at B''s record
   B := lib/Reusable/YD2l.TfibB, the cf instance CfImg_B / CfParams_preset.
   The B' twin of lib/A/CfFreeKeepA.v.
   rule 24: no function proved (kind: composition of proved tops by the layer's keep composer).

   [afree_realizes_cf_rh_keep_B] is YGcfMallocComposeKeep.afree_realizes_cf_rh_keep at tfibsegs / TfibB, by the
   layer's afree_realizes_cf_rh_of_parts_m_keep (lib/Reusable/YGcfMallocComposeKeep.v:469) at atpD := 1 (asan_free's
   alloc_type) and ARX := YGcfInstBase.ARXq_cf TfibB (fun i => i = as_inst TfibB) at AGif2cgif.AImg_cgif, from:
   - the wrapper walk: lib/AU/WrapFreeBWit.v:40 wrap_free_walk_keep_cf_rh_B, the primed keep record, closed, at
     that same relation (no bridge) and K := WrapFreeBF2.K_F;
   - Deallocate: lib/AU/PresetDeallocInstB.v:86 adealloc_realizes_raw_cf_em_m_rh_preset, closed, at
     ARXq_cf TfibB IOK_preset.  [IOK_preset_TfibB] states that this is the walk's relation, by reflexivity
     (lib/AU/PresetDeallocInstB.v:52 is IOK_preset), so no bridge is needed;
   - the relation's fact YGcfInstBase.ARXq_cf_ARcf, the relro rows (lib/AU/CfAroPresetB.v relro_seg_preset_AU /
     errno_relro_preset_AU).
   No premise is left: both parts are closed at TfibB.
   [afree_realizes_cf_rh_B] is the plain primed contract YG0dcfR.afree_realizes_cf_rh, by
   afree_realizes_cf_rh_of_keep (lib/Reusable/YGcfMallocComposeKeep.v:460). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK04 YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01 YG0f YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeKeep YG0dcfR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfAroPresetB PresetDeallocInstB WrapFreeBWit.
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_B.
#[local] Existing Instance CfParams_preset.

(* Deallocate's relation at B''s record is the wrapper walk's, ARXq_cf TfibB (fun i => i = as_inst TfibB). *)
Lemma IOK_preset_TfibB :
  ARXq_cf YD2l.TfibB PresetDeallocInstB.IOK_preset = ARXq_cf YD2l.TfibB (fun i => i = as_inst YD2l.TfibB).
Proof. reflexivity. Qed.

Theorem afree_realizes_cf_rh_keep_B : YGcfMallocComposeKeep.afree_realizes_cf_rh_keep tfibsegs YD2l.TfibB.
Proof.
pose proof YD2l.TfibB_syms as TB.
pose proof PresetDeallocInstB.adealloc_realizes_raw_cf_em_m_rh_preset as DL.
rewrite IOK_preset_TfibB in DL.
exact (YGcfMallocComposeKeep.afree_realizes_cf_rh_of_parts_m_keep tfibsegs YD2l.TfibB 1 _ _
  (ARXq_cf_ARcf YD2l.TfibB (fun i => i = as_inst YD2l.TfibB))
  CfAroPresetB.relro_seg_preset_AU (CfAroPresetB.errno_relro_preset_AU YD2l.TfibB TB) DL
  WrapFreeBWit.wrap_free_walk_keep_cf_rh_B).
Qed.

(* The plain primed free contract at B', by the keep form. *)
Theorem afree_realizes_cf_rh_B : YG0dcfR.afree_realizes_cf_rh tfibsegs YD2l.TfibB.
Proof. exact (YGcfMallocComposeKeep.afree_realizes_cf_rh_of_keep tfibsegs YD2l.TfibB afree_realizes_cf_rh_keep_B). Qed.

End a.
