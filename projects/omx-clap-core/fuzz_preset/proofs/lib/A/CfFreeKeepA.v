(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-31: fuzz_preset: preset's free at image A' (#102 pin
   fuzz_preset.asan 1be0f53d96cb) in KEEP form under the re-hide, at preset's record B := lib/A/AD2l.TfibB, the cf
   instance CfImg_A / CfParams_preset.
   rule 24: no function proved (kind: composition of proved tops by the layer's keep composer).

   [afree_realizes_cf_rh_keep_A] is YGcfMallocComposeKeep.afree_realizes_cf_rh_keep at tfibsegs / TfibB, by the
   layer's afree_realizes_cf_rh_of_parts_m_keep (lib/Reusable/YGcfMallocComposeKeep.v:469) at atpD := 1 (asan_free's
   alloc_type) and ARX := WrapFreeATop.ARXq_A TfibB, from:
   - the wrapper walk: lib/A/WrapFreeATop.v:498 wrap_free_walk_keep_rh_A, the primed keep
     record at K := WrapFreeAK.K_A, premise TfibSyms only (AD2l.TfibB_syms);
   - Deallocate: lib/A/PresetDeallocInstA.v:89 adealloc_realizes_raw_cf_em_m_rh_preset_A, closed, at
     ARXq_cf TfibB IOK_A.  [ARXq_A_TfibB] and [IOK_A_TfibB] state that the two parts' relations are both
     ARXq_cf TfibB (fun i => i = as_inst TfibB), by reflexivity (lib/A/WrapFreeATop.v:431 is that text at the
     instance AImgA.AImg_A; lib/A/YGcfInstDrainTopRhA.v:40 is IOK_A), so no bridge is needed;
   - the relation's fact WrapFreeATop.ARXq_A_HXA, the relro rows (lib/A/CfAroPresetA.v relro_seg_preset_A /
     errno_relro_preset_A).
   No premise is left: both parts are closed at TfibB.
   [afree_realizes_cf_rh_A] is the plain primed contract YG0dcfR.afree_realizes_cf_rh, by
   afree_realizes_cf_rh_of_keep (lib/Reusable/YGcfMallocComposeKeep.v:460). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK04 YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01 YG0f YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeKeep YG0dcfR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfImgA CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l CfAroPresetA YGcfInstDrainTopRhA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetDeallocInstA WrapFreeATop.
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_preset.

(* The wrapper walk's relation at preset's record is ARXq_cf TfibB (fun i => i = as_inst TfibB). *)
Lemma ARXq_A_TfibB : WrapFreeATop.ARXq_A AD2l.TfibB = ARXq_cf AD2l.TfibB (fun i => i = as_inst AD2l.TfibB).
Proof. reflexivity. Qed.

(* Deallocate's relation at preset's record is the same relation. *)
Lemma IOK_A_TfibB :
  ARXq_cf AD2l.TfibB YGcfInstDrainTopRhA.IOK_A = ARXq_cf AD2l.TfibB (fun i => i = as_inst AD2l.TfibB).
Proof. reflexivity. Qed.

Theorem afree_realizes_cf_rh_keep_A : YGcfMallocComposeKeep.afree_realizes_cf_rh_keep tfibsegs AD2l.TfibB.
Proof.
pose proof AD2l.TfibB_syms as TB.
pose proof PresetDeallocInstA.adealloc_realizes_raw_cf_em_m_rh_preset_A as DL.
rewrite IOK_A_TfibB, <- ARXq_A_TfibB in DL.
exact (YGcfMallocComposeKeep.afree_realizes_cf_rh_of_parts_m_keep tfibsegs AD2l.TfibB 1 _ _
  (WrapFreeATop.ARXq_A_HXA AD2l.TfibB)
  CfAroPresetA.relro_seg_preset_A (CfAroPresetA.errno_relro_preset_A AD2l.TfibB TB) DL
  (WrapFreeATop.wrap_free_walk_keep_rh_A AD2l.TfibB TB)).
Qed.

(* The plain primed free contract at A', by the keep form. *)
Theorem afree_realizes_cf_rh_A : YG0dcfR.afree_realizes_cf_rh tfibsegs AD2l.TfibB.
Proof. exact (YGcfMallocComposeKeep.afree_realizes_cf_rh_of_keep tfibsegs AD2l.TfibB afree_realizes_cf_rh_keep_A). Qed.

End a.
