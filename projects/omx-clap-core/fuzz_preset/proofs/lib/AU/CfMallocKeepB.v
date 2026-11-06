(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-31: fuzz_preset: preset's malloc at image B' (#102 pin
   fuzz_preset.asan-ubsan d663f82d7f48, twin c90d4fa54d43) in KEEP form, at B''s record B := lib/Reusable/YD2l.TfibB,
   the cf instance CfImg_B / CfParams_preset.  The B' twin of lib/A/CfMallocKeepA.v.
   rule 24: no function proved (kind: composition of proved tops by the layer's keep composer).

   [amalloc_realizes_cf_keep_B] is YGcfMallocComposeKeep.amalloc_realizes_cf_keep at tfibsegs / TfibB, by the layer's
   amalloc_realizes_cf_of_parts_m_keep (lib/Reusable/YGcfMallocComposeKeep.v:216) at nmax := cf_malloc_max, al := 8,
   atp := 1, acf := 1 (malloc's call), ARX := YGcfInstBase.ARXq_cf TfibB (fun i => i = as_inst TfibB) at AImg_cgif,
   from:
   - the wrapper walk: lib/AU/WrapMallocBInst.v:46 wrap_malloc_walk_keep_cf_B, closed, at that same relation (no
     bridge) and K := WrapMallocBM1.K_B;
   - Allocate: lib/AU/AllocGtopPresetMB.v aalloc_realizes_cf_em_m_TfibB_B;
   - the relation's facts YGcfInstBase.ARXq_cf_ARcf / ARXq_cf_xs, nmax_cf_ok (YGcfMallocComposeE.nmax_cf_ok_of_w),
     the relro rows (lib/AU/CfAroPresetB.v relro_seg_preset_AU / errno_relro_preset_AU).
   Its premises are aalloc_realizes_cf_em_m_TfibB_B's, carried through by name: the secondary IFSc / IFSEc at TfibB.
   [amalloc_realizes_cf_B] is the plain contract YG0dcf.amalloc_realizes_cf, by amalloc_realizes_cf_of_keep.
   [amalloc_realizes_cf_keep_closed_B] / [amalloc_realizes_cf_closed_B]: the same with no premise, over
   AllocGtopPresetMB.aalloc_realizes_cf_em_m_TfibB_closed_B (IFSc / IFSEc by lib/AU/YGcfInstSecB.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK04 YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01 YG0f YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif AGif0cgif AGif4cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require AGif4 ErrnoGS YGcfRmodel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocCompose YGcfMallocComposeE.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstHit YG0dcf YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfAroPresetB AllocGtopPresetMB WrapMallocBInst.
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_B.
#[local] Existing Instance CfParams_preset.

Theorem amalloc_realizes_cf_keep_B :
  (forall Hp, AGif4.AIfaceSw YD2l.TfibB (U_cf YD2l.TfibB) malloc_cf
     (ARXq_cf YD2l.TfibB (fun i => i = as_inst YD2l.TfibB) Hp) (AOXm_cf YD2l.TfibB) (YGcfRmodel.rpre_cfr YD2l.TfibB)
     cf_malloc_max LIVE_MAX qtight (YGcfInstHit.dpost_cf YD2l.TfibB) cf_pc_malloc_max cf_pc_spin_shadow cf_malloc_max
     (2 ^ 29) (2 ^ 30)) ->
  (forall Hp, ErrnoGS.AIfaceSE YD2l.TfibB (U_cf YD2l.TfibB) malloc_cf
     (ARXq_cf YD2l.TfibB (fun i => i = as_inst YD2l.TfibB) Hp) (AOXm_cf YD2l.TfibB) (YGcfRmodel.rpre_cfr YD2l.TfibB)
     cf_malloc_max LIVE_MAX qtight (YGcfInstHit.dpost_cf YD2l.TfibB) cf_pc_malloc_max cf_pc_spin_shadow) ->
  YGcfMallocComposeKeep.amalloc_realizes_cf_keep tfibsegs YD2l.TfibB.
Proof.
intros IFS IFSE.
pose proof YD2l.TfibB_syms as TB.
exact (YGcfMallocComposeKeep.amalloc_realizes_cf_of_parts_m_keep tfibsegs YD2l.TfibB cf_malloc_max 8 1 1 _ _
  nmax_cf_ok_of_w (ARXq_cf_ARcf YD2l.TfibB (fun i => i = as_inst YD2l.TfibB))
  (ARXq_cf_xs YD2l.TfibB (fun i => i = as_inst YD2l.TfibB))
  CfAroPresetB.relro_seg_preset_AU (CfAroPresetB.errno_relro_preset_AU YD2l.TfibB TB)
  (AllocGtopPresetMB.aalloc_realizes_cf_em_m_TfibB_B 1 (or_intror eq_refl) IFS IFSE)
  (WrapMallocBInst.wrap_malloc_walk_keep_cf_B cf_malloc_max)).
Qed.

(* The plain malloc contract at B', by the keep form. *)
Theorem amalloc_realizes_cf_B :
  (forall Hp, AGif4.AIfaceSw YD2l.TfibB (U_cf YD2l.TfibB) malloc_cf
     (ARXq_cf YD2l.TfibB (fun i => i = as_inst YD2l.TfibB) Hp) (AOXm_cf YD2l.TfibB) (YGcfRmodel.rpre_cfr YD2l.TfibB)
     cf_malloc_max LIVE_MAX qtight (YGcfInstHit.dpost_cf YD2l.TfibB) cf_pc_malloc_max cf_pc_spin_shadow cf_malloc_max
     (2 ^ 29) (2 ^ 30)) ->
  (forall Hp, ErrnoGS.AIfaceSE YD2l.TfibB (U_cf YD2l.TfibB) malloc_cf
     (ARXq_cf YD2l.TfibB (fun i => i = as_inst YD2l.TfibB) Hp) (AOXm_cf YD2l.TfibB) (YGcfRmodel.rpre_cfr YD2l.TfibB)
     cf_malloc_max LIVE_MAX qtight (YGcfInstHit.dpost_cf YD2l.TfibB) cf_pc_malloc_max cf_pc_spin_shadow) ->
  YG0dcf.amalloc_realizes_cf tfibsegs YD2l.TfibB.
Proof.
intros IFS IFSE.
exact (YGcfMallocComposeKeep.amalloc_realizes_cf_of_keep tfibsegs YD2l.TfibB (amalloc_realizes_cf_keep_B IFS IFSE)).
Qed.

(* ---- CLOSED: Allocate at B''s record with no premise (AllocGtopPresetMB.aalloc_realizes_cf_em_m_TfibB_closed_B). *)
Corollary amalloc_realizes_cf_keep_closed_B : YGcfMallocComposeKeep.amalloc_realizes_cf_keep tfibsegs YD2l.TfibB.
Proof.
pose proof YD2l.TfibB_syms as TB.
exact (YGcfMallocComposeKeep.amalloc_realizes_cf_of_parts_m_keep tfibsegs YD2l.TfibB cf_malloc_max 8 1 1 _ _
  nmax_cf_ok_of_w (ARXq_cf_ARcf YD2l.TfibB (fun i => i = as_inst YD2l.TfibB))
  (ARXq_cf_xs YD2l.TfibB (fun i => i = as_inst YD2l.TfibB))
  CfAroPresetB.relro_seg_preset_AU (CfAroPresetB.errno_relro_preset_AU YD2l.TfibB TB)
  (AllocGtopPresetMB.aalloc_realizes_cf_em_m_TfibB_closed_B 1 (or_intror eq_refl))
  (WrapMallocBInst.wrap_malloc_walk_keep_cf_B cf_malloc_max)).
Qed.

Corollary amalloc_realizes_cf_closed_B : YG0dcf.amalloc_realizes_cf tfibsegs YD2l.TfibB.
Proof. exact (YGcfMallocComposeKeep.amalloc_realizes_cf_of_keep tfibsegs YD2l.TfibB amalloc_realizes_cf_keep_closed_B). Qed.

End a.
