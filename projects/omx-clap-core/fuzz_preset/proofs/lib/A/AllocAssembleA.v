(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/AllocAssembleA.v, with its module paths changed; 23 of its 66 lines of code are new or changed and 1 line of the source is left out. *)
(* Theorem Labs, 2026-10: fuzz_preset's realloc contracts at image A' in the keep forms that the driver
   (lib/A/Prog/Ent102DrvTopA3.v) and the tx_put walk (lib/A/Prog/TxPut102A_Base.v) take as premises, each proved
   here from proved per-image facts.
   - [arealloc_realizes_cf_A]: realloc(p, n) in its keep _k form (YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep) at
     the program listing's segments and realloc entry, for every run ceiling, float state, ghost set and room k: the
     text of Ent102DrvTopA3's H_arealloc_realizes_cf_A. It is one application of the layer's composition
     YGcfInstReallocKKeep.arealloc_realizes_cf_k_of_parts_keep at segs := tfibsegs, B := AD2l.TfibB,
     (nmax, al, atp, acf, atpD) := (cf_malloc_max, 8, 1, 1, 1), ARX := RGcfWalkA.ARXA TfibB (the layer's call-site
     relation YGcfInstBase.ARXq_cf at AImg_A with the binary's own instance object) and K1 / K2 / K3 := the realloc
     walk's (RGcfK.K1A, RGcfSegs2a.K2A / K3A). The listing's segments and realloc entry are tfibsegs and CfImg_A's
     cf_pc_wrap_realloc by conversion (PAImg_prog.PI_prog_A: pa_segs := Img0.rsegs, the segment list of tfibsegs;
     pa_sigma AS___wrap_realloc is the entry CfImg_A names).
   - [arealloc_null_realizes_cf_A]: realloc(NULL, n) in its keep form
     (YGcfReallocComposeKeep.arealloc_null_realizes_cf_keep) at the same segments and entry, for every run ceiling,
     float state and ghost set: TxPut102A_Base's tp_AREALN at PA := PI_prog_A, ci := CfImg_A, cp := CfParams_preset,
     B := TfibB. It is one application of the layer's composition
     YGcfReallocComposeKeep.arealloc_null_realizes_cf_of_parts_keep at the same segs, B and ARX,
     (nmax, al, atp, acf) := (cf_malloc_max, 8, 1, 1) and Kn := the null walk's (RGcfK.KnA).
   - malloc and free, the D2p layer's premises (lib/A/PresetD2pAPf.v): not proved here; section 2 below.
   rule 24: proves no function (kind: invariant lemma: a composition over proved per-image facts). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05 YG00 YG0f YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeE YGcfInstBase YGcfInstRealloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstReallocKKeep YGcfReallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AD2l CfImgA CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AImgA RGcfK RGcfSegs2a RGcfWalkA RGcfWalkKeepRhA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetImg_errnoword CfAroPresetA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AllocGtopPresetM YGcfInstSecA PresetDeallocInstA.
Local Open Scope Z_scope.

Section a.
(* the image's CfImg record and preset's allocator parameters, the instances every leaf below is stated at *)
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_preset.

(* ---------------------------------------------------------------------- *)
(* 1. realloc. The twelve premises of arealloc_realizes_cf_k_of_parts_keep, in its order, and their proofs:
   acall_prefix_cf        YGcfInstRealloc.acall_prefix_cf_ok (any segment list, any record)
   acall_xs_cf            YGcfInstRealloc.acall_xs_cf_ok at AImg_A (whose im_segs is tfibsegs)
   errno_word_cf          PresetImg_errnoword.errno_word_cf_A_TfibB
   relro_seg_t            CfAroPresetA.relro_seg_preset_A
   errno_relro_t          CfAroPresetA.errno_relro_preset_A at AD2l.TfibB_syms
   nmax_cf_ok             YGcfMallocComposeE.nmax_cf_ok_of_w
   ARX_ARcf / ARX_xs      YGcfInstBase.ARXq_cf_ARcf / ARXq_cf_xs at AImg_A
   ARX_qmh                YGcfInstRealloc.ARX_qm_cfq at AImg_A
   Allocate (em_m)        AllocGtopPresetM.aalloc_realizes_cf_em_m_TfibB_A at acf := 1, over the two secondary
                          interfaces YGcfInstSecA.ifaceSw_TfibB_A / ifaceSE_TfibB_A
   Deallocate (em_m_rh)   PresetDeallocInstA.adealloc_realizes_raw_cf_em_m_rh_preset_A
   the walk record        RGcfWalkKeepRhA.wrap_realloc_walk_keep_cf_rh_A at nmax := cf_malloc_max
   Every leaf's relation is ARXA TfibB by delta / eta: ARXA unfolds through RGcfLaws.ARXqA to ARXq_cf at AImg_A and
   the instance object (fun i => i = as_inst TfibB), which is Deallocate's IOK_A by definition. Every leaf is
   generic in the float state and the run ceiling, so the two binders below are the leaves' own. *)
Theorem arealloc_realizes_cf_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (Hp : list Z) (k : nat),
  YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep (fx := fx) (rc := rc) (ci := CfImg_A) (cp := CfParams_preset)
    (@YC4aP.pa_segs rc A_prog_listing (@PI_prog_A rc)) TfibB Hp
    (@YC4aP.pa_sigma rc A_prog_listing (@PI_prog_A rc) YPsym.AS___wrap_realloc) k.
Proof.
intros rc fx Hp k.
change (YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep (fx := fx) (rc := rc) (ci := CfImg_A)
  (cp := CfParams_preset) tfibsegs TfibB Hp (@cf_pc_wrap_realloc CfImg_A) k).
exact (YGcfInstReallocKKeep.arealloc_realizes_cf_k_of_parts_keep (fx := fx) (rc := rc) (ci := CfImg_A)
  (cp := CfParams_preset) tfibsegs TfibB cf_malloc_max 8 1 1 1
  (RGcfWalkA.ARXA TfibB) (RGcfK.K1A TfibB) (RGcfSegs2a.K2A TfibB) (RGcfSegs2a.K3A TfibB)
  (YGcfInstRealloc.acall_prefix_cf_ok tfibsegs TfibB)
  (YGcfInstRealloc.acall_xs_cf_ok (IM := AImgA.AImg_A) TfibB)
  PresetImg_errnoword.errno_word_cf_A_TfibB
  CfAroPresetA.relro_seg_preset_A
  (CfAroPresetA.errno_relro_preset_A TfibB TfibB_syms)
  YGcfMallocComposeE.nmax_cf_ok_of_w
  (YGcfInstBase.ARXq_cf_ARcf (IM := AImgA.AImg_A) TfibB (fun i => i = as_inst TfibB))
  (YGcfInstBase.ARXq_cf_xs (IM := AImgA.AImg_A) TfibB (fun i => i = as_inst TfibB))
  (YGcfInstRealloc.ARX_qm_cfq (IM := AImgA.AImg_A) TfibB (fun i => i = as_inst TfibB))
  (AllocGtopPresetM.aalloc_realizes_cf_em_m_TfibB_A 1 (or_intror eq_refl)
     YGcfInstSecA.ifaceSw_TfibB_A YGcfInstSecA.ifaceSE_TfibB_A)
  PresetDeallocInstA.adealloc_realizes_raw_cf_em_m_rh_preset_A
  (RGcfWalkKeepRhA.wrap_realloc_walk_keep_cf_rh_A TfibB TfibB_syms cf_malloc_max)
  Hp k).
Qed.

(* ---------------------------------------------------------------------- *)
(* 1b. realloc(NULL, n). The nine premises of arealloc_null_realizes_cf_of_parts_keep, in its order, and their proofs:
   acall_prefix_cf / acall_xs_cf / nmax_cf_ok / ARX_ARcf / ARX_xs / relro_seg_t / errno_relro_t / Allocate (em_m)
                          the proofs section 1 cites for the premises of the same names
   the null walk record   RGcfWalkA.wrap_realloc_null_walk_keep_cf_A at nmax := cf_malloc_max
   realloc(NULL, n) frees no live block, so Deallocate is not a premise. *)
Theorem arealloc_null_realizes_cf_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (Hp : list Z),
  YGcfReallocComposeKeep.arealloc_null_realizes_cf_keep (fx := fx) (rc := rc) (ci := CfImg_A) (cp := CfParams_preset)
    (@YC4aP.pa_segs rc A_prog_listing (@PI_prog_A rc)) TfibB Hp
    (@YC4aP.pa_sigma rc A_prog_listing (@PI_prog_A rc) YPsym.AS___wrap_realloc).
Proof.
intros rc fx Hp.
change (YGcfReallocComposeKeep.arealloc_null_realizes_cf_keep (fx := fx) (rc := rc) (ci := CfImg_A)
  (cp := CfParams_preset) tfibsegs TfibB Hp (@cf_pc_wrap_realloc CfImg_A)).
exact (YGcfReallocComposeKeep.arealloc_null_realizes_cf_of_parts_keep (fx := fx) (rc := rc) (ci := CfImg_A)
  (cp := CfParams_preset) tfibsegs TfibB cf_malloc_max 8 1 1 (RGcfWalkA.ARXA TfibB) RGcfK.KnA
  (YGcfInstRealloc.acall_prefix_cf_ok tfibsegs TfibB)
  (YGcfInstRealloc.acall_xs_cf_ok (IM := AImgA.AImg_A) TfibB)
  YGcfMallocComposeE.nmax_cf_ok_of_w
  (YGcfInstBase.ARXq_cf_ARcf (IM := AImgA.AImg_A) TfibB (fun i => i = as_inst TfibB))
  (YGcfInstBase.ARXq_cf_xs (IM := AImgA.AImg_A) TfibB (fun i => i = as_inst TfibB))
  CfAroPresetA.relro_seg_preset_A
  (CfAroPresetA.errno_relro_preset_A TfibB TfibB_syms)
  (AllocGtopPresetM.aalloc_realizes_cf_em_m_TfibB_A 1 (or_intror eq_refl)
     YGcfInstSecA.ifaceSw_TfibB_A YGcfInstSecA.ifaceSE_TfibB_A)
  (RGcfWalkA.wrap_realloc_null_walk_keep_cf_A TfibB TfibB_syms cf_malloc_max)
  Hp).
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. malloc and free: not proved in this file. PresetD2pAPf's H_amalloc_realizes_cf_A is `forall rc` and its
   H_afree_realizes_cf_A is `forall rc fx`. The per-image keep proofs of these two contracts are
   lib/A/CfMallocKeepA.v's amalloc_realizes_cf_keep_closed_A and lib/A/CfFreeKeepA.v's
   afree_realizes_cf_rh_keep_A. *)

End a.
