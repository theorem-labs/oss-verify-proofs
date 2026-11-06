(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset's realloc contracts at image B' in the keep forms that the driver
   (lib/AU/Prog/Ent102DrvTopB3.v) and the tx_put walk (lib/B/Prog/TxPut102B_Base.v) take as premises, each proved
   here from proved per-image facts. The B' twin of lib/A/AllocAssembleA.v.
   - [arealloc_realizes_cf_B]: realloc(p, n) in its keep _k form (YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep) at
     the program listing's segments and realloc entry, for every run ceiling, float state, ghost set and room k: the
     text of Ent102DrvTopB3's H_arealloc_realizes_cf_B. It is one application of the layer's composition
     YGcfInstReallocKKeep.arealloc_realizes_cf_k_of_parts_keep at segs := YB1v.tfibsegs, B := YD2l.TfibB,
     (nmax, al, atp, acf, atpD) := (cf_malloc_max, 8, 1, 1, 1), ARX := RGcfWalkB.ARXB TfibB (the layer's call-site
     relation YGcfInstBase.ARXq_cf at AImg_cgif with the binary's own instance object) and K1 / K2 / K3 := the
     realloc walk's (RGcfKB.K1B, RGcfSegs2aB.K2B / K3B). The listing's segments and realloc entry are tfibsegs and
     CfImg_B's cf_pc_wrap_realloc by conversion (lib/B/PAImg_prog.v PI_prog_B: pa_segs := Img0.rsegs, the segment
     list of tfibsegs; pa_sigma AS___wrap_realloc is the entry CfImg_B names).
   - [arealloc_null_realizes_cf_B]: realloc(NULL, n) in its keep form
     (YGcfReallocComposeKeep.arealloc_null_realizes_cf_keep) at the same segments and entry, for every run ceiling,
     float state and ghost set: TxPut102B_Base's tp_AREALN at PA := PI_prog_B, ci := CfImg_B, cp := CfParams_preset,
     B := TfibB. It is one application of the layer's composition
     YGcfReallocComposeKeep.arealloc_null_realizes_cf_of_parts_keep at the same segs, B and ARX,
     (nmax, al, atp, acf) := (cf_malloc_max, 8, 1, 1) and Kn := the null walk's (RGcfKB.KnB).
   - malloc and free, the D2p layer's premises (lib/AU/PresetD2pBPf.v): not proved here; section 2 below.
   rule 24: proves no function (kind: invariant lemma: a composition over proved per-image facts). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05 YG00 YG0f YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeE YGcfInstBase YGcfInstRealloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstReallocKKeep YGcfReallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AGif2cgif RGcfKB RGcfSegs2aB RGcfWalkB RGcfWalkKeepRhB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require ErrnoWordB CfAroPresetB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AllocGtopPresetMB YGcfInstSecB PresetDeallocInstB.
Local Open Scope Z_scope.

Section a.
(* the image's CfImg record and preset's allocator parameters, the instances every leaf below is stated at *)
#[local] Existing Instance CfImg_B.
#[local] Existing Instance CfParams_preset.

(* ---------------------------------------------------------------------- *)
(* 1. realloc. The twelve premises of arealloc_realizes_cf_k_of_parts_keep, in its order, and their proofs:
   acall_prefix_cf        YGcfInstRealloc.acall_prefix_cf_ok (any segment list, any record)
   acall_xs_cf            YGcfInstRealloc.acall_xs_cf_ok at AImg_cgif (whose im_segs is tfibsegs)
   errno_word_cf          ErrnoWordB.errno_word_cf_B at YD2l.TfibB_syms
   relro_seg_t            CfAroPresetB.relro_seg_preset_AU
   errno_relro_t          CfAroPresetB.errno_relro_preset_AU at YD2l.TfibB_syms
   nmax_cf_ok             YGcfMallocComposeE.nmax_cf_ok_of_w
   ARX_ARcf / ARX_xs      YGcfInstBase.ARXq_cf_ARcf / ARXq_cf_xs at AImg_cgif
   ARX_qmh                YGcfInstRealloc.ARX_qm_cfq at AImg_cgif
   Allocate (em_m)        AllocGtopPresetMB.aalloc_realizes_cf_em_m_TfibB_B at acf := 1, over the two secondary
                          interfaces YGcfInstSecB.ifaceSw_TfibB_B / ifaceSE_TfibB_B
   Deallocate (em_m_rh)   PresetDeallocInstB.adealloc_realizes_raw_cf_em_m_rh_preset
   the walk record        RGcfWalkKeepRhB.wrap_realloc_walk_keep_cf_rh_B at nmax := cf_malloc_max
   Every leaf's relation is ARXB TfibB by delta / eta: ARXB unfolds through RGcfLawsB.ARXqB to ARXq_cf at AImg_cgif
   and the instance object (fun i => i = as_inst TfibB), which is Deallocate's IOK_preset by definition. Every leaf
   is generic in the float state and the run ceiling, so the two binders below are the leaves' own. *)
Theorem arealloc_realizes_cf_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (Hp : list Z) (k : nat),
  YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep (fx := fx) (rc := rc) (ci := CfImg_B) (cp := CfParams_preset)
    (@YC4aP.pa_segs rc B_prog_listing (@PI_prog_B rc)) TfibB Hp
    (@YC4aP.pa_sigma rc B_prog_listing (@PI_prog_B rc) YPsym.AS___wrap_realloc) k.
Proof.
intros rc fx Hp k.
change (YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep (fx := fx) (rc := rc) (ci := CfImg_B)
  (cp := CfParams_preset) tfibsegs TfibB Hp (@cf_pc_wrap_realloc CfImg_B) k).
exact (YGcfInstReallocKKeep.arealloc_realizes_cf_k_of_parts_keep (fx := fx) (rc := rc) (ci := CfImg_B)
  (cp := CfParams_preset) tfibsegs TfibB cf_malloc_max 8 1 1 1
  (RGcfWalkB.ARXB TfibB) (RGcfKB.K1B TfibB) (RGcfSegs2aB.K2B TfibB) (RGcfSegs2aB.K3B TfibB)
  (YGcfInstRealloc.acall_prefix_cf_ok tfibsegs TfibB)
  (YGcfInstRealloc.acall_xs_cf_ok (IM := AGif2cgif.AImg_cgif) TfibB)
  (ErrnoWordB.errno_word_cf_B TfibB TfibB_syms)
  CfAroPresetB.relro_seg_preset_AU
  (CfAroPresetB.errno_relro_preset_AU TfibB TfibB_syms)
  YGcfMallocComposeE.nmax_cf_ok_of_w
  (YGcfInstBase.ARXq_cf_ARcf (IM := AGif2cgif.AImg_cgif) TfibB (fun i => i = as_inst TfibB))
  (YGcfInstBase.ARXq_cf_xs (IM := AGif2cgif.AImg_cgif) TfibB (fun i => i = as_inst TfibB))
  (YGcfInstRealloc.ARX_qm_cfq (IM := AGif2cgif.AImg_cgif) TfibB (fun i => i = as_inst TfibB))
  (AllocGtopPresetMB.aalloc_realizes_cf_em_m_TfibB_B 1 (or_intror eq_refl)
     YGcfInstSecB.ifaceSw_TfibB_B YGcfInstSecB.ifaceSE_TfibB_B)
  PresetDeallocInstB.adealloc_realizes_raw_cf_em_m_rh_preset
  (RGcfWalkKeepRhB.wrap_realloc_walk_keep_cf_rh_B TfibB TfibB_syms cf_malloc_max)
  Hp k).
Qed.

(* ---------------------------------------------------------------------- *)
(* 1b. realloc(NULL, n). The nine premises of arealloc_null_realizes_cf_of_parts_keep, in its order, and their proofs:
   acall_prefix_cf / acall_xs_cf / nmax_cf_ok / ARX_ARcf / ARX_xs / relro_seg_t / errno_relro_t / Allocate (em_m)
                          the proofs section 1 cites for the premises of the same names
   the null walk record   RGcfWalkB.wrap_realloc_null_walk_keep_cf_B at nmax := cf_malloc_max
   realloc(NULL, n) frees no live block, so Deallocate is not a premise. *)
Theorem arealloc_null_realizes_cf_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (Hp : list Z),
  YGcfReallocComposeKeep.arealloc_null_realizes_cf_keep (fx := fx) (rc := rc) (ci := CfImg_B) (cp := CfParams_preset)
    (@YC4aP.pa_segs rc B_prog_listing (@PI_prog_B rc)) TfibB Hp
    (@YC4aP.pa_sigma rc B_prog_listing (@PI_prog_B rc) YPsym.AS___wrap_realloc).
Proof.
intros rc fx Hp.
change (YGcfReallocComposeKeep.arealloc_null_realizes_cf_keep (fx := fx) (rc := rc) (ci := CfImg_B)
  (cp := CfParams_preset) tfibsegs TfibB Hp (@cf_pc_wrap_realloc CfImg_B)).
exact (YGcfReallocComposeKeep.arealloc_null_realizes_cf_of_parts_keep (fx := fx) (rc := rc) (ci := CfImg_B)
  (cp := CfParams_preset) tfibsegs TfibB cf_malloc_max 8 1 1 (RGcfWalkB.ARXB TfibB) RGcfKB.KnB
  (YGcfInstRealloc.acall_prefix_cf_ok tfibsegs TfibB)
  (YGcfInstRealloc.acall_xs_cf_ok (IM := AGif2cgif.AImg_cgif) TfibB)
  YGcfMallocComposeE.nmax_cf_ok_of_w
  (YGcfInstBase.ARXq_cf_ARcf (IM := AGif2cgif.AImg_cgif) TfibB (fun i => i = as_inst TfibB))
  (YGcfInstBase.ARXq_cf_xs (IM := AGif2cgif.AImg_cgif) TfibB (fun i => i = as_inst TfibB))
  CfAroPresetB.relro_seg_preset_AU
  (CfAroPresetB.errno_relro_preset_AU TfibB TfibB_syms)
  (AllocGtopPresetMB.aalloc_realizes_cf_em_m_TfibB_B 1 (or_intror eq_refl)
     YGcfInstSecB.ifaceSw_TfibB_B YGcfInstSecB.ifaceSE_TfibB_B)
  (RGcfWalkB.wrap_realloc_null_walk_keep_cf_B TfibB TfibB_syms cf_malloc_max)
  Hp).
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. malloc and free: not proved in this file. PresetD2pBPf's H_amalloc_realizes_cf_B is `forall rc` and its
   H_afree_realizes_cf_B is `forall rc fx`. The per-image keep proofs of these two contracts are
   lib/AU/CfMallocKeepB.v's amalloc_realizes_cf_keep_closed_B and lib/AU/CfFreeKeepB.v's
   afree_realizes_cf_rh_keep_B. *)

End a.
