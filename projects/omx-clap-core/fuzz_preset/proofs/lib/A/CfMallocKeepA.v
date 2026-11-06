(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/CfMallocKeepA.v, with its module paths changed; 18 of its 69 lines of code are new or changed and 6 lines of the source are left out. *)
(* Theorem Labs, 2026-10-31: fuzz_preset: preset's malloc at image A' (#102 pin
   fuzz_preset.asan 1be0f53d96cb) in KEEP form, at preset's record B := A/AD2l.TfibB, the cf instance CfImg_A /
   CfParams_preset.
   rule 24: no function proved (kind: composition of proved tops by the layer's keep composer).

   [amalloc_realizes_cf_keep_A] is YGcfMallocComposeKeep.amalloc_realizes_cf_keep at tfibsegs / TfibB, by the layer's
   amalloc_realizes_cf_of_parts_m_keep (lib/Reusable/YGcfMallocComposeKeep.v:216, the layer's keep export) at
   nmax := cf_malloc_max, al := 8, atp := 1, acf := 1 (malloc's call) and ARX := WrapMallocAQ.ARXq_A TfibB, from:
   - the wrapper walk: A/WrapMallocATopG.v wrap_malloc_walk_keep_cf_A, at K := WrapMallocADefs.K_A;
   - Allocate: A/AllocGtopPresetM.v aalloc_realizes_cf_em_m_TfibB_A, at ARXq_cf TfibB (fun i => i =
     as_inst TfibB).  [ARXq_A_TfibB] states that this is ARXq_A TfibB, by reflexivity (A/WrapMallocAQ.v:28 is that
     text at the instance AImg_A), so no bridge is needed;
   - the relation's facts ARXq_A_HXA / ARXq_A_xs (A/WrapMallocAQ.v), nmax_cf_ok (YGcfMallocComposeE.nmax_cf_ok_of_w),
     the relro rows (A/CfAroPresetA.v relro_seg_preset_A / errno_relro_preset_A).
   Its premises are HRW (the refill run at TfibB) and the two secondary interfaces IFSc / IFSEc.  IFSc / IFSEc
   are aalloc_realizes_cf_em_m_TfibB_A's open premises, carried through by name.  AllocGtopPresetM.v closes HRW inside
   the file (its HRW_A, by YGcfRefillToppreset.refill_walk_cf_preset_closed), so the proof does not use
   the HRW premise; the premise stays, so that the statement does not change.
   [amalloc_realizes_cf_A] is the plain contract YG0dcf.amalloc_realizes_cf, by amalloc_realizes_cf_of_keep. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK04 YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01 YG0f YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA AGImgA AGImgSA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require AGif4 ErrnoGS YGcfRmodel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocCompose YGcfMallocComposeE.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstRefill.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstHit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfImgA CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l CfAroPresetA AllocGtopPresetM.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require WrapMallocADefs WrapMallocAQ WrapMallocATopG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require YGcfRefillToppreset YGcfInstSecA.
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_preset.

(* The wrapper walk's relation at preset's record is the relation of aalloc_realizes_cf_em_m_TfibB_A. *)
Lemma ARXq_A_TfibB : WrapMallocAQ.ARXq_A AD2l.TfibB = ARXq_cf AD2l.TfibB (fun i => i = as_inst AD2l.TfibB).
Proof. reflexivity. Qed.

Theorem amalloc_realizes_cf_keep_A :
  refill_walk_cf AD2l.TfibB (fun i => i = as_inst AD2l.TfibB) ->
  (forall Hp, AGif4.AIfaceSw AD2l.TfibB (U_cf AD2l.TfibB) malloc_cf
     (ARXq_cf AD2l.TfibB (fun i => i = as_inst AD2l.TfibB) Hp) (AOXm_cf AD2l.TfibB) (YGcfRmodel.rpre_cfr AD2l.TfibB)
     cf_malloc_max LIVE_MAX qtight (YGcfInstHit.dpost_cf AD2l.TfibB) cf_pc_malloc_max cf_pc_spin_shadow cf_malloc_max (2 ^ 29) (2 ^ 30)) ->
  (forall Hp, ErrnoGS.AIfaceSE AD2l.TfibB (U_cf AD2l.TfibB) malloc_cf
     (ARXq_cf AD2l.TfibB (fun i => i = as_inst AD2l.TfibB) Hp) (AOXm_cf AD2l.TfibB) (YGcfRmodel.rpre_cfr AD2l.TfibB)
     cf_malloc_max LIVE_MAX qtight (YGcfInstHit.dpost_cf AD2l.TfibB) cf_pc_malloc_max cf_pc_spin_shadow) ->
  YGcfMallocComposeKeep.amalloc_realizes_cf_keep tfibsegs AD2l.TfibB.
Proof.
intros HRW IFS IFSE.
pose proof AD2l.TfibB_syms as TB.
pose proof (AllocGtopPresetM.aalloc_realizes_cf_em_m_TfibB_A 1 (or_intror eq_refl) IFS IFSE) as AL.
rewrite <- ARXq_A_TfibB in AL.
exact (YGcfMallocComposeKeep.amalloc_realizes_cf_of_parts_m_keep tfibsegs AD2l.TfibB cf_malloc_max 8 1 1 _ _
  nmax_cf_ok_of_w (WrapMallocAQ.ARXq_A_HXA AD2l.TfibB) (WrapMallocAQ.ARXq_A_xs AD2l.TfibB)
  CfAroPresetA.relro_seg_preset_A (CfAroPresetA.errno_relro_preset_A AD2l.TfibB TB) AL
  (WrapMallocATopG.wrap_malloc_walk_keep_cf_A AD2l.TfibB TB eq_refl)).
Qed.

(* The plain malloc contract at A', by the keep form. *)
Theorem amalloc_realizes_cf_A :
  refill_walk_cf AD2l.TfibB (fun i => i = as_inst AD2l.TfibB) ->
  (forall Hp, AGif4.AIfaceSw AD2l.TfibB (U_cf AD2l.TfibB) malloc_cf
     (ARXq_cf AD2l.TfibB (fun i => i = as_inst AD2l.TfibB) Hp) (AOXm_cf AD2l.TfibB) (YGcfRmodel.rpre_cfr AD2l.TfibB)
     cf_malloc_max LIVE_MAX qtight (YGcfInstHit.dpost_cf AD2l.TfibB) cf_pc_malloc_max cf_pc_spin_shadow cf_malloc_max (2 ^ 29) (2 ^ 30)) ->
  (forall Hp, ErrnoGS.AIfaceSE AD2l.TfibB (U_cf AD2l.TfibB) malloc_cf
     (ARXq_cf AD2l.TfibB (fun i => i = as_inst AD2l.TfibB) Hp) (AOXm_cf AD2l.TfibB) (YGcfRmodel.rpre_cfr AD2l.TfibB)
     cf_malloc_max LIVE_MAX qtight (YGcfInstHit.dpost_cf AD2l.TfibB) cf_pc_malloc_max cf_pc_spin_shadow) ->
  YG0dcf.amalloc_realizes_cf tfibsegs AD2l.TfibB.
Proof.
intros HRW IFS IFSE.
exact (YGcfMallocComposeKeep.amalloc_realizes_cf_of_keep tfibsegs AD2l.TfibB (amalloc_realizes_cf_keep_A HRW IFS IFSE)).
Qed.

(* ---- CLOSED: the three premises at preset's record are proved tops: HRW is lib/A/YGcfRefillToppreset.v:51
   refill_walk_cf_preset_closed (at AGImgA.AGImg_A), IFSc / IFSEc are lib/A/YGcfInstSecA.v ifaceSw_TfibB_A /
   ifaceSE_TfibB_A.  No premise is left. ---- *)
Corollary amalloc_realizes_cf_keep_closed_A : YGcfMallocComposeKeep.amalloc_realizes_cf_keep tfibsegs AD2l.TfibB.
Proof.
exact (amalloc_realizes_cf_keep_A
  (YGcfRefillToppreset.refill_walk_cf_preset_closed AD2l.TfibB (fun i => i = as_inst AD2l.TfibB) AD2l.TfibB_syms
     (fun i H => H))
  YGcfInstSecA.ifaceSw_TfibB_A YGcfInstSecA.ifaceSE_TfibB_A).
Qed.

Corollary amalloc_realizes_cf_closed_A : YG0dcf.amalloc_realizes_cf tfibsegs AD2l.TfibB.
Proof. exact (YGcfMallocComposeKeep.amalloc_realizes_cf_of_keep tfibsegs AD2l.TfibB amalloc_realizes_cf_keep_closed_A). Qed.

End a.
