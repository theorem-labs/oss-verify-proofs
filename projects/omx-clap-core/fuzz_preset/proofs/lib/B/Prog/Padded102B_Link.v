(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 479 of its 545 lines of code are new or changed and 448 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Padded102B_S1.v, with its module names changed; 21 of its 68 lines of code are new or changed and 498 lines of the source are left out. *)
(* fuzz_preset, image B' (#102 pins: asan-ubsan sha256 d663f82d7f488d30): THE LINK of the walk of padded (B' 0x830a8,
   148 bytes, 37 instructions). It composes the six segments by citation and states the walk's theorem:
     S1 Padded102B_S1.v pd_s1 (entry seat, prologue, the raw malloc wrapper by aj_malloc_x_m_keep, the step to PD_TEST),
     S2 Padded102B_S2.v pd_s2 (the NULL test), S3 Padded102B_S3.v pd_s3_of_s4 (size test + __asan_memcpy),
     S4 Padded102B_S4.v pd_s4_of_s6 (UBSan check + __asan_memset), S5 Padded102B_S5.v pd_s5
     (g_own_ran_out := 1), S6 Padded102B_S6.v pd_s6 (epilogue), and the shared seat
     Padded102B.v pd_seat / pd_seat_null.
   rule 24: proves function padded (reuse search: the internal file REWALK-102-PLAN.md section D3: none exists; proof-index, fixed
   build of 16:30:16Z: padded 0 named, 0 by address, its 2 UNRELEASED hits are lib/U/Prog/padded_c.v's Definition
   PADDED, the plain image's C-model constant).
   THE THEOREM is the kit's tpadded_specX (lib/A/PRH_FnCheck.v de94d3f3a7f1: the kit cut's text c40cf3fdcd2a with clause 5
   and the hull budget / hull use), VERBATIM: no twin, no premise
   beyond the text. The wrapper's call trace through the caller's chain comes from the text's own prh_univ_closure and
   prh_ctx by the closure's fifth clause (lib/A/PRH_Witness.v c5_padded_trace_B, Padded102B_S1.v).
   THE OPEN PREMISES, every one a named Section hypothesis or the image record, with its owner or its home file:
     AMALLOC     amalloc_realizes_cf_keep (the raw malloc wrapper's text YG0dcf.v:335 amalloc_realizes_cf with the
                 memnorm keep at the leaf's end)                             lib/Reusable/YGcfMallocComposeKeep.v
     AI_cpy      aintrin_realizes_xm .. OCpy at __asan_memcpy               (runtime row)
     AI_set      aintrin_realizes_xm .. OSet at __asan_memset               (runtime row)
     IMGVIS      the image's shadow is mapped in every allocator state     img_shadow_vis_cf (YGcfAmx2.v)
     AROLINK     the cf layer's read-only fact arodata_ok_cf at ci from the entry's reader form over PA's RELRO
                 bounds (an image fact; at CfImg_B / PI_prog_B: Padded102B_Inst.v pdi_aro_link_B)
     pd_img B    the image record. Its 8 IMAGE fields are witnessed at the real instance PI_prog_B by
                 Padded102B_Inst.v pd_img_B (computation); its 4 SYMBOL-BINDING fields (pst_owned, pst_errno,
                 pdi_malloc, pdi_env) are pd_img_B's premises, each a computation from the B' TfibSyms
                 (YF0m.v (sha256 b9ab0e46c6c4; internal record)), written in Padded102B_Inst.v (pdi_*_of_tfib, pd_img_B_tb)
   No Admitted, no axiom of this unit (Print Assumptions below the theorem lists the closure). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcallx YGcallcf YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG01cf YG00cf YG0ncf YG0dcf YG0sshcf YGcfRoomPre YG0lawscf YGcfApath.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomKeep YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds PresetRoomPos PresetRun
  PresetReqAt PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnAlloc PRH_FnReader
  PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Padded102B Padded102B_Home
  Padded102B_S1 Padded102B_S2 Padded102B_S3 Padded102B_S4 Padded102B_S5 Padded102B_S6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section link. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Existing Instance prh_img_B.
(* the room instance S1 is stated at (Padded102B_S1.v pd_RL = PRH_Base.v:272 prh_room_live_a8) *)
#[local] Existing Instance pd_RL.
#[local] Notation CP := CfParams_preset.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
Variable B : asyms.
#[local] Notation ARc := (fun ly S Hp W mem md => ARcf (cp := CP) SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
Hypothesis AMALLOC : YGcfMallocComposeKeep.amalloc_realizes_cf_keep (cp := CP) SEGS B.
Hypothesis AI_cpy : aintrin_realizes_xm SEGS B ARc OCpy (SIGMA AS___asan_memcpy).
Hypothesis AI_set : aintrin_realizes_xm SEGS B ARc OSet (SIGMA AS___asan_memset).
(* the image band and its shadow, at the INSTANCE bounds: the kit moved kept_at's image arm to pa_lo / pa_hi
   (lib/A/PRH_Base.v 3004a98fe2d9), so the two marked image facts move with it *)
Hypothesis IMGBAND : 0 <= @pa_lo _ B_prog_listing PA /\ @pa_hi _ B_prog_listing PA <= 2 ^ 47.
Hypothesis IMGVIS : forall ly S Hp W mem md a, ARc ly S Hp W mem md ->
  @pa_lo _ B_prog_listing PA <= a < @pa_hi _ B_prog_listing PA ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
Hypothesis AROLINK : forall (W : world SEGS) (mem : word -> option byte),
  arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W) mem) ->
  arodata_ok_cf SEGS B mem.

Theorem padded_B : pd_img B ->
  forall CTX0, tpadded_specX (fx := fx) (rc := rc) (ci := ci) (cp := CP) (PI := prh_img_B) (RL := pd_RL)
    (L := B_prog_listing) (PA := PA) B ARc SK CTX0.
Proof.
intros IMG CTX0.
apply (pd_s1 B AMALLOC IMGBAND IMGVIS AROLINK IMG).
apply pd_s2.
- apply (pd_s3_of_s4 B AI_cpy). apply (pd_s4_of_s6 B AI_set); [apply pd_seat | apply pd_s6].
- apply pd_s5.
Qed.
(* THE RESULT AT THE REAL INSTANCE is Padded102B_Inst.v padded_B_at_PI_prog_B: padded_B at PI_prog_B from one
   TfibSyms B, with pd_img and IMGVIS discharged from it. *)
End link.
Print Assumptions padded_B.
