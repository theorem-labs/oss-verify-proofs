(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 1292 of its 1364 lines of code are new or changed and 442 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Cno102A_E2.v, with its module names changed; 13 of its 81 lines of code are new or changed and 1296 lines of the source are left out. *)
(* fuzz_preset, image A' (#102 pins: asan sha256 1be0f53d96cb9d6c): THE STRETCH CA0-CA4 of the re-walk of
   check_no_overread (cno), entry -> CN_INIT (+608) \/ CN_INIT3 (+792): Cno102A_E.v's cn_seg_E at ARx := ARcfx, from the
   five segments by cn_seg_E_of_segs. FREE-PIECES-102 Part 7 row
   R7-3.
   rule 24: proves no function (kind: segment lemma).
   THE SEGMENTS: cn_CA0 (Cno102A_E0.v) and cn_CA1 (Cno102A_E.v) at a generic ARx, here at ARcfx; cn_CA2 / cn_CA3 /
   cn_CA4 (Cno102A_E2.v / E3.v / E4.v) at ARcfx.
   SECTION HYPOTHESES (the union of the segments'): IMG : cn_img B, PAL : PALib B, SYMS : asyms_ok B, SM3 (the
   stack_malloc pc of class CN_CID is __asan_stack_malloc_3), HW : prh_head_wide, IMGSH (the image's shadow is mapped
   in every ARcf state), AMALLOC (the malloc row, a Theorem Labs lane's), ASM3 (the __asan_stack_malloc_3 row at ARcfx), ACPY / ASET
   (the __asan_memcpy / __asan_memset rows at ARcfx). LAWS and OWNLOW are ARcf's (AR_laws_x_xs, ARx_owned_low_law_xs). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames YG05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YImgTop YG00cf YG01cf YG0ncf YG0dcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcallx YGcallcf YGcallSx YGcallMx YGcallMxmn FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfRoomLivePreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveSec PresetLiveBounds PresetRoomCounts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger Cno102A_Base Cno102A_Ro
  Cno102A_E Cno102A_E0 Cno102A_E2 Cno102A_E3 Cno102A_E4.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeKeep.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section ec. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_room_live_a8.
#[local] Existing Instance prh_room_malloc_a8.
#[local] Existing Instance prh_img_A.
Context {PA : PAImg A_prog_listing}.
#[local] Existing Instance PL_cno_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
Variable B : asyms.
Variable CTX0 : list (list Z).
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
Hypothesis IMG : cn_img B.
Hypothesis PAL : PALib (rc := rc) (L := A_prog_listing) (PI := PA) B.
Hypothesis SYMS : asyms_ok B.
Hypothesis SM3 : pc_stack_malloc (as_code B) CN_CID = SIGMA AS___asan_stack_malloc_3.
Hypothesis HW : prh_head_wide.
Hypothesis IMGSH : forall ly S Hp W mem md a, ARcf SEGS B ly S Hp W mem md -> pa_lo <= a < pa_hi ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* the keep form: cn_CA2 / CA3 / CA4 take the keep contract, so this does too; Cno102A_TopA takes it in the same
   form, discharged by amalloc_realizes_cf_of_parts_keep *)
Hypothesis AMALLOC : forall fz : YK11.FPState, YGcfMallocComposeKeep.amalloc_realizes_cf_keep (fx := fz) SEGS B.
Hypothesis ASM3 : astack_malloc_realizes_xm (fx := fx) SEGS B ARcfx CN_CID.
Hypothesis ACPY : forall fz : YK11.FPState, aintrin_realizes_xm (fx := fz) SEGS B ARcfx OCpy (SIGMA AS___asan_memcpy).
Hypothesis ASET : forall fz : YK11.FPState, aintrin_realizes_xm (fx := fz) SEGS B ARcfx OSet (SIGMA AS___asan_memset).
Let LAWS_cf : AR_laws_cf SEGS B := AR_laws_ok_cf SEGS B.
Let LAWS : AR_laws_x SEGS B ARcfx cf_head := AR_laws_x_xs SEGS B LAWS_cf.
Let OWNLOW := ARx_owned_low_law_xs SEGS B LAWS_cf.

(* ======== THE STRETCH ======== *)
Theorem cn_E : @cn_seg_E fx rc ci CfParams_preset prh_room_live_a8 SK PA B ARcfx CTX0.
Proof.
apply cn_seg_E_of_segs.
- exact (@cn_CA0 fx rc ci CfParams_preset prh_room_live_a8 SK PA B ARcfx CTX0 LAWS IMG PAL SYMS OWNLOW SM3 ASM3 HW).
- exact (@cn_CA1 fx rc ci CfParams_preset prh_room_live_a8 SK PA B ARcfx CTX0 LAWS IMG HW).
- exact (@cn_CA2 fx rc ci SK PA B CTX0 IMG PAL HW IMGSH AMALLOC ACPY ASET).
- exact (@cn_CA3 fx rc ci SK PA B CTX0 IMG PAL HW IMGSH AMALLOC ACPY ASET).
- exact (@cn_CA4 fx rc ci SK PA B CTX0 IMG PAL HW IMGSH AMALLOC ACPY ASET).
Qed.

End ec.
