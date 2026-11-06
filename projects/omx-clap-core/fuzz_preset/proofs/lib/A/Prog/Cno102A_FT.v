(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/LLVMFuzzerTestOneInput_segX_exit_td.v, with its module paths, module names and numbers changed; 619 of its 648 lines of code are new or changed and 323 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Cno102A_FE.v; 25 of its 71 lines of code are new or changed and 602 lines of the source are left out. *)
(* fuzz_preset, image A' (#102 pins: asan sha256 1be0f53d96cb9d6c): THE TWO LAST SEGMENTS of the re-walk of
   check_no_overread (cno) against the kit's text tcheck_no_overread_specX, as lane CnoA102f (a Theorem Labs lane) delivers them:
   CA10 Free (CN_FREE 1060 -> CN_END 1108: three pj_free, three __wrap_free) and CA11 End (CN_END 1108 -> ret 1464).
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   CA10 = cn_seg_free_of_halves (Cno102A_F.v) of its halves CA10a cn_seg_pjf (Cno102A_FA.v) and CA10b cn_seg_fr
   (Cno102A_FB.v); CA11 = cn_seg_end (Cno102A_FE.v). Statements cn_seg_freeP / cn_seg_endP: lib/A/Prog/Cno102A_F.v,
   both at the walk's relation (they conclude SRr' SEGS RZ_cf: the run, or the journal from entry, crosses a free).
   THE ALLOCATOR PARAMETERS: CA10b cites the preset hull admission (PresetHullPay.hull_ok_of_budget), so this file
   binds CfParamsPreset.CfParams_preset, as Cno102A_E2-E4 do; CA10a and CA11 are generic in it.
   NAMED ARGUMENTS (Section hypotheses, the union of the three files'; owners):
     IMG : cn_img B (the base's image facts, lib/A/Prog/Cno102A_Base.v; owner the base / the instance file);
     HPJFREE : the kit's tpj_free_specX at n := DOC_D, every float state (owned by the kit; lib/A/PRH_FnPj.v, the text restated at
       SRr' segs RZ_cf with its post fpostWmR at wle' segs RZ_cf);
     AFREE : YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (lib/Reusable/YGcfMallocComposeKeep.v: YG0dcfR.v's
       afree_realizes_cf_rh, the free wrapper's row in the re-hiding form, its realization over the zone RZ_cf, with
       the memnorm keep in its leaf), every float state;
     PAL : PALib B (the unit's image binding of B; owned by the kit);
     HW : prh_head_wide (the kit's spelling; a CfParams fact; its witness at the preset instance is
       CfParamsPreset.preset_head_wide, cited below as cn_hw_preset);
     SS5M : YGcallMxmn.aset_shadow_realizes_xm for __asan_set_shadow_f5, every float state (the engine's contract with
       the memnorm keep, b47cf7942c3d; the row's owner a Theorem Labs lane);
     ENV : api_env SEGS B (the unit's image binding of B; PAL's pal_env field gives it: CA11 took it alone);
     HH : PRH_Base.prh_head16 (cf_head = PresetReqAt.HEAD, the walk hypothesis the kit's texts name, CFHEAD-16; its
       witness at the preset instance is Cno102A_FA.cn_head16_preset, by reflexivity).
   No other premise. The former D-level cn_room_frees is RETIRED (vacuous, lead 18:4xZ). NO STATE PREMISE: the former
   PJF-TIE is CLOSED at the free cut (the readings' free-order ties, the base's cn_fo); the copies' frees' advance is
   proved (Cno102A_FB.v). THE HULL: tcheck_no_overread_specX's hull budget rides in cn_pre and in every cut's hull
   conjunct (Cno102A_F.v); the pj_free and free calls are paid inside CA10a / CA10b; this file pays nothing.
   Numerals: 16 (LENGTH: the copy's pad), 245 (WORD: the shadow byte 0xf5). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00cf YG01cf YG0ncf YG0dcf.
(* the free wrapper's row in the re-hiding form with the memnorm keep (afree_realizes_cf_rh_keep) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallx YGcallcf YGcallSx YGcallScf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcall YCbqGcallW YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CallerJ PRW_StepKit Cno102_FKit
  Cno102A_Base Cno102A_F.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Cno102A_FA Cno102A_FB Cno102A_FE.
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section cf. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
(* the preset allocator parameters (CA10b's hull admission is the preset's) *)
#[local] Existing Instance CfParamsPreset.CfParams_preset.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_A.
Context {PA : PAImg A_prog_listing}.
#[local] Instance CF_PL : PAListing A_prog_listing := PL_cno_A.
#[local] Instance CF_RL : PrhRoomLive := prh_room_live_a8.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
Variable B : asyms.
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
Variable CTX0 : list (list Z).

Hypothesis IMG : cn_img B.
Hypothesis HPJFREE : forall fz : YK11.FPState,
  tpj_free_specX (fx := fz) (PI := prh_img_A) (RL := CF_RL) B ARcfx SK CTX0 DOC_D.
Hypothesis AFREE : forall fz : YK11.FPState, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fz) SEGS B.
Hypothesis PAL : PALib (L := A_prog_listing) (PI := PA) B.
Hypothesis HW : prh_head_wide.
Hypothesis SS5M : forall fz : YK11.FPState,
  @YGcallMxmn.aset_shadow_realizes_xm fz SEGS B ARcfx (SIGMA AS___asan_set_shadow_f5) 245.
Hypothesis ENV : api_env SEGS B.
Hypothesis HH : PRH_Base.prh_head16.

(* CA10 Free: 1060 -> 1108 *)
Theorem cn_seg_free : cn_seg_freeP B CTX0.
Proof.
apply cn_seg_free_of_halves.
- exact (Cno102A_FA.cn_seg_pjf B CTX0 IMG HPJFREE HH).
- exact (Cno102A_FB.cn_seg_fr B CTX0 AFREE PAL IMG HW).
Qed.

(* CA11 End: 1108 -> ret *)
Theorem cn_seg_end : cn_seg_endP B CTX0.
Proof. exact (Cno102A_FE.cn_seg_end B CTX0 SS5M ENV HW IMG). Qed.
End cf.

(* HW's instance witness (the unit ruling 16:45Z: an image / parameter premise names the lemma that closes it at
   the instance): prh_head_wide holds at the preset allocator parameters *)
Lemma cn_hw_preset : @prh_head_wide CfParamsPreset.CfParams_preset.
Proof. exact CfParamsPreset.preset_head_wide. Qed.

Print Assumptions cn_seg_free.
Print Assumptions cn_seg_end.
