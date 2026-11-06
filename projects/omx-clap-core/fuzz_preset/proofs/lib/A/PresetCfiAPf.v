(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the proof of tfib_lib_x_all_A (lib/A/PresetCfiA.v), made from the proof part of
   proofs/cgif/cgif_file_fuzzer/lib/A/ACfi.v:67-141 (tfib_lib_x_closed / tfib_lib_x_all), for fuzz_preset.
   The donor discharged cgif's harness-walk hypotheses with link lemmas (link_ML, link_SMP, link_FFL, link_ASF,
   link_ASM2, link_AMEMSET, link_AMEMCPY) over cgif's AR. Preset's walk (preset_lib_x_stmt, lib/A/PresetCfnA.v) takes
   one record, preset_callee_contracts, so the closure's link is the assembly of that record from preset's parts:
   the fourteen callee contracts, a8's frame-area API at the unit parameters CfParams_preset, and the class fact
   below. Nothing in this file is a proof of a function (rule 24). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PresetCfiAPf.v, with its module paths and module names changed; 66 of its 88 lines of code are new or changed and 80 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the proof of tfib_lib_x_all_A (lib/A/PresetCfiA.v), made from the proof part of
   proofs/cgif/cgif_file_fuzzer/lib/A/ACfi.v:67-141 (tfib_lib_x_closed / tfib_lib_x_all and the link lemmas
   link_ML / link_SMP / link_FFL / link_ASF, :72-89), for fuzz_preset. lib/AU/PresetCfiBPf.v is the asan-ubsan twin.
   Nothing in this file is a proof of a function (rule 24).
   Contents:
   - tfib_lib_x_all_A_holds: the closure. Preset's walk (preset_lib_x_stmt, lib/A/PresetCfnA.v) takes one
     record, preset_callee_contracts; on #102 the closure takes that record as its part (the composition builds it
     from the kit's texts, the frame-area allocation and a8's PROVED release law astack_free_law_ok_cf, lib/Reusable/YG0tcf.v);
   - link_SMP_A, link_FFL_A, link_ML_A, link_ASF_A: the donor's link lemmas restated over the second allocator
     instance at image A, each UNCONDITIONAL: fake-stack progress over Wf_cf (a8's YG05cf.v), the frame-flag facts
     over ARcf from a8's AR_laws_ok_cf (YG0lawscf.v), the model laws from a8's model_laws_cf_ok (YG0ucf.v), and the
     release law astack_free_law_ok_cf.
   Not restated: link_AMEMSET / link_AMEMCPY (the AsanAPI_cf fields aa_asan_memset_cf / aa_asan_memcpy_cf, whose
   consumer was cgif's harness walk; preset's entry function calls neither). Dropped: link_ASM2 (cgif's class 2;
   preset's classes are cf_fs_classes = [0; 1; 3], taken through the stack-malloc premise of tfib_lib_x_all_A). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v ACej.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG0ncf YG0dcf YG05cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0tcf YG0lawscf YG0ucf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgTop YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset PresetCfnA PresetCfiA.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. The closure.                                                         *)
(* #102 (no-DW interface, PresetCfnA.v, first at commit 8259b94c42ee): the harness walk takes the callee record at
   every float state fx0 (each callee runs at the FP state its caller hands it); the closure applies it to the record.
   The record itself (the kit's sixteen texts, the frame-area allocation and its release) is assembled by the composition
   (lib/A/PresetD2pAPf.v), by field name. *)
Theorem tfib_lib_x_all_A_holds : tfib_lib_x_all_A.
Proof.
intros rc ci L PA B sm iface_room_np MT XM_LIB XN_LIB PAYLOAD_ROOM A_MOD_AT A_STAMP HC HLX fx.
exact (HLX fx HC).
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. The link lemmas over the second instance, image A, unconditional.     *)

(* The donor's link_SMP (ACfi.v:74-75): fake-stack progress, over Wf_cf at image A's trace universe (Tfib_universe,
   lib/A/ACej.v; TfibB's as_universe). *)
Lemma link_SMP_A : forall s cid,
  @Wf_cf CfParams_preset Tfib_universe s -> 0 <= cid <= 10 -> count_cid cid (frames s) < fs_frames cid ->
  exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s').
Proof.
intros s cid H1 H2 H3. exact (@stack_malloc_progress_cf CfParams_preset Tfib_universe s cid H1 H2 H3).
Qed.

(* The donor's frame_flag_lawP (lib/Reusable/YCbq.v:799-804) with AR -> ARcf and the ghost set Hp after S; generic in
   the image's CfImg (ARcf reads it, cf layer field round 2). *)
Definition frame_flag_lawP_cf {ci : CfImg} (rc : YM05.RunCeil) (cp : CfParams) (segs : list Segment) (B : asyms) : Prop :=
forall ly S Hp (W : world segs) mem md cid pos,
ARcf (rc := rc) (cp := cp) segs B ly S Hp W mem md -> In (cid, pos) (frames S) ->
apresent (w_H W) mem (flag_addr ly cid pos) /\ aowned B ly S (flag_addr ly cid pos) /\
(@app_addr rc (flag_addr ly cid pos) /\ ~ in_img segs (flag_addr ly cid pos)) /\
(4096 <= flag_addr ly cid pos /\ zone2 (flag_addr ly cid pos) 1 /\ flag_addr ly cid pos < @alloc_ceiling rc).

(* Image A's loaded segments span [IMG_LO, IMG_TOP) (lib/Reusable/YImgTop.v, generated): one segment starts at the
   bottom, one ends at the top. *)
Lemma tfib_img_ends_A :
  existsb (fun s : Segment => Z.of_N (seg_base s) =? YImgTop.IMG_LO) tfibsegs = true /\
  existsb (fun s : Segment => Z.of_N (seg_base s) + Z.of_N (seg_size s) =? YImgTop.IMG_TOP) tfibsegs = true.
Proof. split; vm_compute; reflexivity. Qed.

(* ALedger_cf's image hull covers [IMG_LO, IMG_TOP). *)
Lemma tfib_img_cover_cf_A : forall (rc : YM05.RunCeil) ly S md, @ALedger_cf rc tfibsegs ly S md ->
  fst (ly_img ly) <= YImgTop.IMG_LO /\ YImgTop.IMG_TOP <= fst (ly_img ly) + snd (ly_img ly).
Proof.
intros rc ly S md L. destruct tfib_img_ends_A as [E1 E2].
apply existsb_exists in E1 as (s1 & Hs1 & Q1). apply existsb_exists in E2 as (s2 & Hs2 & Q2). cbv beta in Q1, Q2.
apply Z.eqb_eq in Q1. apply Z.eqb_eq in Q2.
destruct (@alc_img rc tfibsegs ly S md L s1 Hs1) as [C1 _].
destruct (@alc_img rc tfibsegs ly S md L s2 Hs2) as [_ C2].
split; lia.
Qed.

(* The donor's link_FFL (ACfi.v:76-87), from a8's PROVED AR_laws_cf (AR_laws_ok_cf: alc_flag, alc_client_img) and the
   hull above. *)
Lemma link_FFL_A {ci : CfImg} : forall (rc : YM05.RunCeil) (B : asyms), frame_flag_lawP_cf rc CfParams_preset tfibsegs B.
Proof.
intros rc B ly S Hp W mem md cid pos HAR Hin.
pose proof (AR_laws_ok_cf (rc := rc) (cp := CfParams_preset) tfibsegs B) as LAWS.
destruct (alc_flag (rc := rc) (cp := CfParams_preset) tfibsegs B LAWS ly S Hp W mem md cid pos HAR Hin)
  as (Hpr & Ho & Happ & Hceil).
destruct (alc_client_img (rc := rc) (cp := CfParams_preset) tfibsegs B LAWS ly S Hp W mem md (flag_addr ly cid pos) HAR)
  as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (_ & L & _).
destruct (tfib_img_cover_cf_A rc ly S md L) as [C1 C2].
unfold in_zr in Hhull.
split; [exact Hpr|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- unfold in_app in Happ. split; [lia|]. split; [|exact Hceil].
  unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* The donor's link_ML (ACfi.v:72-73): the model laws over Wf_cf at image A's trace universe, a8's model_laws_cf_ok
   (YG0ucf.v, its free law from YG03dcf.v's ml_free_cf). *)
Lemma link_ML_A : forall ci : CfImg, @model_laws_cf CfParams_preset ci Tfib_universe.
Proof.
intros ci. exact (model_laws_cf_ok (cp := CfParams_preset) (ci := ci) Tfib_universe Tfib_universe_ok).
Qed.

(* The donor's link_ASF (ACfi.v:88-89): the frame release law over ARcf, a8's astack_free_law_ok_cf (YG0tcf.v). *)
Lemma link_ASF_A {ci : CfImg} : forall (rc : YM05.RunCeil) (B : asyms),
  astack_free_law_cf (rc := rc) (cp := CfParams_preset) tfibsegs B.
Proof. intros rc B. exact (astack_free_law_ok_cf (rc := rc) (cp := CfParams_preset) tfibsegs B). Qed.
