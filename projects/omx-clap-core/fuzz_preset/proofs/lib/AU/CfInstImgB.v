(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-31: fuzz_preset (a Theorem Labs lane, row MISS-top at field round 3 part 3c): image rows of a Theorem Labs lane's
   generic cf instance layer at B' (#102 pin fuzz_preset.asan-ubsan d663f82d7f48, twin c90d4fa54d43; image class
   AImg_cgif, lib/AU/AGif2cgif.v: im_syms := TfibSyms, im_img_cover := YF0x.img_cover).  The B' twin of
   lib/A/CfInstImgA.v (this lane's own file, no cgif source), ported between images by the internal file port_img_b.py:
   the same statements and scripts, the B' modules (lib/Reusable YB1v / YF0m / YF0x, lib/AU AGif2cgif / AGif0cgif /
   AGif4cgif / AGis / AGjm / CfImgB; the image-free lib/A/ADIfaceImgA kept) and B''s values.
   rule 24: no function proved (image arithmetic over this unit's generated symbol facts).

   B''s values (lib/Reusable/YF0m.v:15-20, lib/AU/CfImgB.v, lib/Reusable/YB13.v), each the same symbol + offset on
   the twin as A''s: instance 0xa8098 (_ZN6__asanL8instanceE), so the four [img_sapart_B] ranges end at or below
   inst + 720 = 0xa8368, below the store 0x17d5c8, the depot 0x18d5d8, the internal allocator [0xac900, 0x12d930) and
   its flag 0x13b188; ts_junk's window [0xa2000, IMG_TOP_B = 0x601000) (YF0m.v:1811), tiled by two segments
   [0xa2000, 0xa4000) and [0xa4000, 0x601000) (YB13.v:96-113, found by value, junk_segs_check); the errbuf object
   cf_errbuf_obj = 0xaaf68 (error_message_buffer), 56 bytes, inside the 4th owned static extent [0xaaf50, 0x5cdd50)
   (YF0m.v:1789); the oom byte 0x12d960; errno [0x5de68c, +4); both depot zones' static part [0x17d5c8, 0x5cdd50)
   (lib/AU/AGis.v:231, lib/AU/AGjm.v:573); the image window [0x10000, 0x601000) (YF0x.v:27 / :40).
   - [img_sapart_B] IMG_SAPART, [img_junk_B] IMG_JUNK, [exh_off_B] EXH_OFF, [errb_obj_owned_B] ERRB_OWN, as at B'.
   - [dzone_owned_ag_B] / [dzone_apart_ag_B]: YGcfInstHit's HDZO / HDZX; [oom_errb_apart_B]: YGcfInstMiss's HOEB;
     [ERRB_SEP_B]: ERRB_SEP_t, from which YGcfErrbSep.ERRB_SEP_ag gives ERRB_AG. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG ImgBaseAGS.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif0cgif AGif4cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AGis AGjm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require ADIfaceImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfErrbSep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfImgRows.
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The closed equation: the four written ranges end at or below TFIB_INST + 720, below every other area. *)
Lemma sapart_check :
  ((TFIB_INST + 720 <=? TFIB_STORE) && (TFIB_INST + 720 <=? TFIB_DEPOT) && (TFIB_INST + 720 <=? TFIB_IAL_LO)
   && (TFIB_INST + 720 <=? TFIB_IAL_FLAG))%bool = true.
Proof. vm_compute. reflexivity. Qed.

(* IMG_SAPART at B' (cgif/cgif_file_fuzzer lib/YGcfInstRcSec.v (file sha256 787ff930a325; donor not released) :127-130, sdeal_inst :124-126 unfolded; at IM := AImg_cgif,
   im_syms B is TfibSyms B by the instance's field, so `exact img_sapart_B` fits the row by conversion). *)
Theorem img_sapart_B : forall B, TfibSyms B -> forall a,
  (as_inst B + 680 <= a < as_inst B + 684) \/ (as_inst B + 120 <= a < as_inst B + 129) \/
  (as_inst B + 144 <= a < as_inst B + 160) \/ (as_inst B + 704 <= a < as_inst B + 720) ->
  ~ (as_depot B <= a < as_depot B + 4 * 2 ^ 20 + 32) /\ ~ (as_store B <= a < as_store B + 32) /\
  ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2).
Proof.
intros B TB a Ha.
rewrite (ts_inst _ TB) in Ha.
rewrite (ts_depot _ TB), (ts_store _ TB), (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB).
pose proof sapart_check as C. rewrite !andb_true_iff in C. destruct C as (((C1 & C2) & C3) & C4).
apply Z.leb_le in C1, C2, C3, C4.
destruct Ha as [H | [H | [H | H]]]; repeat split; lia.
Qed.

(* The closed equation behind IMG_JUNK: two segments of the image tile ts_junk's window [0xa2000, 0x601000). *)
Lemma junk_segs_check :
  existsb (fun sg => (Z.of_N (seg_base sg) <=? 0xa2000) && (0xa4000 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool
    tfibsegs = true /\
  existsb (fun sg => (Z.of_N (seg_base sg) <=? 0xa4000) && (0x601000 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool
    tfibsegs = true.
Proof. split; vm_compute; reflexivity. Qed.

(* IMG_JUNK at B' (cgif/cgif_file_fuzzer lib/YGcfInstRcSec.v (file sha256 1677f901cdf5; donor not released) :135-137, the body verbatim; im_syms / im_segs at AImg_cgif). *)
Theorem img_junk_B : forall B ly r0, im_syms B -> layout_ok ly -> In r0 (as_junk B ly) -> forall j, 0 <= j < snd r0 ->
exists sg, In sg im_segs /\ Z.of_N (seg_base sg) <= aeval B ly (fst r0) + j < Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
Proof.
intros B ly r0 TB _ Hin j Hj. change (TfibSyms B) in TB.
destruct (ts_junk _ TB ly r0 Hin) as (z & Ez & Z1 & Z2).
rewrite Ez. change (aeval B ly (ANum z)) with z. unfold YImgTop.IMG_TOP_B in Z2.
destruct junk_segs_check as [E2 E3].
destruct (Z.lt_ge_cases (z + j) 0xa4000) as [Hl | Hl].
- apply existsb_exists in E2 as (sg & Hs & Hb). apply andb_true_iff in Hb as [B1 B2]. apply Z.leb_le in B1, B2.
  exists sg. split; [exact Hs | lia].
- apply existsb_exists in E3 as (sg & Hs & Hb). apply andb_true_iff in Hb as [B1 B2]. apply Z.leb_le in B1, B2.
  exists sg. split; [exact Hs | lia].
Qed.

(* ---- The two CfImg rows (a Theorem Labs lane's Hit / Sec instances), at CfImg_B's generated values. ---- *)
#[local] Existing Instance CfImg_B.

Lemma cf_errbuf_obj_B : cf_errbuf_obj = 0xaaf68. Proof. reflexivity. Qed.
Lemma cf_exh_off_B : YGcfImgRows.EXH_OFF_t. Proof. reflexivity. Qed.

(* EXH_OFF: the per-class exhausted byte lies in RegionInfo's 128-byte stride. *)
Theorem exh_off_B : 0 <= cf_exh_off < 128.
Proof. exact (YGcfImgRows.EXH_OFF_bound cf_exh_off_B). Qed.

(* The closed equation behind ERRB_OWN: one owned static extent of this unit's B' table holds the whole 56-byte errbuf
   object [0xaaf68, 0xaafa0) (error_message_buffer 8 + error_report_callback 8 + error_message_buf_mutex 16 +
   error_message_buffer_placeholder 24, twin c90d4fa54d43's .symtab): the 4th extent [0xaaf50, 0x5cdd50) of
   lib/Reusable/YF0m.v:1789's Tfib_owned_static. *)
Lemma errb_own_check :
  existsb (fun r => (fst r <=? 0xaaf68) && (0xaaf68 + 56 <=? fst r + snd r))%bool Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.

(* ERRB_OWN: errb_obj_owned_t (cgif/cgif_file_fuzzer lib/YGcfInstBase.v (file sha256 52402d15ef76; donor not released) :87-88) at B'. *)
Theorem errb_obj_owned_B : forall B, TfibSyms B ->
  forall a, cf_errbuf_obj <= a < cf_errbuf_obj + 56 -> Exists (in_zr a) (as_owned_static B).
Proof.
intros B TB a Ha. rewrite cf_errbuf_obj_B in Ha. rewrite (ts_owned B TB).
pose proof errb_own_check as C. apply existsb_exists in C as (r & Hin & Hr).
apply andb_true_iff in Hr as [R1 R2]. apply Z.leb_le in R1, R2.
apply Exists_exists. exists r. split; [exact Hin|]. unfold in_zr. lia.
Qed.

(* ---- The depot zones (ag_dzone = AGis.DZONE, ims_dzone = AGjm.DZONE: [0x17d5c8, 0x5cdd50) and the nodes / store
   blocks) against the image objects. ---- *)

(* The nodes and store blocks lie off the image (AGis.off_NB / off_SB: zone3 of layout_ok's blocks). *)
Lemma blocks_off_img_B : forall ly a, layout_ok ly -> YF0x.img_cover ly -> 0x10000 <= a < 0x601000 ->
  ~ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) /\ ~ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize).
Proof.
intros ly a LY IC Ha. split; intros H.
- pose proof (AGis.off_NB _ LY IC _ H) as O. unfold YF0x.off_img, YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END in O. lia.
- pose proof (AGis.off_SB _ LY IC _ H) as O. unfold YF0x.off_img, YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END in O. lia.
Qed.

(* The five apartness facts of the errbuf object at B' (the text before a Theorem Labs lane's split; YGcfErrbSep.ERRB_SEP_at's
   form): the 56-byte errbuf object [0xaaf68, 0xaafa0) is apart from the instance [0xa8098, 0xa8ec8), the oom byte
   0x12d960, errno [0x5de68c, +4) and both depot zones (their image part starts at 0x17d5c8; the blocks are off the
   image). *)
Theorem errb_sep5_B : forall B, TfibSyms B -> forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B ->
  cf_errbuf_obj <= a < cf_errbuf_obj + 56 ->
  ~ (as_inst B <= a < as_inst B + 3632) /\ a <> as_oom_byte B /\ ~ (as_errno B <= a < as_errno B + 4) /\
  ~ ims_dzone ly a /\ ~ ag_dzone ly a.
Proof.
intros B TB ly a LY IC HT Ha. rewrite cf_errbuf_obj_B in Ha. change (YF0x.img_cover ly) in IC.
rewrite (ts_inst B TB), (ts_oom B TB), (ts_errno B TB).
destruct (blocks_off_img_B ly a LY IC ltac:(lia)) as [N1 N2].
unfold TFIB_INST, TFIB_OOM, TFIB_ERRNO.
refine (conj _ (conj _ (conj _ (conj _ _)))); [lia | lia | lia | |].
- intros H. change (AGjm.DZONE ly a) in H. unfold AGjm.DZONE in H. destruct H as [H | [H | H]]; [lia | exact (N1 H) | exact (N2 H)].
- intros H. change (AGis.DZONE ly a) in H. unfold AGis.DZONE in H. destruct H as [H | [H | H]]; [lia | exact (N1 H) | exact (N2 H)].
Qed.

(* YGcfInstHit's HDZO at B': ag_dzone's image part lies in one owned static area (found by value), the rest is the
   nodes and store blocks (lib/A/ADIfaceA.v dzone_owned_A's script for AGis.DZONE). *)
Theorem dzone_owned_ag_B : forall B, TfibSyms B -> forall ly a, ag_dzone ly a ->
  Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize).
Proof.
intros B TB ly a Ha. change (AGis.DZONE ly a) in Ha. unfold AGis.DZONE in Ha. destruct Ha as [Ha | [Ha | Ha]].
- left. rewrite (ts_owned _ TB). refine (ADIfaceImgA.covers_b_Exists _ _ _ _ a Ha). clear. vm_compute. reflexivity.
- right. left. exact Ha.
- right. right. exact Ha.
Qed.

(* YGcfInstHit's HDZX at B': ag_dzone misses the instance object, the internal allocator and its flag. *)
Theorem dzone_apart_ag_B : forall B, TfibSyms B -> forall ly a, layout_ok ly -> im_img_cover ly -> ag_dzone ly a ->
  ~ (as_inst B <= a < as_inst B + 3632) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\
  ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2).
Proof.
intros B TB ly a LY IC Ha. change (YF0x.img_cover ly) in IC. change (AGis.DZONE ly a) in Ha.
rewrite (ts_inst B TB), (ts_ial_lo B TB), (ts_ial_hi B TB), (ts_ial_flag B TB).
unfold TFIB_INST, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG.
unfold AGis.DZONE in Ha. destruct Ha as [Ha | [Ha | Ha]].
- lia.
- pose proof (AGis.off_NB _ LY IC _ Ha) as O. unfold YF0x.off_img, YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END in O. lia.
- pose proof (AGis.off_SB _ LY IC _ Ha) as O. unfold YF0x.off_img, YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END in O. lia.
Qed.

(* YGcfInstMiss's HOEB at B': the oom byte 0x12d960 is not in the errbuf object [0xaaf68, 0xaafa0). *)
Theorem oom_errb_apart_B : forall B, TfibSyms B -> ~ (cf_errbuf_obj <= as_oom_byte B < cf_errbuf_obj + 56).
Proof. intros B TB. rewrite cf_errbuf_obj_B, (ts_oom B TB). unfold TFIB_OOM. lia. Qed.

(* ---- ERRB_SEP's final text (cgif/cgif_file_fuzzer lib/YGcfErrbSep.v (file sha256 f62c93ec3f86; donor not released) :26-29):
   ERRB_SEP_t B := YGcfImgRows.ERRB_QAPART /\ (the rest).  Both conjuncts at B'. ---- *)

(* ERRB_QAPART (YGcfImgRows.v:23-24, class-free, every B, no layout premise) at B': the errbuf object [0xaaf68,
   0xaafa0) lies above the instance object [0xa8098, 0xa8ec8). *)
Theorem ERRB_QAPART_B : YGcfImgRows.ERRB_QAPART.
Proof.
intros B TS a Ha. change (TfibSyms B) in TS. rewrite cf_errbuf_obj_B in Ha. rewrite (ts_inst B TS).
unfold TFIB_INST. lia.
Qed.

(* ERRB_SEP_t's second conjunct (YGcfErrbSep.v:27-29), verbatim, at B' (the last four of errb_sep5_B). *)
Theorem ERRB_SEP_rest_B : forall B, TfibSyms B ->
  forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B ->
  cf_errbuf_obj <= a < cf_errbuf_obj + 56 ->
  a <> as_oom_byte B /\ ~ (as_errno B <= a < as_errno B + 4) /\ ~ ims_dzone ly a /\ ~ ag_dzone ly a.
Proof. intros B TB ly a LY IC HT Ha. exact (proj2 (errb_sep5_B B TB ly a LY IC HT Ha)). Qed.

(* ERRB_SEP at B' *)
Theorem ERRB_SEP_B : forall B, TfibSyms B -> YGcfErrbSep.ERRB_SEP_t B.
Proof. intros B TB. exact (conj ERRB_QAPART_B (ERRB_SEP_rest_B B TB)). Qed.

End a.
