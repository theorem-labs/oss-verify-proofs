(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30: fuzz_preset (a Theorem Labs lane memnorm102): image rows of a Theorem Labs lane's generic cf instance layer at
   A' (#102 pin fuzz_preset.asan 1be0f53d96cb; image class AImg_A, A/AImgA.v: im_syms := TfibSyms,
   im_img_cover := AF0x.img_cover).
   rule 24: no function proved (image arithmetic over this unit's generated symbol facts).

   The statements are those of cgif/cgif_file_fuzzer lib/YGcfInstRcSec.v (file sha256 787ff930a325; donor not released).
   - [img_sapart_A] is IMG_SAPART (:127-130, with sdeal_inst :124-126 unfolded) at IM := AImg_A: the four allocator
     word ranges the secondary arm writes ([inst + 680, +684), [inst + 120, +129), [inst + 144, +160),
     [inst + 704, +720)) are apart from the depot [as_depot, +4 * 2^20 + 32), the store [as_store, +32), the
     internal allocator [as_ialloc_lo, as_ialloc_hi) and its flag [as_ialloc_flag, +2).  At A' (A/AF0m.v:14-17,
     TfibSyms' ts_inst / ts_depot / ts_store / ts_ial_lo / ts_ial_hi / ts_ial_flag): inst 0xa7858, so the four ranges
     end at or below inst + 720 = 0xa7b28, and every other area starts above it: store 0x17cd88, depot 0x18cd98,
     ialloc [0xac0c0, 0x12d0f0), flag 0x13a948.  One closed equation decides it (sapart_check, by vm_compute).
     cgif discharges the same row by its numerals (YFf4.v:727 / :736 / :774); this unit's A/AFf4.v:727-777 states
     the same areas through the same TfibSyms fields.
  - [img_junk_A] is IMG_JUNK, the final text (cgif/cgif_file_fuzzer lib/YGcfInstRcSec.v (file sha256 1677f901cdf5; donor not released) :135-137,
     body verbatim at IM := AImg_A): every byte of a junk range lies in one of the image's segments.  At A' TfibSyms'
     ts_junk (A/AF0m.v:1806) puts every junk range at (ANum z, n) with 0xa1000 <= z and z + n <= IMG_TOP = 0x600000,
     and two of tfibsegs' segments tile that window: [0xa1000, 0xa3000) and [0xa3000, 0x600000) (A/AB13.v:105 /
     :110-114; found by value here, junk_segs_check, by vm_compute).  (The earlier form with an image-cover premise,
     a Theorem Labs lane 03:58Z, is replaced by this one.)
   - [exh_off_A] is EXH_OFF (0 <= cf_exh_off < 128) at CfImg_A (cf_exh_off = 68, A/CfImgA.v:36).
   - [errb_obj_owned_A] is ERRB_OWN, YGcfInstBase.errb_obj_owned_t (cgif/cgif_file_fuzzer lib/YGcfInstBase.v (file sha256 52402d15ef76; donor not released) :87-88), at
     CfImg_A (cf_errbuf_obj = 0xaa728, A/CfImgA.v:34): the 56 bytes are error_message_buffer (8),
     error_report_callback (8), error_message_buf_mutex (16) and error_message_buffer_placeholder (24), and the 4th
     extent of the generated Tfib_owned_static (A/AF0m.v:1784, [0xaa710, 0x5cd510)) holds all of them; one
     vm-checked equation (errb_own_check).
   - [ERRB_SEP_A] is ERRB_SEP_t (cgif/cgif_file_fuzzer lib/YGcfErrbSep.v (file sha256 f62c93ec3f86; donor not released) :26-29): ERRB_QAPART_A /\ ERRB_SEP_rest_A. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG ImgBaseAGS.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AGImgA AGImgSA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AGis AGjm ADIfaceImgA.
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

(* IMG_SAPART at A' (cgif/cgif_file_fuzzer lib/YGcfInstRcSec.v (file sha256 787ff930a325; donor not released) :127-130, sdeal_inst :124-126 unfolded; at IM := AImg_A,
   im_syms B is TfibSyms B by the instance's field, so `exact img_sapart_A` fits the row by conversion). *)
Theorem img_sapart_A : forall B, TfibSyms B -> forall a,
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

(* The closed equation behind IMG_JUNK: two segments of the image tile ts_junk's window [0xa1000, 0x600000). *)
Lemma junk_segs_check :
  existsb (fun sg => (Z.of_N (seg_base sg) <=? 0xa1000) && (0xa3000 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool
    tfibsegs = true /\
  existsb (fun sg => (Z.of_N (seg_base sg) <=? 0xa3000) && (0x600000 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool
    tfibsegs = true.
Proof. split; vm_compute; reflexivity. Qed.

(* IMG_JUNK at A' (cgif/cgif_file_fuzzer lib/YGcfInstRcSec.v (file sha256 1677f901cdf5; donor not released) :135-137, the body verbatim; im_syms / im_segs at AImg_A). *)
Theorem img_junk_A : forall B ly r0, im_syms B -> layout_ok ly -> In r0 (as_junk B ly) -> forall j, 0 <= j < snd r0 ->
exists sg, In sg im_segs /\ Z.of_N (seg_base sg) <= aeval B ly (fst r0) + j < Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
Proof.
intros B ly r0 TB _ Hin j Hj. change (TfibSyms B) in TB.
destruct (ts_junk _ TB ly r0 Hin) as (z & Ez & Z1 & Z2).
rewrite Ez. change (aeval B ly (ANum z)) with z. unfold YImgTop.IMG_TOP in Z2.
destruct junk_segs_check as [E2 E3].
destruct (Z.lt_ge_cases (z + j) 0xa3000) as [Hl | Hl].
- apply existsb_exists in E2 as (sg & Hs & Hb). apply andb_true_iff in Hb as [B1 B2]. apply Z.leb_le in B1, B2.
  exists sg. split; [exact Hs | lia].
- apply existsb_exists in E3 as (sg & Hs & Hb). apply andb_true_iff in Hb as [B1 B2]. apply Z.leb_le in B1, B2.
  exists sg. split; [exact Hs | lia].
Qed.

(* ---- The two CfImg rows (a Theorem Labs lane's Hit / Sec instances), at CfImg_A's generated values. ---- *)
#[local] Existing Instance CfImg_A.

Lemma cf_errbuf_obj_A : cf_errbuf_obj = 0xaa728. Proof. reflexivity. Qed.
Lemma cf_exh_off_A : YGcfImgRows.EXH_OFF_t. Proof. reflexivity. Qed.

(* EXH_OFF: the per-class exhausted byte lies in RegionInfo's 128-byte stride. *)
Theorem exh_off_A : 0 <= cf_exh_off < 128.
Proof. exact (YGcfImgRows.EXH_OFF_bound cf_exh_off_A). Qed.

(* The closed equation behind ERRB_OWN: one owned static extent of this unit's table holds the whole 56-byte errbuf
   object [0xaa728, 0xaa760) (error_message_buffer 8 + error_report_callback 8 + error_message_buf_mutex 16 +
   error_message_buffer_placeholder 24, twin bff8519bbe3e's .symtab): the 4th extent [0xaa710, 0x5cd510), the
   generator's (gen_af0m b18d364b513a) image of cgif's owned range [0xa5850, 0x5c8650), which holds cgif's same four
   objects. *)
Lemma errb_own_check :
  existsb (fun r => (fst r <=? 0xaa728) && (0xaa728 + 56 <=? fst r + snd r))%bool Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.

(* ERRB_OWN: errb_obj_owned_t (cgif/cgif_file_fuzzer lib/YGcfInstBase.v (file sha256 52402d15ef76; donor not released) :87-88) at A'. *)
Theorem errb_obj_owned_A : forall B, TfibSyms B ->
  forall a, cf_errbuf_obj <= a < cf_errbuf_obj + 56 -> Exists (in_zr a) (as_owned_static B).
Proof.
intros B TB a Ha. rewrite cf_errbuf_obj_A in Ha. rewrite (ts_owned B TB).
pose proof errb_own_check as C. apply existsb_exists in C as (r & Hin & Hr).
apply andb_true_iff in Hr as [R1 R2]. apply Z.leb_le in R1, R2.
apply Exists_exists. exists r. split; [exact Hin|]. unfold in_zr. lia.
Qed.

(* ---- The depot zones (ag_dzone = AGis.DZONE, ims_dzone = AGjm.DZONE: [0x17cd88, 0x5cd510) and the nodes / store
   blocks) against the image objects. ---- *)

(* The nodes and store blocks lie off the image (AGis.off_NB / off_SB: zone3 of layout_ok's blocks). *)
Lemma blocks_off_img_A : forall ly a, layout_ok ly -> AF0x.img_cover ly -> 0x10000 <= a < 0x600000 ->
  ~ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) /\ ~ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize).
Proof.
intros ly a LY IC Ha. split; intros H.
- pose proof (AGis.off_NB _ LY IC _ H) as O. unfold AF0x.off_img, AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END in O. lia.
- pose proof (AGis.off_SB _ LY IC _ H) as O. unfold AF0x.off_img, AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END in O. lia.
Qed.

(* The five apartness facts of the errbuf object at A' (the text before a Theorem Labs lane's split; YGcfErrbSep.ERRB_SEP_at's
   form): the 56-byte errbuf object [0xaa728, 0xaa760) is apart from the instance [0xa7858, 0xa8688), the oom byte
   0x12d120, errno [0x5dde4c, +4) and both depot zones (their image part starts at 0x17cd88; the blocks are off the
   image). *)
Theorem errb_sep5_A : forall B, TfibSyms B -> forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B ->
  cf_errbuf_obj <= a < cf_errbuf_obj + 56 ->
  ~ (as_inst B <= a < as_inst B + 3632) /\ a <> as_oom_byte B /\ ~ (as_errno B <= a < as_errno B + 4) /\
  ~ ims_dzone ly a /\ ~ ag_dzone ly a.
Proof.
intros B TB ly a LY IC HT Ha. rewrite cf_errbuf_obj_A in Ha. change (AF0x.img_cover ly) in IC.
rewrite (ts_inst B TB), (ts_oom B TB), (ts_errno B TB).
destruct (blocks_off_img_A ly a LY IC ltac:(lia)) as [N1 N2].
unfold TFIB_INST, TFIB_OOM, TFIB_ERRNO.
refine (conj _ (conj _ (conj _ (conj _ _)))); [lia | lia | lia | |].
- intros H. change (AGjm.DZONE ly a) in H. unfold AGjm.DZONE in H. destruct H as [H | [H | H]]; [lia | exact (N1 H) | exact (N2 H)].
- intros H. change (AGis.DZONE ly a) in H. unfold AGis.DZONE in H. destruct H as [H | [H | H]]; [lia | exact (N1 H) | exact (N2 H)].
Qed.

(* YGcfInstHit's HDZO at A': ag_dzone's image part lies in one owned static area (found by value), the rest is the
   nodes and store blocks (ADIfaceA.dzone_owned_A's script for AGis.DZONE). *)
Theorem dzone_owned_ag_A : forall B, TfibSyms B -> forall ly a, ag_dzone ly a ->
  Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize).
Proof.
intros B TB ly a Ha. change (AGis.DZONE ly a) in Ha. unfold AGis.DZONE in Ha. destruct Ha as [Ha | [Ha | Ha]].
- left. rewrite (ts_owned _ TB). refine (ADIfaceImgA.covers_b_Exists _ _ _ _ a Ha). clear. vm_compute. reflexivity.
- right. left. exact Ha.
- right. right. exact Ha.
Qed.

(* YGcfInstHit's HDZX at A': ag_dzone misses the instance object, the internal allocator and its flag. *)
Theorem dzone_apart_ag_A : forall B, TfibSyms B -> forall ly a, layout_ok ly -> im_img_cover ly -> ag_dzone ly a ->
  ~ (as_inst B <= a < as_inst B + 3632) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\
  ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2).
Proof.
intros B TB ly a LY IC Ha. change (AF0x.img_cover ly) in IC. change (AGis.DZONE ly a) in Ha.
rewrite (ts_inst B TB), (ts_ial_lo B TB), (ts_ial_hi B TB), (ts_ial_flag B TB).
unfold TFIB_INST, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG.
unfold AGis.DZONE in Ha. destruct Ha as [Ha | [Ha | Ha]].
- lia.
- pose proof (AGis.off_NB _ LY IC _ Ha) as O. unfold AF0x.off_img, AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END in O. lia.
- pose proof (AGis.off_SB _ LY IC _ Ha) as O. unfold AF0x.off_img, AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END in O. lia.
Qed.

(* YGcfInstMiss's HOEB at A': the oom byte 0x12d120 is not in the errbuf object [0xaa728, 0xaa760). *)
Theorem oom_errb_apart_A : forall B, TfibSyms B -> ~ (cf_errbuf_obj <= as_oom_byte B < cf_errbuf_obj + 56).
Proof. intros B TB. rewrite cf_errbuf_obj_A, (ts_oom B TB). unfold TFIB_OOM. lia. Qed.

(* ---- ERRB_SEP's final text (cgif/cgif_file_fuzzer lib/YGcfErrbSep.v (file sha256 f62c93ec3f86; donor not released) :26-29):
   ERRB_SEP_t B := YGcfImgRows.ERRB_QAPART /\ (the rest).  Both conjuncts at A'. ---- *)

(* ERRB_QAPART (YGcfImgRows.v:23-24, class-free, every B, no layout premise) at A': the errbuf object [0xaa728,
   0xaa760) lies above the instance object [0xa7858, 0xa8688). *)
Theorem ERRB_QAPART_A : YGcfImgRows.ERRB_QAPART.
Proof.
intros B TS a Ha. change (TfibSyms B) in TS. rewrite cf_errbuf_obj_A in Ha. rewrite (ts_inst B TS).
unfold TFIB_INST. lia.
Qed.

(* ERRB_SEP_t's second conjunct (YGcfErrbSep.v:27-29), verbatim, at A' (the last four of errb_sep5_A). *)
Theorem ERRB_SEP_rest_A : forall B, TfibSyms B ->
  forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B ->
  cf_errbuf_obj <= a < cf_errbuf_obj + 56 ->
  a <> as_oom_byte B /\ ~ (as_errno B <= a < as_errno B + 4) /\ ~ ims_dzone ly a /\ ~ ag_dzone ly a.
Proof. intros B TB ly a LY IC HT Ha. exact (proj2 (errb_sep5_A B TB ly a LY IC HT Ha)). Qed.

(* ERRB_SEP at A' *)
Theorem ERRB_SEP_A : forall B, TfibSyms B -> YGcfErrbSep.ERRB_SEP_t B.
Proof. intros B TB. exact (conj ERRB_QAPART_A (ERRB_SEP_rest_A B TB)). Qed.

End a.
