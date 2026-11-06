(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyImg_fvzones.v (commit 4d286b2e618d, file sha256 5fa45ee2f881) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 5 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal, jump-table offsets and list indices by the same stage map), 1 list indices re-picked, and 8 addresses named in comments; facts preset already states are cited, not restated; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, row img-fvzones-B of a Theorem Labs lane's internal file REPLY-IMG-ROWS.md, for the cf layer at
   plugin-hostd/fuzz_reply).  rule 24: no function proved (kind: image rows; closed computations at reply's image B,
   fuzz_reply.asan-ubsan, ELF sha256 3389287e1d61).  Reuse search: a prior worker's proof-index FV_IAL FV_ZONE3
   DZONE_OWNED IZONE_OWNED (index built 2026-10-30T04:38:19Z) found only the cf layer's Definitions and fuzz_preset's
   own discharge, none at reply; a prior worker's reply B rows (8e5ca4c0cd2, PresetImgRowsB.v:
   exh_off_B, img_sapart_B, errb_obj_owned_B, img_junk_B) do not state these four.  This file is the B twin of
   a prior worker's lib/A/PresetImg_fvzones.v (row img-fvzones-A): same lemma names and order, image B's addresses.

   The cf layer states these rows as Definitions over its own Section context; reply has not taken those layer files
   yet.  So each Lemma below states the layer Definition's body VERBATIM at reply's instances (the image class
   ImgBase.AImg at AImg_cgif, B/AGif2cgif.v:24; ImgBaseDG.DImg at DImg_cgif, B/DGif0cgif.v:30), at a B with the
   image's symbol facts (TfibSyms B, = im_syms at AImg_cgif), and a consumer closes the layer's row with `exact` once
   the layer is on reply.  No Definition of the layer is copied here.  Texts from cce338413b7a
   (identical to 89caf2ed683 for all five names used here).  Template: cgif's discharges in YGcfInstFreeImgcgif.v
   FV_IAL_cgif :81, FV_ZONE3_cgif :103, DZONE_OWNED_cgif :106, IZONE_OWNED_cgif :112.
   - FV_IAL (YGcfInstFreeView.v:68, ial_post_cf :62-67 unfolded): DGgi.IAL_POST (B/DGgi.v:152-156) is ial_post_cf's
     text with TFIB_IAL_* in place of the asyms fields that TfibSyms equates them to (ts_ial_*, B/YF0m.v:866-869).
   - FV_ZONE3 (YGcfInstFreeView.v:69-70): YF0x.zone3_intro (B/YF0x.v:66).
   - DZONE_OWNED (YGcfDIface.v:287-288): DGgi.DZONE (B/DGgi.v:515-516); its static part [0x17d5c8, 0x5cdd50) lies in the
     fifth region of Tfib_owned_static, (0xaaf50, 0x5cdd50 - 0xaaf50) (B/YF0m.v:820).
   - IZONE_OWNED (YGcfDIface.v:289-290): DGgi.IZONE (B/DGgi.v:517); its flag part [TFIB_IAL_FLAG, + 4) =
     [0x1360c8, 0x1360cc) (B/YF0m.v:19) lies in that same region. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DGgi.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section rows. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The fifth owned static region of reply B's table, which holds the depot, the store and the internal allocator's
   flag: (0xaaf50, 0x5cdd50 - 0xaaf50), B/YF0m.v:820. *)
Lemma owned_big_img : forall B, TfibSyms B ->
  forall a, 0xaaf50 <= a < 0x5cdd50 -> Exists (in_zr a) (as_owned_static B).
Proof.
intros B TS a Ha. rewrite (ts_owned B TS).
apply Exists_exists. exists (0xaaf50, 0x5cdd50 - 0xaaf50). split.
- apply (nth_error_In Tfib_owned_static 3). reflexivity.
- unfold in_zr. cbn [fst snd]. lia.
Qed.

(* FV_IAL at image B (YGcfInstFreeView.v:68; ial_post_cf, :62-67, unfolded). *)
Lemma fv_ial_img : forall B, TfibSyms B -> forall (W : world im_segs) (m : word -> option byte),
  @dg_ial_post AImg_cgif DImg_cgif W m <->
  (let m' := mrestrict (w_H W) m in
   val_mem im_segs m' (as_ialloc_flag B) 1 1 /\ val_mem im_segs m' (as_ialloc_flag B + 1) 1 0 /\
   val_mem im_segs m' (as_ialloc_w B) 8 4096 /\ val_mem im_segs m' (as_ialloc_w B + 8) 8 (as_ialloc_w B + 16) /\
   (forall a, as_ialloc_lo B <= a < as_ialloc_w B \/ as_ialloc_w B + 16 <= a < as_ialloc_hi B ->
      mbyte im_segs m' a = Some (Z_to_bv 8 0))).
Proof.
intros B TS W m. cbn [dg_ial_post DImg_cgif]. unfold DGgi.IAL_POST.
rewrite (ts_ial_flag B TS), (ts_ial_w B TS), (ts_ial_lo B TS), (ts_ial_hi B TS). reflexivity.
Qed.

(* FV_ZONE3 at image B (YGcfInstFreeView.v:69-70). *)
Lemma fv_zone3_img : forall ly x sz, @im_img_cover AImg_cgif ly -> 0 <= sz -> in_app x sz ->
  zdisjoint (x, sz) (ly_img ly) -> @dg_zone3 AImg_cgif DImg_cgif x sz.
Proof. intros ly x sz IC Hsz Ha D. exact (zone3_intro ly x sz IC Hsz Ha D). Qed.

(* DZONE_OWNED at image B (YGcfDIface.v:287-288). *)
Lemma dzone_owned_img : forall B, TfibSyms B -> forall ly a, @dg_dzone AImg_cgif DImg_cgif ly a ->
  Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/
  (ly_SB ly <= a < ly_SB ly + kStoreBlockSize).
Proof.
intros B TS ly a Ha. cbn [dg_dzone DImg_cgif] in Ha. unfold DGgi.DZONE in Ha.
destruct Ha as [H|[H|H]]; [left; apply (owned_big_img B TS); lia | right; left; exact H | right; right; exact H].
Qed.

(* IZONE_OWNED at image B (YGcfDIface.v:289-290). *)
Lemma izone_owned_img : forall B, TfibSyms B -> forall a, @dg_izone AImg_cgif DImg_cgif a ->
  (as_ialloc_lo B <= a < as_ialloc_hi B) \/ Exists (in_zr a) (as_owned_static B).
Proof.
intros B TS a Ha. cbn [dg_izone DImg_cgif] in Ha. unfold DGgi.IZONE in Ha.
rewrite (ts_ial_lo B TS), (ts_ial_hi B TS).
destruct Ha as [H|H]; [left; exact H | right; apply (owned_big_img B TS); unfold TFIB_IAL_FLAG in H; lia].
Qed.
End rows.

(* The acceptance record of the row: each lemma rests only on the system axioms. *)
Print Assumptions owned_big_img.
Print Assumptions fv_ial_img.
Print Assumptions fv_zone3_img.
Print Assumptions dzone_owned_img.
Print Assumptions izone_owned_img.
