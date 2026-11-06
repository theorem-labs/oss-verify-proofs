(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, row img-fvzones-A of a Theorem Labs lane's REPLY-IMG-ROWS.md (sha256 a33a582e3ffd; internal record), for the cf layer at
   plugin-hostd/fuzz_reply).  rule 24: no function proved (kind: image rows; closed computations at reply's image A,
   fuzz_reply.asan, pin 42c58610e125).  Reuse search: proof-index FV_IAL FV_ZONE3 DZONE_OWNED IZONE_OWNED (index
   built 2026-10-30T04:38:19Z): only the cf layer's Definitions and fuzz_preset's own discharge (WrapFreeATop.v:87), no
   discharge at reply; a Theorem Labs lane's reply rows (a working branch c61d83c6f0c, ReplyImgRowsA.v) do not state them.

   The cf layer states these rows as Definitions over its own Section context; reply has not taken those layer files
   yet.  So each Lemma below states the layer Definition's body VERBATIM at reply's instances (the image class
   ImgBase.AImg at AImg_reply, A/AGif2reply.v:23; ImgBaseDG.DImg at DImg_reply, A/DGif0reply.v:30), at a B with the
   image's symbol facts (TfibSyms B, = im_syms at AImg_reply), and a consumer closes the layer's row with `exact` once the layer is on
   reply.  No Definition of the layer is copied here.  Layer lines at a working branch 89caf2ed683.  Template: cgif's
   discharges in YGcfInstFreeImgcgif.v there, FV_IAL_cgif :81, FV_ZONE3_cgif :103, DZONE_OWNED_cgif :106, IZONE_OWNED_cgif :112.
   - FV_IAL (YGcfInstFreeView.v:68, ial_post_cf :62-67 unfolded): DGgi.IAL_POST (A/DGgi.v:151-155) is ial_post_cf's
     text with TFIB_IAL_* in place of the asyms fields that TfibSyms equates them to (ts_ial_*, A/AF0m.v:867-870).
   - FV_ZONE3 (YGcfInstFreeView.v:69-70): AF0x.zone3_intro (A/AF0x.v:66).
   - DZONE_OWNED (YGcfDIface.v:287-288): DGgi.DZONE (A/DGgi.v:514-515); its static part [0x177f88, 0x5c8710) lies in the
     fifth region of Tfib_owned_static, (0xa5910, 0x5c8710 - 0xa5910) (A/AF0m.v:823).
   - IZONE_OWNED (YGcfDIface.v:289-290): DGgi.IZONE (A/DGgi.v:516); its flag part [TFIB_IAL_FLAG, + 4) =
     [0x135b48, 0x135b4c) (A/AF0m.v:20) lies in that same region. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply ImgBaseDG DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DGgi.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section rows. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The fifth owned static region of reply A's table, which holds the depot, the store and the internal allocator's
   flag: (0xa5910, 0x5c8710 - 0xa5910), A/AF0m.v:823. *)
Lemma owned_big_img : forall B, TfibSyms B ->
  forall a, 0xa5910 <= a < 0x5c8710 -> Exists (in_zr a) (as_owned_static B).
Proof.
intros B TS a Ha. rewrite (ts_owned B TS).
apply Exists_exists. exists (0xa5910, 0x5c8710 - 0xa5910). split.
- apply (nth_error_In Tfib_owned_static 4). reflexivity.
- unfold in_zr. cbn [fst snd]. lia.
Qed.

(* FV_IAL at image A (YGcfInstFreeView.v:68; ial_post_cf, :62-67, unfolded). *)
Lemma fv_ial_img : forall B, TfibSyms B -> forall (W : world im_segs) (m : word -> option byte),
  @dg_ial_post AImg_reply DImg_reply W m <->
  (let m' := mrestrict (w_H W) m in
   val_mem im_segs m' (as_ialloc_flag B) 1 1 /\ val_mem im_segs m' (as_ialloc_flag B + 1) 1 0 /\
   val_mem im_segs m' (as_ialloc_w B) 8 4096 /\ val_mem im_segs m' (as_ialloc_w B + 8) 8 (as_ialloc_w B + 16) /\
   (forall a, as_ialloc_lo B <= a < as_ialloc_w B \/ as_ialloc_w B + 16 <= a < as_ialloc_hi B ->
      mbyte im_segs m' a = Some (Z_to_bv 8 0))).
Proof.
intros B TS W m. cbn [dg_ial_post DImg_reply]. unfold DGgi.IAL_POST.
rewrite (ts_ial_flag B TS), (ts_ial_w B TS), (ts_ial_lo B TS), (ts_ial_hi B TS). reflexivity.
Qed.

(* FV_ZONE3 at image A (YGcfInstFreeView.v:69-70). *)
Lemma fv_zone3_img : forall ly x sz, @im_img_cover AImg_reply ly -> 0 <= sz -> in_app x sz ->
  zdisjoint (x, sz) (ly_img ly) -> @dg_zone3 AImg_reply DImg_reply x sz.
Proof. intros ly x sz IC Hsz Ha D. exact (zone3_intro ly x sz IC Hsz Ha D). Qed.

(* DZONE_OWNED at image A (YGcfDIface.v:287-288). *)
Lemma dzone_owned_img : forall B, TfibSyms B -> forall ly a, @dg_dzone AImg_reply DImg_reply ly a ->
  Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/
  (ly_SB ly <= a < ly_SB ly + kStoreBlockSize).
Proof.
intros B TS ly a Ha. cbn [dg_dzone DImg_reply] in Ha. unfold DGgi.DZONE in Ha.
destruct Ha as [H|[H|H]]; [left; apply (owned_big_img B TS); lia | right; left; exact H | right; right; exact H].
Qed.

(* IZONE_OWNED at image A (YGcfDIface.v:289-290). *)
Lemma izone_owned_img : forall B, TfibSyms B -> forall a, @dg_izone AImg_reply DImg_reply a ->
  (as_ialloc_lo B <= a < as_ialloc_hi B) \/ Exists (in_zr a) (as_owned_static B).
Proof.
intros B TS a Ha. cbn [dg_izone DImg_reply] in Ha. unfold DGgi.IZONE in Ha.
rewrite (ts_ial_lo B TS), (ts_ial_hi B TS).
destruct Ha as [H|H]; [left; exact H | right; apply (owned_big_img B TS); unfold TFIB_IAL_FLAG in H; lia].
Qed.
End rows.
