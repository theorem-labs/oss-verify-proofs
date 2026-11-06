(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyImg_hdzx.v (commit 4d286b2e618d, file sha256 bd7ed09eb2d4) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 7 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a prior worker, row img-hdzx-B of a Theorem Labs lane's internal file REPLY-IMG-ROWS.md, for a Theorem Labs lane's cf layer at
   plugin-hostd/fuzz_reply).
   rule 24: no function proved (kind: image row; a closed computation at reply's image B, fuzz_reply.asan-ubsan).

   HDZX is the cf layer's Hypothesis of YGcfInstHit.v:154-155 (commit ee95275bccb, Section b):
     forall ly' a, layout_ok ly' -> im_img_cover ly' -> ag_dzone ly' a ->
       ~ (as_inst B <= a < as_inst B + 3632) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\
       ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2).
   Every name in it is already in reply's tree, so hdzx_B states it verbatim at reply's instance, as hdzo_B
   (lib/B/PresetImg_hdzo.v) does for HDZO: the image class ImgBase.AImg at image B's AImg_cgif (B/AGif2cgif.v, whose
   im_img_cover is B/YF0x.v's img_cover and im_syms is TfibSyms) and ImgBaseAG.AGImg at B/AGif0cgif.v's
   AGImg_cgif (whose ag_dzone is AGis.DZONE), for a B with the image's symbol facts. A consumer closes the layer's
   HDZX with `exact (hdzx_B B TS)` once the layer is on reply. Same stem as the A twin, hdzx_A (a prior worker).

   The proof is cgif's HDZX_cgif (YGcfInstHitcgif.v:78 @ ee95275bccb) at this image, with image B's OWN numerals,
   read from B/YF0m.v and B/AGis.v, none carried over from cgif:
     instance object   TFIB_INST     0xa8098,   [0xa8098, 0xa8098 + 3632)
     internal allocator TFIB_IAL_LO/HI [0xac900, 0x128870)
     its flag          TFIB_IAL_FLAG 0x1360c8,  [0x1360c8, 0x1360ca)
   all inside the image and all below AGis.DZONE's image part [0x17d5c8, 0x5cdd50). DZONE's other two parts are the
   depot's blocks NB and SB, which layout_ok's lo_disj keeps apart from the image window (static extents 4 and 5
   against 9: B/../Reusable/YG0f.v owned_extents lists prim, Q, T, F, NB, SB, C, D, then the stack and ly_img, the
   same order as cgif's), and img_cover puts the image window over [TFIB_IMG_LO, TFIB_IMG_END) = [0x10000, 0x601000).
   So each of the three cells, being in the image, is in none of DZONE's three parts. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ImgBaseAG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AGis AGif0cgif.
Open Scope Z_scope.

(* Two distinct static extents of a layout are disjoint: layout_ok's lo_disj, read at two positions. cgif's
   pairwise_nth_c / static_disj_c (YGcfInstHitcgif.v:41-53 @ ee95275bccb) are local to that file, so they are
   repeated here, not imported. *)
Lemma pairwise_nth_r {X : Type} (R : X -> X -> Prop) : forall l i j x y, pairwise R l ->
  nth_error l i = Some x -> nth_error l j = Some y -> (i < j)%nat -> R x y.
Proof.
induction l as [|h t IH]; intros i j x y P Hi Hj Lt; [destruct i; discriminate|].
cbn [pairwise] in P. destruct P as [F P]. destruct i as [|i].
- cbn in Hi. injection Hi as <-. destruct j as [|j]; [lia|]. cbn in Hj.
  exact (proj1 (Forall_forall _ _) F y (nth_error_In _ _ Hj)).
- destruct j as [|j]; [lia|]. cbn in Hi, Hj. exact (IH i j x y P Hi Hj ltac:(lia)).
Qed.

(* layout_ok reads the run's ceiling, so the rest is stated in cgif's own context (YGcfInstHitcgif.v:37). *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma static_disj_r : forall ly, layout_ok ly -> forall i j x y, nth_error (static_extents ly) i = Some x ->
  nth_error (static_extents ly) j = Some y -> (i < j)%nat -> zdisjoint x y.
Proof. intros ly LO i j x y Hi Hj Lt. exact (pairwise_nth_r zdisjoint _ i j x y (lo_disj _ LO) Hi Hj Lt). Qed.

(* HDZX at image B (YGcfInstHit.v:154-155 @ ee95275bccb). *)
Lemma hdzx_B : forall B, @im_syms AImg_cgif B ->
  forall ly' a, layout_ok ly' -> @im_img_cover AImg_cgif ly' ->
  @ImgBaseAG.ag_dzone AImg_cgif AGif0cgif.AGImg_cgif ly' a ->
  ~ (as_inst B <= a < as_inst B + 3632) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\
  ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2).
Proof.
intros B TS ly a LY IMG Hd. change (TfibSyms B) in TS. change (img_cover ly) in IMG. destruct IMG as [I1 I2].
change (AGis.DZONE ly a) in Hd. unfold AGis.DZONE in Hd.
(* the depot's two blocks (static extents 4 and 5) against the image window (static extent 9) *)
pose proof (static_disj_r ly LY 4 9 _ _ eq_refl eq_refl ltac:(lia)) as D4.
pose proof (static_disj_r ly LY 5 9 _ _ eq_refl eq_refl ltac:(lia)) as D5.
unfold zdisjoint in D4, D5. cbn [fst snd] in D4, D5.
rewrite (ts_inst B TS), (ts_ial_lo B TS), (ts_ial_hi B TS), (ts_ial_flag B TS).
unfold TFIB_INST, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in *.
unfold YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END in I1, I2.
split; [|split]; intros Ha; lia.
Qed.
End a.
