(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, row img-hdzx-A of a Theorem Labs lane's REPLY-IMG-ROWS.md (sha256 a33a582e3ffd; internal record); merger ReallocPrimary.CfW).
   rule 24: no function proved (kind: image rows; a closed computation at reply's image A, fuzz_reply.asan).
   Reuse search: the row's cgif discharge, YGcfInstHitcgif.v:78 HDZX_cgif (a working branch cc4fb1f2a13); no HDZX
   discharge at reply.

   HDZX is the cf layer's YGcfInstHit.v:154-155 (a working branch ee95275bccb):
     forall ly' a, layout_ok ly' -> im_img_cover ly' -> ag_dzone ly' a ->
       ~ (as_inst B <= a < as_inst B + 3632) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\
       ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2).
   [ag_dzone] is the cf interface class AGImg's field, which reply does not carry yet, so it is stated UNFOLDED, as in
   ReplyImg_hdzo.v (row img-hdzo-A, the same zone):
   - [hdzx_A_any]: for ANY image part [lo, hi) with lo above the instance object, the internal allocator's zone and its
     flag (the highest of the three ends is the flag's, 0x135b48 + 2), plus the depot's nodes and store blocks;
   - [hdzx_A]: with ag_dzone := ReplyImg_hdzo.DZONE_A (cgif's AGis.DZONE at reply A's numbers, image part [TFIB_STORE =
     0x177f88, 0x5c8710)).
   Reply A's symbols (A/AF0m.v:17-20): TFIB_INST 0xa2a58 (+ 3632 = 0xa3888), TFIB_IAL_LO / HI 0xa72c0 / 0x1282f0,
   TFIB_IAL_FLAG 0x135b48. The blocks are apart from the image window by layout_ok's lo_disj (static_extents indices 4
   (NB), 5 (SB), 9 (ly_img), Reusable/YG0f.v:297-302, the same order as cgif's), and the window covers the image
   [TFIB_IMG_LO, TFIB_IMG_END) = [0x10000, 0x5fb000) (img_cover, A/AF0x.v:54), which holds the three objects. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply ReplyImg_hdzo.
Import ListNotations.
Open Scope Z_scope.

(* Two distinct entries of a pairwise list are related (copied from cgif's YGcfInstHitcgif.v:34-43, pairwise_nth_c). *)
Lemma hdzx_pairwise_nth {X : Type} (R : X -> X -> Prop) : forall l i j x y, pairwise R l ->
  nth_error l i = Some x -> nth_error l j = Some y -> (i < j)%nat -> R x y.
Proof.
induction l as [|h t IH]; intros i j x y P Hi Hj Lt; [destruct i; discriminate|].
cbn [pairwise] in P. destruct P as [F P]. destruct i as [|i].
- cbn in Hi. injection Hi as <-. destruct j as [|j]; [lia|]. cbn in Hj.
  exact (proj1 (Forall_forall _ _) F y (nth_error_In _ _ Hj)).
- destruct j as [|j]; [lia|]. cbn in Hi, Hj. exact (IH i j x y P Hi Hj ltac:(lia)).
Qed.

(* layout_ok and img_cover read the run ceiling (layout_ok is in Reusable/YG0f.v's Section with {rc}): the lemmas below
   take it as a context variable; the cf layer states HDZX inside Sections that carry {fx} {rc} among their context. *)
Section rows. Context {rc : YM05.RunCeil}.

(* The depot's two blocks are apart from the image window, which covers [0x10000, 0x5fb000). *)
Lemma hdzx_blocks_off_img_A : forall ly, layout_ok ly -> img_cover ly -> forall a,
  ((ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize)) ->
  a < TFIB_IMG_LO \/ TFIB_IMG_END <= a.
Proof.
intros ly LY [I1 I2] a Ha.
pose proof (hdzx_pairwise_nth zdisjoint _ 4 9 _ _ (lo_disj _ LY) eq_refl eq_refl ltac:(lia)) as D4.
pose proof (hdzx_pairwise_nth zdisjoint _ 5 9 _ _ (lo_disj _ LY) eq_refl eq_refl ltac:(lia)) as D5.
unfold zdisjoint in D4, D5. cbn [fst snd] in D4, D5. lia.
Qed.

(* HDZX at image A for any image part [lo, hi) above the three objects. *)
Lemma hdzx_A_any : forall lo hi, 0x135b48 + 2 <= lo ->
  forall B, @im_syms AImg_reply B -> forall ly' a, layout_ok ly' -> @im_img_cover AImg_reply ly' ->
  ((lo <= a < hi) \/ (ly_NB ly' <= a < ly_NB ly' + kNodesBlockSize) \/ (ly_SB ly' <= a < ly_SB ly' + kStoreBlockSize)) ->
  ~ (as_inst B <= a < as_inst B + 3632) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\
  ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2).
Proof.
intros lo hi Hlo B TS ly a LY IMG Hd. change (TfibSyms B) in TS. change (img_cover ly) in IMG.
rewrite (ts_inst B TS), (ts_ial_lo B TS), (ts_ial_hi B TS), (ts_ial_flag B TS).
unfold TFIB_INST, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG.
destruct Hd as [Hd|Hb].
- split; [|split]; intros Ha; lia.
- pose proof (hdzx_blocks_off_img_A ly LY IMG a Hb) as Off. unfold TFIB_IMG_LO, TFIB_IMG_END in Off.
  split; [|split]; intros Ha; lia.
Qed.

(* HDZX at image A, with ag_dzone := DZONE_A (ReplyImg_hdzo.v). *)
Theorem hdzx_A : forall B, @im_syms AImg_reply B -> forall ly' a, layout_ok ly' -> @im_img_cover AImg_reply ly' ->
  DZONE_A ly' a ->
  ~ (as_inst B <= a < as_inst B + 3632) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\
  ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2).
Proof.
intros B TS ly a LY IMG Hd. unfold DZONE_A, TFIB_STORE in Hd.
exact (hdzx_A_any 0x177f88 0x5c8710 ltac:(lia) B TS ly a LY IMG Hd).
Qed.

End rows.
