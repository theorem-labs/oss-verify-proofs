(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, for lane W of a Theorem Labs lane's cf layer at plugin-hostd/fuzz_reply): the unit row
   PF_APART at reply's image B (fuzz_reply.asan-ubsan), the twin of lib/A/ReplyPfApartA.v, the premise HPFA of the cf layer's Deallocate tops
   (lane F2a, lib/B/YGcfInstFreePost.v PF_APART B at B := TfibB).
   rule 24: no function proved (kind: per-unit image fact about the layout of reply's image A; no function walk).

   PF_APART B := forall a, pf_byte a -> ~ dg_izone a /\ (forall ly, LGUARD ly -> ~ dg_dzone ly a), where pf_byte is
   Printf's two writable image cells (CfImg_B's cf_toolname_cell / cf_pfcb_cell, 8 bytes each) and LGUARD ly :=
   ly_img_ok B ly /\ im_img_cover ly /\ asyms_ok B (YGcfInstFreePost.v:71, :125).  [pf_apart_reply_B] states that text
   unfolded at reply's DImg_reply (DGif0reply: dg_izone := DGgi.IZONE, dg_dzone := DGgi.DZONE) and AImg_reply
   (im_img_cover := YF0x.img_cover), so the layer's PF_APART TfibB is it by conversion.  The twin of cgif's
   YGcfInstFreeImgcgif.PF_APART_of_rows_cgif (a working branch d3b943ec6dd3), on the same route, from the
   reply rows of three other lanes:
   - not in IZONE: a Theorem Labs lane's row ReplyRelroGeoB.pf_ial_apart_reply_B (YG0ncf.pf_ial_apart_t at TfibSyms);
   - not in DZONE's first disjunct [dzone_static_lo, dzone_static_hi) (= TFIB_STORE .. YD20.RS_LO, stackStore ..
     read_stage; ReplyRelroGeoB.dzone_static_text_B): a Theorem Labs lane's row ReplyRelroGeoB.pf_dzone_static_reply_B;
   - not in the node / store blocks (ly_NB, ly_SB): a Theorem Labs lane's row ReplyImg_pfrowsB.pf_cells_static_reply_B puts
     each cell in a static-owned extent of TfibB, LGUARD's ly_img_ok puts that extent inside ly_img ly, and layout_ok's
     lo_disj keeps ly_img apart from both blocks (static_extents ly: owned_extents' NB at index 4, SB at 5, ly_img at 9;
     Reusable/YG0f.v:297-302).  This is cgif's route; no image numeral is typed here. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YF0m YF0x CfImgB YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply ImgBaseDG DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DGgi ReplyRelroGeoB ReplyImg_pfrowsB.
Import ListNotations.
Local Open Scope Z_scope.

(* reply's image constants (Printf's cells) are this file's CfImg instance *)
#[local] Existing Instance CfImg_B.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Local Lemma pairwise_nth_pf {X} (R : X -> X -> Prop) : forall (l : list X) i j x y,
  pairwise R l -> nth_error l i = Some x -> nth_error l j = Some y -> (i < j)%nat -> R x y.
Proof.
induction l as [|h t IH]; intros [|i] [|j] x y P Hi Hj Hij; cbn in *; try discriminate; try lia.
- injection Hi as <-. destruct P as [F _]. apply nth_error_In in Hj. exact (proj1 (Forall_forall _ _) F _ Hj).
- destruct P as [_ P]. eapply IH; eauto. lia.
Qed.

(* PF_APART TfibB (YGcfInstFreePost.v:126), unfolded at DImg_reply / AImg_reply. *)
Lemma pf_apart_reply_B : forall a,
  (cf_toolname_cell <= a < cf_toolname_cell + 8 \/ cf_pfcb_cell <= a < cf_pfcb_cell + 8) ->
  ~ dg_izone a /\
  (forall ly, (layout_ok ly /\ ly_tsd ly = as_tsd TfibB /\
                 Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static TfibB ++ as_zero_shadow TfibB)) /\
              im_img_cover ly /\ asyms_ok TfibB ->
              ~ dg_dzone ly a).
Proof.
intros a Ha. split.
- cbn [dg_izone DImg_reply]. unfold DGgi.IZONE.
  destruct (ReplyRelroGeoB.pf_ial_apart_reply_B TfibB TfibB_syms a Ha) as [I1 I2].
  rewrite (ts_ial_lo _ TfibB_syms), (ts_ial_hi _ TfibB_syms) in I1. rewrite (ts_ial_flag _ TfibB_syms) in I2.
  intros [Hz|Hz]; [exact (I1 Hz) | exact (I2 Hz)].
- intros ly ((LO & _ & SI) & _ & _) Hd.
  cbn [dg_dzone DImg_reply] in Hd.
  change (DGgi.DZONE ly a) with ((ReplyRelroGeoB.dzone_static_lo <= a < ReplyRelroGeoB.dzone_static_hi) \/
    (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize)) in Hd.
  destruct Hd as [Hs|Hd]; [exact (ReplyRelroGeoB.pf_dzone_static_reply_B a Ha Hs)|].
  destruct (ReplyImg_pfrowsB.pf_cells_static_reply_B TfibB TfibB_syms a Ha) as [OS _].
  apply Exists_exists in OS as (r & Hr & Hin).
  pose proof (proj1 (Forall_forall _ _) SI r ltac:(apply in_or_app; left; exact Hr)) as [Z1 Z2].
  pose proof (pairwise_nth_pf zdisjoint _ 4 9 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as DN.
  pose proof (pairwise_nth_pf zdisjoint _ 5 9 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as DS.
  unfold zdisjoint, in_zr in *. cbn [fst snd] in DN, DS. lia.
Qed.

End a.
