(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Uint63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import W64 ITrie FxState FxMem FxRel FxImage.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition odflt {A : Type} (d : A) (o : option A) : A := match o with Some x => x | None => d end.

Definition im_ro (IM : fimage) : fimage := filter (fun sg => negb (sg_wr sg)) IM.

Lemma im_ro_ok : forall segs IM, image_ok segs IM -> image_ok segs (im_ro IM).
Proof.
  intros segs IM H. unfold image_ok, im_ro in *. rewrite Forall_forall in *.
  intros sg Hin. apply filter_In in Hin as [Hin _]. exact (H sg Hin).
Qed.

Lemma im_ro_wr_ok : forall IM, image_wr_ok IM -> image_wr_ok (im_ro IM).
Proof.
  intros IM H. unfold image_wr_ok, im_ro in *. rewrite Forall_forall in *.
  intros sg Hin. apply filter_In in Hin as [Hin _]. exact (H sg Hin).
Qed.

Lemma im_ro_nowr : forall IM, Forall (fun sg => sg_wr sg = false) (im_ro IM).
Proof.
  intros IM. unfold im_ro. rewrite Forall_forall. intros sg Hin.
  apply filter_In in Hin as [_ Hn]. destruct (sg_wr sg); [discriminate | reflexivity].
Qed.

Lemma find_seg_In : forall IM a sg, find_seg IM a = Some sg -> In sg IM.
Proof.
  induction IM as [|s IM IH]; intros a sg H; cbn in H; [discriminate|].
  destruct ((sg_base s <=? a)%uint63 && (a <? sg_base s + sg_size s)%uint63).
  - injection H as <-. left. reflexivity.
  - right. exact (IH a sg H).
Qed.

Lemma im_ro_find_seg : forall IM a sg, find_seg (im_ro IM) a = Some sg -> sg_wr sg = false.
Proof.
  intros IM a sg H. apply find_seg_In in H.
  exact (proj1 (Forall_forall _ _) (im_ro_nowr IM) sg H).
Qed.
