(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound CxPlan CxPlanSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Conv.
  Variable SEGS : list Segment.
  Variable A : APC.atable.
  Variable LIMIT : Z.
  Variable SINV : AX2.env -> (word -> option byte) -> Prop.
  Variable argH : AX2.env -> word -> bool.
  Variable ISP : Z.
  Variable FS0 : Fs.Fs.
  (* [comment removed for export] *)
  Lemma CH_eq : CXS.CH = APS.CH. Proof. unfold CXS.CH, APS.CH. reflexivity. Qed.
  Lemma chunk_eq : forall j c, CXS.chunk j c = APS.chunk j c. Proof. intros. unfold CXS.chunk, APS.chunk. rewrite CH_eq. reflexivity. Qed.
  Lemma fds_std_eq : CXS.fds_std = APS.fds_std. Proof. reflexivity. Qed.
  Lemma fds3_eq : forall e, CXS.fds3 e = APS.fds3 e. Proof. intros e. unfold CXS.fds3, APS.fds3. rewrite fds_std_eq. reflexivity. Qed.
  Lemma fds_ok_of_aps : forall (E : AX2.env) f model, APS.fds_ok E f model -> CXS.fds_ok E f model.
  Proof.
    intros E f model H. destruct f as [|k len off|].
    - unfold APS.fds_ok in H. unfold CXS.fds_ok. rewrite fds_std_eq. exact H.
    - unfold APS.fds_ok in H. unfold CXS.fds_ok.
      destruct H as (p & c & H1 & H2 & H3 & H4 & H5). exists p, c. rewrite fds3_eq.
      split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
      intros j Hj. rewrite chunk_eq. exact (H5 j Hj).
    - unfold APS.fds_ok in H. unfold CXS.fds_ok. rewrite fds3_eq. exact H.
  Qed.
  Lemma seps_of_aps : forall l, APS.seps l -> CXS.seps l.
  Proof. induction 1 as [|p l Hf _ IH]; constructor; [exact Hf | exact IH]. Qed.
  (* [comment removed for export] *)
  Lemma maps_match_of_aps : forall (E : AX2.env) ms l, APS.maps_match E ms l -> CXS.maps_match E ms l.
  Proof.
    intros E ms. induction ms as [|m ms IH]; intros l H; [exact H|].
    cbn [APS.maps_match] in H. cbn [CXS.maps_match]. destruct (APC.is_fog m).
    - destruct H as [H|(iv & l' & Hl & Hs & H)]; [left; exact (IH _ H) | right; exists iv, l'; split; [exact Hl|]; split; [exact Hs | exact (IH _ H)]].
    - destruct H as (l' & Hl & H). right. exists l'. split; [exact Hl | exact (IH _ H)].
  Qed.
  Lemma cxs_cs_ok_of_aps : forall (E : AX2.env) (cs : APC.acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model),
    APS.cs_ok SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model -> CXS.cs_ok SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model.
  Proof.
    intros E cs R FULL model H. destruct H as [h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29]. constructor; [exact h1 | exact h2 | exact h3 | exact h4 | exact (fds_ok_of_aps _ _ _ h5) | exact h6 | exact h7 | exact h8 | exact h9 | exact (maps_match_of_aps _ _ _ h10) | exact h11 | exact (seps_of_aps _ h12) | exact h13 | exact h14 | exact h15 | exact h16 | exact h17 | exact h18 | exact h19 | exact h20 | exact h21 | exact h22 | exact h23 | exact h24 | exact h25 | exact h26 | exact h27 | exact h28 | exact h29].
  Qed.
End Conv.
