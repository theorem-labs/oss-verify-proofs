(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad StdioCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section Crawl.
  Context {St : Type}.
  Notation mleaf := (@mleaf St).

  Lemma mleaf_bind_inv : forall {A B} (m : @M St A) (f : A -> @M St B) s b s'',
    mleaf (mbind m f) s b s'' -> exists a s', mleaf m s a s' /\ mleaf (f a) s' b s''.
  Proof using rc. intros. apply mleaf_bind. exact H. Qed.

  Lemma towrite_leaf : forall f st f' st', mleaf (towrite f) st f' st' -> f_nowr f = false /\ f' = set_w true [] (set_rbuf [] f) /\ st' = st.
  Proof using rc.
    intros f st f' st' H. unfold towrite in H. destruct (f_nowr f) eqn:E.
    - exfalso. exact (mleaf_unr _ _ _ H).
    - destruct (mleaf_ret _ _ _ _ H) as [-> ->]. auto.
  Qed.

  Lemma ensure_w_leaf : forall f st f' st', mleaf (ensure_w f) st f' st' -> fx_inv f f' /\ st' = st.
  Proof using rc.
    intros f st f' st' H. unfold ensure_w in H. destruct (f_wactive f) eqn:E.
    - destruct (mleaf_ret _ _ _ _ H) as [-> ->]. split; [apply fx_inv_refl; exact E| reflexivity].
    - destruct (towrite_leaf _ _ _ _ H) as (NW & -> & ->). split; [apply fx_inv_towrite; exact E| reflexivity].
  Qed.

  Lemma writev_loop_leaf : forall fuel f iovs rem st u st', mleaf (writev_loop fuel f iovs rem) st u st' -> st' = st.
  Proof using rc.
    induction fuel as [|fuel IH]; intros f iovs rem st u st' H; cbn [writev_loop] in H.
    - exfalso. exact (mleaf_unr _ _ _ H).
    - destruct (mleaf_bind_inv _ _ _ _ _ H) as (cnt & s1 & H1 & H2).
      destruct (mleaf_sys _ _ _ _ _ H1) as [-> _].
      destruct (cnt =? rem); [destruct (mleaf_ret _ _ _ _ H2) as [_ ->]; reflexivity | eapply IH; exact H2].
  Qed.

  Lemma stdio_write_leaf : forall f s st f' st', mleaf (stdio_write f s) st f' st' -> f' = set_w true [] f /\ st' = st.
  Proof using rc.
    intros f s st f' st' H. unfold stdio_write in H.
    destruct (mleaf_bind_inv _ _ _ _ _ H) as (u & s1 & H1 & H2).
    pose proof (writev_loop_leaf _ _ _ _ _ _ _ H1) as ->. destruct (mleaf_ret _ _ _ _ H2) as [-> ->]. auto.
  Qed.

  Lemma file_writefn_leaf : forall f s st f' st', mleaf (file_writefn f s) st f' st' ->
    (f' = set_w true [] f \/ f' = set_w true [] (after_ioctl f)) /\ st' = st.
  Proof using rc.
    intros f s st f' st' H. unfold file_writefn in H. destruct (f_stdoutw f).
    - destruct (mleaf_bind_inv _ _ _ _ _ H) as (r & s1 & H1 & H2). destruct (mleaf_sys _ _ _ _ _ H1) as [-> _].
      destruct r; [| exfalso; exact (mleaf_unr _ _ _ H2)].
      destruct (stdio_write_leaf _ _ _ _ _ H2) as [-> ->]. auto.
    - destruct (stdio_write_leaf _ _ _ _ _ H) as [-> ->]. auto.
  Qed.

  Lemma fx_inv_after_ioctl_w : forall f0 f1, fx_inv f0 f1 -> fx_inv f0 (set_w true [] (after_ioctl f1)).
  Proof using Type.
    unfold fx_inv, after_ioctl. intros f0 f1 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10). cbn.
    repeat split; auto; intros HH; discriminate HH.
  Qed.

  Lemma fx_inv_trans : forall f0 f1 f2, fx_inv f0 f1 -> fx_inv f1 f2 -> fx_inv f0 f2.
  Proof using Type.
    unfold fx_inv. intros f0 f1 f2 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10) (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
    rewrite B1, B2, B3, B4, B5, B6, B8, A7. repeat split; auto.
  Qed.

  Lemma file_writefn_leaf_fx : forall f0 f s st f' st', fx_inv f0 f -> mleaf (file_writefn f s) st f' st' -> fx_inv f0 f' /\ st' = st.
  Proof using rc.
    intros f0 f s st f' st' FX H. destruct (file_writefn_leaf _ _ _ _ _ H) as [[-> | ->] ->].
    - split; [apply fx_inv_set_w; exact FX| reflexivity].
    - split; [apply fx_inv_after_ioctl_w; exact FX| reflexivity].
  Qed.

  Lemma fwritex_leaf : forall f s st f' st', mleaf (fwritex f s) st f' st' -> fx_inv f f' /\ st' = st.
  Proof using rc.
    intros f s st f' st' H. unfold fwritex in H.
    destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2). destruct (ensure_w_leaf _ _ _ _ H1) as [FX ->].
    destruct (f_bufsize f1 - zlength (f_wbuf f1) <? zlength s).
    - exact (file_writefn_leaf_fx _ _ _ _ _ _ FX H2).
    - destruct (f_lbf_nl f1).
      + destruct (mleaf_bind_inv _ _ _ _ _ H2) as (f2 & s2 & H3 & H4).
        assert (FX2 : fx_inv f f2 /\ s2 = st).
        { destruct (0 <? after_last_nl s); [exact (file_writefn_leaf_fx _ _ _ _ _ _ FX H3)|].
          destruct (mleaf_ret _ _ _ _ H3) as [-> ->]. auto. }
        destruct FX2 as [FX2 ->]. destruct (mleaf_ret _ _ _ _ H4) as [-> ->]. split; [apply fx_inv_set_w; exact FX2| reflexivity].
      + destruct (mleaf_ret _ _ _ _ H2) as [-> ->]. split; [apply fx_inv_set_w; exact FX| reflexivity].
  Qed.

  Lemma out_pieces_leaf : forall ps f st f' st', mleaf (out_pieces f ps) st f' st' -> (f' = f \/ fx_inv f f') /\ st' = st.
  Proof using rc.
    induction ps as [|p ps IH]; intros f st f' st' H; cbn [out_pieces] in H.
    - destruct (mleaf_ret _ _ _ _ H) as [-> ->]. auto.
    - destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2). destruct (fwritex_leaf _ _ _ _ _ H1) as [FX ->].
      destruct (IH _ _ _ _ H2) as [[-> | FX2] ->]; (split; [right | reflexivity]); [exact FX | exact (fx_inv_trans _ _ _ FX FX2)].
  Qed.

  (* [comment removed for export] *)
  Lemma vfprintf_leaf_buffered : forall f ps st f' st', f_bufsize f <> 0 ->
    mleaf (vfprintf f ps) st f' st' -> fx_inv f f' /\ st' = st.
  Proof using rc.
    intros f ps st f' st' BS H. unfold vfprintf in H. destruct (Z.eqb_spec (f_bufsize f) 0); [lia|].
    destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2). destruct (ensure_w_leaf _ _ _ _ H1) as [FX ->].
    destruct (out_pieces_leaf _ _ _ _ _ H2) as [[-> | FX2] ->]; split; auto. exact (fx_inv_trans _ _ _ FX FX2).
  Qed.

  (* [comment removed for export] *)
  Definition wl_rel (f f' : file_st) : Prop :=
    (f_stdoutw f' = f_stdoutw f /\ f_lbf_nl f' = f_lbf_nl f) \/ (f_stdoutw f' = false /\ f_lbf_nl f' = false).
  Lemma wl_rel_refl : forall f, wl_rel f f.
  Proof using Type. intros f. left. auto. Qed.
  Lemma wl_rel_trans : forall f0 f1 f2, wl_rel f0 f1 -> wl_rel f1 f2 -> wl_rel f0 f2.
  Proof using Type.
    unfold wl_rel. intros f0 f1 f2 [[A1 A2]|[A1 A2]] [[B1 B2]|[B1 B2]].
    - left. split; congruence. - right. auto. - right. split; congruence. - right. auto.
  Qed.
  Lemma wl_rel_set_w : forall f0 f1 a w, wl_rel f0 f1 -> wl_rel f0 (set_w a w f1).
  Proof using Type. intros f0 f1 a w R. unfold wl_rel in *. cbn. exact R. Qed.
  Lemma file_writefn_leaf_wl : forall f0 f s st f' st', wl_rel f0 f -> mleaf (file_writefn f s) st f' st' -> wl_rel f0 f'.
  Proof using rc.
    intros f0 f s st f' st' R H. destruct (file_writefn_leaf _ _ _ _ _ H) as [[-> | ->] _].
    - apply wl_rel_set_w. exact R.
    - unfold wl_rel. cbn. right. auto.
  Qed.
  Lemma ensure_w_leaf_wl : forall f st f' st', mleaf (ensure_w f) st f' st' -> wl_rel f f'.
  Proof using rc.
    intros f st f' st' H. unfold ensure_w in H. destruct (f_wactive f) eqn:E.
    - destruct (mleaf_ret _ _ _ _ H) as [-> ->]. apply wl_rel_refl.
    - destruct (towrite_leaf _ _ _ _ H) as (NW & -> & ->). unfold wl_rel. cbn. left. auto.
  Qed.
  Lemma fwritex_leaf_wl : forall f s st f' st', mleaf (fwritex f s) st f' st' -> wl_rel f f'.
  Proof using rc.
    intros f s st f' st' H. unfold fwritex in H.
    destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2). pose proof (ensure_w_leaf_wl _ _ _ _ H1) as R1.
    destruct (ensure_w_leaf _ _ _ _ H1) as [_ ->].
    destruct (f_bufsize f1 - zlength (f_wbuf f1) <? zlength s).
    - exact (file_writefn_leaf_wl _ _ _ _ _ _ R1 H2).
    - destruct (f_lbf_nl f1).
      + destruct (mleaf_bind_inv _ _ _ _ _ H2) as (f2 & s2 & H3 & H4).
        assert (R2 : wl_rel f f2 /\ s2 = st).
        { destruct (0 <? after_last_nl s).
          - split; [exact (file_writefn_leaf_wl _ _ _ _ _ _ R1 H3)|]. exact (proj2 (file_writefn_leaf _ _ _ _ _ H3)).
          - destruct (mleaf_ret _ _ _ _ H3) as [-> ->]. auto. }
        destruct R2 as [R2 ->]. destruct (mleaf_ret _ _ _ _ H4) as [-> ->]. apply wl_rel_set_w. exact R2.
      + destruct (mleaf_ret _ _ _ _ H2) as [-> ->]. apply wl_rel_set_w. exact R1.
  Qed.
  Lemma out_pieces_leaf_wl : forall ps f st f' st', mleaf (out_pieces f ps) st f' st' -> wl_rel f f'.
  Proof using rc.
    induction ps as [|p ps IH]; intros f st f' st' H; cbn [out_pieces] in H.
    - destruct (mleaf_ret _ _ _ _ H) as [-> ->]. apply wl_rel_refl.
    - destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2).
      exact (wl_rel_trans _ _ _ (fwritex_leaf_wl _ _ _ _ _ H1) (IH _ _ _ _ H2)).
  Qed.
  Lemma vfprintf_leaf_buffered_wl : forall f ps st f' st', f_bufsize f <> 0 ->
    mleaf (vfprintf f ps) st f' st' -> wl_rel f f'.
  Proof using rc.
    intros f ps st f' st' BS H. unfold vfprintf in H. destruct (Z.eqb_spec (f_bufsize f) 0); [lia|].
    destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2).
    exact (wl_rel_trans _ _ _ (ensure_w_leaf_wl _ _ _ _ H1) (out_pieces_leaf_wl _ _ _ _ _ H2)).
  Qed.

  (* [comment removed for export] *)
  Definition ubf_rel (f f' : file_st) : Prop :=
    f_fd f' = f_fd f /\ f_chan f' = f_chan f /\ f_bufsize f' = 0 /\ f_nord f' = f_nord f /\ f_nowr f' = f_nowr f /\ f_eof f' = f_eof f
    /\ f_wactive f' = false /\ f_wbuf f' = [] /\ f_rbuf f' = []
    /\ (f_stdoutw f' = true -> f_stdoutw f = true) /\ (f_lbf_nl f' = true -> f_lbf_nl f = true).

  Lemma vfprintf_leaf_unbuffered : forall f ps st f' st', f_bufsize f = 0 ->
    mleaf (vfprintf f ps) st f' st' -> ubf_rel f f' /\ st' = st.
  Proof using rc.
    intros f ps st f' st' BS H. unfold vfprintf in H. rewrite BS in H. change (0 =? 0) with true in H. cbv iota in H.
    destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2). destruct (towrite_leaf _ _ _ _ H1) as (NW & -> & ->).
    destruct (mleaf_bind_inv _ _ _ _ _ H2) as (f2 & s2 & H3 & H4).
    destruct (mleaf_bind_inv _ _ _ _ _ H4) as (f3 & s3 & H5 & H6).
    destruct (mleaf_ret _ _ _ _ H6) as [-> ->].
    assert (FX1 : fx_inv f (set_w true [] (set_rbuf [] (set_w false [] (set_bufsize INTERNAL_BUFSIZ f)))) \/ True) by (right; exact I).
    set (g := set_w true [] (set_rbuf [] (set_w false [] (set_bufsize INTERNAL_BUFSIZ f)))) in *.
    assert (G2 : f2 = g \/ fx_inv g f2) by (destruct (out_pieces_leaf _ _ _ _ _ H3) as [X _]; exact X).
    assert (S2 : s2 = st) by (destruct (out_pieces_leaf _ _ _ _ _ H3) as [_ X]; exact X). subst s2.
    destruct (file_writefn_leaf _ _ _ _ _ H5) as [F3 ->]. split; [| reflexivity].
    assert (K2 : f_fd f2 = f_fd f /\ f_chan f2 = f_chan f /\ f_nord f2 = f_nord f /\ f_nowr f2 = f_nowr f /\ f_eof f2 = f_eof f
                 /\ (f_stdoutw f2 = true -> f_stdoutw f = true) /\ (f_lbf_nl f2 = true -> f_lbf_nl f = true) /\ f_rbuf f2 = []).
    { destruct G2 as [-> | (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10)]; [subst g; cbn; repeat split; auto|].
      subst g. cbn in *. repeat split; auto. }
    destruct K2 as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8).
    unfold ubf_rel. destruct F3 as [-> | ->]; cbn; repeat split; cbn; auto; try congruence; try (intros HH; discriminate HH).
  Qed.
End Crawl.

End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section Crawl.
  Context {St : Type}.
  Notation mleaf := (@mleaf St).

  Lemma mleaf_bind_inv : forall {A B} (m : @M St A) (f : A -> @M St B) s b s'',
    mleaf (mbind m f) s b s'' -> exists a s', mleaf m s a s' /\ mleaf (f a) s' b s''.
  Proof using rc. intros. apply mleaf_bind. exact H. Qed.

  Lemma towrite_leaf : forall f st f' st', mleaf (towrite f) st f' st' -> f_nowr f = false /\ f' = set_w true [] (set_rbuf [] f) /\ st' = st.
  Proof using rc.
    intros f st f' st' H. unfold towrite in H. destruct (f_nowr f) eqn:E.
    - exfalso. exact (mleaf_unr _ _ _ H).
    - destruct (mleaf_ret _ _ _ _ H) as [-> ->]. auto.
  Qed.

  Lemma ensure_w_leaf : forall f st f' st', mleaf (ensure_w f) st f' st' -> fx_inv f f' /\ st' = st.
  Proof using rc.
    intros f st f' st' H. unfold ensure_w in H. destruct (f_wactive f) eqn:E.
    - destruct (mleaf_ret _ _ _ _ H) as [-> ->]. split; [apply fx_inv_refl; exact E| reflexivity].
    - destruct (towrite_leaf _ _ _ _ H) as (NW & -> & ->). split; [apply fx_inv_towrite; exact E| reflexivity].
  Qed.

  Lemma writev_loop_leaf : forall fuel f iovs rem st u st', mleaf (writev_loop fuel f iovs rem) st u st' -> st' = st.
  Proof using rc.
    induction fuel as [|fuel IH]; intros f iovs rem st u st' H; cbn [writev_loop] in H.
    - exfalso. exact (mleaf_unr _ _ _ H).
    - destruct (mleaf_bind_inv _ _ _ _ _ H) as (cnt & s1 & H1 & H2).
      destruct (mleaf_sys _ _ _ _ _ H1) as [-> _].
      destruct (cnt =? rem); [destruct (mleaf_ret _ _ _ _ H2) as [_ ->]; reflexivity | eapply IH; exact H2].
  Qed.

  Lemma stdio_write_leaf : forall f s st f' st', mleaf (stdio_write f s) st f' st' -> f' = set_w true [] f /\ st' = st.
  Proof using rc.
    intros f s st f' st' H. unfold stdio_write in H.
    destruct (mleaf_bind_inv _ _ _ _ _ H) as (u & s1 & H1 & H2).
    pose proof (writev_loop_leaf _ _ _ _ _ _ _ H1) as ->. destruct (mleaf_ret _ _ _ _ H2) as [-> ->]. auto.
  Qed.

  Lemma file_writefn_leaf : forall f s st f' st', mleaf (file_writefn f s) st f' st' ->
    (f' = set_w true [] f \/ f' = set_w true [] (after_ioctl f)) /\ st' = st.
  Proof using rc.
    intros f s st f' st' H. unfold file_writefn in H. destruct (f_stdoutw f).
    - destruct (mleaf_bind_inv _ _ _ _ _ H) as (r & s1 & H1 & H2). destruct (mleaf_sys _ _ _ _ _ H1) as [-> _].
      destruct r; [| exfalso; exact (mleaf_unr _ _ _ H2)].
      destruct (stdio_write_leaf _ _ _ _ _ H2) as [-> ->]. auto.
    - destruct (stdio_write_leaf _ _ _ _ _ H) as [-> ->]. auto.
  Qed.

  Lemma fx_inv_after_ioctl_w : forall f0 f1, fx_inv f0 f1 -> fx_inv f0 (set_w true [] (after_ioctl f1)).
  Proof using Type.
    unfold fx_inv, after_ioctl. intros f0 f1 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10). cbn.
    repeat split; auto; intros HH; discriminate HH.
  Qed.

  Lemma fx_inv_trans : forall f0 f1 f2, fx_inv f0 f1 -> fx_inv f1 f2 -> fx_inv f0 f2.
  Proof using Type.
    unfold fx_inv. intros f0 f1 f2 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10) (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
    rewrite B1, B2, B3, B4, B5, B6, B8, A7. repeat split; auto.
  Qed.

  Lemma file_writefn_leaf_fx : forall f0 f s st f' st', fx_inv f0 f -> mleaf (file_writefn f s) st f' st' -> fx_inv f0 f' /\ st' = st.
  Proof using rc.
    intros f0 f s st f' st' FX H. destruct (file_writefn_leaf _ _ _ _ _ H) as [[-> | ->] ->].
    - split; [apply fx_inv_set_w; exact FX| reflexivity].
    - split; [apply fx_inv_after_ioctl_w; exact FX| reflexivity].
  Qed.

  Lemma fwritex_leaf : forall f s st f' st', mleaf (fwritex f s) st f' st' -> fx_inv f f' /\ st' = st.
  Proof using rc.
    intros f s st f' st' H. unfold fwritex in H.
    destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2). destruct (ensure_w_leaf _ _ _ _ H1) as [FX ->].
    destruct (f_bufsize f1 - zlength (f_wbuf f1) <? zlength s).
    - exact (file_writefn_leaf_fx _ _ _ _ _ _ FX H2).
    - destruct (f_lbf_nl f1).
      + destruct (mleaf_bind_inv _ _ _ _ _ H2) as (f2 & s2 & H3 & H4).
        assert (FX2 : fx_inv f f2 /\ s2 = st).
        { destruct (0 <? after_last_nl s); [exact (file_writefn_leaf_fx _ _ _ _ _ _ FX H3)|].
          destruct (mleaf_ret _ _ _ _ H3) as [-> ->]. auto. }
        destruct FX2 as [FX2 ->]. destruct (mleaf_ret _ _ _ _ H4) as [-> ->]. split; [apply fx_inv_set_w; exact FX2| reflexivity].
      + destruct (mleaf_ret _ _ _ _ H2) as [-> ->]. split; [apply fx_inv_set_w; exact FX| reflexivity].
  Qed.

  Lemma out_pieces_leaf : forall ps f st f' st', mleaf (out_pieces f ps) st f' st' -> (f' = f \/ fx_inv f f') /\ st' = st.
  Proof using rc.
    induction ps as [|p ps IH]; intros f st f' st' H; cbn [out_pieces] in H.
    - destruct (mleaf_ret _ _ _ _ H) as [-> ->]. auto.
    - destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2). destruct (fwritex_leaf _ _ _ _ _ H1) as [FX ->].
      destruct (IH _ _ _ _ H2) as [[-> | FX2] ->]; (split; [right | reflexivity]); [exact FX | exact (fx_inv_trans _ _ _ FX FX2)].
  Qed.

  (* [comment removed for export] *)
  Lemma vfprintf_leaf_buffered : forall f ps st f' st', f_bufsize f <> 0 ->
    mleaf (vfprintf f ps) st f' st' -> fx_inv f f' /\ st' = st.
  Proof using rc.
    intros f ps st f' st' BS H. unfold vfprintf in H. destruct (Z.eqb_spec (f_bufsize f) 0); [lia|].
    destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2). destruct (ensure_w_leaf _ _ _ _ H1) as [FX ->].
    destruct (out_pieces_leaf _ _ _ _ _ H2) as [[-> | FX2] ->]; split; auto. exact (fx_inv_trans _ _ _ FX FX2).
  Qed.

  (* [comment removed for export] *)
  Definition wl_rel (f f' : file_st) : Prop :=
    (f_stdoutw f' = f_stdoutw f /\ f_lbf_nl f' = f_lbf_nl f) \/ (f_stdoutw f' = false /\ f_lbf_nl f' = false).
  Lemma wl_rel_refl : forall f, wl_rel f f.
  Proof using Type. intros f. left. auto. Qed.
  Lemma wl_rel_trans : forall f0 f1 f2, wl_rel f0 f1 -> wl_rel f1 f2 -> wl_rel f0 f2.
  Proof using Type.
    unfold wl_rel. intros f0 f1 f2 [[A1 A2]|[A1 A2]] [[B1 B2]|[B1 B2]].
    - left. split; congruence. - right. auto. - right. split; congruence. - right. auto.
  Qed.
  Lemma wl_rel_set_w : forall f0 f1 a w, wl_rel f0 f1 -> wl_rel f0 (set_w a w f1).
  Proof using Type. intros f0 f1 a w R. unfold wl_rel in *. cbn. exact R. Qed.
  Lemma file_writefn_leaf_wl : forall f0 f s st f' st', wl_rel f0 f -> mleaf (file_writefn f s) st f' st' -> wl_rel f0 f'.
  Proof using rc.
    intros f0 f s st f' st' R H. destruct (file_writefn_leaf _ _ _ _ _ H) as [[-> | ->] _].
    - apply wl_rel_set_w. exact R.
    - unfold wl_rel. cbn. right. auto.
  Qed.
  Lemma ensure_w_leaf_wl : forall f st f' st', mleaf (ensure_w f) st f' st' -> wl_rel f f'.
  Proof using rc.
    intros f st f' st' H. unfold ensure_w in H. destruct (f_wactive f) eqn:E.
    - destruct (mleaf_ret _ _ _ _ H) as [-> ->]. apply wl_rel_refl.
    - destruct (towrite_leaf _ _ _ _ H) as (NW & -> & ->). unfold wl_rel. cbn. left. auto.
  Qed.
  Lemma fwritex_leaf_wl : forall f s st f' st', mleaf (fwritex f s) st f' st' -> wl_rel f f'.
  Proof using rc.
    intros f s st f' st' H. unfold fwritex in H.
    destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2). pose proof (ensure_w_leaf_wl _ _ _ _ H1) as R1.
    destruct (ensure_w_leaf _ _ _ _ H1) as [_ ->].
    destruct (f_bufsize f1 - zlength (f_wbuf f1) <? zlength s).
    - exact (file_writefn_leaf_wl _ _ _ _ _ _ R1 H2).
    - destruct (f_lbf_nl f1).
      + destruct (mleaf_bind_inv _ _ _ _ _ H2) as (f2 & s2 & H3 & H4).
        assert (R2 : wl_rel f f2 /\ s2 = st).
        { destruct (0 <? after_last_nl s).
          - split; [exact (file_writefn_leaf_wl _ _ _ _ _ _ R1 H3)|]. exact (proj2 (file_writefn_leaf _ _ _ _ _ H3)).
          - destruct (mleaf_ret _ _ _ _ H3) as [-> ->]. auto. }
        destruct R2 as [R2 ->]. destruct (mleaf_ret _ _ _ _ H4) as [-> ->]. apply wl_rel_set_w. exact R2.
      + destruct (mleaf_ret _ _ _ _ H2) as [-> ->]. apply wl_rel_set_w. exact R1.
  Qed.
  Lemma out_pieces_leaf_wl : forall ps f st f' st', mleaf (out_pieces f ps) st f' st' -> wl_rel f f'.
  Proof using rc.
    induction ps as [|p ps IH]; intros f st f' st' H; cbn [out_pieces] in H.
    - destruct (mleaf_ret _ _ _ _ H) as [-> ->]. apply wl_rel_refl.
    - destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2).
      exact (wl_rel_trans _ _ _ (fwritex_leaf_wl _ _ _ _ _ H1) (IH _ _ _ _ H2)).
  Qed.
  Lemma vfprintf_leaf_buffered_wl : forall f ps st f' st', f_bufsize f <> 0 ->
    mleaf (vfprintf f ps) st f' st' -> wl_rel f f'.
  Proof using rc.
    intros f ps st f' st' BS H. unfold vfprintf in H. destruct (Z.eqb_spec (f_bufsize f) 0); [lia|].
    destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2).
    exact (wl_rel_trans _ _ _ (ensure_w_leaf_wl _ _ _ _ H1) (out_pieces_leaf_wl _ _ _ _ _ H2)).
  Qed.

  (* [comment removed for export] *)
  Definition ubf_rel (f f' : file_st) : Prop :=
    f_fd f' = f_fd f /\ f_chan f' = f_chan f /\ f_bufsize f' = 0 /\ f_nord f' = f_nord f /\ f_nowr f' = f_nowr f /\ f_eof f' = f_eof f
    /\ f_wactive f' = false /\ f_wbuf f' = [] /\ f_rbuf f' = []
    /\ (f_stdoutw f' = true -> f_stdoutw f = true) /\ (f_lbf_nl f' = true -> f_lbf_nl f = true).

  Lemma vfprintf_leaf_unbuffered : forall f ps st f' st', f_bufsize f = 0 ->
    mleaf (vfprintf f ps) st f' st' -> ubf_rel f f' /\ st' = st.
  Proof using rc.
    intros f ps st f' st' BS H. unfold vfprintf in H. rewrite BS in H. change (0 =? 0) with true in H. cbv iota in H.
    destruct (mleaf_bind_inv _ _ _ _ _ H) as (f1 & s1 & H1 & H2). destruct (towrite_leaf _ _ _ _ H1) as (NW & -> & ->).
    destruct (mleaf_bind_inv _ _ _ _ _ H2) as (f2 & s2 & H3 & H4).
    destruct (mleaf_bind_inv _ _ _ _ _ H4) as (f3 & s3 & H5 & H6).
    destruct (mleaf_ret _ _ _ _ H6) as [-> ->].
    assert (FX1 : fx_inv f (set_w true [] (set_rbuf [] (set_w false [] (set_bufsize INTERNAL_BUFSIZ f)))) \/ True) by (right; exact I).
    set (g := set_w true [] (set_rbuf [] (set_w false [] (set_bufsize INTERNAL_BUFSIZ f)))) in *.
    assert (G2 : f2 = g \/ fx_inv g f2) by (destruct (out_pieces_leaf _ _ _ _ _ H3) as [X _]; exact X).
    assert (S2 : s2 = st) by (destruct (out_pieces_leaf _ _ _ _ _ H3) as [_ X]; exact X). subst s2.
    destruct (file_writefn_leaf _ _ _ _ _ H5) as [F3 ->]. split; [| reflexivity].
    assert (K2 : f_fd f2 = f_fd f /\ f_chan f2 = f_chan f /\ f_nord f2 = f_nord f /\ f_nowr f2 = f_nowr f /\ f_eof f2 = f_eof f
                 /\ (f_stdoutw f2 = true -> f_stdoutw f = true) /\ (f_lbf_nl f2 = true -> f_lbf_nl f = true) /\ f_rbuf f2 = []).
    { destruct G2 as [-> | (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10)]; [subst g; cbn; repeat split; auto|].
      subst g. cbn in *. repeat split; auto. }
    destruct K2 as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8).
    unfold ubf_rel. destruct F3 as [-> | ->]; cbn; repeat split; cbn; auto; try congruence; try (intros HH; discriminate HH).
  Qed.
End Crawl.

End CANSEC1.
End TwB.
