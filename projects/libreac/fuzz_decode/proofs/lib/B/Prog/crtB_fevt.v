(* crtB_fevt: LeafCgKit.v:101 bridge_evtF_stmt PROVED at cgif's world, w_H and SRr of decode's image B
   (decodesegsB0, lib/A/DecodeTFIB.v:27, which is rsegs of lib/B/Img0.v:3 by its module path), so the
   check_round_trip walk (lib/B/Prog/crtB_walk.v) takes no kit hypothesis.
   The proof is the image-neutral kit lib/Lib/CrtFevt.v (crt_fevt_SRr_mstepsF; that file is this file's own generic
   half, which image A's lane renamed and made neutral: taken by path from
   a working branch 2f75616c444), at decodesegsB0; only the wx_segs_nowrap fact of the
   image (crtB_wx) is image-specific.  Twin of lib/A/Prog/crtA_fevt.v. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YM05 YK04 YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import CrtFevt.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require LeafCgKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.

(* decodesegsB0 has no writable-and-executable segment that wraps (YK04.v:40). *)
Lemma crtB_wx : wx_segs_nowrap decodesegsB0.
Proof.
  intros seg Hin Hx.
  assert (Hall : forallb (fun s => negb (seg_executable s && seg_writable s) ||
                         (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 2 ^ 64)%Z) decodesegsB0 = true)
    by (clear; vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) Hall seg Hin) as Hs. cbv beta in Hs.
  rewrite Hx in Hs. cbn [negb orb] in Hs. apply Z.leb_le in Hs. exact Hs.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* lib/Lib/CrtFevt.v crt_fevt_SRr_mstepsF at decodesegsB0. *)
Theorem crtB_SRr_mstepsF : forall (W : world decodesegsB0) ms ms' model RNG (Q : world decodesegsB0 -> config -> Prop),
  ExecF.mstepsF decodesegsB0 RNG ms ms' ->
  crt_fevt_fp_avoids (w_H W) RNG ->
  (forall model', same_but_materialized model model' -> SRr decodesegsB0 W (mkCfg ms' model') Q) ->
  SRr decodesegsB0 W (mkCfg ms model) Q.
Proof. exact (crt_fevt_SRr_mstepsF decodesegsB0 crtB_wx). Qed.

(* LeafCgKit.v:101 at the concrete world / w_H / SRr of decodesegsB0: the form of crtA_walk.v's `Hypothesis BRIDGE`.
   The run is over rsegs, which is decodesegsB0 (both AsanUbsan.M.loaded_segments); LeafCgKit.fp_avoids is
   crt_fevt_fp_avoids (LeafCgKit.v:35-39 copy YK04.v:44-47). *)
Theorem crtB_bridge_holds :
  LeafCgKit.bridge_evtF_stmt (world decodesegsB0) (@w_H decodesegsB0) (SRr decodesegsB0) same_but_materialized.
Proof.
  unfold LeafCgKit.bridge_evtF_stmt.
  intros W ms model RNG P Q (ms' & Hrun & HP) Hfp Hk.
  exact (crtB_SRr_mstepsF W ms ms' model RNG Q Hrun Hfp (fun model' Hs => Hk ms' model' HP Hs)).
Qed.
End a.
