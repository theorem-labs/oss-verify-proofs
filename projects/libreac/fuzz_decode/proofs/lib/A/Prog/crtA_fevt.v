(* crtA_fevt: LeafCgKit.v:101 bridge_evtF_stmt PROVED at cgif's world, w_H and SRr of decode's image A
   (decodesegs0, lib/A/DecodeTFIB.v:19, which is rsegs of lib/A/Img0.v:3 by its module path), so the check_round_trip
   walk (lib/A/Prog/crtA_walk.v) takes no kit hypothesis: crtA_walk's `Hypothesis BRIDGE` is crtA_bridge_holds.
   The proof is the image-neutral kit lib/Lib/CrtFevt.v (crt_fevt_SRr_mstepsF, a port of image B's
   lib/B/Prog/crtB_fevt.v on a working branch at 82cbfac97a3) at decodesegs0; only the
   wx_segs_nowrap fact of the image (crtA_wx, image B's crtB_wx at decodesegs0) is image-specific. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YM05 YK04 YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import CrtFevt.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require LeafCgKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.

(* decodesegs0 has no writable-and-executable segment that wraps (YK04.v:40). *)
Lemma crtA_wx : wx_segs_nowrap decodesegs0.
Proof.
  intros seg Hin Hx.
  assert (Hall : forallb (fun s => negb (seg_executable s && seg_writable s) ||
                         (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 2 ^ 64)%Z) decodesegs0 = true)
    by (clear; vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) Hall seg Hin) as Hs. cbv beta in Hs.
  rewrite Hx in Hs. cbn [negb orb] in Hs. apply Z.leb_le in Hs. exact Hs.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* lib/Lib/CrtFevt.v crt_fevt_SRr_mstepsF at decodesegs0. *)
Theorem crtA_SRr_mstepsF : forall (W : world decodesegs0) ms ms' model RNG (Q : world decodesegs0 -> config -> Prop),
  ExecF.mstepsF decodesegs0 RNG ms ms' ->
  crt_fevt_fp_avoids (w_H W) RNG ->
  (forall model', same_but_materialized model model' -> SRr decodesegs0 W (mkCfg ms' model') Q) ->
  SRr decodesegs0 W (mkCfg ms model) Q.
Proof. exact (crt_fevt_SRr_mstepsF decodesegs0 crtA_wx). Qed.

(* LeafCgKit.v:101 at the concrete world / w_H / SRr of decodesegs0: the form of crtA_walk.v:36 `Hypothesis BRIDGE`.
   The run is over rsegs, which is decodesegs0 (both Asan.M.loaded_segments); LeafCgKit.fp_avoids is
   crt_fevt_fp_avoids (LeafCgKit.v:35-39 copy YK04.v:44-47). *)
Theorem crtA_bridge_holds :
  LeafCgKit.bridge_evtF_stmt (world decodesegs0) (@w_H decodesegs0) (SRr decodesegs0) same_but_materialized.
Proof.
  unfold LeafCgKit.bridge_evtF_stmt.
  intros W ms model RNG P Q (ms' & Hrun & HP) Hfp Hk.
  exact (crtA_SRr_mstepsF W ms ms' model RNG Q Hrun Hfp (fun model' Hs => Hk ms' model' HP Hs)).
Qed.
End a.
