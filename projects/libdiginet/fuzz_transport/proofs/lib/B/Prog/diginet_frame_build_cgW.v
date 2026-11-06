(* diginet_frame_build_cgW: the image-B statement transport_diginet_frame_build_cg_holds_stmt
   (lib/B/Prog/diginet_frame_build_cg.v) for libdiginet/fuzz_transport's diginet_frame_build (fuzz_transport.asan-ubsan
   0x8b818 = transportb_sigma TB_diginet_frame_build), for every record B.

   The walk is lib/B/Prog/diginet_frame_build_walk.v fb_cg_holds_of_segs, in the G form: it runs in the caller's
   journal ajournal_gx G_HARNESS_B 0 [] and cuts diginet_body_check by TransportGCg.v gx_call_cg, the leaf
   diginet_sum16 by gx_call_leaf, and __asan_memcpy / __asan_memset by gx_intrin_at. It takes the eighteen footprint
   segments of lib/B/Prog/diginet_frame_build_iface.v as hypotheses; they are proved in
   lib/B/Prog/diginet_frame_build_seg_{a,b,h1,h2a,h2b}.v. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_build_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require diginet_frame_build_walk.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require diginet_frame_build_seg_a
  diginet_frame_build_seg_b diginet_frame_build_seg_h1 diginet_frame_build_seg_h2a diginet_frame_build_seg_h2b.
Module SA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_frame_build_seg_a.
Module SB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_frame_build_seg_b.
Module SH1 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_frame_build_seg_h1.
Module SH2A := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_frame_build_seg_h2a.
Module SH2B := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_frame_build_seg_h2b.
Module FBW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_frame_build_walk.

Theorem transport_diginet_frame_build_cg_holds : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT,
  @transport_diginet_frame_build_cg_holds_stmt fx rc B MT.
Proof.
  intros fx rc B MT.
  exact (@FBW.fb_cg_holds_of_segs
           SA.fb_seg1_F SA.fb_seg1L_F SA.fb_seg1M_F SA.fb_seg2R_F SA.fb_seg2S_F SA.fb_seg2C_F SA.fb_seg3_F
           SH1.fb_h1_F SB.fb_sumZ_F SB.fb_sumC_F SB.fb_sumR_F SH2A.fb_h2a_F SH2B.fb_h2b_F
           SB.fb_seg4Z_F SB.fb_seg4_F SB.fb_seg5Z_F SB.fb_seg5_F SB.fb_epi_F fx rc B MT).
Qed.
