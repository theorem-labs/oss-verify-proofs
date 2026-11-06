(* build_and_receive_cgW: Theorem transport_build_and_receive_cg_holds : the statement
   transport_build_and_receive_cg_holds_stmt of lib/A/Prog/build_and_receive_cg.v, the machine walk of
   build_and_receive on fuzz_transport.asan at 0x857e0 (804 bytes), a G-form caller-journal walk with a class-5
   side-stack frame of its own that hands the frame it builds to receive.

   The walk is in these files:
   - lib/A/Prog/build_and_receive_segs.v: the context, the three cuts (mid +0x178, call +0x22c, rel +0x2ac), the
     piece statements and their composition bar_walk;
   - lib/A/Prog/build_and_receive_seg_head.v: the entry .. +0x178 (the frame, the saves, the realign, the class-5
     stack malloc, the frame's header and shadow bytes, the two __asan_set_shadow calls);
   - lib/A/Prog/build_and_receive_seg_mid.v: +0x178 .. +0x22c (s8 = max (len, 30), the two MAC memcpys, the
     memset, the four length stores and the body sum loop);
   - lib/A/Prog/build_and_receive_seg_call.v: +0x22c .. +0x2a8 (the fourteen header stores, the body memcpy and
     the call of receive);
   - lib/A/Prog/build_and_receive_seg_rel.v: +0x2ac .. the return (the shadow fill, the header word, the call of
     __asan_stack_free_5 and the epilogue).
   Here they are put together at the statement's values: the record facts and the callee contracts become bar_rt
   (with gx_ok and gx_noerrno read off trans_g_unowned and trans_g_no_errno by DgnTransportCg.v G_HARNESS_gx_ok
   and G_HARNESS_gx_noerrno), and the contract's 53 premises become bar_ok at the context the entry fixes. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportRtCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import send_data_cg on_announce_cg on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_poll_cg receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import build_and_receive_cg build_and_receive_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  build_and_receive_seg_head build_and_receive_seg_mid build_and_receive_seg_call build_and_receive_seg_rel.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Section bar_holds. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.

Lemma bar_holds : forall CTX, @transport_build_and_receive_cg_holds_stmt fx rc B MT CTX.
Proof.
  intros CTX.
  intros HPCS HCELLS HGU HGE HRU HRE LAWS MTL MTF SMP FFL ASM AF8 A00 AICPY AISET RECVC ASF.
  unfold transport_build_and_receive_cg.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
    dstp srcp bodyp send ack retry cmd T dst src body Bw ch.
  intros HJ Hret Hra4 Hgp Htp H10 H11 H12 H13 H14 H15 H16 H17 HCH HIN Hsp16 Hlo Hhi
    HSEND HACK HRETRY HCMD HLD HGD HSD HWD HLS HGS HSS HWS HGB HSB HTW HFN HMOD HROM
    I1 I2 IQ I4 IN I5a I5b HDN C5 C1 C4 C0 C2 HEV HLIVE HMOK HCOST.
  set (c := mkBAR STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
                  dstp srcp bodyp send ack retry cmd T dst src body Bw ch CTX).
  assert (HRT : bar_rt B MT CTX).
  { exact (conj HPCS (conj HCELLS (conj HGU (conj HGE (conj HRU (conj HRE (conj LAWS (conj MTL (conj MTF (conj SMP (conj
      FFL (conj (G_HARNESS_gx_ok B HGU) (conj (G_HARNESS_gx_noerrno B HGE) (conj ASM (conj AF8 (conj A00 (conj AICPY
      (conj AISET (conj RECVC ASF))))))))))))))))))). }
  assert (HCOSTn : recv_cost MT (bar_nn body) <= T).
  { rewrite <- (bar_frame_len dst src send ack retry cmd body HLD HLS). exact HCOST. }
  assert (HOK : bar_ok B MT c).
  { exact (conj HJ (conj Hret (conj Hra4 (conj Hgp (conj Htp (conj H10 (conj H11 (conj H12 (conj H13 (conj H14 (conj H15
      (conj H16 (conj H17 (conj HCH (conj HIN (conj Hsp16 (conj Hlo (conj Hhi (conj HSEND (conj HACK (conj HRETRY
      (conj HCMD (conj HLD (conj HGD (conj HSD (conj HWD (conj HLS (conj HGS (conj HSS (conj HWS (conj HGB (conj HSB
      (conj HTW (conj HFN (conj HMOD (conj HROM (conj I1 (conj I2 (conj IQ (conj I4 (conj IN (conj I5a (conj I5b
      (conj HDN (conj C5 (conj C1 (conj C4 (conj C0 (conj C2 (conj HEV (conj HLIVE (conj HMOK
      HCOSTn)))))))))))))))))))))))))))))))))))))))))))))))))))). }
  exact (bar_walk B MT (bar_head_piece fx rc B MT) (bar_mid_piece fx rc B MT) (bar_call_piece fx rc B MT)
           (bar_rel_piece fx rc B MT) c HRT HOK).
Qed.

End bar_holds.

(* The statement of lib/A/Prog/build_and_receive_cg.v. *)
Theorem transport_build_and_receive_cg_holds :
  forall fx rc B MT CTX, @transport_build_and_receive_cg_holds_stmt fx rc B MT CTX.
Proof. intros fx rc B MT CTX. exact (@bar_holds fx rc B MT CTX). Qed.

Print Assumptions transport_build_and_receive_cg_holds.
