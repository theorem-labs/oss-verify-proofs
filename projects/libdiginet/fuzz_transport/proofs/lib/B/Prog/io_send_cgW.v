(* io_send_cgW: Theorem transport_io_send_cg_holds : the statement transport_io_send_cg_holds_stmt of
   lib/B/Prog/io_send_cg.v, the machine walk of io_send (fuzz/fuzz_transport.c:823-899) on fuzz_transport.asan-ubsan
   (41113a03c82f) at 0x82ffc = TImgB.v ti_io_send timg_B (876 bytes, frame 160; spec_read_frame and tagged_of are
   CALLED on this image).

   The walk is a G-form caller-journal walk (lib/A/W_journalG.v ajournal_gx G_HARNESS_B 0 [] from the entry to the
   return), cut at the points of lib/B/Prog/io_send_seg_cut.v into thirteen segments, each a statement of that file
   proved in its own file:
     io_send_seg_entry.v  ios_entry     entry .. IOS_SRF: prologue, g_fail_next = 0, spec_read_frame (G form);
     io_send_seg_csf.v    ios_csf_seg   IOS_SRF .. IOS_CSF: check_sent_frame (donor form);
     io_send_seg_ack.v    ios_ack_seg   the dispatch on f.cmd, the ACK and E3 arms (their overflow branches to the
                                        trap word refuted by the model), to the epilogue; E2 / DATA on;
     io_send_seg_e2.v     ios_e2_head, ios_e2_test   f.retry, then f.cmd against 0xe2;
     io_send_seg_rty.v    ios_rty_arm   the retry arm (check_inflight_retry, M.fly.retries / .sent);
     io_send_seg_e2a.v    ios_e2_arm    the E2 arm (check_state_wake, check_latest_control, GOT.e2, g_last_counter);
     io_send_seg_data.v   iod_head      the DATA arm's head (body[0], check_inflight_new, g_raw);
     io_send_seg_loop.v   ios_loop      the command count loop (tagged_of, a leaf, once per round);
     io_send_seg_dmid.v   iod_mid       check_latest_frame and the stores of M.host_counter and g_last_counter;
     io_send_seg_tail.v   ios_tail_seg  the keepalive case, or check_latest_sent (G form) and the display;
     io_send_seg_fly.v    ios_fly_seg   the frame in flight (the stores into M.fly, __asan_memcpy);
     io_send_seg_epi.v    ios_epi       the epilogue: a0 = ios_ret Bw, the reloads, the post.
   io_send_seg_top.v ios_holds_of joins them (through io_send_seg_head.v, io_send_seg_e2w.v, io_send_seg_dpost.v and
   io_send_seg_join.v); the model side is image A's lib/A/Prog/io_send_segs.v (io_send_m reads no image:
   io_send_seg_cut.v ios_m_arm_B). *)
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_seg_cut io_send_seg_top.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require
  io_send_seg_entry io_send_seg_csf io_send_seg_ack io_send_seg_e2 io_send_seg_rty io_send_seg_e2a
  io_send_seg_data io_send_seg_loop io_send_seg_dmid io_send_seg_tail io_send_seg_fly io_send_seg_epi.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Section top. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.

Lemma ios_holds : @transport_io_send_cg_holds_stmt fx rc B MT.
Proof.
  exact (ios_holds_of B MT
           (@io_send_seg_entry.ios_entry fx rc B MT) (@io_send_seg_csf.ios_csf_seg fx rc B MT)
           (@io_send_seg_ack.ios_ack_seg fx rc B MT)
           (@io_send_seg_e2.ios_e2_head fx rc B MT) (@io_send_seg_e2.ios_e2_test fx rc B MT)
           (@io_send_seg_rty.ios_rty_arm fx rc B MT) (@io_send_seg_e2a.ios_e2_arm fx rc B MT)
           (@io_send_seg_data.iod_head fx rc B MT) (@io_send_seg_loop.ios_loop fx rc B MT)
           (@io_send_seg_dmid.iod_mid fx rc B MT) (@io_send_seg_tail.ios_tail_seg fx rc B MT)
           (@io_send_seg_fly.ios_fly_seg fx rc B MT) (@io_send_seg_epi.ios_epi fx rc B MT)).
Qed.

End top.

(* The statement of lib/B/Prog/io_send_cg.v. *)
Theorem transport_io_send_cg_holds : forall fx rc B MT, @transport_io_send_cg_holds_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@ios_holds fx rc B MT). Qed.

Print Assumptions transport_io_send_cg_holds.
