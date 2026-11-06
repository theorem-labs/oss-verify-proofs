(* diginet_session_close_cgW: Theorem transport_diginet_session_close_cg_holds : the statement
   transport_diginet_session_close_cg_holds_stmt of lib/B/Prog/diginet_session_close_cg.v, the machine walk of
   diginet_session_close on fuzz_transport.asan-ubsan at 0x87648 (316 bytes), a G-form caller-journal walk with no
   side-stack frame of its own and two G-form program callees (send_control, set_state). It composes the three pieces
   at the cuts of lib/B/Prog/diginet_session_close_segs.v (close_holds_of): the head (entry .. +0x88, the frame, the
   four saves and the three tests of :153; diginet_session_close_seg_head.v), the send (+0xd8 .. +0xf4, the call of
   send_control; diginet_session_close_seg_send.v) and the join (+0x8c .. the return: g_s.inflight := 0, the call of
   set_state and the epilogue; diginet_session_close_seg_join.v). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
diginet_session_close_cg diginet_session_close_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require
diginet_session_close_seg_head diginet_session_close_seg_send diginet_session_close_seg_join.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module CHead := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_close_seg_head.
Module CSend := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_close_seg_send.
Module CJoin := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_close_seg_join.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Theorem transport_diginet_session_close_cg_holds : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT,
  @transport_diginet_session_close_cg_holds_stmt fx rc B MT.
Proof.
  intros fx rc B MT.
  exact (@close_holds_of fx rc B MT (@CHead.close_head fx rc B MT) (@CSend.close_send fx rc B MT)
           (@CJoin.close_join fx rc B MT)).
Qed.
