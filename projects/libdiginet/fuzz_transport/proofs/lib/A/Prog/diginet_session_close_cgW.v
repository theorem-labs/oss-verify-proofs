(* diginet_session_close_cgW: Theorem transport_diginet_session_close_cg_holds : the statement
   transport_diginet_session_close_cg_holds_stmt of lib/A/Prog/diginet_session_close_cg.v, the machine walk of
   diginet_session_close on fuzz_transport.asan at 0x8713c (1112 bytes), a G-form caller-journal walk with a class-2
   side-stack frame of its own, a G-form program callee (send_control) and an indirect call of notice. It composes
   the five pieces at the cuts of lib/A/Prog/diginet_session_close_segs.v (close_holds_of): the head (entry ..
   +0x188, the stack malloc through lib/A/Prog/TransportGFrame.v gx_stack_malloc_at and the three tests of :153;
   diginet_session_close_seg_head.v), the send (+0x3c4 .. +0x3e0, the call of send_control;
   diginet_session_close_seg_send.v), the join (+0x18c .. +0x1bc, g_s.inflight := 0 and the state test;
   diginet_session_close_seg_join.v), the notice (+0x1c0 .. +0x288, __asan_memset and the indirect call;
   diginet_session_close_seg_ntc.v) and the release (+0x290 .. the return, the frame's flag byte through
   gx_flag_store_pi; diginet_session_close_seg_rel.v). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
diginet_session_close_cg diginet_session_close_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require
diginet_session_close_seg_head diginet_session_close_seg_send diginet_session_close_seg_join
diginet_session_close_seg_ntc diginet_session_close_seg_rel.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module CHead := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_close_seg_head.
Module CSend := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_close_seg_send.
Module CJoin := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_close_seg_join.
Module CNtc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_close_seg_ntc.
Module CRel := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_close_seg_rel.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Theorem transport_diginet_session_close_cg_holds : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT,
  @transport_diginet_session_close_cg_holds_stmt fx rc B MT.
Proof.
  intros fx rc B MT.
  exact (@close_holds_of fx rc B MT (@CHead.close_head fx rc B MT) (@CSend.close_send fx rc B MT)
           (@CJoin.close_join fx rc B MT) (@CNtc.close_ntc fx rc B MT) (@CRel.close_rel fx rc B MT)).
Qed.
