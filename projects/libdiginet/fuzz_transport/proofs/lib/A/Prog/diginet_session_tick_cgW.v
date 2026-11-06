(* diginet_session_tick_cgW: Theorem transport_diginet_session_tick_cg_holds : the statement
   transport_diginet_session_tick_cg_holds_stmt of lib/A/Prog/diginet_session_tick_cg.v, the machine walk of
   diginet_session_tick on fuzz_transport.asan at 0x892b8 (3128 bytes), a G-form caller-journal walk with a class-5
   side-stack frame of its own, released by a call of __asan_stack_free_5. It composes the ten pieces at the cuts of
   lib/A/Prog/TickCut.v (tick_holds_of): the head (entry, the stack malloc, the frame's shadow, the set_shadow_f8 call,
   the state dispatch; TickHead.v), the wake and online lost arms (memset and the indirect call of notice; TickWake.v,
   TickOnline.v), the ack-timeout step (TickStep.v), the retransmit (the indirect call of io_send; TickRetx.v), the
   ack-lost arm (memset and notice; TickAckl.v), the keepalive / queue tests (TickTail.v), the keepalive (send_data;
   TickKa.v), the queue (set_shadow_00, take, send_data, set_shadow_f8; TickQueue.v) and the epilogue (the stack free
   and the return; TickEpi.v). The pieces are loaded with Require only: the theorem TickTail.tick_tail would hide the
   model function diginet_session_tick_cg.tick_tail. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TickCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require
  TickHead TickWake TickOnline TickStep TickRetx TickAckl TickTail TickKa TickQueue TickEpi.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Theorem transport_diginet_session_tick_cg_holds : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT,
  @transport_diginet_session_tick_cg_holds_stmt fx rc B MT.
Proof.
  intros fx rc B MT.
  exact (@TickCut.tick_holds_of fx rc B MT
           (@TickHead.tick_head fx rc B MT) (@TickWake.tick_wake fx rc B MT) (@TickOnline.tick_online fx rc B MT)
           (@TickStep.tick_step fx rc B MT) (@TickRetx.tick_retx fx rc B MT) (@TickAckl.tick_ackl fx rc B MT)
           (@TickTail.tick_tail fx rc B MT) (@TickKa.tick_ka fx rc B MT) (@TickQueue.tick_queue fx rc B MT)
           (@TickEpi.tick_epi fx rc B MT)).
Qed.

Print Assumptions transport_diginet_session_tick_cg_holds.
