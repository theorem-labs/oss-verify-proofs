(* diginet_session_tick_cgW (image B): Theorem transport_diginet_session_tick_cg_holds : the statement
   transport_diginet_session_tick_cg_holds_stmt of lib/B/Prog/diginet_session_tick_cg.v, the machine walk of
   diginet_session_tick on fuzz_transport.asan-ubsan at 0x8909c, a G-form caller-journal walk with a class-5
   side-stack frame of its own, released by a call of __asan_stack_free_5. It composes the eleven pieces at the cuts
   of lib/B/Prog/TickCutB.v (tick_holds_of): the head (entry, the stack malloc, the frame's shadow, the set_shadow_f8
   call, the state dispatch; TickBHead.v), the wake and online tests and stores (TickBWake.v, TickBOnline.v), the lost
   arm's call of set_state (TickBLost.v), the ack-timeout step (TickBStep.v), the retransmit (the indirect call of
   io_send; TickBRetx.v), the ack-lost arm (memset and notice; TickBAckl.v), the keepalive / queue tests
   (TickBTail.v), the keepalive (send_data; TickBKa.v), the queue (set_shadow_00, take, send_data, set_shadow_f8;
   TickBQueue.v) and the epilogue (the stack free and the return; TickBEpi.v). The pieces are loaded with Require
   only: the theorem TickBTail.tick_tail would hide the model function diginet_session_tick_cg.tick_tail. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require TickCutB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require
  TickBHead TickBWake TickBOnline TickBLost TickBStep TickBRetx TickBAckl TickBTail TickBKa TickBQueue TickBEpi.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Theorem transport_diginet_session_tick_cg_holds : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT,
  @transport_diginet_session_tick_cg_holds_stmt fx rc B MT.
Proof.
  intros fx rc B MT.
  exact (@TickCutB.tick_holds_of fx rc B MT
           (@TickBHead.tick_head fx rc B MT) (@TickBWake.tick_wake fx rc B MT) (@TickBOnline.tick_online fx rc B MT)
           (@TickBLost.tick_lost fx rc B MT) (@TickBStep.tick_step fx rc B MT) (@TickBRetx.tick_retx fx rc B MT)
           (@TickBAckl.tick_ackl fx rc B MT) (@TickBTail.tick_tail fx rc B MT) (@TickBKa.tick_ka fx rc B MT)
           (@TickBQueue.tick_queue fx rc B MT) (@TickBEpi.tick_epi fx rc B MT)).
Qed.

Print Assumptions transport_diginet_session_tick_cg_holds.
