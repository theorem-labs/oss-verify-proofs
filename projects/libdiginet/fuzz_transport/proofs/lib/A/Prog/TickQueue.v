(* TickQueue: the queue piece of diginet_session_tick's image-A walk (libdiginet/fuzz_transport, fuzz_transport.asan
   0x892b8), tick_queue_stmt of TickCut.v: from the queue cut (+0x85c) to the epilogue cut (+0x7cc), code +0x85c ..
   +0x8d4, +0x7c8 and +0x96c .. +0xa08 (0x89b14 .. 0x89b8c, 0x89a80, 0x89c24 .. 0x89cc0). Five segments, each a
   lemma from the cut it ends at to the cut it starts at (TickQueue_kit.v states the four inner ones):
     TickQueue_hd.v    tq_hd_holds    tick_epi_at -> tq_body_at -> tick_queue_at   the queued test (0: s10 = 0, to the
                                                                                    epilogue cut) and the display test;
     TickQueue_body.v  tq_body_holds  tq_tk_at -> tq_body_at                        __asan_set_shadow_00 (185 bytes),
                                                                                    the shadow byte 233 = 4, take;
     TickQueue_tk.v    tq_tk_holds    tq_f8_at -> tq_sd_at -> tq_tk_at              the taken test (0: s10 = 0, to
                                                                                    +0x9fc), has_display, the two
                                                                                    display stores;
     TickQueue_sd.v    tq_sd_holds    tq_f8_at -> tq_sd_at                          send_data, s10 = its result;
     TickQueue_f8.v    tq_f8_holds    tick_epi_at -> tq_f8_at                       __asan_set_shadow_f8 (186 bytes),
                                                                                    to the epilogue cut.
   The set_shadow calls go through TransportGRt.v gx_set_shadow_at; take and send_data through their bundle contracts
   (take_cg.v transport_take_cg, send_data_cg.v transport_send_data_cg) in the walk's G journal, their posts folded
   into tick_cur by TickQueue_kit.v tq_cur_call; take_m's footprint (TickQueue_kit.v tq_take_keep) carries the run
   invariants (1) and (4) and g_fail_next to send_data's world. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TickCut TickQueue_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require
  TickQueue_f8 TickQueue_sd TickQueue_tk TickQueue_body TickQueue_hd.

Theorem tick_queue : forall fx rc B MT, @tick_queue_stmt fx rc B MT.
Proof.
  intros fx rc B MT EPI.
  pose proof (@TickQueue_f8.tq_f8_holds fx rc B MT EPI) as F8.
  pose proof (@TickQueue_sd.tq_sd_holds fx rc B MT F8) as SD.
  pose proof (@TickQueue_tk.tq_tk_holds fx rc B MT F8 SD) as TK.
  pose proof (@TickQueue_body.tq_body_holds fx rc B MT TK) as BODY.
  exact (@TickQueue_hd.tq_hd_holds fx rc B MT EPI BODY).
Qed.

Print Assumptions tick_queue.
