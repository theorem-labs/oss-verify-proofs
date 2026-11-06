(* TickBQueue: the queue piece of diginet_session_tick's image-B walk (libdiginet/fuzz_transport,
   fuzz_transport.asan-ubsan 0x8909c), tick_queue_stmt of TickCutB.v: from the queue cut (+0x698) to the epilogue cut
   (+0x608), code +0x698 .. +0x710, +0x604 and +0x7a8 .. +0x840 (0x89734 .. 0x897ac, 0x896a0, 0x89844 .. 0x898dc). Five
   segments, each a lemma from the cut it ends at to the cut it starts at (TickBQueue_kit.v states the four inner ones):
     TickBQueue_hd.v    tq_hd_holds    tick_epi_at -> tq_body_at -> tick_queue_at  the queued test (0: s10 = 0, to the
                                                                                    epilogue cut) and the display test;
     TickBQueue_body.v  tq_body_holds  tq_tk_at -> tq_body_at                       __asan_set_shadow_00 (185 bytes),
                                                                                    the shadow byte 205 = 4, take;
     TickBQueue_tk.v    tq_tk_holds    tq_f8_at -> tq_sd_at -> tq_tk_at             the taken test (0: s10 = 0, to
                                                                                    +0x830), has_display, the two
                                                                                    display stores;
     TickBQueue_sd.v    tq_sd_holds    tq_f8_at -> tq_sd_at                         send_data, s10 = its result;
     TickBQueue_f8.v    tq_f8_holds    tick_epi_at -> tq_f8_at                      __asan_set_shadow_f8 (186 bytes),
                                                                                    to the epilogue cut.
   The set_shadow calls go through lib/A/Prog/TransportGRt.v gx_set_shadow_at; take and send_data through their bundle
   contracts (take_cg.v transport_take_cg, send_data_cg.v transport_send_data_cg) in the walk's G journal, their posts
   folded into tick_cur by TickBQueue_kit.v tq_cur_call; take_m's footprint (TickBQueue_kit.v tq_take_keep) carries the
   run invariants (1) and (4) and g_fail_next to send_data's world. Image A's template: lib/A/Prog/TickQueue.v.
   rule 24: proves no function (one piece of the walk of diginet_session_tick; the walk is composed at TickCutB.v
   tick_holds_of). *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TickCutB TickBQueue_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require
  TickBQueue_f8 TickBQueue_sd TickBQueue_tk TickBQueue_body TickBQueue_hd.

Theorem tick_queue : forall fx rc B MT, @tick_queue_stmt fx rc B MT.
Proof.
  intros fx rc B MT EPI.
  pose proof (@TickBQueue_f8.tq_f8_holds fx rc B MT EPI) as F8.
  pose proof (@TickBQueue_sd.tq_sd_holds fx rc B MT F8) as SD.
  pose proof (@TickBQueue_tk.tq_tk_holds fx rc B MT F8 SD) as TK.
  pose proof (@TickBQueue_body.tq_body_holds fx rc B MT TK) as BODY.
  exact (@TickBQueue_hd.tq_hd_holds fx rc B MT EPI BODY).
Qed.

Print Assumptions tick_queue.
