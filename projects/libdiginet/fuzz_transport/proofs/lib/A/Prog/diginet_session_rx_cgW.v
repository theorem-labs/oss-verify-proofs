(* diginet_session_rx_cgW: Theorem transport_diginet_session_rx_cg_holds : the statement
   transport_diginet_session_rx_cg_holds_stmt of lib/A/Prog/diginet_session_rx_cg.v, the machine walk of
   diginet_session_rx on fuzz_transport.asan at 0x87594, a G-form caller-journal walk with a class-1 side-stack frame
   of its own. It composes the fourteen pieces at the cuts of lib/A/Prog/SrxCut.v (srx_holds_of): the head (entry ..
   the call of diginet_frame_parse; SrxHead.v), parse (SrxParse.v), the three MAC tests (SrxMac.v), the desk test
   (SrxDesk.v), learning the desk (SrxLearn.v), the closed test, the two counter stores and the switch (SrxSw.v), the
   four switch arms (SrxAnn.v, SrxAck.v, SrxData.v, SrxLost.v), the call of diginet_session_tick (SrxTick.v), the
   ignored counter and the release (SrxRel.v), and the model invariants across the learned, stored and switched worlds
   (SrxInv.v). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_rx_cg SrxCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require SrxHead SrxParse SrxMac SrxDesk SrxLearn SrxSw
  SrxAnn SrxAck SrxData SrxLost SrxTick SrxRel SrxInv.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Theorem transport_diginet_session_rx_cg_holds : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT,
  @transport_diginet_session_rx_cg_holds_stmt fx rc B MT.
Proof.
  intros fx rc B MT.
  exact (@srx_holds_of fx rc B MT (@SrxHead.srx_head_ok fx rc B MT) (@SrxParse.srx_parse_ok fx rc B MT)
    (@SrxMac.srx_mac_ok fx rc B MT) (@SrxDesk.srx_desk_ok fx rc B MT) (@SrxLearn.srx_learn_ok fx rc B MT)
    (@SrxSw.srx_sw_ok fx rc B MT) (@SrxAnn.srx_ann_ok fx rc B MT) (@SrxAck.srx_ack_ok fx rc B MT)
    (@SrxData.srx_data_ok fx rc B MT) (@SrxLost.srx_lost_ok fx rc B MT) (@SrxTick.srx_tick_ok fx rc B MT)
    (@SrxRel.srx_ign_ok fx rc B MT) (@SrxRel.srx_rel_ok fx rc B MT) SrxInv.srx_inv_ok).
Qed.
