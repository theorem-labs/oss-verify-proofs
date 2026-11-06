(* diginet_session_rx_cgW: Theorem transport_diginet_session_rx_cg_holds : the statement
   transport_diginet_session_rx_cg_holds_stmt of lib/B/Prog/diginet_session_rx_cg.v, the machine walk of
   diginet_session_rx on fuzz_transport.asan-ubsan at 0x87784, a G-form caller-journal walk with a class-1 side-stack
   frame of its own. It composes the fourteen pieces at the cuts of lib/B/Prog/SrxBCut.v (srxb_holds_of): the head
   (entry .. the call of diginet_frame_parse; SrxBHead.v), parse (SrxBParse.v), the three MAC tests (SrxBMac.v), the
   desk test (SrxBDesk.v), learning the desk (SrxBLearn.v), the closed test, the two counter stores and the switch
   (SrxBSw.v), the four switch arms (SrxBAnn.v, SrxBAck.v, SrxBData.v, and SrxBLost.v, where image B inlines
   session_lost), the call of diginet_session_tick (SrxBTick.v), the ignored counter and the release (SrxBRel.v), and
   the model invariants across the learned, stored and switched worlds (SrxBInv.v). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_rx_cg SrxBCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require SrxBHead SrxBParse SrxBMac SrxBDesk SrxBLearn
  SrxBSw SrxBAnn SrxBAck SrxBData SrxBLost SrxBTick SrxBRel SrxBInv.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Theorem transport_diginet_session_rx_cg_holds : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT,
  @transport_diginet_session_rx_cg_holds_stmt fx rc B MT.
Proof.
  intros fx rc B MT.
  exact (@srxb_holds_of fx rc B MT (@SrxBHead.srxb_head_ok fx rc B MT) (@SrxBParse.srxb_parse_ok fx rc B MT)
    (@SrxBMac.srxb_mac_ok fx rc B MT) (@SrxBDesk.srxb_desk_ok fx rc B MT) (@SrxBLearn.srxb_learn_ok fx rc B MT)
    (@SrxBSw.srxb_sw_ok fx rc B MT) (@SrxBAnn.srxb_ann_ok fx rc B MT) (@SrxBAck.srxb_ack_ok fx rc B MT)
    (@SrxBData.srxb_data_ok fx rc B MT) (@SrxBLost.srxb_lost_ok fx rc B MT) (@SrxBTick.srxb_tick_ok fx rc B MT)
    (@SrxBRel.srxb_ign_ok fx rc B MT) (@SrxBRel.srxb_rel_ok fx rc B MT) SrxBInv.srxb_inv_ok).
Qed.
