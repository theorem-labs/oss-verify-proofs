(* diginet_msg_next_walk: the frozen statement decode_diginet_msg_next_cg_holds_stmt of lib/A/Prog/diginet_msg_next_cg.v
   (fuzz_decode.asan 0x820e8), proved. The walk is lib/A/Prog/diginet_msg_next_walk_lib.v mw_main; its two footprint
   pieces are lib/A/Prog/diginet_msg_next_seg_entry.v (the entry to the __asan_memset call or the return) and the
   code after the call, composed here from lib/A/Prog/diginet_msg_next_seg_body.v (the dispatch and the epilogue),
   diginet_msg_next_seg_sys.v (body[pos] = 0xf0) and diginet_msg_next_seg_chan.v (a channel message). Every premise
   of the theorem is a premise of the statement. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_msg_next_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_msg_next_segs diginet_msg_next_walk_lib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_msg_next_seg_entry diginet_msg_next_seg_body.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_msg_next_seg_sys diginet_msg_next_seg_chan.
Module MNW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_msg_next_walk_lib.
Module MNE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_msg_next_seg_entry.
Module MNB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_msg_next_seg_body.
Module MNY := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_msg_next_seg_sys.
Module MNC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_msg_next_seg_chan.
Module MNS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_msg_next_segs.

(* The code after the memset call: the dispatch with its two pieces, each closed by the epilogue. *)
Theorem mn_body_holds : MNS.mn_body_F.
Proof.
  exact (MNB.mn_body_of (MNY.mn_sys_of_fin MNB.mn_fin_holds) (MNC.mn_chan_of_fin MNB.mn_fin_holds)).
Qed.

Theorem transport_diginet_msg_next_cg_holds : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT,
  @transport_diginet_msg_next_cg_holds_stmt fx rc B MT.
Proof.
  intros fx rc B MT HCELLS LAWS MTL AMSET.
  unfold transport_diginet_msg_next_cg.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs c m body bb mj pos st
    HJ Hret Hra4 Hgp Htp H10 H11 Hal Hwlo Hwhi Hc0 Hm0 Hpos Hst Gc Hmj Gm Gb Hblk Hob Hfc Hfm Htc Htm Hrc Hrm Hoc
    Hom Hcm Hcb Hmb Hev.
  eapply (@MNW.mw_main fx rc B MT).
  all: first [ exact MNE.mn_entry_holds | exact mn_body_holds | eassumption ].
Qed.
