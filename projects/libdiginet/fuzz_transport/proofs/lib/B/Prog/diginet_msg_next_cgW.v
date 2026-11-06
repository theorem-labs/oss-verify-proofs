(* diginet_msg_next_cgW: the image-B walk of diginet_msg_next (fuzz_decode.asan-ubsan 0x82328 = dgndecb_sigma
   DDB_diginet_msg_next) proves its frozen caller-journal statement lib/B/Prog/diginet_msg_next_cg.v
   decode_diginet_msg_next_cg_holds_stmt.
   - mn_entry_holds: the footprint run of the whole function (lib/B/Prog/diginet_msg_next_segs.v mn_entry_F), from
     its pieces: the entry to the dispatch (diginet_msg_next_seg_entry.v), the dispatch and the epilogue
     (diginet_msg_next_seg_body.v), the sysex arm (diginet_msg_next_seg_sys.v) and the channel arm
     (diginet_msg_next_seg_chan.v). Inside those runs every UBSan check (the 10 branches to the `unimp` word at
     0x827c4) is shown not taken and every error-path call (36) is shown unreached.
   - decode_diginet_msg_next_cg_holds_any: the statement for every record B, from the caller-journal composition
     lib/B/Prog/diginet_msg_next_walk_lib.v mw_main at mn_entry_holds. The function calls no function, so the walk
     takes no callee statement: its premises are the statement's own (decode_cells, AR_laws, ameter_laws).
     The statement at one record (the core's TransportB) is this theorem at that record. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_msg_next_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require diginet_msg_next_segs diginet_msg_next_seg_entry
  diginet_msg_next_seg_body diginet_msg_next_seg_sys diginet_msg_next_seg_chan diginet_msg_next_walk_lib.
Open Scope Z_scope.
Module MNS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_msg_next_segs.
Module MNE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_msg_next_seg_entry.
Module MNB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_msg_next_seg_body.
Module MNY := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_msg_next_seg_sys.
Module MNC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_msg_next_seg_chan.
Module MW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_msg_next_walk_lib.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The footprint run of the whole function, from its pieces. *)
Theorem mn_entry_holds : MNS.mn_entry_F.
Proof.
  exact (MNE.mn_entry_of MNB.mn_fin_holds
           (MNB.mn_disp_of MNB.mn_fin_holds (MNY.mn_sys_of_fin MNB.mn_fin_holds) (MNC.mn_chan_of_fin MNB.mn_fin_holds))).
Qed.

(* The statement for every record B. *)
Theorem transport_diginet_msg_next_cg_holds_any :
  forall (fx : YK11.FPState) (rc : YM05.RunCeil) (B : asyms) (MT : ameter_ops),
    @transport_diginet_msg_next_cg_holds_stmt fx rc B MT.
Proof.
  intros fx rc B MT HCELLS LAWS MTL.
  unfold transport_diginet_msg_next_cg.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs c m body bb mj pos st
    HJ Hret Hra Hgp Htp H10 H11 Hal Hwlo Hwhi Hc0 Hm0 Hc8 Hm8 Hpos Hst Gc Hmj Gm Gb Hblk Hob Hfc Hfm Htc Htm Hrc Hrm
    Hoc Hom Hcm Hcb Hmb Hev.
  exact (@MW.mw_main fx rc B MT HCELLS LAWS MTL mn_entry_holds STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
           regs c m body bb mj pos st HJ Hret H10 H11 Hwlo Hwhi Hc0 Hm0 Hc8 Hm8 Hpos Hst Gc Hmj Gm Gb Hblk Hob Hfc Hfm
           Htc Htm Hrc Hrm Hoc Hom Hcm Hcb Hmb).
Qed.
