(* receive_cgW: the image-B ASan walk of receive (fuzz_transport.asan-ubsan 41113a03c82f at 0x836a8 = transportb_sigma
   TB_receive, 404 bytes), proved against the statement lib/B/Prog/receive_cg.v. The walk is cut into seven code
   pieces at the six pcs of lib/B/Prog/receive_seg_cut.v (+0x038, +0x054, +0x098, +0x0b8, +0x12c, +0x158), one call
   piece (spec_read_frame, called twice) and one model piece; each piece is a file of its own:
     lib/B/Prog/receive_seg_head.v  recv_head : recv_head_stmt  (the entry .. +0x034: the prologue, the malloc)
     lib/B/Prog/receive_seg_cpy.v   recv_cpy  : recv_cpy_stmt   (+0x038 .. +0x050: the memcpy into the new block)
     lib/B/Prog/receive_seg_opb.v   recv_opb  : recv_opb_stmt   (+0x054 .. +0x094: op_begin's memsets and stores)
     lib/B/Prog/receive_seg_rf.v    recv_rf   : recv_rf_stmt    (+0x098 .. +0x0b4: spec_read_frame, the send store)
     lib/B/Prog/receive_seg_poll.v  recv_poll : recv_poll_stmt  (+0x0b8 .. +0x128: the by-poll path)
     lib/B/Prog/receive_seg_mrx.v   recv_mrx  : recv_mrx_stmt   (+0x12c .. +0x154: m_rx, diginet_session_rx)
     lib/B/Prog/receive_seg_set.v   recv_set  : recv_set_stmt   (+0x158 .. +0x184: settle, the free, the epilogue)
     lib/B/Prog/receive_seg_srf.v   recv_srf  : recv_srf_stmt   (the call of spec_read_frame from receive's frame)
     lib/B/Prog/receive_seg_inv.v   recv_inv  : recv_inv_stmt   (the run invariants at the callees' worlds)
   and the allocator calls are lib/A/Prog/receive_seg_alloc.v's (image-free). This file is the composition: the cut
   file's recv_holds_of applied to the nine, then recv_top. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import receive_cg receive_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
receive_seg_head receive_seg_cpy receive_seg_opb receive_seg_rf receive_seg_poll receive_seg_mrx receive_seg_set
receive_seg_srf receive_seg_inv.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.

(* The statement of lib/B/Prog/receive_cg.v. *)
Theorem transport_receive_cg_holds :
  forall fx rc B MT CTX, @transport_receive_cg_holds_stmt fx rc B MT CTX.
Proof.
  intros fx rc B MT CTX.
  exact (@recv_top fx rc B MT
           (@recv_holds_of fx rc B MT (@recv_head fx rc B MT) (@recv_cpy fx rc B MT) (@recv_opb fx rc B MT)
              (@recv_rf fx rc B MT) (@recv_poll fx rc B MT) (@recv_mrx fx rc B MT) (@recv_set fx rc B MT)
              (@recv_srf fx rc B MT) recv_inv)
           CTX).
Qed.

Print Assumptions transport_receive_cg_holds.
