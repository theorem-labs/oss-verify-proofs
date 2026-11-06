(* receive_cgW: the image-A ASan walk of receive (fuzz_transport.asan e89be137db17 at 0x837d0 = transport_sigma
   TS_receive, 1124 bytes), proved against the statement lib/A/Prog/receive_cg.v. The walk is cut into seven code
   pieces at the six pcs of lib/A/Prog/receive_seg_cut.v (+0x048, +0x064, +0x0ac, +0x14c, +0x248, +0x274) and one model
   piece; each piece is a file of its own:
     lib/A/Prog/receive_seg_head.v  recv_head : recv_head_stmt  (the entry .. +0x044: the prologue, the malloc)
     lib/A/Prog/receive_seg_cpy.v   recv_cpy  : recv_cpy_stmt   (+0x048 .. +0x060: the memcpy into the new block)
     lib/A/Prog/receive_seg_opb.v   recv_opb  : recv_opb_stmt   (+0x064 .. +0x0a8: op_begin's memsets and stores)
     lib/A/Prog/receive_seg_rf.v    recv_rf   : recv_rf_stmt    (+0x0ac .. +0x148, +0x2a4 .. +0x31c: the frame's send)
     lib/A/Prog/receive_seg_poll.v  recv_poll : recv_poll_stmt  (+0x14c .. +0x244, +0x320 .. +0x398: the by-poll path)
     lib/A/Prog/receive_seg_mrx.v   recv_mrx  : recv_mrx_stmt   (+0x248 .. +0x270: m_rx, diginet_session_rx)
     lib/A/Prog/receive_seg_set.v   recv_set  : recv_set_stmt   (+0x274 .. +0x2a0: settle, the epilogue, the free)
     lib/A/Prog/receive_seg_inv.v   recv_inv  : recv_inv_stmt   (the run invariants at the callees' worlds)
   and the allocator calls are lib/A/Prog/receive_seg_alloc.v's. This file is the composition: the cut file's
   recv_holds_of applied to the eight, then recv_top. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import receive_cg receive_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
receive_seg_head receive_seg_cpy receive_seg_opb receive_seg_rf receive_seg_poll receive_seg_mrx receive_seg_set
receive_seg_inv.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.

(* The statement of lib/A/Prog/receive_cg.v. *)
Theorem transport_receive_cg_holds :
  forall fx rc B MT CTX, @transport_receive_cg_holds_stmt fx rc B MT CTX.
Proof.
  intros fx rc B MT CTX.
  exact (@recv_top fx rc B MT
           (@recv_holds_of fx rc B MT (@recv_head fx rc B MT) (@recv_cpy fx rc B MT) (@recv_opb fx rc B MT)
              (@recv_rf fx rc B MT) (@recv_poll fx rc B MT) (@recv_mrx fx rc B MT) (@recv_set fx rc B MT) recv_inv)
           CTX).
Qed.

Print Assumptions transport_receive_cg_holds.
