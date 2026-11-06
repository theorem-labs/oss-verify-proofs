(* on_ack_cgW: the frozen statement transport_on_ack_cg_holds_stmt of lib/A/Prog/on_ack_cg.v (fuzz_transport.asan
   0x8842c = transport_sigma TS_on_ack, 1188 bytes), proved. The walk is cut in five pieces at four cut points
   (lib/A/Prog/on_ack_segs.v, which composes them in onack_holds_of):
     head  the entry .. +0x17c   lib/A/Prog/on_ack_seg_head.v  onack_head
     ntc   +0x180 .. +0x248      lib/A/Prog/on_ack_seg_ntc.v   onack_ntc_piece
     aft   +0x24c .. +0x2ac      lib/A/Prog/on_ack_seg_aft.v   onack_aft_piece
     ign   +0x2b0 .. +0x2d4      lib/A/Prog/on_ack_seg_ign.v   onack_ign_piece
     rel   +0x2d8 .. +0x404      lib/A/Prog/on_ack_seg_rel.v   onack_rel
   Every premise of the theorem is a premise of the statement. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_ack_cg on_ack_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require
  on_ack_seg_head on_ack_seg_ntc on_ack_seg_aft on_ack_seg_ign on_ack_seg_rel.
Module OAH := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.on_ack_seg_head.
Module OAN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.on_ack_seg_ntc.
Module OAA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.on_ack_seg_aft.
Module OAI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.on_ack_seg_ign.
Module OAR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.on_ack_seg_rel.

Theorem transport_on_ack_cg_holds : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT,
  @transport_on_ack_cg_holds_stmt fx rc B MT.
Proof.
  intros fx rc B MT.
  exact (@onack_holds_of fx rc B MT
           (@OAH.onack_head fx rc B MT) (@OAN.onack_ntc_piece fx rc B MT) (@OAA.onack_aft_piece fx rc B MT)
           (@OAI.onack_ign_piece fx rc B MT) (@OAR.onack_rel fx rc B MT)).
Qed.
