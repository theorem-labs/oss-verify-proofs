(* on_ack_cgW: the image-B ASan walk of on_ack (fuzz_transport.asan-ubsan 0x8858c = transportb_sigma TB_on_ack,
   1212 bytes): Theorem transport_on_ack_cg_holds : transport_on_ack_cg_holds_stmt (lib/B/Prog/on_ack_cg.v), the
   composition (lib/B/Prog/on_ack_segs.v onack_holds_of) of the five pieces of the walk:
     head  lib/B/Prog/on_ack_seg_head.v  onack_head       the entry .. +0x18c, then the notice or the ignored cut;
     ntc   lib/B/Prog/on_ack_seg_ntc.v   onack_ntc_piece  +0x190 .. +0x258 (the struct, the memset, notice);
     aft   lib/B/Prog/on_ack_seg_aft.v   onack_aft_piece  +0x25c .. +0x2bc (maybe_online when S_WAKING);
     ign   lib/B/Prog/on_ack_seg_ign.v   onack_ign_piece  +0x2c0 .. +0x2e4 (the ignored path);
     rel   lib/B/Prog/on_ack_seg_rel.v   onack_rel        +0x2e8 .. the return (the frame released). *)
From Stdlib Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_ack_cg on_ack_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require
  on_ack_seg_head on_ack_seg_ntc on_ack_seg_aft on_ack_seg_ign on_ack_seg_rel.
Module OH := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_ack_seg_head.
Module ON := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_ack_seg_ntc.
Module OA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_ack_seg_aft.
Module OI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_ack_seg_ign.
Module OR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_ack_seg_rel.

Theorem transport_on_ack_cg_holds {fx : YK11.FPState} {rc : YM05.RunCeil} (B : asyms) (MT : ameter_ops) :
  @transport_on_ack_cg_holds_stmt fx rc B MT.
Proof.
exact (@onack_holds_of fx rc B MT (OH.onack_head fx rc B MT) (ON.onack_ntc_piece fx rc B MT)
  (OA.onack_aft_piece fx rc B MT) (OI.onack_ign_piece fx rc B MT) (@OR.onack_rel fx rc B MT)).
Qed.
