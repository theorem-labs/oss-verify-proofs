(* on_data_cgW: the image-B ASan walk of on_data (fuzz_transport.asan-ubsan 0x88a48 = transportb_sigma TB_on_data,
   1620 bytes): Theorem transport_on_data_cg_holds : transport_on_data_cg_holds_stmt (lib/B/Prog/on_data_cg.v), the
   composition (lib/B/Prog/on_data_segs.v od_holds_of) of the nine pieces of the walk (offsets from AF_on_data =
   0x77a8 of lib/B/Prog/DgnTransportBList.v; the cuts are lib/B/Prog/on_data_seg_cut.v):
     head   lib/B/Prog/on_data_seg_head.v  od_head   the entry .. +0x16c, then send_control's entry (+0x170);
     sc     lib/B/Prog/on_data_seg_sc.v    od_sc     the call of send_control, to its return (+0x174);
     acks   lib/B/Prog/on_data_seg_acks.v  od_acks   +0x174 .. +0x23c (the UBSan check of s, the counters, the backoff);
     dup    lib/B/Prog/on_data_seg_dup.v   od_dup    +0x240 .. +0x2a8 (the duplicate test and the duplicate path);
     set    lib/B/Prog/on_data_seg_set.v   od_set    +0x2ac .. +0x2e0, then the leaf's entry (+0x2e4);
     ka     lib/B/Prog/on_data_seg_ka.v    od_ka     the call of diginet_frame_is_keepalive and `bnez a0` (+0x2e8);
     ntc    lib/B/Prog/on_data_seg_ntc.v   od_ntc    +0x2ec .. +0x3dc (the notice struct, the memset);
     ncall  lib/B/Prog/on_data_seg_ncall.v od_ncall  the call of notice (+0x3e0) .. +0x408;
     rel    lib/B/Prog/on_data_seg_rel.v   od_rel    +0x40c .. the return (the frame released). *)
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_data_cg on_data_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require
  on_data_seg_head on_data_seg_sc on_data_seg_acks on_data_seg_dup on_data_seg_set on_data_seg_ka on_data_seg_ntc
  on_data_seg_ncall on_data_seg_rel.
Module OH := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_data_seg_head.
Module OS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_data_seg_sc.
Module OA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_data_seg_acks.
Module OD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_data_seg_dup.
Module OT := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_data_seg_set.
Module OK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_data_seg_ka.
Module ON := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_data_seg_ntc.
Module OC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_data_seg_ncall.
Module OR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_data_seg_rel.

Theorem transport_on_data_cg_holds {fx : YK11.FPState} {rc : YM05.RunCeil} (B : asyms) (MT : ameter_ops) :
  @transport_on_data_cg_holds_stmt fx rc B MT.
Proof.
exact (@od_holds_of fx rc B MT (OH.od_head fx rc B MT) (OS.od_sc fx rc B MT) (OA.od_acks fx rc B MT)
  (OD.od_dup fx rc B MT) (OT.od_set fx rc B MT) (OK.od_ka fx rc B MT) (ON.od_ntc fx rc B MT)
  (OC.od_ncall fx rc B MT) (OR.od_rel fx rc B MT)).
Qed.
