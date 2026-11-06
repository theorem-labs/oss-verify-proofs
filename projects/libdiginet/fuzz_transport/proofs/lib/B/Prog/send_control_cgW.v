(* send_control_cgW: Theorem transport_send_control_cg_holds : the statement transport_send_control_cg_holds_stmt
   of lib/B/Prog/send_control_cg.v (image B, fuzz_transport.asan-ubsan 0x86ed4 = transportb_sigma TB_send_control),
   from the five pieces of the walk at the cuts of lib/B/Prog/SendctlBCut.v: the head (entry .. +0x1a8,
   lib/B/Prog/SendctlBHead.v sendctl_head), the frame-build call (+0x1ac .. +0x1b8, SendctlBFb.v sendctl_fb), the
   keep path (+0x1bc .. +0x1e8, SendctlBKeep.v sendctl_keep), the send path (+0x1ec .. +0x25c, SendctlBSend.v
   sendctl_send) and the release (+0x260 .. +0x3b8, SendctlBRel.v sendctl_rel). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
SendctlBCut SendctlBHead SendctlBFb SendctlBKeep SendctlBSend SendctlBRel.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Theorem transport_send_control_cg_holds : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT,
  @transport_send_control_cg_holds_stmt fx rc B MT.
Proof.
  intros fx rc B MT.
  exact (@sendctl_holds_of fx rc B MT (@sendctl_head fx rc B MT) (@sendctl_fb fx rc B MT)
           (@sendctl_keep fx rc B MT) (@sendctl_send fx rc B MT) (@sendctl_rel fx rc B MT)).
Qed.

Print Assumptions transport_send_control_cg_holds.
