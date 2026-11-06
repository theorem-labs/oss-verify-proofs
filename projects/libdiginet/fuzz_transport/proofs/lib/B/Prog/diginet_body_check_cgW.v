(* Modified by Theorem Labs, 2026-10: libdiginet/fuzz_frame image B's copy of this unit's image-A assembly lib/A/Prog/diginet_body_check_cgW.v: module paths lib/B and image B's cut offsets in the comment. *)
(* diginet_body_check_cgW (image B): Theorem decode_diginet_body_check_cg_holds : the statement of
   lib/B/Prog/diginet_body_check_cg.v, from the four pieces of the walk at the cuts of lib/B/Prog/DgnBcCut.v:
   the head (entry .. +0x168, lib/B/Prog/DgnBcHead.v bc_holds_of), the msg_next loop (+0x16c, DgnBcLoop.v
   bc_loop), the prefix scan (+0x1f8, DgnBcScan.v bc_scan) and the release (+0x2d0, DgnBcRel.v bc_rel). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnBcCut DgnBcHead DgnBcLoop DgnBcScan DgnBcRel.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Theorem transport_diginet_body_check_cg_holds : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT,
  @transport_diginet_body_check_cg_holds_stmt fx rc B MT.
Proof.
  intros fx rc B MT.
  exact (@bc_holds_of fx rc B MT
           (@bc_loop fx rc B MT (@bc_rel fx rc B MT) (@bc_scan fx rc B MT (@bc_rel fx rc B MT)))).
Qed.
