(* send_data_cgW: Theorem transport_send_data_cg_holds : the statement transport_send_data_cg_holds_stmt of
   lib/B/Prog/send_data_cg.v (image B, fuzz_transport.asan-ubsan 0x89d78), from the three pieces of the walk at the
   cuts of lib/B/Prog/send_data_segs.v: the head (the entry .. +0x184, lib/B/Prog/send_data_seg_head.v sd_head, which
   also refutes the one UBSan branch to the trap word), the stores and the indirect call of io_send (+0x188 .. +0x2a8,
   lib/B/Prog/send_data_seg_mid.v sd_mid) and the release (+0x2ac .. the ret, lib/B/Prog/send_data_seg_rel.v sd_rel).
   The three piece files are Required, not Imported, and named in full: each declares many private sd_* names, which
   an Import of two of them would let shadow the cut file's. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require
send_data_segs send_data_seg_head send_data_seg_mid send_data_seg_rel.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Theorem transport_send_data_cg_holds : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT,
  @transport_send_data_cg_holds_stmt fx rc B MT.
Proof.
  intros fx rc B MT.
  exact (@send_data_segs.sd_holds_of fx rc B MT
           (@send_data_seg_head.sd_head fx rc B MT)
           (@send_data_seg_mid.sd_mid fx rc B MT)
           (@send_data_seg_rel.sd_rel fx rc B MT)).
Qed.

Print Assumptions transport_send_data_cg_holds.
