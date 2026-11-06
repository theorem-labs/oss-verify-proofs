(* TransportGRwA: image A's harness globals lie in its segments. Every byte of TransportG.v G_HARNESS (the payloads of
   the 18 harness globals, hull [0x5df080, 0x5f3190)) is a byte of the fourth loaded segment of fuzz_transport.asan
   (e89be137db17), [0xa5000, 0x616000) with perms "rw-", whose snapshot holds all 0x571000 bytes of the segment (the
   .bss part as zeros). So TransportGCg.v gx_rw holds, decided by vm_compute: at every memory a byte of G is writable
   and visible, and a walk of image A needs no presence of G's bytes. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.

Lemma G_HARNESS_rw : gx_rw tfibsegs G_HARNESS.
Proof. apply gx_rw_of_b. vm_compute. reflexivity. Qed.
