(* TransportGRwB: image B's harness globals lie in its segments. Every byte of lib/B/TransportGB.v G_HARNESS_B (the
   payloads of the 18 harness globals, hull [0x5ded00, 0x5f2e10)) is a byte of the fourth loaded segment of
   fuzz_transport.asan-ubsan (41113a03c82f), [0xa5000, 0x616000) with perms "rw-", whose snapshot holds all 0x571000
   bytes of the segment (the .bss part as zeros). So lib/A/Prog/TransportGCg.v gx_rw holds at the image's loaded
   segments, decided by vm_compute: at every memory a byte of G is writable and visible, and a walk of image B needs no
   presence of G's bytes. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.libdiginet.fuzz_transport.images Require Import AsanUbsan.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.

Lemma G_HARNESS_B_rw : gx_rw AsanUbsan.M.loaded_segments G_HARNESS_B.
Proof. apply gx_rw_of_b. vm_compute. reflexivity. Qed.
