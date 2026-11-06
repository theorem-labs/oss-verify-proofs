(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/Prog/memcmp.v: ported from a working branch affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/B/Prog/memcmp.v, which equals the A->B relocation (Theorem Labs tools) of lib/A/Prog/memcmp.v at a working branch 5d8d8a15571 modulo module paths; module paths for this tree. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Prog Require Import memcmp_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require R_memchr.

Theorem memcmp_holds : memcmp_contract.
Proof.
  unfold memcmp_contract. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ls rs v LS RS HM MI.
  exact (R_memchr.R_memcmp.memcmp_body ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ls rs v MI LS RS HM).
Qed.
