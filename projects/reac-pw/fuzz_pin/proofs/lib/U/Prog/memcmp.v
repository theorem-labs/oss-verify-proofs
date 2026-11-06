From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog Require Import memcmp_c bcmp_c.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U Require R_memchr.

Theorem memcmp_holds : memcmp_contract.
Proof.
  unfold memcmp_contract. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ls rs v LS RS HM MI.
  exact (R_memchr.R_memcmp.memcmp_body ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ls rs v MI LS RS HM).
Qed.
