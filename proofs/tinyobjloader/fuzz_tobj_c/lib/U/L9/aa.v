From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require Import S_aa.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require aa1 aa16.

Theorem aa_sum : aa_stmt_U.
Proof.
  intros al [-> | ->] ok Kc FB rho0 HS ML MC.
  - exact (aa1.aa1_sum_S ok Kc FB rho0 HS ML MC).
  - exact (aa16.aa16_sum_S ok Kc FB rho0 HS ML MC).
Qed.

Theorem aa_sum_ex : aa_ex_stmt_U.
Proof.
  intros al [-> | ->] Kc FB rho0 Hvi ML MCX.
  - exact (aa1.aa1_sum_E Kc FB rho0 ML Hvi MCX).
  - exact (aa16.aa16_sum_E Kc FB rho0 ML Hvi MCX).
Qed.
