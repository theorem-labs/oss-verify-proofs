(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import Frame RzCPS.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import RT_iface RT_rep D_iface D_defs D_libiface Lept_iface Km_iface.
Import ListNotations.
Open Scope Z_scope.

Lemma outside_libfp_km : forall x, outside D_libiface.LIB_FP x -> outside Lept_iface.LIB_FP x.
Proof. intros x H. unfold D_libiface.LIB_FP, Lept_iface.LIB_FP, g_stderr_handler in *. cbn [outside] in *. tauto. Qed.

Theorem km_fuzz_adapt : forall RT, Km_iface.km_fuzz_one_cps RT -> D_libiface.fuzz_one_cps RT D_libiface.LIB_A.
Proof.
  intros RT H Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
    H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26.
  eapply cps_conseq; [exact (H Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
    H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26) | intros c Hc; exact Hc |].
  intros c (Σ' & HA & R). exists Σ'. split; [|exact R].
  eapply (ASTA_conseq RT); [exact HA|]. intros ms (m' & X1 & X2 & X3 & X4). exists m'. split; [exact X1|]. split; [exact X2|].
  split; [|exact X4]. intros a Ha Ho. apply (X3 a Ha). apply outside_libfp_km. exact Ho.
Qed.
