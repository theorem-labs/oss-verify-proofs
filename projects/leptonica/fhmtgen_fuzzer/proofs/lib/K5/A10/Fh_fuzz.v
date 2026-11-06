(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import RT_iface RT_gaps_iface Lept_iface D_iface D_defs D_libiface Gm_iface
  Fh_iface Fh_sel_iface Fh_fuzz_defs Fh_fuzz_c0 Fh_fuzz_c16.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FUZZ.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis DESER : pixDeserialize_cps RT.
Hypothesis DESTROY : pixDestroy_cps RT.
Hypothesis DNULL : pixDestroy_null_cps RT.
Hypothesis PCOPY : pixCopy_cps RT.
Hypothesis SAHM : selaAddHitMiss_cps RT.
Hypothesis SAD : selaDestroy_cps RT.
Hypothesis HMT : pixHMTDwa_1_cps RT.

Theorem fuzz_one_ok : D_libiface.fuzz_one_cps RT D_libiface.LIB_A.
Proof using AF RC GP DESER DESTROY DNULL PCOPY SAHM SAD HMT.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
    H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25.
  assert (AL : bv_unsigned sp mod 32 = 0 \/ bv_unsigned sp mod 32 = 16) by (clear - H24; Z.div_mod_to_equations; lia).
  destruct AL as [AL|AL].
  - exact (fuzz_c0 RT AF RC GP DESER DESTROY DNULL PCOPY SAHM SAD HMT
             Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
             H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 AL).
  - exact (fuzz_c16 RT AF RC GP DESER DESTROY DNULL PCOPY SAHM SAD HMT
             Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
             H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 AL).
Qed.
End FUZZ.
