(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.Lib Require Import Tac RzCPS.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.A22 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface Lept_kit D_iface D_defs Lept_iface
  Lept_gmax_defs Lept_gmax_c0 Lept_gmax_c16.
Import ListNotations.
Open Scope Z_scope.

Section GMAX.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis ZERO : pixZero_cps RT.

Theorem pixGetMaxColorIndex_ok : pixGetMaxColorIndex_cps RT.
Proof using AF GP ZERO.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix pmax v cv x
    H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 ENV H12.
  assert (AL : bv_unsigned sp mod 32 = 0 \/ bv_unsigned sp mod 32 = 16).
  { destruct ENV as (_ & _ & _ & _ & _ & _ & _ & _ & SPA & _). Z.div_mod_to_equations. lia. }
  destruct AL as [AL|AL].
  - exact (gmax_c0 RT AF GP ZERO Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix pmax v cv x
             H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 ENV H12 AL).
  - exact (gmax_c16 RT AF GP ZERO Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix pmax v cv x
             H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 ENV H12 AL).
Qed.
End GMAX.
