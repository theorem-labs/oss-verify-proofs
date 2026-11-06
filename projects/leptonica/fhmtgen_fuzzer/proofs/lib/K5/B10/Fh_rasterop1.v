(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_gaps_iface Lept_iface Gm_iface Fh_rop_iface Fh_rasterop1_defs
  Fh_rasterop1_clr_c0 Fh_rasterop1_clr_c16 Fh_rasterop1_src_c0 Fh_rasterop1_src_c16 Fh_uni1 Fh_roplow1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ROP1.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Theorem pixRasterop_clr1_of_low : rasteropUniLow_clr1_cps RT -> rop_clr1_cps RT.
Proof using AF GP.
  intros UNI. apply rop_clr1_of_cases; [exact (rop_clr1_c0 RT AF GP UNI)| exact (rop_clr1_c16 RT AF GP UNI)].
Qed.

Theorem pixRasterop_src1_of_low : rasteropLow_src1_cps RT -> rop_src1_cps RT.
Proof using AF GP.
  intros LOW. apply rop_src1_of_cases; [exact (rop_src1_c0 RT AF GP LOW)| exact (rop_src1_c16 RT AF GP LOW)].
Qed.
End ROP1.
