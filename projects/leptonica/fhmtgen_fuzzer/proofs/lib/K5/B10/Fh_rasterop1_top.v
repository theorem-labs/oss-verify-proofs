(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_gaps_iface Lept_iface Gm_iface Fh_iface Fh_rop_iface Fh_rasterop1_defs
  Fh_uni1 Fh_roplow1 Fh_rasterop1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ROP1TOP.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis GM : gm_gaps RT.

(* [comment removed for export] *)
Theorem pixRasterop_clr1_ok : pixRasterop_clr1_cps RT.
Proof using AF GP GM.
  exact (pixRasterop_clr1_of_low RT AF GP (rasteropUniLow_clr1_ok RT AF GP GM)).
Qed.

Theorem pixRasterop_src1_ok : pixRasterop_src1_cps RT.
Proof using AF GP GM.
  exact (pixRasterop_src1_of_low RT AF GP (rasteropLow_src1_ok RT AF GP GM)).
Qed.
End ROP1TOP.
