(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import RT_iface RT_gaps_iface Lept_iface Gm_iface Gm_rasterop_defs
  Gm_rasterop_uni_c0 Gm_rasterop_uni_c16 Gm_rasterop_src_c0 Gm_rasterop_src_c16.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ROP.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Theorem pixRasterop_uni_ok : rasteropUniLow_cps RT -> pixRasterop_uni_cps RT.
Proof using AF GP.
  intros UNI. apply rop_uni_of_cases; [exact (rop_uni_c0 RT AF GP UNI)| exact (rop_uni_c16 RT AF GP UNI)].
Qed.

Theorem pixRasterop_src_ok : rasteropLow_cps RT -> pixRasterop_src_cps RT.
Proof using AF GP.
  intros LOW. apply rop_src_of_cases; [exact (rop_src_c0 RT AF GP LOW)| exact (rop_src_c16 RT AF GP LOW)].
Qed.
End ROP.
