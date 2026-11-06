(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import RT_iface RT_gaps_iface Lept_iface Gm_iface Gm_sbv_defs Gm_sbv_c0 Gm_sbv_c16.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section SBVF.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Theorem pixSetBorderVal_ok : pixSetBorderVal_cps RT.
Proof using AF GP.
  apply sbv_of_cases; [exact (sbv_c0 RT AF GP)| exact (sbv_c16 RT AF GP)].
Qed.
End SBVF.
