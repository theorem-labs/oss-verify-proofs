(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import RT_iface RT_gaps_iface Lept_iface Gm_iface Gm_cmapvalid_defs Gm_cmapvalid_F Gm_cmapvalid_S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CVN.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Theorem pixcmapIsValid_null_ok : pixcmapIsValid_null_cps RT.
Proof using AF GP.
  exact (cmapvalid_null_of_cases RT (pixcmapIsValid_null_F_ok RT AF GP) (pixcmapIsValid_null_S_ok RT AF GP)).
Qed.
End CVN.
