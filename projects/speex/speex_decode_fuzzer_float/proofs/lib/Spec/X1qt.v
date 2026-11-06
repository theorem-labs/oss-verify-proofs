(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Export X1qs X1pe X1os.

Notation mspec := (mspecL LBUDGET) (only parsing).
Notation mspec_ret := (mspecL_ret LBUDGET) (only parsing).
Notation mspec_bind := (mspecL_bind LBUDGET) (only parsing).
Notation mspec_seq := (mspecL_seq LBUDGET) (only parsing).
Notation mspec_conseq := (mspecL_conseq LBUDGET) (only parsing).
Notation mspec_pre := (mspecL_pre LBUDGET) (only parsing).
Notation mspec_post := (mspecL_post LBUDGET) (only parsing).
Notation mspec_munr := (mspecL_munr LBUDGET) (only parsing).
Notation mspec_false := (mspecL_false LBUDGET) (only parsing).
Notation mspec_get := (mspecL_get LBUDGET) (only parsing).
Notation mspec_put := (mspecL_put LBUDGET) (only parsing).
Notation mspec_upd := (mspecL_upd LBUDGET) (only parsing).
Notation mspec_upd' := (mspecL_upd' LBUDGET) (only parsing).
Notation mspec_sys := (mspecL_sys LBUDGET) (only parsing).
Notation mspec_if := (mspecL_if LBUDGET) (only parsing).
Notation mspec_if_pre := (mspecL_if_pre LBUDGET) (only parsing).
Notation mspec_exI := (mspecL_exI LBUDGET) (only parsing).
Notation mspec_pure := (mspecL_pure LBUDGET) (only parsing).
Notation mspec_pure_l := (mspecL_pure_l LBUDGET) (only parsing).
Notation mspec_pointwise := (mspecL_pointwise LBUDGET) (only parsing).
Notation mspec_when := (mspecL_when LBUDGET) (only parsing).
Notation mspec_loop := (mspecL_loop LBUDGET) (only parsing).
