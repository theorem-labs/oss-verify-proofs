(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require LMBS_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Definition LMSB : SP.summ :=
  SP.SUMY (SP.p_G LMBS_defs.LMBS) LMBS_defs.T0 (SP.p_ex LMBS_defs.LMBS) (SP.p_W LMBS_defs.LMBS) (SP.p_A LMBS_defs.LMBS)
    (SP.p_PS LMBS_defs.LMBS) false (SP.p_CR LMBS_defs.LMBS).
