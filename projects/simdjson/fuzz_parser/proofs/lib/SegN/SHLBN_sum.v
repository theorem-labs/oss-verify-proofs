(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require SHLBN_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Definition SHLSBN : SP.summ :=
  SP.SUMY (SP.p_G SHLBN_defs.SHLBN) SHLBN_defs.T0 (SP.p_ex SHLBN_defs.SHLBN) (SP.p_W SHLBN_defs.SHLBN) (SP.p_A SHLBN_defs.SHLBN)
    (SP.p_PS SHLBN_defs.SHLBN) false (SP.p_CR SHLBN_defs.SHLBN).
