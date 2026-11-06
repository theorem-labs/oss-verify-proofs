(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require HI64B_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Definition HI64SB : SP.summ :=
  SP.SUMY (SP.p_G HI64B_defs.HI64B) HI64B_defs.T0 (SP.p_ex HI64B_defs.HI64B) (SP.p_W HI64B_defs.HI64B) (SP.p_A HI64B_defs.HI64B)
    (SP.p_PS HI64B_defs.HI64B) false (SP.p_CR HI64B_defs.HI64B).
