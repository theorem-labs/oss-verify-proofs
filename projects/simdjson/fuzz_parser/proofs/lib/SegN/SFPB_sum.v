(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require SFPB_defs SFPCB_defs PFFB_defs PFFCB_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Definition SFPBS : SP.summ :=
  SP.SUMY (SP.p_G SFPB_defs.SFPB) SFPB_defs.T0 (SP.p_ex SFPB_defs.SFPB) (SP.p_W SFPB_defs.SFPB) (SP.p_A SFPB_defs.SFPB)
    (SP.p_PS SFPB_defs.SFPB) false (SP.p_CR SFPB_defs.SFPB).
Definition SFPCBS : SP.summ :=
  SP.SUMY (SP.p_G SFPCB_defs.SFPCB) SFPCB_defs.T0 (SP.p_ex SFPCB_defs.SFPCB) (SP.p_W SFPCB_defs.SFPCB) (SP.p_A SFPCB_defs.SFPCB)
    (SP.p_PS SFPCB_defs.SFPCB) false (SP.p_CR SFPCB_defs.SFPCB).
Definition PFFBS : SP.summ :=
  SP.SUMY (SP.p_G PFFB_defs.PFFB) PFFB_defs.T0 (SP.p_ex PFFB_defs.PFFB) (SP.p_W PFFB_defs.PFFB) (SP.p_A PFFB_defs.PFFB)
    (SP.p_PS PFFB_defs.PFFB) false (SP.p_CR PFFB_defs.PFFB).
Definition PFFCBS : SP.summ :=
  SP.SUMY (SP.p_G PFFCB_defs.PFFCB) PFFCB_defs.T0 (SP.p_ex PFFCB_defs.PFFCB) (SP.p_W PFFCB_defs.PFFCB) (SP.p_A PFFCB_defs.PFFCB)
    (SP.p_PS PFFCB_defs.PFFCB) false (SP.p_CR PFFCB_defs.PFFCB).
