(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Export IcptIfaceA.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Record as0_icpt_layout (IL : icpt_layout) : Prop := AICL {
  aicl_strlen : icl_strlen IL = 0x4de30;
  aicl_scr_strlen : icl_scr_strlen IL = 2304;
  aicl_ro_lo : icl_ro_lo IL = 0x10370; aicl_ro_hi : icl_ro_hi IL = 0x10390;
  aicl_globals : icl_globals IL = [(0x22960, 39); (0x229c0, 13); (0x22b20, 60); (0x22ba0, 42); (0x22c00, 37); (0x22c60, 51); (0x22cc0, 13)];
  aicl_poison : icl_poison IL = [(0x22960, 0x22ce0); (0xdaeb0, 0xdb070)];
  aicl_memcpy : icl_memcpy IL = 0x5e350;        (* [comment removed for export] *)
  aicl_memmove : icl_memmove IL = 0x5e34c;      (* [comment removed for export] *)
  aicl_ctxslot : icl_ctxslot IL = 0x632cb0;     (* [comment removed for export] *)
  aicl_strerror_r : icl_strerror_r IL = 0x4de84;                                                         (* [comment removed for export] *)
  aicl_scr_strerror : icl_scr_strerror IL = 4320;                                                        (* [comment removed for export] *)
  aicl_strerror_cells : icl_strerror_cells IL = [(0x6118d8, 8, 0x631bd0); (0x631bf8, 8, 0)];             (* [comment removed for export] *)
  aicl_sro_lo : icl_sro_lo IL = 0x10000; aicl_sro_hi : icl_sro_hi IL = 0xd8000                            (* [comment removed for export] *)
}.
