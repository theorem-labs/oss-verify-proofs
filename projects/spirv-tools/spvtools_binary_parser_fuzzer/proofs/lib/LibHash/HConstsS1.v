(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HStmts.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.

Definition hc : hconsts := {|
  hc_find_u32     := 0x695ec;
  hc_find_nt      := 0x69718;
  hc_emplace_u32  := 0x69e1c;
  hc_emplace_ext  := 0x6a488;
  hc_rehash_u32   := 0x6a2cc;
  hc_rehash_ext   := 0x6a938;
  hc_mva_u32      := 0x6850c;
  hc_mva_ext      := 0x6860c;
  hc_next_prime   := 0x8a4a4;
  hc_state_mva    := 0x664c8;
  hc_state_dtor   := 0x666fc;
  hc_memset       := 0xe13c4;
  hc_delete_sized := 0x6db74;
  hc_nt_entry     := 0x67ed4;
  hc_nt_exit      := 0x68360
|}.
