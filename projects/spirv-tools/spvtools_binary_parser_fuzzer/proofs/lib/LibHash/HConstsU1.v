(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HStmts.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.

Definition hc : hconsts := {|
  hc_find_u32     := 0x6b21c;
  hc_find_nt      := 0x6a89c;
  hc_emplace_u32  := 0x6aa04;
  hc_emplace_ext  := 0x6b528;
  hc_rehash_u32   := 0x6aff8;
  hc_rehash_ext   := 0x6bb1c;
  hc_mva_u32      := 0x690e4;
  hc_mva_ext      := 0x69254;
  hc_next_prime   := 0x8c1fc;
  hc_state_mva    := 0x66d94;
  hc_state_dtor   := 0x67088;
  hc_memset       := 0xe311c;
  hc_delete_sized := 0x6f8cc;
  hc_nt_entry     := 0x689f8;
  hc_nt_exit      := 0x69080
|}.
