(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: generated for omx-clap-core/fuzz_preset's ASan image (ELF sha256 bff8519bbe3ea0e4) by
   the internal file gen_cells.py: every constant below is read from that ELF by the rule in its comment, so a re-pin
   regenerates the file and no other file needs to carry the number. A shadow address is a FUNCTION of an image
   address (shadow_of), never a literal. *)
(* Generator: tools/startup/gen_cells.py sha256 29dd926cd6b2098996ffd84a619a4748091f285feae2901c3eaa1145c120ee9f; image sha256 bff8519bbe3ea0e4d8edf35fa48015b5846960886633a77a5e9f86cb565bd590. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
Open Scope Z_scope.
Definition shadow_of (a : Z) : Z := a / 8 + 0x7fff8000.
Definition A_UAR_OPT : Z := 0xaaec0.   (* symbol __asan_option_detect_stack_use_after_return (4 bytes) *)
Definition A_GOT_UAR_OPT : Z := 0xa2068.   (* .got slot holding A_UAR_OPT *)
Definition A_SHADOW_BASE_CELL : Z := 0xaaeb8.   (* symbol __asan_shadow_memory_dynamic_address (8 bytes) *)
Definition A_GOT_SHADOW_BASE_CELL : Z := 0xa2010.   (* .got slot holding A_SHADOW_BASE_CELL *)
Definition A_OOM_CELL : Z := 0x12d120.   (* symbol __sanitizer::allocator_out_of_memory (1 bytes) *)
Definition A_GOT_SEALED_FLAG : Z := 0xa2050.   (* the one .got slot __sanitizer::GetEnviron loads that holds 1: the sealed-runtime flag it returns NULL behind (value 1) *)
Definition A_SEALED_FLAG_VALUE : Z := 1.   (* the 8 bytes at A_GOT_SEALED_FLAG *)
Definition A_BUILTIN_TLS : Z := 0x5dde28.   (* symbol builtin_tls (131280 bytes) *)
Definition A_BUILTIN_TLS_SZ : Z := 0x200d0.   (* size of builtin_tls *)
Definition A_BUILTIN : Z := 0x5fdf58.   (* symbol builtin (520 bytes) *)
Definition A_BUILTIN_SZ : Z := 520.   (* size of builtin *)
Definition A_STACK_CHK_GUARD : Z := 0x5fdf30.   (* symbol __stack_chk_guard *)
Definition A_GOT_STACK_CHK_GUARD : Z := 0xa2c98.   (* .got slot holding A_STACK_CHK_GUARD *)
Definition A_ASAN_GLOBALS : Z := 0xa6920.   (* start of the asan_globals section *)
Definition A_ASAN_GLOBALS_SZ : Z := 3776.   (* size of asan_globals = 64 * 59 registered globals *)
Definition A_NGLOBALS : Z := 59.   (* the number of registered globals *)
Definition A_EMPTY : Z := 0x5dd520.   (* symbol oft_aligned_copy.empty (32 bytes): the empty-copy object A/ACfl.v, A/ACfn.v and A/AD2f.v cite *)
Definition A_INSTANCE : Z := 0xa7858.   (* symbol __asan::instance (3632 bytes) *)
Definition A_DEPOT : Z := 0x18cd98.   (* symbol __sanitizer::theDepot *)
Definition A_STORE : Z := 0x17cd88.   (* symbol __sanitizer::stackStore *)

(* shadow names the ported files need; each is shadow_of of a named cell, not a literal *)
Definition A_SHADOW_BUILTIN_TLS : Z := shadow_of A_BUILTIN_TLS.
Definition A_SHADOW_BUILTIN_TLS_EB8 : Z := shadow_of (A_BUILTIN_TLS + 0xeb8).
Definition A_SHADOW_ASAN_GLOBALS : Z := shadow_of A_ASAN_GLOBALS.
Lemma shadow_of_builtin_tls_eb8 : A_SHADOW_BUILTIN_TLS_EB8 = 2148220316.
Proof. reflexivity. Qed.
