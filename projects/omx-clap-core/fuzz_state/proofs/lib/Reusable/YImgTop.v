(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* fuzz_state's loaded image, measured from the pinned binaries' program headers:
   fuzz_state.asan's last PT_LOAD ends 0x5fc810, fuzz_state.asan-ubsan's ends 0x5fcd10,
   so both images round up to the same page 0x5fd000 (= lib/{A,B}/FSH_Base's FS_IMG_END).
   The donor cgif_file_fuzzer's top was 0x5fb000; anything stated over that range is about
   fuzz_state's own .bss, which is why these two numbers carry names. *)
From Stdlib Require Import ZArith.
Local Open Scope Z_scope.
(* Notations, not Definitions: every proof over the image bounds ends in `lia`, which needs
   the literal. A Definition would have to be unfolded in 30+ files to say the same thing. *)
Notation IMG_LO := 0x10000.
Notation IMG_TOP := 0x5fd000.
