(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Export U2AObj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* every A_ below is the #1390 build's address (symbol table of its ASan symbol twin) *)
Definition A_HARNESS : Z := 0x8c920.
Definition A_UNCOMPRESS2 : Z := 0x8cb28.
Definition A_INFLATEINIT : Z := 0x8db00.
Definition A_INFLATE : Z := 0x8db10.
Definition A_UPDATEWINDOW : Z := 0x93678.
Definition A_INFLATEEND : Z := 0x93b18.
Definition A_ZCALLOC : Z := 0x93d24.
Definition A_ZCFREE : Z := 0x93d34.
Definition A_ADLER32Z : Z := 0x94ec8.
Definition A_ADLER32 : Z := 0x95890.
Definition A_ITABLE : Z := 0x9589c.
Definition A_IFAST : Z := 0x96794.
Definition A_DISP : Z := 0x8df7c.
Definition A_LEAVE : Z := 0x9266c.
Definition A_EPI : Z := 0x92998.
Definition A_JTAB : Z := 0x227b0.
Definition A_OUTBUF : Z := 0x60acc0.
