(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U2A Require Export U2AObj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Definition A_HARNESS : Z := 0x8cb14.
Definition A_UNCOMPRESS2 : Z := 0x8ce40.   (* 1.4: uncompress2_z (the 1.3.1 mover had the uncompress2 wrapper, 0x8d2ac) *)
Definition A_INFLATEINIT : Z := 0x8de60.
Definition A_INFLATE : Z := 0x8de70.
Definition A_UPDATEWINDOW : Z := 0x939d8.
Definition A_INFLATEEND : Z := 0x93e78.
Definition A_ZCALLOC : Z := 0x94084.
Definition A_ZCFREE : Z := 0x94094.
Definition A_ADLER32Z : Z := 0x95228.
Definition A_ADLER32 : Z := 0x95bf0.
Definition A_ITABLE : Z := 0x95bfc.
Definition A_IFAST : Z := 0x96af4.
Definition A_DISP : Z := 0x8e2dc.
Definition A_LEAVE : Z := 0x929cc.
Definition A_EPI : Z := 0x92cf8.
Definition A_JTAB : Z := 0x227c0.
Definition A_OUTBUF : Z := 0x60b000.
