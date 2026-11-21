(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Definition A_HARNESS : Z := 0x8cb3c.
Definition A_UNCOMPRESS2 : Z := 0x8ce88.
Definition A_INFLATEINIT : Z := 0x8de6c.
Definition A_INFLATE : Z := 0x8e128.
Definition A_UPDATEWINDOW : Z := 0x94918.
Definition A_INFLATEEND : Z := 0x94e40.
Definition A_ZCALLOC : Z := 0x95058.
Definition A_ZCFREE : Z := 0x95068.
Definition A_ADLER32Z : Z := 0x962b0.
Definition A_ADLER32 : Z := 0x96db4.
Definition A_ITABLE : Z := 0x96dc0.
Definition A_IFAST : Z := 0x97eb4.
Definition A_DISP : Z := 0x8e5ec.
Definition A_LEAVE : Z := 0x93758.
Definition A_EPI : Z := 0x93b24.
Definition A_JTAB : Z := 0x227c8.
Definition A_OUTBUF : Z := 0x60c540.
