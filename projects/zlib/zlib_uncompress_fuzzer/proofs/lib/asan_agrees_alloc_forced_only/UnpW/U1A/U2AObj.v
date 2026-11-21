(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Export U2AObj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Definition A_HARNESS : Z := 0x8c920.      (* [comment removed for export] *)
Definition A_UNCOMPRESS2 : Z := 0x8cb28.
Definition A_INFLATEINIT : Z := 0x8db00.  (* [comment removed for export] *)
Definition A_INFLATE : Z := 0x8db10.
Definition A_UPDATEWINDOW : Z := 0x93660.
Definition A_INFLATEEND : Z := 0x93b00.
Definition A_ZCALLOC : Z := 0x93d0c.
Definition A_ZCFREE : Z := 0x93d1c.
Definition A_ADLER32Z : Z := 0x94eb0.
Definition A_ADLER32 : Z := 0x95878.
Definition A_ITABLE : Z := 0x95884.
Definition A_IFAST : Z := 0x9677c.
Definition A_DISP : Z := 0x8df8c.         (* [comment removed for export] *)
Definition A_LEAVE : Z := 0x925a8.        (* [comment removed for export] *)
Definition A_EPI : Z := 0x92900.          (* [comment removed for export] *)
Definition A_JTAB : Z := 0x227b0.         (* [comment removed for export] *)
Definition A_OUTBUF : Z := 0x60ac80.      (* [comment removed for export] *)
