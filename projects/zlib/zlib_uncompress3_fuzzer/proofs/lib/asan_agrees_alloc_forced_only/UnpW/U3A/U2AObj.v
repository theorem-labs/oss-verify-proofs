(* reloc-zl14c 5b5055a48df29bf302ad900c7dfa75c4 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Export U2AObj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Definition A_HARNESS : Z := 0x8cb14.      (* [comment removed for export] *)
Definition A_UNCOMPRESS2 : Z := 0x8ce40.   (* an earlier development run 1.4: uncompress2_z (the 1.3.1 mover had the uncompress2 wrapper, 0x8d2ac) *)
Definition A_INFLATEINIT : Z := 0x8de60.  (* [comment removed for export] *)
Definition A_INFLATE : Z := 0x8de70.
Definition A_UPDATEWINDOW : Z := 0x939c0.
Definition A_INFLATEEND : Z := 0x93e60.
Definition A_ZCALLOC : Z := 0x9406c.
Definition A_ZCFREE : Z := 0x9407c.
Definition A_ADLER32Z : Z := 0x95210.
Definition A_ADLER32 : Z := 0x95bd8.
Definition A_ITABLE : Z := 0x95be4.
Definition A_IFAST : Z := 0x96adc.
Definition A_DISP : Z := 0x8e2ec.         (* [comment removed for export] *)
Definition A_LEAVE : Z := 0x92908.        (* [comment removed for export] *)
Definition A_EPI : Z := 0x92c60.          (* [comment removed for export] *)
Definition A_JTAB : Z := 0x227c0.         (* [comment removed for export] *)
Definition A_OUTBUF : Z := 0x60b000.      (* [comment removed for export] *)
