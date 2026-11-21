(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* headrow-r1 (ruling 2): istate_cells is the zlib 1.4 inflate_state head, 168 bytes; reqwrap = 5 and reqbits = 15 as constants, the two holes = 0 (1.4 inflateInit2_ zeroes the state). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import PropExec MState Mem Cells Step Frame Arr Bytes.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AArr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition A_HARNESS : Z := 0x8cae4.
Definition A_UNCOMPRESS2 : Z := 0x8cd44.   (* 1.4: uncompress2_z (the 1.3.1 mover had the uncompress2 wrapper, 0x8d1e0) *)
Definition A_INFLATEINIT : Z := 0x8dd64.
Definition A_INFLATE : Z := 0x8dd74.
Definition A_UPDATEWINDOW : Z := 0x938dc.
Definition A_INFLATEEND : Z := 0x93d7c.
Definition A_ZCALLOC : Z := 0x93f88.
Definition A_ZCFREE : Z := 0x93f98.
Definition A_ADLER32Z : Z := 0x9512c.
Definition A_ADLER32 : Z := 0x95af4.
Definition A_ITABLE : Z := 0x95b00.
Definition A_IFAST : Z := 0x969f8.
Definition A_DISP : Z := 0x8e1e0.
Definition A_LEAVE : Z := 0x928d0.
Definition A_EPI : Z := 0x92bfc.
Definition A_JTAB : Z := 0x227c0.
Definition A_OUTBUF : Z := 0x60af00.

Definition strm_cells (next_in avail_in total_in next_out avail_out total_out msg state zalloc zfree opaque data_type adler reserved : word)
    (p1 p2 p3 : word) : list cell :=
  [C8 next_in; C4 avail_in; C4 p1; C8 total_in; C8 next_out; C4 avail_out; C4 p2; C8 total_out; C8 msg; C8 state;
   C8 zalloc; C8 zfree; C8 opaque; C4 data_type; C4 p3; C8 adler; C8 reserved].

Definition istate_cells (strm mode last wrap havedict flags dmax check total head wbits wsize whave wnext window hold bits
    length offset extra lencode distcode lenbits distbits ncode nlen ndist have next : word) : list cell :=
  [C8 strm; C4 mode; C4 last; C4 wrap; C4 (Z_to_bv 64 5); C4 havedict; C4 flags; C4 dmax; C4 (Z_to_bv 64 0); C8 check; C8 total; C8 head; C4 (Z_to_bv 64 15); C4 wbits; C4 wsize;
   C4 whave; C4 wnext; C4 (Z_to_bv 64 0); C8 window; C8 hold; C4 bits; C4 length; C4 offset; C4 extra; C8 lencode; C8 distcode;
   C4 lenbits; C4 distbits; C4 ncode; C4 nlen; C4 ndist; C4 have; C8 next].

Definition itail_cells (sane back was pad : word) : list cell := [C4 sane; C4 back; C4 was; C4 pad].

Lemma strm_cells_size : forall a b c d e f g h i j k l m n p1 p2 p3,
  cells_size (strm_cells a b c d e f g h i j k l m n p1 p2 p3) = 112%nat.
Proof. reflexivity. Qed.
Lemma istate_cells_size : forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29,
  cells_size (istate_cells a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29) = 168%nat.
Proof. reflexivity. Qed.

Definition icx_of (S D n OB osz Wd cin0 cout0 W0 : Z) : ictx :=
  ICX 0 S D n OB osz Wd cin0 cout0 W0 (fun _ => 0) 0.
