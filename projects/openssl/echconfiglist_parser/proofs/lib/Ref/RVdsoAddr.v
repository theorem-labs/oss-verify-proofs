(* SPDX-License-Identifier: MIT *)
(* The binary-specific inputs of the __vdsosym walk (Ref/RVdsoSegs.v, Ref/RVdsoSym.v,
   Ref/RVdsoWalk.v): the binary's own segment list, the entry of musl's __vdsosym, the
   address of the cell holding musl's auxv pointer, and the two strings its one caller
   (cgt_init) passes.  Those three files name nothing else of the binary, so another binary
   built from the same musl takes the walk by copying them with its own version of this file.
   All four addresses are read from this binary's text: __vdsosym begins with
   [addi sp, sp, -0x70] at 0x27da80; its [auipc a2, 0x92; ld a2, -0x3a8(a2)] at 0x27dab8 reads
   the cell at 0x30f710; cgt_init's [auipc a0, 0xffdb7; addi a0, a0, 0x5a5] at 0x27da10 and
   [auipc a1, 0xffd98; addi a1, a1, -0x356] at 0x27da14 load "LINUX_4.15" at 0x34fb5 and
   "__vdso_clock_gettime" at 0x156be, both NUL-terminated in read-only data. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Export RSegs.
Open Scope Z_scope.

Notation VW_BSEGS := rsegs (only parsing).
Definition VW_ENTRY : Z := 0x27da80.
Definition VW_AUXV_CELL : Z := 0x30f710.
Definition VW_VERNAME : Z := 0x34fb5.
Definition VW_NAME : Z := 0x156be.
