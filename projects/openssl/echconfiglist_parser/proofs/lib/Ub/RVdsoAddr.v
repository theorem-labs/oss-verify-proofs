(* SPDX-License-Identifier: MIT *)
(* The ubsan binary's inputs of the __vdsosym walk (Ub/RVdsoSegs.v, Ub/RVdsoSym.v,
   Ub/RVdsoWalk.v, copies of the Ref files of the same names): the binary's own segment list,
   the entry of musl's __vdsosym, the address of the cell holding musl's auxv pointer, and the
   two strings its one caller (cgt_init) passes.  All four addresses are read from this
   binary's text: __vdsosym begins with [addi sp, sp, -0x70] at 0x2c46b4; its
   [auipc a2, 0x92; ld a2, -0x3bc(a2)] at 0x2c46ec reads the cell at 0x356330; cgt_init's
   [auipc a0, 0xffd71; addi a0, a0, -0x6d9] at 0x2c4644 and [auipc a1, 0xffd51; addi a1, a1,
   0x65] at 0x2c4648 load "LINUX_4.15" at 0x34f6b and "__vdso_clock_gettime" at 0x156ad, both
   NUL-terminated in read-only data. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Export USegs.
Open Scope Z_scope.

Notation VW_BSEGS := usegs (only parsing).
Definition VW_ENTRY : Z := 0x2c46b4.
Definition VW_AUXV_CELL : Z := 0x356330.
Definition VW_VERNAME : Z := 0x34f6b.
Definition VW_NAME : Z := 0x156ad.
