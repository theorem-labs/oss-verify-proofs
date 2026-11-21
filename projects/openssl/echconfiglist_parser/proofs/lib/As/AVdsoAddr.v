(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 727298f3): the binary-specific inputs of the __vdsosym walk of the
   ASan build (echconfiglist_parser.asan), the counterpart of Ref/RVdsoAddr.v: the binary's
   segment list, the entry of musl's __vdsosym, the cell holding musl's auxv pointer, the two
   strings its one caller (cgt_init) passes, and the two calls __vdsosym makes to ASan's strcmp
   interceptor.  Ref/RVdsoSegs.v, RVdsoSym.v and RVdsoWalk.v name nothing else of a binary; their
   As copies (AVdsoSegs.v, AVdsoSym.v, AVdsoWalk.v) read this file.

   Every number is read from this binary's text and data:
   - __vdsosym begins with [addi sp, sp, -0x70] at 0x534f74 (ECH_AImg.P_vdsosym);
   - its [auipc a2, 0x69a; ld a2, -0x6c4(a2)] at 0x534fac reads the cell 0xbce8e8 (AsAuxv.AAUXV_CELL);
   - cgt_init (0x534eec) loads [auipc a0, 0xffb0d; addi a0, a0, -0x1f] at 0x534f04/0x534f0c, the
     string "LINUX_4.15" at 0x41ee5, and [auipc a1, 0xffae2; addi a1, a1, 0x601] at
     0x534f08/0x534f10, the string "__vdso_clock_gettime" at 0x17509; both are NUL-terminated in the
     first (r--) segment, 0x10000-0x199c80 (read from the ELF file);
   - [auipc ra, 0xffc78; jalr ra, ra, 0x63c] at 0x53519c and [auipc ra, 0xffc78; jalr ra, ra, 0x5d0]
     at 0x535208 both jump to 0x1ad7d8, the [j 0x624] slot in front of the interceptor
     (AsStrcmp.ASTRCMP_THUNK); they return to 0x5351a4 and 0x535210. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Export ASegs.
Import ListNotations.
Open Scope Z_scope.

Notation VW_BSEGS := asegs (only parsing).
Definition VW_ENTRY : Z := 0x534f74.
Definition VW_AUXV_CELL : Z := 0xbce8e8.
Definition VW_VERNAME : Z := 0x41ee5.
Definition VW_NAME : Z := 0x17509.
Definition VW_CALL_VER : Z := 0x53519c.      (* checkver's strcmp(vername, ...) *)
Definition VW_CALL_NAME : Z := 0x535208.     (* the symbol loop's strcmp(name, ...) *)
Definition VW_STRCMP_SLOT : Z := 0x1ad7d8.   (* the target of both calls *)

(* The two strings' bytes, NUL excluded: "LINUX_4.15" and "__vdso_clock_gettime". *)
Definition VW_VERNAME_S : list byte :=
  map (Z_to_bv 8) [76; 73; 78; 85; 88; 95; 52; 46; 49; 53].
Definition VW_NAME_S : list byte :=
  map (Z_to_bv 8) [95; 95; 118; 100; 115; 111; 95; 99; 108; 111; 99; 107; 95; 103; 101; 116; 116; 105; 109; 101].
