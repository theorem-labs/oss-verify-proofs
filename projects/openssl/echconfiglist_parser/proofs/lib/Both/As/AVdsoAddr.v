(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 727298f3): the binary-specific inputs of the __vdsosym walk of the
   ASan+UBSan build (echconfiglist_parser.asan-ubsan), the counterpart of Ref/RVdsoAddr.v: the
   binary's segment list, the entry of musl's __vdsosym, the cell holding musl's auxv pointer, the
   two strings its one caller (cgt_init) passes, and the two calls __vdsosym makes to ASan's strcmp
   interceptor.  Ref/RVdsoSegs.v, RVdsoSym.v and RVdsoWalk.v name nothing else of a binary; their
   copies in this directory (AVdsoSegs.v, AVdsoSym.v, AVdsoWalk.v) read this file.

   Every number is read from this binary's text and data:
   - __vdsosym begins with [addi sp, sp, -0x70] at 0x56e584 (ECH_AImg.P_vdsosym);
   - its [auipc a2, 0x694; ld a2, -0x694(a2)] at 0x56e5bc reads the cell 0xc01f28 (AsAuxv.AAUXV_CELL);
   - cgt_init (0x56e4fc) loads [auipc a0, 0xffad4; addi a0, a0, -0x291] at 0x56e514/0x56e51c, the
     string "LINUX_4.15" at 0x42283, and [auipc a1, 0xffaa9; addi a1, a1, -0x6e] at
     0x56e518/0x56e520, the string "__vdso_clock_gettime" at 0x174aa; both are NUL-terminated in the
     first (r--) segment, 0x10000-0x194ba8 (read from the ELF file);
   - [auipc ra, 0xffc3a; jalr ra, ra, -0xac] at 0x56e7ac and [auipc ra, 0xffc3a; jalr ra, ra, -0x118]
     at 0x56e818 both jump to 0x1a8700, the [j 0x624] slot in front of the interceptor
     (AsStrcmp.ASTRCMP_THUNK); they return to 0x56e7b4 and 0x56e820. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Export ASegs.
Import ListNotations.
Open Scope Z_scope.

Notation VW_BSEGS := asegs (only parsing).
Definition VW_ENTRY : Z := 0x56e584.
Definition VW_AUXV_CELL : Z := 0xc01f28.
Definition VW_VERNAME : Z := 0x42283.
Definition VW_NAME : Z := 0x174aa.
Definition VW_CALL_VER : Z := 0x56e7ac.      (* checkver's strcmp(vername, ...) *)
Definition VW_CALL_NAME : Z := 0x56e818.     (* the symbol loop's strcmp(name, ...) *)
Definition VW_STRCMP_SLOT : Z := 0x1a8700.   (* the target of both calls *)

(* The two strings' bytes, NUL excluded: "LINUX_4.15" and "__vdso_clock_gettime". *)
Definition VW_VERNAME_S : list byte :=
  map (Z_to_bv 8) [76; 73; 78; 85; 88; 95; 52; 46; 49; 53].
Definition VW_NAME_S : list byte :=
  map (Z_to_bv 8) [95; 95; 118; 100; 115; 111; 95; 99; 108; 111; 99; 107; 95; 103; 101; 116; 116; 105; 109; 101].
