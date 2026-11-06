(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: REGENERATED for libreac/fuzz_boxreg's asan from plugin-hostd/fuzz_reply's
   lib/A/RT_gxa_mem_Tbl.v (a working branch 86b50358d34): the four entries and the build identity
   re-read from fuzz_boxreg.asan (nm + bytes); the rest of the file is the donor's form. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/RT_gxa_mem_Tbl.v, with its module paths and addresses changed; 2 lines of the source are left out. *)
(* Image B twin of lib/A/RT_gxa_mem_Tbl.v at d49bd1db505: module paths lib.A -> lib.B; 15 image numerals moved to fuzz_reply.asan-ubsan by symbol + offset, each checked against that image (CHAINB-numerals.tsv sha256 3cedf5e564f7; internal record). *) (* fuzz_reply.asan-ubsan numerals of GXA's memcpy and memset call contracts (RT_gxa_calls_mem.v): the image B twin of
   lib/A/RT_gxa_mem_Tbl.v.  lib/A/RT_gxa_mem_Tbl.v's header records how the image A values were paired, by code
   bytes, with a working branch 840c4afa7e2 (fuzz_state.asan) for the eighteen files those contracts
   compose: lib/{A,B}/Bz/A/{I_memcpyw, I_memcpyw2, I_amemcpyw, I_amemcpyw2, I_amemcpy, I_memcpy, I_memsetw, F_memset,
   I_imemset}.v, lib/{A,B}/Prog/{memcpy_c, memcpy, memcpy_same_c, memcpy_same, memset_c, memset}.v,
   lib/{A,B}/R_memset.v, lib/{A,B}/Strw/{STRW_tac, STRWaj3}.v.

   PAIRING A -> B.  Each fuzz_reply.asan region below has the same symbol at the same offset in the asan-ubsan
   image's symbol table and was decoded instruction by instruction on both ELFs (fuzz_reply.asan
   sha256 42c58610e125e0b47770217f7175ffe2f23ed5ee1399b3e81539eff364611d5a; fuzz_reply.asan-ubsan
   sha256 10ffb5f9202ae2bdb01b7a49df9866843a6a6a0e0c50bc67cdba6ce2f6d3cf2c): same instruction count, same lengths,
   every word equal except the immediates (pc-relative fields).
     fuzz_reply.asan                     fuzz_reply.asan-ubsan  delta    what
     0x52720, 0x52724                    0x52778, 0x5277c       +0x58    trampolines memset, memcpy (`j` each, words equal)
     [0x52728, 0x52bc4)   295 insns      [0x52780, 0x52c1c)     +0x58    __asan_memcpy
     [0x53174, 0x53464)   188 insns      [0x531cc, 0x534bc)     +0x58    ___interceptor_memset
     [0x53464, 0x53a54)   380 insns      [0x534bc, 0x53aac)     +0x58    ___interceptor_memcpy
     [0x964cc, 0x968d0)   257 insns      [0x96a4c, 0x96e50)     +0x580   musl memcpy (every word equal)
     [0x96900, 0x969f8)    62 insns      [0x96e80, 0x96f78)     +0x580   musl memset (every word equal)
   Data cells, each the same symbol (or the .got slot holding the same symbol) in both images:
     .got 0x9d9d0 -> 0x9df50 (value: the shadow cell 0xa60b8 -> 0xa6638); .got 0x9e538 -> 0x9eab8 (value: the
     replace_intrin flag byte 0xa6d99 -> 0xa7319); REAL(memcpy) 0x9f868 -> 0x9fde8 (value: musl memcpy 0x964cc ->
     0x96a4c); REAL(memset) 0x9f870 -> 0x9fdf0 (value: musl memset 0x96900 -> 0x96e80).  lib/B/YF0m.v holds the same
     B cells.  Every B numeral of the eighteen files and of this one is in CHAINB-numerals.tsv (sha256 3cedf5e564f7; internal record).

   STACK.  The paired code is identical, so the depths are image A's, measured again here: the memcpy interceptor's
   frame is 0x7f0 + 0x80 = 2160 B (0x534bc, 0x534ec), the memset interceptor's 0x7f0 + 0x70 = 2144 B (0x531cc,
   0x531f4); each calls __asan_region_is_poisoned 0x559b4 (frame 0x40) and from it mem_is_zero 0x6578c (frame 0x10)
   on the path the walks take, so 2160 + 80 = 2240 and 2144 + 80 = 2224.  musl memcpy / memset are leaves with no
   frame.  GXA's COPY_DEPTH 2240 (CopyCall.v:8) and SET_DEPTH 2224 (SetCall.v:8) are exactly these depths: no slack
   on either side.

   The fuzz_state.asan column of image A's table is not repeated: every image B value here is read from
   fuzz_reply.asan-ubsan itself. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib Require Import ImageA.
Open Scope Z_scope.

(* the entries of the two call contracts *)
Definition MC_TRAMP : Z := 0x5277c.   (* __interceptor_trampoline_memcpy: `j 0x534bc`; GXA's memcpy call target *)
Definition MC_ICPT : Z := 0x534bc.    (* ___interceptor_memcpy: imemcpy_spec's entry (I_memcpy.v) *)
Definition MS_TRAMP : Z := 0x52778.   (* __interceptor_trampoline_memset: `j 0x531cc`; GXA's memset call target *)
Definition MS_ICPT : Z := 0x531cc.    (* ___interceptor_memset: imemset_spec's entry (I_imemset.v) *)

(* Build identity: this is fuzz_reply.asan-ubsan.  The first words of main 0x81ea4 and LLVMFuzzerTestOneInput 0x84408
   (as RT_asan_memmove.v:63-67), the two trampolines' `j` words, the first word of each interceptor
   (`addi sp, sp, -2032`), and the first word of musl memcpy 0x96a4c (`andi a3, a1, 3`) and of musl memset 0x96e80
   (`beqz a2, +0xf4`), the REAL() targets the walks call. *)
Lemma rt_gxa_mem_build_identity :
  fetch_word asegs (Z_to_bv 64 0x81ea4) = Some (Z_to_bv 32 0xfb010113) /\
  fetch_word asegs (Z_to_bv 64 0x84408) = Some (Z_to_bv 32 0xec010113) /\
  fetch_word asegs (Z_to_bv 64 MC_TRAMP) = Some (Z_to_bv 32 0x5410006f) /\
  fetch_word asegs (Z_to_bv 64 MS_TRAMP) = Some (Z_to_bv 32 0x2550006f) /\
  fetch_word asegs (Z_to_bv 64 MC_ICPT) = Some (Z_to_bv 32 0x81010113) /\
  fetch_word asegs (Z_to_bv 64 MS_ICPT) = Some (Z_to_bv 32 0x81010113) /\
  fetch_word asegs (Z_to_bv 64 0x96a4c) = Some (Z_to_bv 32 0x0035f693) /\
  fetch_word asegs (Z_to_bv 64 0x96e80) = Some (Z_to_bv 32 0x0e060a63).
Proof. repeat split; vm_compute; reflexivity. Qed.
