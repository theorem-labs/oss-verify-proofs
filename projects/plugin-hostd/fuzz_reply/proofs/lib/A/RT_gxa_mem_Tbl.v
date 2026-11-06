(* fuzz_reply.asan numerals of GXA's memcpy and memset call contracts (RT_gxa_calls_mem.v), and the relocation table of
   the eighteen files those contracts compose, copied from a working branch 840c4afa7e2
   (proofs/omx-clap-core/fuzz_state/lib): lib/A/Bz/A/{I_memcpyw, I_memcpyw2, I_amemcpyw, I_amemcpyw2, I_amemcpy,
   I_memcpy, I_memsetw, F_memset, I_imemset}.v, lib/A/Prog/{memcpy_c, memcpy, memcpy_same_c, memcpy_same, memset_c,
   memset}.v, lib/A/R_memset.v, lib/A/Strw/{STRW_tac, STRWaj3}.v.

   PAIRING (by code bytes, never by symbol name).  Each fuzz_state.asan region below was decoded instruction by
   instruction on both ELFs (fuzz_state.asan sha256 64b53ff86172bb07f93f146e67b81a0354bca88e0a580e93fb1da01406fb76e0,
   the pinned image of omx-clap-core/fuzz_state; fuzz_reply.asan
   sha256 42c58610e125e0b47770217f7175ffe2f23ed5ee1399b3e81539eff364611d5a): same instruction count, same lengths, and
   every word equal except the pc-relative fields (auipc / jal immediates and the low 12 bits of an auipc's consumer).
     fuzz_state.asan                     fuzz_reply.asan        delta    what
     0x51d18, 0x51d1c                    0x52720, 0x52724       +0xa08   trampolines memset, memcpy (`j` each)
     [0x51d20, 0x521bc)   295 insns      [0x52728, 0x52bc4)     +0xa08   __asan_memcpy
     [0x523fc, 0x526ec)   188 insns      [0x53174, 0x53464)     +0xd78   ___interceptor_memset
     [0x526ec, 0x52cdc)   380 insns      [0x53464, 0x53a54)     +0xd78   ___interceptor_memcpy
     [0x98a20, 0x98e24)   257 insns      [0x964cc, 0x968d0)     -0x2554  musl memcpy
     [0x98e24, 0x98f1c)    62 insns      [0x96900, 0x969f8)     -0x2524  musl memset
   Data cells, each paired by the auipc pair that loads it in the paired code above, and its value read from both ELFs:
     .got 0x9f6f0 -> 0x9d9d0 (value: the shadow cell 0xa7f38 -> 0xa60b8); .got 0xa0258 -> 0x9e538 (value: the
     replace_intrin flag byte 0xa8c19 -> 0xa6d99); REAL(memcpy) 0xa1568 -> 0x9f868 (value: musl memcpy 0x98a20 ->
     0x964cc); REAL(memset) 0xa1570 -> 0x9f870 (value: musl memset 0x98e24 -> 0x96900).  The same pairs are in
     RT_kit.v (R1) and AB1w.v:143-148 / AE2y.v:74 (RelocA).
   Counts over the eighteen files: 97 code numerals and 14 data numerals moved, 108 geometry constants kept
   (0x7fff8000 = 2147450880, 0x10007fff8000, 2^64 - 1 / - 4 / - 8, 2^64, 2^16, 2^24); no `%bv` encoding and no
   donor symbol key occurs in them.  The tool relocate-walk.py (sha256 d480bb87bb70; internal record) maps 0x523fc to 0x52e04, which is wrong
   (no trampoline jumps there; seven `jal ra` sites call it): it was not used.

   STACK.  The paired code is identical, so the depths are the donor's, measured on fuzz_reply.asan: the memcpy
   interceptor's frame is 0x7f0 + 0x80 = 2160 B (0x53464, 0x53494), the memset interceptor's 0x7f0 + 0x70 = 2144 B
   (0x53174, 0x5319c); each calls __asan_region_is_poisoned 0x5595c (frame 0x40) and from it mem_is_zero 0x65734
   (frame 0x10) on the path the walks take, so 2160 + 80 = 2240 and 2144 + 80 = 2224.  musl memcpy / memset are
   leaves with no frame.  GXA's COPY_DEPTH 2240 (CopyCall.v:8) and SET_DEPTH 2224 (SetCall.v:8) are exactly these
   depths: no slack on either side. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib Require Import ImageA.
Open Scope Z_scope.

(* the entries of the two call contracts *)
Definition MC_TRAMP : Z := 0x52724.   (* __interceptor_trampoline_memcpy: `j 0x53464`; GXA's memcpy call target *)
Definition MC_ICPT : Z := 0x53464.    (* ___interceptor_memcpy: imemcpy_spec's entry (I_memcpy.v) *)
Definition MS_TRAMP : Z := 0x52720.   (* __interceptor_trampoline_memset: `j 0x53174`; GXA's memset call target *)
Definition MS_ICPT : Z := 0x53174.    (* ___interceptor_memset: imemset_spec's entry (I_imemset.v) *)

(* Build identity: this is fuzz_reply.asan.  The first words of main 0x81e4c and LLVMFuzzerTestOneInput 0x840b0
   (as RT_asan_memmove.v:63-67), the two trampolines' `j` words, the first word of each interceptor
   (`addi sp, sp, -2032`), and the first word of musl memcpy 0x964cc (`andi a3, a1, 3`) and of musl memset 0x96900
   (`beqz a2, +0xf4`), the REAL() targets the walks call. *)
Lemma rt_gxa_mem_build_identity :
  fetch_word asegs (Z_to_bv 64 0x81e4c) = Some (Z_to_bv 32 0xfb010113) /\
  fetch_word asegs (Z_to_bv 64 0x840b0) = Some (Z_to_bv 32 0xec010113) /\
  fetch_word asegs (Z_to_bv 64 MC_TRAMP) = Some (Z_to_bv 32 0x5410006f) /\
  fetch_word asegs (Z_to_bv 64 MS_TRAMP) = Some (Z_to_bv 32 0x2550006f) /\
  fetch_word asegs (Z_to_bv 64 MC_ICPT) = Some (Z_to_bv 32 0x81010113) /\
  fetch_word asegs (Z_to_bv 64 MS_ICPT) = Some (Z_to_bv 32 0x81010113) /\
  fetch_word asegs (Z_to_bv 64 0x964cc) = Some (Z_to_bv 32 0x0035f693) /\
  fetch_word asegs (Z_to_bv 64 0x96900) = Some (Z_to_bv 32 0x0e060a63).
Proof. repeat split; vm_compute; reflexivity. Qed.
