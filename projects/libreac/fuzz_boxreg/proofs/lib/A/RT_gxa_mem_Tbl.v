(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: REGENERATED for libreac/fuzz_boxreg's asan from plugin-hostd/fuzz_reply's
   lib/A/RT_gxa_mem_Tbl.v (a working branch 86b50358d34): the four entries and the build identity
   re-read from fuzz_boxreg.asan (nm + bytes); the rest of the file is the donor's form. *)
(* fuzz_boxreg.asan numerals of GXA's memcpy and memset call contracts (RT_gxa_calls_mem.v).

   PAIRING.  fuzz_reply.asan's interceptor and musl code that RT_gxa_calls_mem.v composes (the donor's eighteen
   files, relocated from a working branch 840c4afa7e2) pairs with fuzz_boxreg.asan's instruction for instruction
   (objdump, every instruction equal modulo numerals; same counts): ___interceptor_memcpy 380 insns at 0x51a64,
   ___interceptor_memset 188 at 0x51774, __asan_region_is_poisoned 209, mem_is_zero 45, MemToShadow 395,
   AsanInited 6, musl memcpy 257 at 0x92184, musl memset 62 at 0x92588.  The file's numerals were moved
   by symbol + offset (port_addr_check 5033540ba83b predict mode), not by a uniform delta.

   STACK, measured on fuzz_boxreg.asan: the memcpy interceptor's frame is 2032 + 128 = 2160 B, the memset
   interceptor's 2032 + 112 = 2144 B; __asan_region_is_poisoned frame 64, mem_is_zero 16 on the walks' path; so
   2160 + 80 = 2240 = GXA's COPY_DEPTH (CopyCall.v:8) and 2144 + 80 = 2224 = SET_DEPTH (SetCall.v:8), as on fuzz_reply. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Bz.Lib Require Import ImageA.
Open Scope Z_scope.

(* the entries of the two call contracts *)
Definition MC_TRAMP : Z := 0x51094.   (* __interceptor_trampoline_memcpy: `j 0x51a64`; GXA's memcpy call target *)
Definition MC_ICPT : Z := 0x51a64.    (* ___interceptor_memcpy: imemcpy_spec's entry (I_memcpy.v) *)
Definition MS_TRAMP : Z := 0x51090.   (* __interceptor_trampoline_memset: `j 0x51774`; GXA's memset call target *)
Definition MS_ICPT : Z := 0x51774.    (* ___interceptor_memset: imemset_spec's entry (I_imemset.v) *)

(* Build identity: this is fuzz_boxreg.asan.  The first words of main 0x7faac and LLVMFuzzerTestOneInput 0x7ff4c,
   the two trampolines' `j` words, the first word of each interceptor (`addi sp, sp, -2032`), and the first word of
   musl memcpy 0x92184 and of musl memset 0x92588, the REAL() targets the walks call. *)
Lemma rt_gxa_mem_build_identity :
  fetch_word asegs (Z_to_bv 64 0x7faac) = Some (Z_to_bv 32 0xfb010113) /\
  fetch_word asegs (Z_to_bv 64 0x7ff4c) = Some (Z_to_bv 32 0xf0010113) /\
  fetch_word asegs (Z_to_bv 64 MC_TRAMP) = Some (Z_to_bv 32 0x1d10006f) /\
  fetch_word asegs (Z_to_bv 64 MS_TRAMP) = Some (Z_to_bv 32 0x6e40006f) /\
  fetch_word asegs (Z_to_bv 64 MC_ICPT) = Some (Z_to_bv 32 0x81010113) /\
  fetch_word asegs (Z_to_bv 64 MS_ICPT) = Some (Z_to_bv 32 0x81010113) /\
  fetch_word asegs (Z_to_bv 64 0x92184) = Some (Z_to_bv 32 0x0035f693) /\
  fetch_word asegs (Z_to_bv 64 0x92588) = Some (Z_to_bv 32 0x0e060a63).
Proof. repeat split; vm_compute; reflexivity. Qed.
