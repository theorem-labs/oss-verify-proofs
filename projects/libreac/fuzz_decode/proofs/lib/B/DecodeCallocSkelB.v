(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AFhy.v (SS0, REG0, FG: the symbolic
   state at the entry of cgif's malloc wrapper) to libreac/fuzz_decode's calloc wrapper chain in image A
   (lib/A/DecodeCallocSkel.v), and from there to image B (fuzz_decode.asan-ubsan); module paths changed. *)
(* The symbolic states of the calloc walk of image B: the state at the entry of the trampoline, and the state the walk
   reaches at the wrapper's first call.  Data only; lib/A/DecodeCallocSeedB.v proves the entry state from the unit's
   call precondition and runs the walk from the one to the other.

   Addresses, read with capstone (pyelftools for the PT_LOAD map) from the ORIGINAL unstripped binary
   fuzz_decode.asan-ubsan:

     0x51fb4  __interceptor_trampoline_calloc   `j 0x523b0` (word 0x3fc0006f): the 4-byte jump into the wrapper.
     0x523b0  ___interceptor_calloc, the wrapper:
       0x523b0 `addi sp, sp, -0x7f0`
       0x523b4 `sd ra, 0x7e8(sp)`   0x523b8 `sd s0, 0x7e0(sp)`   0x523bc `sd s1, 0x7d8(sp)`   0x523c0 `sd s2, 0x7d0(sp)`
       0x523c4 `sd s3, 0x7c8(sp)`   0x523c8 `sd s4, 0x7c0(sp)`   0x523cc `sd s5, 0x7b8(sp)`   0x523d0 `sd s6, 0x7b0(sp)`
       0x523d4 `addi s0, sp, 0x7f0`  (s0 = the entry sp)
       0x523d8 `addi sp, sp, -0x70`  (the frame is 0x7f0 + 0x70 = 2144 bytes)
       0x523dc `mv s3, ra`   0x523e0 `mv s1, a1` (sz)   0x523e4 `mv s2, a0` (nm)
       0x523e8 `jal 0x590f8` (word 0x511060ef): the call of TryAsanInitFromRtl, the wrapper's first call.
     0x31c20  __asan::asan_calloc, which the wrapper calls at 0x524f0 with sp = entry sp - 2144, opens a 48-byte frame
              (0x31c20 `addi sp, sp, -0x30`).

   The entry state.  Every register is its own atom (atom i is the value of x_i at the trampoline), the sp atom 2 has
   the range and alignment of the call precondition, and memory holds one region: the stack window
   [sp - ASTACK, sp), writable, empty, as cgif's REG0 starts (AFhy.v:82).  ASTACK = 16384 (YG0d.v:18) covers the
   wrapper's 2144 bytes, asan_calloc's 48 bytes below them, and the callees below those; the walk to the first call
   reads no other memory, so the state names no image cell.  cgif's REG0 also carries the cells its later segments
   hand to the runtime entries (AFhy.v:83-106); a region for such a cell can be added at the call that reads it
   (YN2j.v:36 st_ok_add_region, as cgif's segA adds its frame regions, AFip.v:371-417), with the cell's value read from
   the entry memory through the frame conjunct of DecodeCallocSeedB.at_C1B (memory outside the stack window is the
   entry memory). *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YP0m YP09 YP0l YI04 YG0f YG0d.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The wrapper's first call site (image B); the trampoline and the wrapper are DecodeCalloc.v's DEC_B_wrap_calloc
   (0x51fb4) and DEC_B_icpt_calloc (0x523b0), and the callee, TryAsanInitFromRtl at 0x590f8, is DecodeCallocRt.v's
   DEC_B_TryAsanInitFromRtl. *)
Definition DEC_B_calloc_call1 : Z := 0x523e8.
(* The wrapper's frame: 0x523b0 `addi sp, sp, -0x7f0` and 0x523d8 `addi sp, sp, -0x70`. *)
Definition ICPT_FRAMEB : Z := 0x7f0 + 0x70.

(* The entry state at the trampoline. *)
Definition REG0B : smem := [YP09.mkRegion (Some 2%nat) (- ASTACK) 0 (- ASTACK) 0 []].
Definition FG0B : facts := mkFacts [(2%nat, mkAF (kHighMemBeg + ASTACK) kHighMemEnd 4)] [] [].
Definition SS0B : sstate := mkSS DEC_B_wrap_calloc sr_atoms REG0B None FG0B.

(* The state at 0x523e8, before the `jal`: sp = entry sp - 2144, s0 = the entry sp, s1 = sz (atom 11), s2 = nm
   (atom 10), s3 = ra (atom 1); the eight 8-byte stores of 0x523b4..0x523d0 are chunks of the stack region at
   entry sp - 8 (ra) down to entry sp - 64 (s6).  Every other register still holds its entry value. *)
Definition SR_C1B : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 2%bv (SOff 2 (- ICPT_FRAMEB))) 8%bv (SOff 2 0))
9%bv (SOff 11 0)) 18%bv (SOff 10 0)) 19%bv (SOff 1 0).
Definition REG_C1B : smem :=
[YP09.mkRegion (Some 2%nat) (- ASTACK) 0 (- ASTACK) 0
[YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]].
Definition SS_C1B : sstate := mkSS DEC_B_calloc_call1 SR_C1B REG_C1B None FG0B.
