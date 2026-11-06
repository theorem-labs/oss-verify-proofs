From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFkp.v, with its module paths changed and its addresses moved to libreac/fuzz_pcap's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFhy.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 6. Set Printing Width 250.
Definition rT : nat := 32.   Definition rC : nat := 33.   Definition rSB : nat := 34.  Definition rTOP : nat := 35.
Definition rCL : nat := 36.  Definition rP : nat := 37.   Definition rMAX : nat := 38. Definition rN : nat := 39.  Definition rCSZ : nat := 40.
Definition rRG : nat := 41.  Definition rRB : nat := 42.  Definition rFA : nat := 43.
Definition rNF : nat := 44.  Definition rMF : nat := 45.  Definition rAU : nat := 46.  Definition rMU : nat := 47.
Definition rSHB : nat := 48. Definition rJ64 : nat := 49. Definition rJNA : nat := 50. Definition rJNF : nat := 51.
Definition rJSM : nat := 52. Definition rJM1 : nat := 53. Definition rJM2 : nat := 54.
Definition aHAVR : nat := 64.
Definition FR : facts := mkFacts
[ (2%nat, mkAF (kHighMemBeg + 1024) kHighMemEnd 4);
(rT, mkAF 4096 (CEIL_MAX - 4096) 12)       ;
(rC, mkAF 4096 (CEIL_MAX - 256) 3)         ;
(rSB, mkAF kHighMemBeg CEIL_MAX 16);
(rTOP, mkAF kHighMemBeg kHighMemEnd 12);
(rCL, mkAF 1 31 0);
(rP, mkAF 4096 CEIL_MAX 4)                  ;
(rMAX, mkAF 2 16 1);
(rN, mkAF 1 8 0);
(rCSZ, mkAF 16 131072 4);
(rRG, mkAF kHighMemBeg CEIL_MAX 7);
(rRB, mkAF kHighMemBeg CEIL_MAX 16);
(rFA, mkAF kHighMemBeg CEIL_MAX 12);
(rNF, mkAF 0 (2 ^ 27) 0);
(rMF, mkAF 0 (2 ^ 29) 18);
(rAU, mkAF 0 3758096384 4);
(rMU, mkAF 0 3758096384 18);
(rSHB, mkAF 0x7fff8000 0x7fff8000 12);
(rJ64, mkAF 0 (2 ^ 32 - 1) 0);
(rJNA, mkAF 0 (2 ^ 64 - 1) 0); (rJNF, mkAF 0 (2 ^ 64 - 1) 0);
(rJSM, mkAF 0 (2 ^ 64 - 1) 0); (rJM1, mkAF 0 (2 ^ 64 - 1) 0); (rJM2, mkAF 0 (2 ^ 64 - 1) 0) ] [] [].
Definition REG0R : smem :=
[
YP09.mkRegion (Some 2%nat) (- 1024) 0 (- 1024) 0 [];
lit1 (symaddr Symbols.Asan.s__ZN6__asanL11asan_initedE) 1; lit8 (symaddr (Symbols.Asan.Sec.s_got + 0x50)%Z) (symaddr Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE); lit1 (symaddr Symbols.Asan.s__ZN6__asanL14tsd_key_initedE) 1; lit4 (symaddr Symbols.Asan.s__ZN6__asanL7tsd_keyE) 0; lit1 (symaddr Symbols.Asan.s__ZN6__asanL17can_poison_memoryE) 1;
atom8 (symaddr (Symbols.Asan.s__ZN6__asanL8instanceE + 0x20)%Z) rSB;
YP09.mkRegion None (symaddr (Symbols.Asan.s__ZN6__asanL8instanceE + 0x30)%Z) (symaddr (Symbols.Asan.s__ZN6__asanL8instanceE + 0x38)%Z) 0 0 [YP09.mkChunk (symaddr (Symbols.Asan.s__ZN6__asanL8instanceE + 0x30)%Z) (CVal 8 (SOff rSB (2 ^ 37)))];
lit8 (symaddr (Symbols.Asan.s__ZN6__asanL8instanceE + 0x38)%Z) 0; lit8 (symaddr (Symbols.Asan.s__ZN6__asanL8instanceE + 0x28)%Z) 0xffffffff;
lit8 (symaddr (Symbols.Asan.Sec.s_rodata + 0xc0)%Z) 0xafffff00000fffff; lits8 (symaddr (Symbols.Asan.Sec.s_rodata + 0x140)%Z) CTZ_TABLE; lits8 (symaddr (Symbols.Asan.Sec.s_rodata + 0x240)%Z) CTZ_TABLE;
lit8 (symaddr (Symbols.Asan.Sec.s_got + 0x58)%Z) (symaddr Symbols.Asan.s__ZN6__asan28asan_flags_dont_use_directlyE); lit8 (symaddr (Symbols.Asan.Sec.s_got + 0x60)%Z) (symaddr Symbols.Asan.s___asan_shadow_memory_dynamic_address); lit8 (symaddr (Symbols.Asan.Sec.s_got + 0x68)%Z) (symaddr Symbols.Asan.s__ZN6__asan10kMidMemBegE); lit8 (symaddr (Symbols.Asan.Sec.s_got + 0x70)%Z) (symaddr Symbols.Asan.s__ZN6__asan10kMidMemEndE); lit8 (symaddr (Symbols.Asan.Sec.s_got + 0x78)%Z) (symaddr Symbols.Asan.s__ZN6__asan11kHighMemEndE);
lit8 (symaddr (Symbols.Asan.Sec.s_got + 0x80)%Z) (symaddr Symbols.Asan.s__ZN14__interception11real_memsetE); lit8 (symaddr (Symbols.Asan.Sec.s_got + 0x40)%Z) (symaddr Symbols.Asan.s__ZN11__sanitizer14PageSizeCachedE); lit8 (symaddr Symbols.Asan.s__ZN11__sanitizer14PageSizeCachedE) 4096; lit8 (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0x78)%Z) 0xffffffffffffffff; lit8 (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0x90)%Z) 0;
atom8 (symaddr Symbols.Asan.s___asan_shadow_memory_dynamic_address) rSHB; lit8 (symaddr Symbols.Asan.s__ZN6__asan11kHighMemEndE) 0x7fffffffffff; lit8 (symaddr Symbols.Asan.s__ZN6__asan10kMidMemBegE) 0; lit8 (symaddr Symbols.Asan.s__ZN6__asan10kMidMemEndE) 0; lit8 (symaddr Symbols.Asan.s__ZN14__interception11real_memsetE) (symaddr Symbols.Asan.s_memset);
lit4 (symaddr (Symbols.Asan.s_builtin_tls + 0xd8)%Z) 0; lit8 (symaddr Symbols.Asan.s__ZN11__sanitizerL7MFHooksE) 0;
lit8 (TFIB_TP - 88) TFIB_TSD; atom8 TFIB_TSD rC;
YP09.mkRegion (Some rC) 0 160 0 0 [YP09.mkChunk 152 (CVal 8 (SOff rT 0))];
YP09.mkRegion (Some rT) 2768 2800 2768 2800 [YP09.mkChunk 2792 (CVal 8 (SOff rJSM 0))];
YP09.mkRegion (Some rT) 2872 2888 2872 2888 [YP09.mkChunk 2872 (CVal 8 (SOff rJM1 0)); YP09.mkChunk 2880 (CVal 8 (SOff rJM2 0))];
YP09.mkRegion (Some rP) 0 16 0 16 [YP09.mkChunk 0 (CVal 4 (SLit 0)); YP09.mkChunk 4 (CVal 4 (SOff rMAX 0)); YP09.mkChunk 8 (CVal 8 (SOff rCSZ 0))];
YP09.mkRegion (Some rRG) 0 128 0 128
[YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0)); YP09.mkChunk 16 (CVal 8 (SOff rNF 0));
YP09.mkChunk 24 (CVal 8 (SOff rMF 0)); YP09.mkChunk 32 (CVal 8 (SOff rAU 0)); YP09.mkChunk 40 (CVal 8 (SLit 0));
YP09.mkChunk 48 (CVal 8 (SOff rMU 0)); YP09.mkChunk 56 (CVal 8 (SLit 0)); YP09.mkChunk 64 (CVal 4 (SOff rJ64 0));
YP09.mkChunk 68 (CVal 1 (SLit 0)); YP09.mkChunk 72 (CVal 8 (SOff rJNA 0)); YP09.mkChunk 80 (CVal 8 (SOff rJNF 0))] ].
Definition REGS0R : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 4%bv (SLit TFIB_TP)) 10%bv (SOff rT t_cache)) 11%bv (SOff rP 0)) 12%bv (SLit (symaddr Symbols.Asan.s__ZN6__asanL8instanceE))) 13%bv (SOff rCL 0).
Definition SS0R : sstate := mkSS (symaddr Symbols.Asan.s__ZN11__sanitizer30SizeClassAllocator64LocalCacheINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEEE6RefillEPNS7_8PerClassEPS6_m) REGS0R REG0R None FR.
