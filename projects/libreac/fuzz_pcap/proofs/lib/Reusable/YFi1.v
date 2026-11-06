From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YFi1.v, with its module paths changed and its addresses moved to libreac/fuzz_pcap's ASan build. *)
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x YFl0 YFhy.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 6. Set Printing Width 250.
Definition aNP : nat := 62.
Definition FK : facts := mkFacts
[ (2%nat, mkAF (kHighMemBeg + ASTACK) kHighMemEnd 4);
(10%nat, mkAF 0 48 0);
(aT, mkAF 4096 (CEIL_MAX - 4096) 12)       ;
(aC, mkAF 4096 (CEIL_MAX - 256) 3)         ;
(aSB, mkAF kHighMemBeg CEIL_MAX 16)         ;
(aTOP, mkAF kHighMemBeg kHighMemEnd 12);
(aLEN, mkAF 1 30 0);
(aJ0, mkAF 0 (2 ^ 64 - 1) 0);
(aR8, mkAF 8 48 3);
(aCL, mkAF 1 2 0);
(aP, mkAF 4096 CEIL_MAX 4)                  ;
(aCNT, mkAF 1 16 0);
(aV, mkAF 0 (2 ^ 28 - 1) 0);
(aCSZ, mkAF 0 (2 ^ 64 - 1) 0);
(aPV, mkAF 4096 CEIL_MAX 2)                 ;
(aK, mkAF kHighMemBeg CEIL_MAX 5)            ;
(aJB, mkAF 0 255 0);
(aSHB, mkAF 0x7fff8000 0x7fff8000 12);
(aSK, mkAF 0x2008fff7000 0x10007fff7fff 2);
(aJ1, mkAF 0 (2 ^ 64 - 1) 0); (aJ2, mkAF 0 (2 ^ 64 - 1) 0); (aJ3, mkAF 0 (2 ^ 64 - 1) 0);
(aSSLOT, mkAF 4096 CEIL_MAX 3)              ;
(aJ4, mkAF 0 (2 ^ 64 - 1) 0);
(aPB, mkAF 0x2008fff7000 0x10007fff7fff 0);
(aN8D, mkAF 0 48 3);
(aCNT8, mkAF 0 6 0);
(aNP, mkAF 1 48 0);
(aND, mkAF 24 64 3) ] [] [].
Definition REG0K : smem :=
[
YP09.mkRegion (Some 2%nat) (- ASTACK) 0 (- ASTACK) 0 [];
lit1 (symaddr Symbols.AsanUbsan.s__ZN6__asanL11asan_initedE) 1; lit4 (symaddr Symbols.AsanUbsan.s__ZN6__asanL19malloc_context_sizeE) 30; lit8 (symaddr (Symbols.AsanUbsan.Sec.s_got + 0x50)%Z) (symaddr Symbols.AsanUbsan.s__ZN11__sanitizer21common_flags_dont_useE); lit8 (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer21common_flags_dont_useE + 0x20)%Z) 0x1e00010000;
lit1 (symaddr Symbols.AsanUbsan.s__ZN11__sanitizerL18rss_limit_exceededE) 0; lit1 (symaddr Symbols.AsanUbsan.s__ZN6__asanL14tsd_key_initedE) 1; lit4 (symaddr Symbols.AsanUbsan.s__ZN6__asanL7tsd_keyE) 0; lit1 (symaddr Symbols.AsanUbsan.s__ZN6__asanL17can_poison_memoryE) 1;
atom8 (symaddr (Symbols.AsanUbsan.s__ZN6__asanL8instanceE + 0x20)%Z) aSB; lits8 (symaddr (Symbols.AsanUbsan.s__ZN6__asanL8instanceE + 0xe20)%Z) [0x10000000000; 0x108000010];
lit8 (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xd0)%Z) 0x218a392cd3d5dbf; lits8 (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x140)%Z) CTZ_TABLE; lits8 (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x240)%Z) CTZ_TABLE; lit8 (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x48)%Z) 0xcc6e96b9cc6e96b9;
lit8 (symaddr (Symbols.AsanUbsan.Sec.s_got + 0x58)%Z) (symaddr Symbols.AsanUbsan.s__ZN6__asan28asan_flags_dont_use_directlyE); lit8 (symaddr (Symbols.AsanUbsan.Sec.s_got + 0x60)%Z) (symaddr Symbols.AsanUbsan.s___asan_shadow_memory_dynamic_address); lit8 (symaddr (Symbols.AsanUbsan.Sec.s_got + 0x68)%Z) (symaddr Symbols.AsanUbsan.s__ZN6__asan10kMidMemBegE); lit8 (symaddr (Symbols.AsanUbsan.Sec.s_got + 0x70)%Z) (symaddr Symbols.AsanUbsan.s__ZN6__asan10kMidMemEndE); lit8 (symaddr (Symbols.AsanUbsan.Sec.s_got + 0x78)%Z) (symaddr Symbols.AsanUbsan.s__ZN6__asan11kHighMemEndE);
lit8 (symaddr (Symbols.AsanUbsan.Sec.s_got + 0x80)%Z) (symaddr Symbols.AsanUbsan.s__ZN14__interception11real_memsetE); lit8 (symaddr (Symbols.AsanUbsan.Sec.s_got + 0x40)%Z) (symaddr Symbols.AsanUbsan.s__ZN11__sanitizer14PageSizeCachedE); lit8 (symaddr Symbols.AsanUbsan.s__ZN11__sanitizer14PageSizeCachedE) 4096; lit8 (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer21common_flags_dont_useE + 0x78)%Z) 0xffffffffffffffff;
atom8 (symaddr Symbols.AsanUbsan.s___asan_shadow_memory_dynamic_address) aSHB; lit8 (symaddr Symbols.AsanUbsan.s__ZN6__asan11kHighMemEndE) 0x7fffffffffff; lit8 (symaddr Symbols.AsanUbsan.s__ZN6__asan10kMidMemBegE) 0; lit8 (symaddr Symbols.AsanUbsan.s__ZN6__asan10kMidMemEndE) 0; lit8 (symaddr Symbols.AsanUbsan.s__ZN14__interception11real_memsetE) (symaddr Symbols.AsanUbsan.s_memset);
lits8 (symaddr (Symbols.AsanUbsan.s__ZN6__asan28asan_flags_dont_use_directlyE + 0x28)%Z) [0x100000000000; 0xbe00000000]; lits8 (symaddr (Symbols.AsanUbsan.s__ZN6__asan28asan_flags_dont_use_directlyE + 0x48)%Z) [0x1000100000000; 0x101010101000001];
lit8 (symaddr (Symbols.AsanUbsan.Sec.s_got + 0xcb8)%Z) 0x10; lit4 (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0xd8)%Z) 0  ; lit8 (symaddr Symbols.AsanUbsan.s__ZN11__sanitizerL7MFHooksE) 0;
lit8 (TFIB_TP - 88) TFIB_TSD; atom8 TFIB_TSD aC;
YP09.mkRegion (Some aC) 0 160 0 0 [YP09.mkChunk 8 (CVal 4 (SLit 0)); YP09.mkChunk 152 (CVal 8 (SOff aT 0))];
YP09.mkRegion (Some aT) 0 208 0 0 [YP09.mkChunk 0 (CVal 8 (SOff aC 0)); YP09.mkChunk 8 (CVal 8 (SOff aTOP 0));
YP09.mkChunk 16 (CVal 8 (SOff aTOP (- kStackSpan))); YP09.mkChunk 40 (CVal 1 (SLit 0))];
YP09.mkRegion (Some aT) 2768 2800 2768 2800 [YP09.mkChunk 2784 (CVal 8 (SOff aJ0 0))];
YP09.mkRegion (Some aT) t_unwinding (t_unwinding + 1) t_unwinding (t_unwinding + 1) [YP09.mkChunk t_unwinding (CVal 1 (SLit 0))];
YP09.mkRegion (Some aT) 2800 2824 2800 2824 [YP09.mkChunk 2800 (CVal 8 (SOff aJ1 0)); YP09.mkChunk 2808 (CVal 8 (SOff aJ2 0));
YP09.mkChunk 2816 (CVal 8 (SOff aJ3 0))];
YP09.mkRegion (Some aSSLOT) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff aJ4 0))];
YP09.mkRegion (Some aP) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff aCNT 0))];
YP09.mkRegion (Some aP) 4 16 0 0 [YP09.mkChunk 8 (CVal 8 (SOff aCSZ 0))];
YP09.mkRegion (Some aPV) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff aV 0))];
YP09.mkRegion (Some aK) 0 16 0 16 [YP09.mkChunk 1 (CVal 1 (SOff aJB 0))];
YP09.mkRegion (Some aSK) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 250))] ].
Definition SS0K : sstate := mkSS (symaddr Symbols.AsanUbsan.s___wrap_malloc) (sr_set sr_atoms 4%bv (SLit TFIB_TP)) REG0K None FK.
