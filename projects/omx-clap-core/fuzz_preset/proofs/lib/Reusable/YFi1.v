(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YFi1.v, with its module paths changed; relocated to fuzz_preset asan-ubsan (pin f8f98a95bc52), map sha256 69a6a2e91fb7, checker port_addr_check.py 39e67a7eb166. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgCellsB.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x YFl0 YFhy.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
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
lit1 B_ASAN_INITED_CELL 1; lit4 B_MALLOC_CONTEXT_SIZE_CELL 30; lit8 B_GOT_0X50 B_GOT_OFF_50_VAL; lit8 B_COMMON_FLAGS_DONT_USE_OFF_20_CELL 0x1e00010000;
lit1 B_RSS_LIMIT_EXCEEDED_CELL 0; lit1 B_TSD_KEY_INITED_CELL 1; lit4 B_TSD_KEY_CELL 0; lit1 B_CAN_POISON_MEMORY_CELL 1;
atom8 B_INSTANCE_OFF_20_CELL aSB; lits8 B_INSTANCE_OFF_E20_CELL [0x10000000000; 0x108000010];
lit8 B_RODATA_0XE8 0x218a392cd3d5dbf; lits8 B_RODATA_0X158 CTZ_TABLE; lits8 B_RODATA_0X258 CTZ_TABLE; lit8 B_RODATA_0X48 0xcc6e96b9cc6e96b9;
lit8 B_GOT_0X58 B_GOT_OFF_58_VAL; lit8 B_GOT_0X60 B_GOT_OFF_60_VAL; lit8 B_GOT_0X68 B_GOT_OFF_68_VAL; lit8 B_GOT_0X70 B_GOT_OFF_70_VAL; lit8 B_GOT_0X78 B_GOT_OFF_78_VAL;
lit8 B_GOT_0X80 B_GOT_OFF_80_VAL; lit8 B_GOT_0X40 B_GOT_OFF_40_VAL; lit8 B_PAGESIZECACHED_CELL 4096; lit8 B_COMMON_FLAGS_DONT_USE_OFF_78_CELL 0xffffffffffffffff;
atom8 B_ASAN_SHADOW_MEMORY_DYNAMIC_ADDRESS_CELL aSHB; lit8 B_KHIGHMEMEND_CELL 0x7fffffffffff; lit8 B_KMIDMEMBEG_CELL 0; lit8 B_KMIDMEMEND_CELL 0; lit8 B_REAL_MEMSET_CELL B_MEMSET_PC;
lits8 B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_28_CELL [0x100000000000; 0xbe00000000]; lits8 B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_48_CELL [0x1000100000000; 0x101010101000001];
lit8 B_GOT_0XCB8 0x10; lit4 B_BUILTIN_TLS_OFF_D8_CELL 0  ; lit8 B_MFHOOKS_CELL 0;
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
Definition SS0K : sstate := mkSS B_WRAP_MALLOC_PC (sr_set sr_atoms 4%bv (SLit TFIB_TP)) REG0K None FK.
