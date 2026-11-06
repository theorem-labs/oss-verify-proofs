(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YB1v YB1q YF0l YF0m YF0x YFl0 YFhy.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
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
lit1 0xa6f58 1; lit4 0xa6f7c 30; lit8 0x9e1f8 0x137da8; lit8 0x137dc8 0x1e00010000;
lit1 0x1284e2 0; lit1 0xa5ae0 1; lit4 0xa5ae4 0; lit1 0xa5adc 1;
atom8 0xa2c38 aSB; lits8 0xa3a38 [0x10000000000; 0x108000010];
lit8 0x103b8 0x218a392cd3d5dbf; lits8 0x10428 CTZ_TABLE; lits8 0x10528 CTZ_TABLE; lit8 0x10328 0xcc6e96b9cc6e96b9;
lit8 0x9e200 0xa3a78; lit8 0x9e208 0xa6278; lit8 0x9e210 0xa6f68; lit8 0x9e218 0xa6f70; lit8 0x9e220 0xa6f60;
lit8 0x9e228 0xa0098; lit8 0x9e1e8 0x135d20; lit8 0x135d20 4096; lit8 0x137e20 0xffffffffffffffff;
atom8 0xa6278 aSHB; lit8 0xa6f60 0x7fffffffffff; lit8 0xa6f68 0; lit8 0xa6f70 0; lit8 0xa0098 0x9790c;
lits8 0xa3aa0 [0x100000000000; 0xbe00000000]; lits8 0xa3ac0 [0x1000100000000; 0x101010101000001];
lit8 0x9ee60 0x10; lit4 0x5d9220 0  ; lit8 0x137d40 0;
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
Definition SS0K : sstate := mkSS 0x52960 (sr_set sr_atoms 4%bv (SLit TFIB_TP)) REG0K None FK.
