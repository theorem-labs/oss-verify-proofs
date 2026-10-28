(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFhy.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 6. Set Printing Width 250.
Definition aQ : nat := 39.    Definition aRES : nat := 40.  Definition aNCH : nat := 41.
Definition aMS : nat := 42.   Definition aMAP : nat := 45.
Definition aEND : nat := 46.  Definition aTL : nat := 48.   Definition aQS : nat := 52.   Definition aBSL : nat := 55.
Definition aJ5 : nat := 43.   Definition aJ6 : nat := 44.   Definition aJ7 : nat := 54.   Definition aJ8 : nat := 56.
Definition aJ9 : nat := 57.   Definition aI1 : nat := 58.   Definition aI2 : nat := 59.   Definition aI3 : nat := 60.
Definition aSM : nat := 61.   Definition aUE : nat := 62.   Definition aRL : nat := 64.   Definition aN8DS : nat := 65.  Definition aPBS : nat := 66.
Definition sHAV : nat := 80.
Definition sU1 : nat := 80.
Definition sL1 : nat := 96.
Definition sM1 : nat := 104.
Definition sL2 : nat := 110.
Definition sM2 : nat := 118.
Definition sMX : nat := 128.
Definition sD1 : nat := 129.
Definition sGA : nat := 145.
Definition sL3 : nat := 146.
Definition sM3 : nat := 154.
Definition sL4 : nat := 160.
Definition sM4 : nat := 168.
Definition sL5 : nat := 174.
Definition atom8w (a : Z) (n : nat) : YP09.region := YP09.mkRegion None a (a + 8) a (a + 8) [YP09.mkChunk a (CVal 8 (SOff n 0))].
Definition FS_atoms : list (nat * afact) :=
[ (2%nat, mkAF (kHighMemBeg + ASTACK) kHighMemEnd 4);
(10%nat, mkAF 64513 (MALLOC_MAX - 1) 0);
(aT, mkAF 4096 (CEIL_MAX - 4096) 12)       ;
(aC, mkAF 4096 (CEIL_MAX - 256) 3)         ;
(aSB, mkAF kHighMemBeg CEIL_MAX 16)         ;
(aTOP, mkAF kHighMemBeg kHighMemEnd 12);
(aLEN, mkAF 1 30 0);
(aJ0, mkAF 0 (2 ^ 64 - 1) 0);
(aR8, mkAF 64520 MALLOC_MAX 3);
(aQ, mkAF 4096 CEIL_MAX 12)                ;
(aRES, mkAF 0 1048576 14);
(aNCH, mkAF 0 1048575 0);
(aMS, mkAF 73728 (MALLOC_MAX + 2 * 4096) 12);
(aJ5, mkAF 0 (2 ^ 64 - 1) 0); (aJ6, mkAF 0 (2 ^ 64 - 1) 0);
(aSHB, mkAF 0x7fff8000 0x7fff8000 12);
(aJ1, mkAF 0 (2 ^ 64 - 1) 0); (aJ2, mkAF 0 (2 ^ 64 - 1) 0); (aJ3, mkAF 0 (2 ^ 64 - 1) 0);
(aJ4, mkAF 0 (2 ^ 64 - 1) 0); (aJ7, mkAF 0 (2 ^ 64 - 1) 0); (aJ8, mkAF 0 (2 ^ 64 - 1) 0); (aJ9, mkAF 0 (2 ^ 64 - 1) 0);
(aI1, mkAF 0 (2 ^ 64 - 1) 0); (aI2, mkAF 0 (2 ^ 64 - 1) 0); (aI3, mkAF 0 (2 ^ 64 - 1) 0);
(aND, mkAF (64520 + 4096) (MALLOC_MAX + 4096) 3) ].
Definition FS : facts := mkFacts FS_atoms [] [].
Definition FS2_atoms : list (nat * afact) :=
FS_atoms ++
[ (aMAP, mkAF TFIB_IMG_END (CEIL_MAX - 73728) 12)    ;
(aEND, mkAF (TFIB_IMG_END + 4096) CEIL_MAX 3);
(aTL, mkAF 0 4088 3);
(aQS, mkAF 4096 CEIL_MAX 3)                 ;
(aBSL, mkAF (TFIB_INST + 168) (TFIB_INST + 672) 3);
(aSM, mkAF (kLowShadowBeg + TFIB_IMG_END / 8) kHighShadowEnd 9)    ;
(aUE, mkAF (TFIB_IMG_END + 4096) CEIL_MAX 3);
(aRL, mkAF 2048 (2048 + 2 * 4096) 3);
(aN8DS, mkAF 64512 MALLOC_MAX 3);
(aPBS, mkAF (kLowShadowBeg + TFIB_IMG_END / 8) kHighShadowEnd 0)     ].
Definition FS2 : facts := mkFacts FS2_atoms [] [].
Definition R_bsl : YP09.region := YP09.mkRegion (Some aBSL) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff aJ8 0))].
Definition SREG0 : smem :=
firstn 41 REG0 ++
[ YP09.mkRegion (Some aT) 2872 2888 2872 2888 [YP09.mkChunk 2872 (CVal 8 (SOff aJ4 0)); YP09.mkChunk 2880 (CVal 8 (SOff aJ5 0))];
YP09.mkRegion (Some aT) 2904 2912 2904 2912 [YP09.mkChunk 2904 (CVal 8 (SOff aJ9 0))];
lit8 (TFIB_INST + o_sec) 4096;
atom8 (TFIB_INST + o_sec_chunks) aQ; atom8 (TFIB_INST + 80) aQ; lit8 (TFIB_INST + 88) kPtrArrayResv;
atom8w (TFIB_INST + o_sec_reserved) aRES; atom8w (TFIB_INST + o_sec_n) aNCH;
YP09.mkRegion None (TFIB_INST + o_sec_sorted) (TFIB_INST + o_sec_sorted + 1) (TFIB_INST + o_sec_sorted) (TFIB_INST + o_sec_sorted + 1) [];
YP09.mkRegion None (TFIB_INST + o_sec_stats) (TFIB_INST + o_sec_stats + 32) (TFIB_INST + o_sec_stats) (TFIB_INST + o_sec_stats + 32)
[YP09.mkChunk (TFIB_INST + o_sec_stats) (CVal 8 (SOff aI1 0)); YP09.mkChunk (TFIB_INST + o_sec_stats + 16) (CVal 8 (SOff aI2 0));
YP09.mkChunk (TFIB_INST + o_sec_stats + 24) (CVal 8 (SOff aI3 0))];
YP09.mkRegion None (TFIB_INST + o_sec_mutex) (TFIB_INST + o_sec_mutex + 4) (TFIB_INST + o_sec_mutex) (TFIB_INST + o_sec_mutex + 4)
[YP09.mkChunk (TFIB_INST + o_sec_mutex) (CVal 4 (SLit 0))];
YP09.mkRegion None 0xa2c48 0xa2c70 0xa2c48 0xa2c70 [YP09.mkChunk 0xa2c58 (CVal 8 (SOff aJ6 0)); YP09.mkChunk 0xa2c60 (CVal 8 (SOff aJ7 0))];
lit8 0x9df80 0x9fe60; lit8 0x9fe60 0x19241; lit8 0x137c28 0x1010101; lit8 0x137bb8 0; R_bsl ].
Lemma SREG0_len : length SREG0 = 58%nat. Proof. reflexivity. Qed.
Definition S0 : sstate := mkSS 0x52930 (sr_set sr_atoms 4%bv (SLit TFIB_TP)) SREG0 None FS.
Definition runtoC (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN_sh tfibsegs tfibtbl_rtC FUEL pc ss).
