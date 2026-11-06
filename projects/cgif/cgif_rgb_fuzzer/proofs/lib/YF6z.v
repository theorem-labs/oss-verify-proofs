(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF77.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
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
Definition atom8w (a : Z) (n : nat) : YQ0b.region := YQ0b.mkRegion None a (a + 8) a (a + 8) [YQ0b.mkChunk a (CVal 8 (SOff n 0))].
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
Definition FS2_atoms {imgk : img} : list (nat * afact) :=
FS_atoms ++
[ (aMAP, mkAF TFX_IMG_END (CEIL_MAX - 73728) 12)    ;
(aEND, mkAF (TFX_IMG_END + 4096) CEIL_MAX 3);
(aTL, mkAF 0 4088 3);
(aQS, mkAF 4096 CEIL_MAX 3)                 ;
(aBSL, mkAF (TFX_INST + 168) (TFX_INST + 672) 3);
(aSM, mkAF (kLowShadowBeg + TFX_IMG_END / 8) kHighShadowEnd 9)    ;
(aUE, mkAF (TFX_IMG_END + 4096) CEIL_MAX 3);
(aRL, mkAF 2048 (2048 + 2 * 4096) 3);
(aN8DS, mkAF 64512 MALLOC_MAX 3);
(aPBS, mkAF (kLowShadowBeg + TFX_IMG_END / 8) kHighShadowEnd 0)     ].
Definition FS2 {imgk : img} : facts := mkFacts FS2_atoms [] [].
Definition R_bsl : YQ0b.region := YQ0b.mkRegion (Some aBSL) 0 8 0 8 [YQ0b.mkChunk 0 (CVal 8 (SOff aJ8 0))].
Definition SREG0 {imgk : img} : smem :=
firstn 41 REG0 ++
[ YQ0b.mkRegion (Some aT) 2872 2888 2872 2888 [YQ0b.mkChunk 2872 (CVal 8 (SOff aJ4 0)); YQ0b.mkChunk 2880 (CVal 8 (SOff aJ5 0))];
YQ0b.mkRegion (Some aT) 2904 2912 2904 2912 [YQ0b.mkChunk 2904 (CVal 8 (SOff aJ9 0))];
lit8 (TFX_INST + o_sec) 4096;
atom8 (TFX_INST + o_sec_chunks) aQ; atom8 (TFX_INST + 80) aQ; lit8 (TFX_INST + 88) kPtrArrayResv;
atom8w (TFX_INST + o_sec_reserved) aRES; atom8w (TFX_INST + o_sec_n) aNCH;
YQ0b.mkRegion None (TFX_INST + o_sec_sorted) (TFX_INST + o_sec_sorted + 1) (TFX_INST + o_sec_sorted) (TFX_INST + o_sec_sorted + 1) [];
YQ0b.mkRegion None (TFX_INST + o_sec_stats) (TFX_INST + o_sec_stats + 32) (TFX_INST + o_sec_stats) (TFX_INST + o_sec_stats + 32)
[YQ0b.mkChunk (TFX_INST + o_sec_stats) (CVal 8 (SOff aI1 0)); YQ0b.mkChunk (TFX_INST + o_sec_stats + 16) (CVal 8 (SOff aI2 0));
YQ0b.mkChunk (TFX_INST + o_sec_stats + 24) (CVal 8 (SOff aI3 0))];
YQ0b.mkRegion None (TFX_INST + o_sec_mutex) (TFX_INST + o_sec_mutex + 4) (TFX_INST + o_sec_mutex) (TFX_INST + o_sec_mutex + 4)
[YQ0b.mkChunk (TFX_INST + o_sec_mutex) (CVal 4 (SLit 0))];
YQ0b.mkRegion None (0xa6e08 + D_10c0) (0xa6e30 + D_10c0) (0xa6e08 + D_10c0) (0xa6e30 + D_10c0) [YQ0b.mkChunk (0xa6e18 + D_10c0) (CVal 8 (SOff aJ6 0)); YQ0b.mkChunk (0xa6e20 + D_10c0) (CVal 8 (SOff aJ7 0))];
lit8 (0xa2148 + D_10f0) (0xa4038 + D_10f0); lit8 (0xa4038 + D_10f0) (0x192b8 + D_20); lit8 (0x13bde8 + D_10c0) 0x1010101; lit8 (0x13bd78 + D_10c0) 0; R_bsl ].

Definition R_bstA : YQ0b.region :=
YQ0b.mkRegion (Some 2%nat) (- 2136) (- 2120) 0 0 [YQ0b.mkChunk (- 2136) (CVal 8 (SOff 2 (- 2120))); YQ0b.mkChunk (- 2128) (CVal 8 (SOff aLEN 0))].
Definition R_scrA {imgk : img} : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (- ASTACK) (- 2136) (- ASTACK) (- 2136)
[YQ0b.mkChunk (-2208) (CVal 8 (SLit 1)); YQ0b.mkChunk (-2200) (CVal 8 (SLit (0x53640 + D_2c4))); YQ0b.mkChunk (-2192) (CVal 8 (SOff 11 0)); YQ0b.mkChunk (-2184) (CVal 8 (SOff 10 0));
YQ0b.mkChunk (-2176) (CVal 8 (SOff 2 0)); YQ0b.mkChunk (-2168) (CVal 8 (SLit (0x32340 + D_150))); YQ0b.mkChunk (-2152) (CVal 8 (SLit (0x536b0 + D_2c4)))].
Definition R_topA : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (-64) 0 (-64) 0
[YQ0b.mkChunk (-64) (CVal 8 (SOff 22 0)); YQ0b.mkChunk (-56) (CVal 8 (SOff 21 0)); YQ0b.mkChunk (-48) (CVal 8 (SOff 20 0)); YQ0b.mkChunk (-40) (CVal 8 (SOff 19 0));
YQ0b.mkChunk (-32) (CVal 8 (SOff 18 0)); YQ0b.mkChunk (-24) (CVal 8 (SOff 9 0)); YQ0b.mkChunk (-16) (CVal 8 (SOff 8 0)); YQ0b.mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition REGS_A {imgk : img} : list sv :=
[SLit 0; SLit (0x32388 + D_150); SOff 2 (-2208); SOff 3 0; SLit TFX_TP; SOff 5 0; SOff 6 0; SOff 7 0; SOff 2 (-2136); SOff 11 0; SLit TFX_INST; SOff 10 0; SLit 8; SOff 2 (-2136); SLit 1; SLit 1;
SOff 2 (-2136); SOff 17 0; SLit TFX_INST; SOff 10 0; SLit 1; SOff 2 (-2136); SOff 2 (-89); SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition S0 {imgk : img} : sstate := mkSS (0x323b8 + D_150) REGS_A (R_bstA :: R_scrA :: R_topA :: tl SREG0) None FS.
Definition runto {imgk : img} (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN_sh tfxsegs tfxtbl_rr FUEL pc ss).
Definition IFRAME : Z := 2136.
Definition runtoC {imgk : img} (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN_sh tfxsegs tfxtbl_rtC FUEL pc ss).
