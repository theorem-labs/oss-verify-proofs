(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFhy.v, with its module paths changed and its addresses moved to libreac/fuzz_knock's ASan build; AB1v's tfibsegs is A/AWalkFw0.v's. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/A/AFhy.v (donor image sha256 61768cf4739b), with its module paths changed and its addresses moved to reac-pw/fuzz_qdisc's ASan build. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AFhy.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from reac-pw/fuzz_qdisc's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AFhy.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.

From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.

From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require Import AWalkFw0 YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 6. Set Printing Width 250.
Definition lit8 (a v : Z) : YP09.region := YP09.mkRegion None a (a + 8) 0 0 [YP09.mkChunk a (CVal 8 (SLit v))].
Definition lit4 (a v : Z) : YP09.region := YP09.mkRegion None a (a + 4) 0 0 [YP09.mkChunk a (CVal 4 (SLit v))].
Definition lit1 (a v : Z) : YP09.region := YP09.mkRegion None a (a + 1) 0 0 [YP09.mkChunk a (CVal 1 (SLit v))].
Definition lits8 (a : Z) (vs : list Z) : YP09.region :=
YP09.mkRegion None a (a + 8 * Z.of_nat (length vs)) 0 0
(map (fun iv => YP09.mkChunk (a + 8 * Z.of_nat (fst iv)) (CVal 8 (SLit (snd iv)))) (combine (seq 0 (length vs)) vs)).
Definition atom8 (a : Z) (n : nat) : YP09.region := YP09.mkRegion None a (a + 8) 0 0 [YP09.mkChunk a (CVal 8 (SOff n 0))].
Definition CTZ_TABLE : list Z :=
[0x13080d0307020100; 0x281422091c0e1904; 0x301d2e0f261a1105; 0x3929321536231f0a;
0x27211b18120c063f; 0x3831351e2f2d2510; 0x37342c2420170b3e; 0x3a3b2a3c332b163d].
Definition aT : nat := 32.   Definition aC : nat := 33.   Definition aSB : nat := 34.  Definition aTOP : nat := 35.
Definition aLEN : nat := 36. Definition aJ0 : nat := 37.  Definition aR8 : nat := 38.  Definition aCL : nat := 39.
Definition aP : nat := 40.   Definition aCNT : nat := 41. Definition aV : nat := 42.   Definition aCSZ : nat := 43.
Definition aPV : nat := 44.  Definition aK : nat := 45.   Definition aJB : nat := 46.  Definition aSHB : nat := 47.
Definition aSK : nat := 48.  Definition aJ1 : nat := 49.  Definition aJ2 : nat := 50.  Definition aJ3 : nat := 51.
Definition aSSLOT : nat := 52. Definition aJ4 : nat := 53. Definition aPB : nat := 54. Definition aN8D : nat := 55.
Definition aCNT8 : nat := 56.
Definition aKL : nat := 57.  Definition aRZ : nat := 58.  Definition aH : nat := 59.   Definition aU : nat := 60.
Definition aSU : nat := 61.  Definition aFIL : nat := 62. Definition aND : nat := 63.
Definition aHAV : nat := 64.
Definition rz_lo (k : Z) : Z := match k with 1 => 49 | 2 => 97 | 3 => 449 | 4 => 3969 | 5 => 16129 | 6 => 32257 | _ => 0 end.
Definition rz_hi (k : Z) : Z := match k with 0 => 48 | 1 => 96 | 2 => 448 | 3 => 3968 | 4 => 16128 | 5 => 32256 | 6 => 64512 | _ => 0 end.
Definition rz_of (k : Z) : Z := 16 * 2 ^ k.
Definition FG : facts := mkFacts
[ (2%nat, mkAF (kHighMemBeg + ASTACK) kHighMemEnd 4);
(10%nat, mkAF 49 64512 0);
(aT, mkAF 4096 (CEIL_MAX - 4096) 12)       ;
(aC, mkAF 4096 (CEIL_MAX - 256) 3)         ;
(aSB, mkAF kHighMemBeg CEIL_MAX 16)         ;
(aTOP, mkAF kHighMemBeg kHighMemEnd 12);
(aLEN, mkAF 1 30 0);
(aJ0, mkAF 0 (2 ^ 64 - 1) 0);
(aR8, mkAF 56 64512 3);
(aCL, mkAF 1 31 0);
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
(aN8D, mkAF 48 64512 3);
(aCNT8, mkAF 6 8064 0);
(aKL, mkAF 1 6 0);
(aRZ, mkAF 32 1024 5);
(aH, mkAF kHighMemBeg CEIL_MAX 4);
(aU, mkAF kHighMemBeg CEIL_MAX 5);
(aSU, mkAF 0x2008fff7000 0x10007fff7fff 2);
(aFIL, mkAF 49 4096 0);
(aND, mkAF 88 65536 3) ] [] [].
Definition IFRAME : Z := 2128.
Definition REG0 : smem :=
[
YP09.mkRegion (Some 2%nat) (- ASTACK) 0 (- ASTACK) 0 [];
lit1 0x9e598 1; lit4 0x9e5bc 30; lit8 0x958f0 0x12f3e8; lit8 0x12f408 0x1e00010000;
lit1 0x11fb22 0; lit1 0x9d120 1; lit4 0x9d124 0; lit1 0x9d11c 1;
atom8 0x9a278 aSB; lits8 0x9b078 [0x10000000000; 0x108000010];
lit8 0x103a8 0x218a392cd3d5dbf; lits8 0x10418 CTZ_TABLE; lits8 0x10518 CTZ_TABLE; lit8 0x10328 0xcc6e96b9cc6e96b9;
lit8 0x958f8 0x9b0b8; lit8 0x95900 0x9d8b8; lit8 0x95908 0x9e5a8; lit8 0x95910 0x9e5b0; lit8 0x95918 0x9e5a0;
lit8 0x95920 0x97760; lit8 0x958e0 0x12d360; lit8 0x12d360 4096; lit8 0x12f460 0xffffffffffffffff;
atom8 0x9d8b8 aSHB; lit8 0x9e5a0 0x7fffffffffff; lit8 0x9e5a8 0; lit8 0x9e5b0 0; lit8 0x97760 0x8f034;
lits8 0x9b0e0 [0x100000000000; 0xbe00000000]; lits8 0x9b100 [0x1000100000000; 0x101010101000001];
lit8 0x96558 0x10; lit4 0x5d0860 0  ; lit8 0x12f380 0;
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
YP09.mkRegion (Some aK) 0 16 0 16 [];
YP09.mkRegion (Some aU) (- 16) 0 (- 16) 0 [YP09.mkChunk (- 15) (CVal 1 (SOff aJB 0))];
YP09.mkRegion (Some aSK) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 250))] ].
Definition SS0 : sstate := mkSS 0x50b34 (sr_set sr_atoms 4%bv (SLit TFIB_TP)) REG0 None FG.
