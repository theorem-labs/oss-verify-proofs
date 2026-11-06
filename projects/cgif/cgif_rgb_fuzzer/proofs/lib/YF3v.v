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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 6. Set Printing Width 250.
Definition lit8 (a v : Z) : YQ0b.region := YQ0b.mkRegion None a (a + 8) 0 0 [YQ0b.mkChunk a (CVal 8 (SLit v))].
Definition lit4 (a v : Z) : YQ0b.region := YQ0b.mkRegion None a (a + 4) 0 0 [YQ0b.mkChunk a (CVal 4 (SLit v))].
Definition lit1 (a v : Z) : YQ0b.region := YQ0b.mkRegion None a (a + 1) 0 0 [YQ0b.mkChunk a (CVal 1 (SLit v))].
Definition lits8 (a : Z) (vs : list Z) : YQ0b.region :=
YQ0b.mkRegion None a (a + 8 * Z.of_nat (length vs)) 0 0
(map (fun iv => YQ0b.mkChunk (a + 8 * Z.of_nat (fst iv)) (CVal 8 (SLit (snd iv)))) (combine (seq 0 (length vs)) vs)).
Definition atom8 (a : Z) (n : nat) : YQ0b.region := YQ0b.mkRegion None a (a + 8) 0 0 [YQ0b.mkChunk a (CVal 8 (SOff n 0))].
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
Definition REG0 {imgk : img} : smem :=
[
YQ0b.mkRegion (Some 2%nat) (- ASTACK) 0 (- ASTACK) 0 [];
lit1 (0xaae98 + D_10c0) 1; lit4 (0xaaebc + D_10c0) 30; lit8 (0xa2150 + D_10f0) (0x13bce8 + D_10c0); lit8 (0x13bd08 + D_10c0) 0x1e00010000;
lit1 (0x12c422 + D_10c0) 0; lit1 (0xa9a20 + D_10c0) 1; lit4 (0xa9a24 + D_10c0) 0; lit1 (0xa9a1c + D_10c0) 1;
atom8 (0xa6b78 + D_10c0) aSB; lits8 (0xa7978 + D_10c0) [0x10000000000; 0x108000010];
lit8 (0x103c0 + D_20) 0x218a392cd3d5dbf; lits8 (0x10430 + D_20) CTZ_TABLE; lits8 (0x10530 + D_20) CTZ_TABLE; lit8 (0x10328 + D_10) 0xcc6e96b9cc6e96b9;
lit8 (0xa2158 + D_10f0) (0xa79b8 + D_10c0); lit8 (0xa2160 + D_10f0) (0xaa1b8 + D_10c0); lit8 (0xa2168 + D_10f0) (0xaaea8 + D_10c0); lit8 (0xa2170 + D_10f0) (0xaaeb0 + D_10c0); lit8 (0xa2178 + D_10f0) (0xaaea0 + D_10c0);
lit8 (0xa2180 + D_10f0) (0xa4000 + D_10f0); lit8 (0xa2140 + D_10f0) (0x139c60 + D_10c0); lit8 (0x139c60 + D_10c0) 4096; lit8 (0x13bd60 + D_10c0) 0xffffffffffffffff;
atom8 (0xaa1b8 + D_10c0) aSHB; lit8 (0xaaea0 + D_10c0) 0x7fffffffffff; lit8 (0xaaea8 + D_10c0) 0; lit8 (0xaaeb0 + D_10c0) 0; lit8 (0xa4000 + D_10f0) (0x9b894 + D_10ec);
lits8 (0xa79e0 + D_10c0) [0x100000000000; 0xbe00000000]; lits8 (0xa7a00 + D_10c0) [0x1000100000000; 0x101010101000001];
lit8 (0xa2db8 + D_10f0) 0x10; lit4 (0x5dd160 + D_10c0) 0  ; lit8 (0x13bc80 + D_10c0) 0;
lit8 (TFX_TP - 88) TFX_TSD; atom8 TFX_TSD aC;
YQ0b.mkRegion (Some aC) 0 160 0 0 [YQ0b.mkChunk 8 (CVal 4 (SLit 0)); YQ0b.mkChunk 152 (CVal 8 (SOff aT 0))];
YQ0b.mkRegion (Some aT) 0 208 0 0 [YQ0b.mkChunk 0 (CVal 8 (SOff aC 0)); YQ0b.mkChunk 8 (CVal 8 (SOff aTOP 0));
YQ0b.mkChunk 16 (CVal 8 (SOff aTOP (- kStackSpan))); YQ0b.mkChunk 40 (CVal 1 (SLit 0))];
YQ0b.mkRegion (Some aT) 2768 2800 2768 2800 [YQ0b.mkChunk 2784 (CVal 8 (SOff aJ0 0))];
YQ0b.mkRegion (Some aT) t_unwinding (t_unwinding + 1) t_unwinding (t_unwinding + 1) [YQ0b.mkChunk t_unwinding (CVal 1 (SLit 0))];
YQ0b.mkRegion (Some aT) 2800 2824 2800 2824 [YQ0b.mkChunk 2800 (CVal 8 (SOff aJ1 0)); YQ0b.mkChunk 2808 (CVal 8 (SOff aJ2 0));
YQ0b.mkChunk 2816 (CVal 8 (SOff aJ3 0))];
YQ0b.mkRegion (Some aSSLOT) 0 8 0 8 [YQ0b.mkChunk 0 (CVal 8 (SOff aJ4 0))];
YQ0b.mkRegion (Some aP) 0 4 0 4 [YQ0b.mkChunk 0 (CVal 4 (SOff aCNT 0))];
YQ0b.mkRegion (Some aP) 4 16 0 0 [YQ0b.mkChunk 8 (CVal 8 (SOff aCSZ 0))];
YQ0b.mkRegion (Some aPV) 0 4 0 0 [YQ0b.mkChunk 0 (CVal 4 (SOff aV 0))];
YQ0b.mkRegion (Some aK) 0 16 0 16 [];
YQ0b.mkRegion (Some aU) (- 16) 0 (- 16) 0 [YQ0b.mkChunk (- 15) (CVal 1 (SOff aJB 0))];
YQ0b.mkRegion (Some aSK) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SLit 250))] ].
Definition SS0 {imgk : img} : sstate := mkSS (0x53104 + D_2c4) (sr_set sr_atoms 4%bv (SLit TFX_TP)) REG0 None FG.
