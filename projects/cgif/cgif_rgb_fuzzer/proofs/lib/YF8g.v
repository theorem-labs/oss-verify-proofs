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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
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
Definition REG0R {imgk : img} : smem :=
[
YQ0b.mkRegion (Some 2%nat) (- 1024) 0 (- 1024) 0 [];
lit1 (0xaae98 + D_10c0) 1; lit8 (0xa2150 + D_10f0) (0x13bce8 + D_10c0); lit1 (0xa9a20 + D_10c0) 1; lit4 (0xa9a24 + D_10c0) 0; lit1 (0xa9a1c + D_10c0) 1;
atom8 (0xa6b78 + D_10c0) rSB;
YQ0b.mkRegion None (0xa6b88 + D_10c0) (0xa6b90 + D_10c0) 0 0 [YQ0b.mkChunk (0xa6b88 + D_10c0) (CVal 8 (SOff rSB (2 ^ 37)))];
lit8 (0xa6b90 + D_10c0) 0; lit8 (0xa6b80 + D_10c0) 0xffffffff;
lit8 (0x103a8 + D_20) 0xafffff00000fffff; lits8 (0x10430 + D_20) CTZ_TABLE; lits8 (0x10530 + D_20) CTZ_TABLE;
lit8 (0xa2158 + D_10f0) (0xa79b8 + D_10c0); lit8 (0xa2160 + D_10f0) (0xaa1b8 + D_10c0); lit8 (0xa2168 + D_10f0) (0xaaea8 + D_10c0); lit8 (0xa2170 + D_10f0) (0xaaeb0 + D_10c0); lit8 (0xa2178 + D_10f0) (0xaaea0 + D_10c0);
lit8 (0xa2180 + D_10f0) (0xa4000 + D_10f0); lit8 (0xa2140 + D_10f0) (0x139c60 + D_10c0); lit8 (0x139c60 + D_10c0) 4096; lit8 (0x13bd60 + D_10c0) 0xffffffffffffffff; lit8 (0x13bd78 + D_10c0) 0;
atom8 (0xaa1b8 + D_10c0) rSHB; lit8 (0xaaea0 + D_10c0) 0x7fffffffffff; lit8 (0xaaea8 + D_10c0) 0; lit8 (0xaaeb0 + D_10c0) 0; lit8 (0xa4000 + D_10f0) (0x9b894 + D_10ec);
lit4 (0x5dd160 + D_10c0) 0; lit8 (0x13bc80 + D_10c0) 0;
lit8 (TFX_TP - 88) TFX_TSD; atom8 TFX_TSD rC;
YQ0b.mkRegion (Some rC) 0 160 0 0 [YQ0b.mkChunk 152 (CVal 8 (SOff rT 0))];
YQ0b.mkRegion (Some rT) 2768 2800 2768 2800 [YQ0b.mkChunk 2792 (CVal 8 (SOff rJSM 0))];
YQ0b.mkRegion (Some rT) 2872 2888 2872 2888 [YQ0b.mkChunk 2872 (CVal 8 (SOff rJM1 0)); YQ0b.mkChunk 2880 (CVal 8 (SOff rJM2 0))];
YQ0b.mkRegion (Some rP) 0 16 0 16 [YQ0b.mkChunk 0 (CVal 4 (SLit 0)); YQ0b.mkChunk 4 (CVal 4 (SOff rMAX 0)); YQ0b.mkChunk 8 (CVal 8 (SOff rCSZ 0))];
YQ0b.mkRegion (Some rRG) 0 128 0 128
[YQ0b.mkChunk 0 (CVal 8 (SLit 0)); YQ0b.mkChunk 8 (CVal 8 (SLit 0)); YQ0b.mkChunk 16 (CVal 8 (SOff rNF 0));
YQ0b.mkChunk 24 (CVal 8 (SOff rMF 0)); YQ0b.mkChunk 32 (CVal 8 (SOff rAU 0)); YQ0b.mkChunk 40 (CVal 8 (SLit 0));
YQ0b.mkChunk 48 (CVal 8 (SOff rMU 0)); YQ0b.mkChunk 56 (CVal 8 (SLit 0)); YQ0b.mkChunk 64 (CVal 4 (SOff rJ64 0));
YQ0b.mkChunk 68 (CVal 1 (SLit 0)); YQ0b.mkChunk 72 (CVal 8 (SOff rJNA 0)); YQ0b.mkChunk 80 (CVal 8 (SOff rJNF 0))] ].
Definition REGS0R {imgk : img} : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 4%bv (SLit TFX_TP)) 10%bv (SOff rT t_cache)) 11%bv (SOff rP 0)) 12%bv (SLit (0xa6b58 + D_10c0))) 13%bv (SOff rCL 0).
Definition SS0R {imgk : img} : sstate := mkSS (0x3670c + D_150) REGS0R REG0R None FR.
