(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFkp.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AFkp.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_rate's ASan build. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/AFkp.v at 4e3a0a9ad299, derived by derive_y.py: addresses moved from reac-pw/fuzz_rate's asan image (image A) to its asan-ubsan image (image B), the image module Asan -> AsanUbsan; the Modified-by lines above describe how lib/A/AFkp.v was made and quote that file's image-A values; the code below carries image B's values. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.

From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.

From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import YB1v YB1q YF0l YF0m YF0x YFl0 YFhy.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05.
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
lit1 0xa5c18 1; lit8 0x9c160 0x136a68; lit1 0xa47a0 1; lit4 0xa47a4 0; lit1 0xa479c 1;
atom8 0xa18f8 rSB;
YP09.mkRegion None 0xa1908 0xa1910 0 0 [YP09.mkChunk 0xa1908 (CVal 8 (SOff rSB (2 ^ 37)))];
lit8 0xa1910 0; lit8 0xa1900 0xffffffff;
lit8 0x103c8 0xafffff00000fffff; lits8 0x10460 CTZ_TABLE; lits8 0x10560 CTZ_TABLE;
lit8 0x9c168 0xa2738; lit8 0x9c170 0xa4f38; lit8 0x9c178 0xa5c28; lit8 0x9c180 0xa5c30; lit8 0x9c188 0xa5c20;
lit8 0x9c190 0x9dfd8; lit8 0x9c150 0x1349e0; lit8 0x1349e0 4096; lit8 0x136ae0 0xffffffffffffffff; lit8 0x136af8 0;
atom8 0xa4f38 rSHB; lit8 0xa5c20 0x7fffffffffff; lit8 0xa5c28 0; lit8 0xa5c30 0; lit8 0x9dfd8 0x95660;
lit4 0x5d7ee0 0; lit8 0x136a00 0;
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
sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 4%bv (SLit TFIB_TP)) 10%bv (SOff rT t_cache)) 11%bv (SOff rP 0)) 12%bv (SLit 0xa18d8)) 13%bv (SOff rCL 0).
Definition SS0R : sstate := mkSS 0x36834 REGS0R REG0R None FR.
