(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/YFkpcf.v (commit f01d79f3fb5, cf refill round 3; file sha256 7fcd6088076d) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 41 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code except at the by-hand acceptances named below (strictcmp3 65688e94214a, by funcpair_reply 6963bc4a94fc on the cgif twin ce511d541cda; 38 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair; 3 pair(s) carry a BY-HAND acceptance (accept.tsv, re-measured each run): _ZN6__asan9Allocator10DeallocateEPvmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE+0x20c (data-differs: ACCEPTED by hand: bounded read-only table (De Bruijn ctz, 64 bytes read, equal and read-only on both images)), _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb+0xdc (data-differs: ACCEPTED by hand: bounded read-only table (De Bruijn ctz, 64 bytes read, equal and read-only on both images)), _ZN6__asanL10RZSize2LogEj+0x44 (data-differs: ACCEPTED by hand: bounded read-only table (De Bruijn ctz, 64 bytes read, equal and read-only on both images))); 4 hand maps (resolve-run-f01d79f3fb5.tsv (sha256 ba54f3af32ab; internal record), each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane for a Theorem Labs lane, lane refill-b2, base a working branch d50ec3c8a93a): YFkpcf, the cf
   twin of YFkp.v (this tree's copy, = c5 8d6c9f45705b).  The one change: region RG's byte 68 (the class's
   exhausted byte, YFkp.v:73 `CVal 1 (SLit 0)`) is the junk atom rJEX (`CVal 1 (SOff rJEX 0)`, fact 0 <= rJEX < 2 ^ 8),
   like rJNA / rJNF on the same line, because under ARmcf that byte is junk: the class-full arm sets it
   (YG0ncf.v:10-11, region_cells_cf).  Everything else is YFkp.v verbatim.
   EVENT-FREE: no st_nev, EV_A, EV_MAX, refill_reg, qloosem or non-cf abudget.  rule 24: no function proved (kind:
   re-base of the proved refill walk onto the cf instance). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0 YFhy.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
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
(* the class's exhausted byte RI+68, junk under ARmcf (acells_cf drops it, YG0ncf.v region_cells_cf) *)
Definition rJEX : nat := 55.
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
(rJSM, mkAF 0 (2 ^ 64 - 1) 0); (rJM1, mkAF 0 (2 ^ 64 - 1) 0); (rJM2, mkAF 0 (2 ^ 64 - 1) 0);
(rJEX, mkAF 0 (2 ^ 8 - 1) 0) ] [] [].
Definition REG0R : smem :=
[
YP09.mkRegion (Some 2%nat) (- 1024) 0 (- 1024) 0 [];
lit1 0xa7318 1; lit8 0x9df40 0x138168; lit1 0xa5ea0 1; lit4 0xa5ea4 0; lit1 0xa5e9c 1;
atom8 0xa2ff8 rSB;
YP09.mkRegion None 0xa3008 0xa3010 0 0 [YP09.mkChunk 0xa3008 (CVal 8 (SOff rSB (2 ^ 37)))];
lit8 0xa3010 0; lit8 0xa3000 0xffffffff;
lit8 0x103a0 0xafffff00000fffff; lits8 0x10420 CTZ_TABLE; lits8 0x10520 CTZ_TABLE;
lit8 0x9df48 0xa3e38; lit8 0x9df50 0xa6638; lit8 0x9df58 0xa7328; lit8 0x9df60 0xa7330; lit8 0x9df68 0xa7320;
lit8 0x9df70 0x9fdf0; lit8 0x9df30 0x1360e0; lit8 0x1360e0 4096; lit8 0x1381e0 0xffffffffffffffff; lit8 0x1381f8 0;
atom8 0xa6638 rSHB; lit8 0xa7320 0x7fffffffffff; lit8 0xa7328 0; lit8 0xa7330 0; lit8 0x9fdf0 0x96e80;
lit4 0x5d9a00 0; lit8 0x138100 0;
lit8 (TFIB_TP - 88) TFIB_TSD; atom8 TFIB_TSD rC;
YP09.mkRegion (Some rC) 0 160 0 0 [YP09.mkChunk 152 (CVal 8 (SOff rT 0))];
YP09.mkRegion (Some rT) 2768 2800 2768 2800 [YP09.mkChunk 2792 (CVal 8 (SOff rJSM 0))];
YP09.mkRegion (Some rT) 2872 2888 2872 2888 [YP09.mkChunk 2872 (CVal 8 (SOff rJM1 0)); YP09.mkChunk 2880 (CVal 8 (SOff rJM2 0))];
YP09.mkRegion (Some rP) 0 16 0 16 [YP09.mkChunk 0 (CVal 4 (SLit 0)); YP09.mkChunk 4 (CVal 4 (SOff rMAX 0)); YP09.mkChunk 8 (CVal 8 (SOff rCSZ 0))];
YP09.mkRegion (Some rRG) 0 128 0 128
[YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0)); YP09.mkChunk 16 (CVal 8 (SOff rNF 0));
YP09.mkChunk 24 (CVal 8 (SOff rMF 0)); YP09.mkChunk 32 (CVal 8 (SOff rAU 0)); YP09.mkChunk 40 (CVal 8 (SLit 0));
YP09.mkChunk 48 (CVal 8 (SOff rMU 0)); YP09.mkChunk 56 (CVal 8 (SLit 0)); YP09.mkChunk 64 (CVal 4 (SOff rJ64 0));
YP09.mkChunk 68 (CVal 1 (SOff rJEX 0)); YP09.mkChunk 72 (CVal 8 (SOff rJNA 0)); YP09.mkChunk 80 (CVal 8 (SOff rJNF 0))] ].
Definition REGS0R : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 4%bv (SLit TFIB_TP)) 10%bv (SOff rT t_cache)) 11%bv (SOff rP 0)) 12%bv (SLit 0xa2fd8)) 13%bv (SOff rCL 0).
Definition SS0R : sstate := mkSS 0x36a20 REGS0R REG0R None FR.
