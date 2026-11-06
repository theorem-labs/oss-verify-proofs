(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/YFkpcf.v (a working branch 9031d3b24a79, file sha256 7fcd6088076d) onto omx-clap-core/fuzz_preset's asan-ubsan image (unstripped fuzz_preset.asan-ubsan, sha256 3b5e1a099b53; pin f8f98a95bc52); module paths changed; its 42 image addresses moved by code-verified function pairs (42 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from the old pin B (pinned fuzz_preset.asan-ubsan f8f98a95bc52, twin 3b5e1a099b53; this file at 74f20580f552) to B' (#102 pin d663f82d7f48, twin c90d4fa54d43) by the relocation route of record, frozen alreloc a5c53bb2bed4ad03 (a Theorem Labs lane's internal file alreloc.py.frozen-a5c53bb2bed4ad03), --assume-source, --resolve resolve-B102.txt (sha256 5cd2316e3413; internal record) (3 lines name this file); 39 numerals changed. *)
(* Theorem Labs, 2026-10-30: YFkpcf, the cf
   twin of cgif/cgif_file_fuzzer lib/YFkp.v (file sha256 07ecd7c9638c; donor not released).  The one change: region RG's byte 68 (the class's
   exhausted byte, YFkp.v:73 `CVal 1 (SLit 0)`) is the junk atom rJEX (`CVal 1 (SOff rJEX 0)`, fact 0 <= rJEX < 2 ^ 8),
   like rJNA / rJNF on the same line, because under ARmcf that byte is junk: the class-full arm sets it
   (YG0ncf.v:10-11, region_cells_cf).  Everything else is YFkp.v verbatim.
   EVENT-FREE: no st_nev, EV_A, EV_MAX, refill_reg, qloosem or non-cf abudget.  rule 24: no function proved (kind:
   re-base of the proved refill walk onto the cf instance). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
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
lit1 0xac3d8 1; lit8 0xa2840 0x13d228; lit1 0xaaf60 1; lit4 0xaaf64 0; lit1 0xaaf5c 1;
atom8 0xa80b8 rSB;
YP09.mkRegion None 0xa80c8 0xa80d0 0 0 [YP09.mkChunk 0xa80c8 (CVal 8 (SOff rSB (2 ^ 37)))];
lit8 0xa80d0 0; lit8 0xa80c0 0xffffffff;
lit8 0x103b8 0xafffff00000fffff; lits8 0x10438 CTZ_TABLE; lits8 0x10538 CTZ_TABLE;
lit8 0xa2848 0xa8ef8; lit8 0xa2850 0xab6f8; lit8 0xa2858 0xac3e8; lit8 0xa2860 0xac3f0; lit8 0xa2868 0xac3e0;
lit8 0xa2870 0xa46d0; lit8 0xa2830 0x13b1a0; lit8 0x13b1a0 4096; lit8 0x13d2a0 0xffffffffffffffff; lit8 0x13d2b8 0;
atom8 0xab6f8 rSHB; lit8 0xac3e0 0x7fffffffffff; lit8 0xac3e8 0; lit8 0xac3f0 0; lit8 0xa46d0 0x9bf08;
lit4 0x5de740 0; lit8 0x13d1c0 0;
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
sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 4%bv (SLit TFIB_TP)) 10%bv (SOff rT t_cache)) 11%bv (SOff rP 0)) 12%bv (SLit 0xa8098)) 13%bv (SOff rCL 0).
Definition SS0R : sstate := mkSS 0x37494 REGS0R REG0R None FR.
