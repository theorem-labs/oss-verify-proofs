(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/YFk6cf.v (commit f01d79f3fb5, cf refill round 3; file sha256 cebffe420017) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 8 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code (strictcmp3 65688e94214a, by funcpair_reply 6963bc4a94fc on the cgif twin ce511d541cda; 7 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair); 4 hand maps (resolve-run-f01d79f3fb5.tsv (sha256 ba54f3af32ab; internal record), each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (ReallocPrimary.CfW, lane W, cf refill re-base, B3 half; base a working branch on a working branch d50ec3c8a93a): YFk6cf, the cf twin of YFk6.v (this tree's copy, = c5 8d6c9f45705b).
   A hand port of YFk6.v at commit 8d6c9f45705b (its mechanical part scripted outside the tree): imports YFkpcf / YFhmcf / YFhncf and the B3 cf twins; RI+68 is the junk
   atom rJEX = 55 of YFkpcf with value jex (0 <= jex < 2 ^ 8), so the B3 atoms are 56..69; the text is otherwise YFk6.v verbatim.
   EVENT-FREE: no st_nev, EV_A, EV_MAX, EV_BIG, mtr_ok, aregime, refill_reg, qloosem or non-cf abudget.
   rule 24: no function proved (kind: re-base of the proved refill walk onto the cf instance). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFhy YFkpcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 6. Set Printing Width 250.
Definition rNEED : nat := 56. Definition rTOT : nat := 57. Definition rADR : nat := 58. Definition rSHA : nat := 59. Definition rMU2 : nat := 60.
Definition rNCe : nat := 61. Definition rNCg : nat := 62. Definition rNFe : nat := 63. Definition rNFg : nat := 64.
Definition rFADR : nat := 65. Definition rSHF : nat := 66. Definition rMF2 : nat := 67. Definition rAUe : nat := 68. Definition rAUg : nat := 69.
Definition aHAV3 : nat := 96.
Definition FR3 : facts := mkFacts
(f_atoms FR ++
[ (rNEED, mkAF 1 8 0);
(rTOT, mkAF 16 3758161920 4);
(rADR, mkAF kHighMemBeg CEIL_MAX 16);
(rSHA, mkAF 0x5c8710 kHighMemBeg 12);
(rMU2, mkAF 262144 3758358528 18);
(rNCe, mkAF 0 (2 ^ 28) 0); (rNCg, mkAF 0 (2 ^ 28) 0); (rNFe, mkAF 0 (2 ^ 29) 0); (rNFg, mkAF 0 (2 ^ 29) 0);
(rFADR, mkAF kHighMemBeg CEIL_MAX 16);
(rSHF, mkAF 0x5c8710 kHighMemBeg 12);
(rMF2, mkAF 262144 (2 ^ 29 + 262144) 18);
(rAUe, mkAF 0 3758358528 4); (rAUg, mkAF 0 3758358528 4) ]) [] [].
Definition REG0R3 : smem := REG0R ++ [lit8 0x137ce8 0x1010101; lit8 0x9da10 1; lit8 0x9da18 0x137bdc; lit4 0x137bdc 0].
Definition SS0R3 : sstate := mkSS 0x369c8 REGS0R REG0R3 None FR3.
