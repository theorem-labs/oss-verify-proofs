(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/YFk6cf.v (commit eb934de95d13, blob 056b8244e01d) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 8 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFhy YFkpcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
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
(rSHA, mkAF 0x5cd510 kHighMemBeg 12);
(rMU2, mkAF 262144 3758358528 18);
(rNCe, mkAF 0 (2 ^ 28) 0); (rNCg, mkAF 0 (2 ^ 28) 0); (rNFe, mkAF 0 (2 ^ 29) 0); (rNFg, mkAF 0 (2 ^ 29) 0);
(rFADR, mkAF kHighMemBeg CEIL_MAX 16);
(rSHF, mkAF 0x5cd510 kHighMemBeg 12);
(rMF2, mkAF 262144 (2 ^ 29 + 262144) 18);
(rAUe, mkAF 0 3758358528 4); (rAUg, mkAF 0 3758358528 4) ]) [] [].
Definition REG0R3 : smem := REG0R ++ [lit8 0x13cae8 0x1010101; lit8 0xa2050 1; lit8 0xa2058 0x13c9dc; lit4 0x13c9dc 0].
Definition SS0R3 : sstate := mkSS 0x373a8 REGS0R REG0R3 None FR3.
