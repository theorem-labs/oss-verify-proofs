(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YFk6.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to omx-clap-core/fuzz_manifest's ASan build. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YB1q YF0l YF0m YF0x YFl0 YFhy YFkp.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 6. Set Printing Width 250.
Definition rNEED : nat := 55. Definition rTOT : nat := 56. Definition rADR : nat := 57. Definition rSHA : nat := 58. Definition rMU2 : nat := 59.
Definition rNCe : nat := 60. Definition rNCg : nat := 61. Definition rNFe : nat := 62. Definition rNFg : nat := 63.
Definition rFADR : nat := 64. Definition rSHF : nat := 65. Definition rMF2 : nat := 66. Definition rAUe : nat := 67. Definition rAUg : nat := 68.
Definition aHAV3 : nat := 96.
Definition FR3 : facts := mkFacts
(f_atoms FR ++
[ (rNEED, mkAF 1 8 0);
(rTOT, mkAF 16 3758161920 4);
(rADR, mkAF kHighMemBeg CEIL_MAX 16);
(rSHA, mkAF 0x5c46d0 kHighMemBeg 12);
(rMU2, mkAF 262144 3758358528 18);
(rNCe, mkAF 0 (2 ^ 28) 0); (rNCg, mkAF 0 (2 ^ 28) 0); (rNFe, mkAF 0 (2 ^ 29) 0); (rNFg, mkAF 0 (2 ^ 29) 0);
(rFADR, mkAF kHighMemBeg CEIL_MAX 16);
(rSHF, mkAF 0x5c46d0 kHighMemBeg 12);
(rMF2, mkAF 262144 (2 ^ 29 + 262144) 18);
(rAUe, mkAF 0 3758358528 4); (rAUg, mkAF 0 3758358528 4) ]) [] [].
Definition REG0R3 : smem := REG0R ++ [lit8 0x133ca8 0x1010101; lit8 0x99cd8 1; lit8 0x99ce0 0x133b9c; lit4 0x133b9c 0].
Definition SS0R3 : sstate := mkSS 0x3628c REGS0R REG0R3 None FR3.
