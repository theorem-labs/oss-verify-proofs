(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YA00.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YA00.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses; none is left, and the file is kept for its Requires, because 7 files of lib/BudgetWit Require it. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK16 YK11 YK15.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK0y YK00 YK01 YK13 YK0v YK02 YK04 YK0g YK06.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.BudgetWit.AW Require Import YA05_w.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope Z_scope.
