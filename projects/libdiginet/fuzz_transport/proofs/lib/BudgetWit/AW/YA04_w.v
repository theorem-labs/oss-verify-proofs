(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YA04.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YA04.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Modified by Theorem Labs, 2026-11: internal commit ids in comments replaced by public commits or removed. *)
(* Relocated from proofs/libreac/fuzz_grant/lib/YA04.v by port_core 83f5203d2a2f onto libdiginet/fuzz_transport (asan). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK15.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK00 YK04.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.BudgetWit.AW Require Import YK05_w.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK0c YK0e YK0f YK09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.BudgetWit.AW Require Import YA0c_w.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.BudgetWit.AW Require Import YA0e_w.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
Section a.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable TOP : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Definition OBL_mmap2 : Prop := mm2_stmt SEGS A nx0 LIMIT TOP SINV argH FS0 (node_mmap2g A nx0 LIMIT).
Definition OBL_mmapin : Prop := forall hole : bool, mm3_stmt SEGS A nx0 LIMIT TOP SINV argH FS0 (node_mmapin_g A LIMIT hole).
Definition OBL_mmapin2 : Prop := mm2_stmt SEGS A nx0 LIMIT TOP SINV argH FS0 (node_mmapin2_g A LIMIT).
Definition OBL_mprotect2 : Prop := mm2_stmt SEGS A nx0 LIMIT TOP SINV argH FS0 (node_mprotect2g A LIMIT).
End a.
