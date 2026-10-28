(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Mem ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import SegRw. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_intalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma seg_rw_IAP1 : seg_rw_ok bsegs (IAP + 8) 0x40000 = true. Proof. vm_compute. reflexivity. Qed.
Lemma seg_rw_IAP2 : seg_rw_ok bsegs (IAP + 0x40040) 0xd80 = true. Proof. vm_compute. reflexivity. Qed.
Lemma seg_rw_IAP3 : seg_rw_ok bsegs (IAP + 0x40dc0) 0x40248 = true. Proof. vm_compute. reflexivity. Qed.
