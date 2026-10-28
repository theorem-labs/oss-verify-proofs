(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Mem Frame Cells Step Arr RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface R_cache_defs R_prim_defs R_m2s R_fs_defs R_tlsgetaddr RT_state RT_rep RT_facts0 RT_sep RT_facts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section IC2.
Variables (Σ : rtsA) (m : mem).
Hypothesis HA : ART_A Σ m.

(* [comment removed for export] *)
Local Ltac pick := let IC := fresh "IC" in
  pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & IC); unfold icells_rep in IC;
  repeat lazymatch type of IC with _ /\ _ => let X := fresh "X" in destruct IC as [X IC] end;
  lazymatch goal with |- ?G => match goal with H : G |- _ => exact H end end.

(* [comment removed for export] *)
Lemma rta_real_strcpy : ro_cells ctasegs m 0x5ac450 [C8 (Z_to_bv 64 0x52b730)].
Proof. pick. Qed.
End IC2.
