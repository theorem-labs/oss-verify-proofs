(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Mem Frame Cells Step Arr Exec RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs R_cache_defs R_thread R_asan_defs R_allocate1 RT_state RT_rep RT_maltail RT_reatail RT_malcore_stmt RT_reacore_stmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition rcore_case (P : Z -> Prop) : Prop :=
  forall (Σ : rtsA) (PMc : Model -> Prop) (mX : mem) (B : Z)
         (gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (tr : list Z) (tb : list word) (j0 : list byte),
  fdfs_only PMc -> mat_stable PMc -> P n -> 1 <= n <= 0x8000000 ->
  live_room (live Σ) n -> mcost n <= credit Σ ->      (* [comment removed for export] *)
  ART_A Σ mX -> mem_inv ctasegs mX ->
  stk ctasegs mX lo (B + -200) -> l_ACEIL (lay Σ) <= lo -> lo + 0x1000 <= B + -200 -> B + 2144 <= USTACK_TOP -> B mod 16 = 8 ->
  In tr T_MAIN -> (1 <= length tr <= TR_MAX)%nat -> trc_cells B tr mX tb ->
  raf_cells B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A mX j0 ->
  cps ctasegs (ASTA RTA Σ PMc (eq (rcore_entry Σ B gp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc n mX)))
            (rcore_post Σ PMc B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A n lo mX).

Definition rcore_stmt_sec : Prop := rcore_case (fun n => 64512 < n).

(* [comment removed for export] *)
Lemma rcore_prim_case : core_stmt_realloc -> rcore_case (fun n => n <= 64512).
Proof. intros H. unfold rcore_case. intros. eapply H; try eassumption. lia. Qed.
