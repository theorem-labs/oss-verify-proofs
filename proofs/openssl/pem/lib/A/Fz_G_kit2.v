(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs Fz_kit Fz_G_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma wg_keep_live_nw : forall live frames sp W (m m' : mem) p n X cs, rw_cells asegs m X cs -> rt_pres_fp live frames sp W m m' ->
  In (p, n) live -> p <= X -> X + Z.of_nat (cells_size cs) <= p + n ->
  (forall x, X <= x < X + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells asegs m' X cs.
Proof.
  intros live frames sp W m m' p n X cs H PR IN H1 H2 HO. apply (rw_cells_agree_nw asegs m m' X cs H).
  intros a Ha. apply PR; [|exact (HO _ Ha)]. right; right; left. exists p, n. split; [exact IN | lia].
Qed.

Lemma wg_keep_static_nw : forall live frames sp W (m m' : mem) X cs, rw_cells asegs m X cs -> rt_pres_fp live frames sp W m m' ->
  (forall x, X <= x < X + Z.of_nat (cells_size cs) -> client_static x /\ outside W x) -> rw_cells asegs m' X cs.
Proof.
  intros live frames sp W m m' X cs H PR HO. apply (rw_cells_agree_nw asegs m m' X cs H).
  intros a Ha. destruct (HO _ Ha) as [S O]. apply PR; [right; left; exact S | exact O].
Qed.

Lemma wg_keep_seg_nw : forall W (m m' : mem) X cs, rw_cells asegs m X cs -> munch W m m' ->
  (forall x, X <= x < X + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells asegs m' X cs.
Proof. intros W m m' X cs H MU HO. apply (rw_cells_agree_nw asegs m m' X cs H). intros a Ha. apply MU. exact (HO _ Ha). Qed.

(* [comment removed for export] *)
Ltac cl_keep_nw H AG H' :=
  lazymatch type of H with
  | rw_cells _ ?m ?a ?cs =>
      lazymatch type of AG with forall a k, _ -> _ -> agree_on _ m ?m' =>
        assert (H' : rw_cells asegs m' a cs)
          by (apply (rw_cells_agree_nw asegs m m' a cs H); apply AG; [lia | cbn [cells_size csize Nat.add]; unfold USTACK_TOP in *; lia]) end
  end.
