(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma wr_at_not_ro : forall m A n, mem_inv usegs m -> wr_at usegs m A n -> 0 < n ->
  A + n <= 0x10000 \/ 0x36000 <= A.
Proof.
  intros m A n MI (A0 & AN & W) Hn.
  destruct (Z.le_gt_cases (A + n) 0x10000) as [L|L]; [left; exact L|].
  destruct (Z.le_gt_cases 0x36000 A) as [G|G]; [right; exact G|]. exfalso.
  set (x := Z.max A 0x10000).
  assert (RX : A <= x < A + n /\ 0x10000 <= x < 0x36000) by (unfold x; lia).
  specialize (W (x - A) ltac:(lia)). replace (A + (x - A)) with x in W by lia.
  assert (RO : ro_addr usegs (wa x) = false).
  { destruct (m (wa x)) as [b|] eqn:E; [exact (MI _ _ E)| exact (wview_not_ro usegs m (wa x) W E)]. }
  rewrite u_ro_addr in RO. unfold wa in RO. rewrite unsigned_lit in RO by lia.
  destruct RX as [_ [R1 R2]].
  replace (0x10000 <=? x) with true in RO by (symmetry; apply Z.leb_le; lia).
  replace (x <? 0x36000) with true in RO by (symmetry; apply Z.ltb_lt; lia). discriminate RO.
Qed.

Lemma rw_cells_not_ro : forall m A cs, mem_inv usegs m -> rw_cells usegs m A cs -> (0 < cells_size cs)%nat ->
  A + Z.of_nat (cells_size cs) <= 0x10000 \/ 0x36000 <= A.
Proof. intros m A cs MI [_ W] Hn. apply (wr_at_not_ro m A _ MI W). lia. Qed.

Lemma stk_not_ro : forall m lo hi, mem_inv usegs m -> stk usegs m lo hi -> lo < hi ->
  hi <= 0x10000 \/ 0x36000 <= lo.
Proof.
  intros m lo hi MI (L0 & H0 & S) Hlt.
  assert (W : wr_at usegs m lo (hi - lo)).
  { split; [lia|]. split; [lia|]. intros i Hi. apply (S (lo + i)). lia. }
  pose proof (wr_at_not_ro m lo (hi - lo) MI W ltac:(lia)). lia.
Qed.
