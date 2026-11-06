(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma wr_at_not_ro : forall m A n, mem_inv usegs m -> wr_at usegs m A n -> 0 < n ->
  A + n <= 0x10000 \/ 0x36000 <= A.
Proof.
  intros m A n Hinv (HA & Hn & Hw) Hpos.
  assert (Hro : forall x, 65536 <= x < 221184 -> wview usegs m (wa x) = None).
  { intros x Hx.
    assert (Ux : bv_unsigned (wa x) = x) by (apply wa_unsigned; lia).
    assert (R : ro_addr usegs (wa x) = true).
    { rewrite u_ro_addr, Ux. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    unfold wview. destruct (m (wa x)) as [b|] eqn:E.
    - apply Hinv in E. congruence.
    - unfold ro_addr in R.
      destruct (find_segment usegs (bv_unsigned (wa x)) 1) as [s|]; [|discriminate].
      destruct (seg_writable s); [discriminate|reflexivity]. }
  destruct (Z_lt_le_dec A 65536) as [Hlo|Hlo].
  - destruct (Z_le_gt_dec (A + n) 65536) as [H|H]; [left; exact H|].
    exfalso. apply (Hw (65536 - A)); [lia|].
    replace (A + (65536 - A)) with 65536 by lia. apply Hro. lia.
  - destruct (Z_lt_le_dec A 221184) as [H|H]; [|right; exact H].
    exfalso. apply (Hw 0); [lia|]. rewrite Z.add_0_r. apply Hro. lia.
Qed.

Lemma rw_cells_not_ro : forall m A cs, mem_inv usegs m -> rw_cells usegs m A cs -> (0 < cells_size cs)%nat ->
  A + Z.of_nat (cells_size cs) <= 0x10000 \/ 0x36000 <= A.
Proof.
  intros m A cs Hinv (_ & Hw) Hpos.
  apply (wr_at_not_ro m A _ Hinv Hw). lia.
Qed.

Lemma stk_not_ro : forall m lo hi, mem_inv usegs m -> stk usegs m lo hi -> lo < hi ->
  hi <= 0x10000 \/ 0x36000 <= lo.
Proof.
  intros m lo hi inv_m (lo_nonneg & hi_fits & stk_bytes) lo_lt_hi.
  replace hi with (lo + (hi - lo)) by ring.
  apply (wr_at_not_ro m lo (hi - lo) inv_m).
  2: { apply Z.lt_0_sub. exact lo_lt_hi. }
  refine (conj lo_nonneg (conj _ _)).
  - lia.
  - intros off off_in_span.
    assert (addr_in_stk : lo <= lo + off < hi) by lia.
    destruct (stk_bytes (lo + off) addr_in_stk) as [wview_some _].
    exact wview_some.
Qed.
