(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BLPropExec BMState BMem BCells BExec BStep BLFrame.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.

Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma rw_cells_CB_split : forall segs m A n k junk,
  rw_cells segs m A [CB n junk] -> (k <= n)%nat ->
  rw_cells segs m A [CB k (firstn k junk)] /\ rw_cells segs m (A + Z.of_nat k) [CB (n - k) (skipn k junk)].
Proof.
  intros segs m A n k junk H Hk.
  assert (E : rw_cells segs m A ([CB k (firstn k junk)] ++ [CB (n - k) (skipn k junk)])).
  { destruct H as [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [L _].
    split; [split|].
    - cbn. rewrite firstn_length, skipn_length. repeat split; lia.
    - cbn [cells_bytes cbytes app]. rewrite app_nil_r, firstn_skipn. cbn [cells_bytes cbytes app] in Hb. rewrite app_nil_r in Hb. exact Hb.
    - cbn [cells_size csize app] in *. replace (k + (n - k + 0))%nat with (n + 0)%nat by lia. exact Hw. }
  apply rw_cells_app in E. cbn [cells_size csize Nat.add] in E. rewrite Nat.add_0_r in E. exact E.
Qed.

Lemma rw_cells_CB_join : forall segs m A n1 n2 b1 b2,
  rw_cells segs m A [CB n1 b1] -> rw_cells segs m (A + Z.of_nat n1) [CB n2 b2] ->
  rw_cells segs m A [CB (n1 + n2) (b1 ++ b2)].
Proof.
  intros segs m A n1 n2 b1 b2 H1 H2.
  assert (E : rw_cells segs m A ([CB n1 b1] ++ [CB n2 b2])).
  { apply rw_cells_app. cbn [cells_size csize]. rewrite Nat.add_0_r. split; assumption. }
  destruct E as [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as (L1 & L2 & _).
  split; [split|].
  - cbn. rewrite length_app. repeat split; lia.
  - cbn [cells_bytes cbytes app] in *. rewrite app_nil_r in *. exact Hb.
  - cbn [cells_size csize app] in *. rewrite Nat.add_0_r in *. replace (n1 + n2 + 0)%nat with (n1 + n2)%nat by lia. exact Hw.
Qed.
