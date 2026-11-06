(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
intros segs m a n1 n2 H1 H2. unfold wr_at. split.
- intros (Ha & Hb & H). Local Ltac2 Set LiaHints.tbl := fun () => "00>0>15538427734.1316044545734.1117101216130.1320927221579.1126981515745.1126983613675.144844197302.17 51508892605.1754736999318.1454743291548.1157036176010.1761783614061.1163513398541.137651745753.14 00000700>00E00L00P00T00Z00`00a00b00c00g00h00mS2H22HiS2H22HbS2H12HiS2H12HaS2HaS2HaS2Hi1HS2Hi1HFFSS2HbSS3Hb'".
repeat split; try lia.
+ intros i Hi. apply H. lia.
+ intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
- intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
intros i Hi. destruct (Z.lt_ge_cases i n1).
+ apply HA. lia.
+ replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rw_cells_app : forall segs m A cs1 cs2,
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
#[using="Type"] Lemma bytes_eq_of_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
induction l1 as [|b1 l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate; [reflexivity|].
injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.
#[using="Type"] Lemma rw_cells_recell_mid : forall segs m A pre mid post mid',
rw_cells segs m A (pre ++ mid ++ post) -> cells_wf mid' ->
map bv_unsigned (cells_bytes mid') = map bv_unsigned (cells_bytes mid) ->
rw_cells segs m A (pre ++ mid' ++ post).
Proof.
intros segs m A pre mid post mid' RW WF E.
apply bytes_eq_of_unsigned in E.
destruct RW as [[Hwf Hb] Hw].
apply cells_wf_app in Hwf. destruct Hwf as [W1 W23]. apply cells_wf_app in W23. destruct W23 as [W2 W3].
assert (SZ : cells_size mid' = cells_size mid).
{ rewrite <- (cells_bytes_length mid' WF), <- (cells_bytes_length mid W2), E. reflexivity. }
split; [split|].
- apply cells_wf_app. split; [exact W1|]. apply cells_wf_app. split; assumption.
- rewrite !cells_bytes_app in *. rewrite E. exact Hb.
- rewrite !cells_size_app in *. rewrite SZ. exact Hw.
Qed.
#[using="Type"] Lemma Z_to_le_bytes_add : forall a b z, Z_to_le_bytes (a + b) z = Z_to_le_bytes a z ++ Z_to_le_bytes b (Z.shiftr z (8 * Z.of_nat a)).
Proof.
induction a as [|a IH]; intros b z; cbn [Z_to_le_bytes Nat.add app].
- rewrite Z.shiftr_0_r. reflexivity.
- f_equal. rewrite IH. f_equal. f_equal. Local Ltac2 Set LiaHints.tbl := fun () => "0020=53891794422.57537770688.5 000001002SS".
rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma le8_small_split : forall v, (0 <= v < 2^32)%Z -> le8 (Z_to_bv 64 v) = le4 (Z_to_bv 64 v) ++ le4 (Z_to_bv 64 0).
Proof.
intros v Hv. unfold le8, le4, word_to_le_bytes. Local Ltac2 Set LiaHints.tbl := fun () => "0040=29442573076.336557432084.344015170280.353519161044.300000400800900:S2HvS2HvSS".
rewrite !unsigned_lit by lia.
change 8%nat with (4 + 4)%nat at 1. rewrite Z_to_le_bytes_add. f_equal.
change (8 * Z.of_nat 4)%Z with 32%Z. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rw_cells_C8_C4C4 : forall segs m A pre post v,
rw_cells segs m A (pre ++ C8 (Z_to_bv 64 v) :: post) -> (0 <= v < 2^32)%Z ->
rw_cells segs m A (pre ++ C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 0) :: post).
Proof.
intros segs m A pre post v H Hv.
change (pre ++ C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 0) :: post) with (pre ++ [C4 (Z_to_bv 64 v); C4 (Z_to_bv 64 0)] ++ post).
eapply rw_cells_recell_mid with (mid := [C8 (Z_to_bv 64 v)]); [exact H | cbv; repeat split |].
cbn [cells_bytes cbytes app]. rewrite app_nil_r. rewrite (le8_small_split v Hv). reflexivity.
Qed.
End CANSEC1.
