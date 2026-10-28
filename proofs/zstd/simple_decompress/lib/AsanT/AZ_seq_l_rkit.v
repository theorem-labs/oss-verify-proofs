(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_hkit .
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Ltac kxa_norm ::= unfold shspan in *.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac kxl_hyp ::= lazymatch goal with |- ?G => first [ match goal with H : G |- _ => exact H end | match goal with H : rheld G |- _ => exact H end ] end.
Ltac kxa_rng ::= first [ kxl_hyp | kxa_rng0 ].
Ltac kxl_rng ::=
  first [ kxl_hyp
        | lazymatch goal with |- rng ?RNG ?A ?N => match goal with H : rng RNG ?A0 ?N0 |- _ => apply (rng_sub' RNG A0 N0 A N H); solve [kxl_lia_small] end end
        | kx_rng ].
(* [comment removed for export] *)

Definition sql_ring_cells (rl rm ro : Z -> Z) : list cell := [C8 (Z_to_bv 64 (rl 0)); C8 (Z_to_bv 64 (rm 0)); C8 (Z_to_bv 64 (ro 0)); C8 (Z_to_bv 64 (rl 1)); C8 (Z_to_bv 64 (rm 1)); C8 (Z_to_bv 64 (ro 1)); C8 (Z_to_bv 64 (rl 2)); C8 (Z_to_bv 64 (rm 2)); C8 (Z_to_bv 64 (ro 2)); C8 (Z_to_bv 64 (rl 3)); C8 (Z_to_bv 64 (rm 3)); C8 (Z_to_bv 64 (ro 3)); C8 (Z_to_bv 64 (rl 4)); C8 (Z_to_bv 64 (rm 4)); C8 (Z_to_bv 64 (ro 4)); C8 (Z_to_bv 64 (rl 5)); C8 (Z_to_bv 64 (rm 5)); C8 (Z_to_bv 64 (ro 5)); C8 (Z_to_bv 64 (rl 6)); C8 (Z_to_bv 64 (rm 6)); C8 (Z_to_bv 64 (ro 6)); C8 (Z_to_bv 64 (rl 7)); C8 (Z_to_bv 64 (rm 7)); C8 (Z_to_bv 64 (ro 7))].

Lemma sql_ring_open : forall (m : amem) A pre post rl rm ro,
  rw_cells bsegs m A (pre ++ CB 192 (sql_ring_bytes rl rm ro) :: post) -> rw_cells bsegs m A (pre ++ sql_ring_cells rl rm ro ++ post).
Proof.
  intros m A pre post rl rm ro H. pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 [_ W2]].
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact W1|]. apply cells_wf_app. split; [|exact W2]. cbn [sql_ring_cells cells_wf cell_wf]. repeat split.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes sql_ring_cells]. unfold sql_ring_bytes. rewrite !app_nil_r, <- !app_assoc. reflexivity.
Qed.

Lemma sql_ring_close : forall (m : amem) A pre post rl rm ro,
  rw_cells bsegs m A (pre ++ sql_ring_cells rl rm ro ++ post) -> rw_cells bsegs m A (pre ++ CB 192 (sql_ring_bytes rl rm ro) :: post).
Proof.
  intros m A pre post rl rm ro H. pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 W2]. apply cells_wf_app in W2. destruct W2 as [_ W2].
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact W1|]. split; [|exact W2]. cbn [cell_wf]. unfold sql_ring_bytes. rewrite !length_app, !length_le8. reflexivity.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes sql_ring_cells]. unfold sql_ring_bytes. rewrite !app_nil_r, <- !app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Definition ring_upd (f : Z -> Z) (c v : Z) : Z -> Z := fun j => if j =? c then v else f j.

Lemma sql_ring_ok_upd : forall v rl rm ro c a b d, sql_ring_ok v rl rm ro ->
  0 <= a < 2^18 -> 0 <= b < 2^18 -> 0 <= d < 2^64 -> sql_ring_ok v (ring_upd rl c a) (ring_upd rm c b) (ring_upd ro c d).
Proof.
  intros v rl rm ro c a b d OK Ha Hb Hd j Hj. unfold ring_upd. destruct (Z.eqb_spec j c); [repeat split; lia | apply OK; exact Hj].
Qed.

Lemma sql_ring_ok_grow : forall v rl rm ro a b d, sql_ring_ok v rl rm ro ->
  0 <= a < 2^18 -> 0 <= b < 2^18 -> 0 <= d < 2^64 -> sql_ring_ok (v + 1) (ring_upd rl v a) (ring_upd rm v b) (ring_upd ro v d).
Proof.
  intros v rl rm ro a b d OK Ha Hb Hd j Hj. unfold ring_upd. destruct (Z.eqb_spec j v); [repeat split; lia | apply OK; lia].
Qed.

Lemma sql_ring_ok_le : forall v v' rl rm ro, sql_ring_ok v rl rm ro -> v' <= v -> sql_ring_ok v' rl rm ro.
Proof. intros v v' rl rm ro OK L j Hj. apply OK. lia. Qed.

Lemma sql_ring_open_0 : forall (m : amem) A pre post rl rm ro a b d, a = rl 0 -> b = rm 0 -> d = ro 0 ->
  rw_cells bsegs m A (pre ++ CB 192 (sql_ring_bytes rl rm ro) :: post) -> rw_cells bsegs m A (pre ++ [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 d); CB 168 (le8 (Z_to_bv 64 (rl 1)) ++ le8 (Z_to_bv 64 (rm 1)) ++ le8 (Z_to_bv 64 (ro 1)) ++ le8 (Z_to_bv 64 (rl 2)) ++ le8 (Z_to_bv 64 (rm 2)) ++ le8 (Z_to_bv 64 (ro 2)) ++ le8 (Z_to_bv 64 (rl 3)) ++ le8 (Z_to_bv 64 (rm 3)) ++ le8 (Z_to_bv 64 (ro 3)) ++ le8 (Z_to_bv 64 (rl 4)) ++ le8 (Z_to_bv 64 (rm 4)) ++ le8 (Z_to_bv 64 (ro 4)) ++ le8 (Z_to_bv 64 (rl 5)) ++ le8 (Z_to_bv 64 (rm 5)) ++ le8 (Z_to_bv 64 (ro 5)) ++ le8 (Z_to_bv 64 (rl 6)) ++ le8 (Z_to_bv 64 (rm 6)) ++ le8 (Z_to_bv 64 (ro 6)) ++ le8 (Z_to_bv 64 (rl 7)) ++ le8 (Z_to_bv 64 (rm 7)) ++ le8 (Z_to_bv 64 (ro 7)))] ++ post).
Proof.
  intros m A pre post rl rm ro a b d -> -> -> H. pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 [_ W2]].
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact W1|]. apply cells_wf_app. split; [|exact W2]. cbn [cells_wf cell_wf]. rewrite ?length_app, ?length_le8. repeat split.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. unfold sql_ring_bytes. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.
Lemma sql_ring_shut_0 : forall (m : amem) A pre post rl rm ro,
  rw_cells bsegs m A (pre ++ [C8 (Z_to_bv 64 (rl 0)); C8 (Z_to_bv 64 (rm 0)); C8 (Z_to_bv 64 (ro 0)); CB 168 (le8 (Z_to_bv 64 (rl 1)) ++ le8 (Z_to_bv 64 (rm 1)) ++ le8 (Z_to_bv 64 (ro 1)) ++ le8 (Z_to_bv 64 (rl 2)) ++ le8 (Z_to_bv 64 (rm 2)) ++ le8 (Z_to_bv 64 (ro 2)) ++ le8 (Z_to_bv 64 (rl 3)) ++ le8 (Z_to_bv 64 (rm 3)) ++ le8 (Z_to_bv 64 (ro 3)) ++ le8 (Z_to_bv 64 (rl 4)) ++ le8 (Z_to_bv 64 (rm 4)) ++ le8 (Z_to_bv 64 (ro 4)) ++ le8 (Z_to_bv 64 (rl 5)) ++ le8 (Z_to_bv 64 (rm 5)) ++ le8 (Z_to_bv 64 (ro 5)) ++ le8 (Z_to_bv 64 (rl 6)) ++ le8 (Z_to_bv 64 (rm 6)) ++ le8 (Z_to_bv 64 (ro 6)) ++ le8 (Z_to_bv 64 (rl 7)) ++ le8 (Z_to_bv 64 (rm 7)) ++ le8 (Z_to_bv 64 (ro 7)))] ++ post) -> rw_cells bsegs m A (pre ++ CB 192 (sql_ring_bytes rl rm ro) :: post).
Proof.
  intros m A pre post rl rm ro H. pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 W2]. apply cells_wf_app in W2. destruct W2 as [_ W2].
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact W1|]. split; [|exact W2]. cbn [cell_wf]. unfold sql_ring_bytes. rewrite !length_app, !length_le8. reflexivity.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. unfold sql_ring_bytes. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.
Lemma sql_ring_close_0 : forall (m : amem) A pre post rl rm ro a b d,
  rw_cells bsegs m A (pre ++ [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 d); CB 168 (le8 (Z_to_bv 64 (rl 1)) ++ le8 (Z_to_bv 64 (rm 1)) ++ le8 (Z_to_bv 64 (ro 1)) ++ le8 (Z_to_bv 64 (rl 2)) ++ le8 (Z_to_bv 64 (rm 2)) ++ le8 (Z_to_bv 64 (ro 2)) ++ le8 (Z_to_bv 64 (rl 3)) ++ le8 (Z_to_bv 64 (rm 3)) ++ le8 (Z_to_bv 64 (ro 3)) ++ le8 (Z_to_bv 64 (rl 4)) ++ le8 (Z_to_bv 64 (rm 4)) ++ le8 (Z_to_bv 64 (ro 4)) ++ le8 (Z_to_bv 64 (rl 5)) ++ le8 (Z_to_bv 64 (rm 5)) ++ le8 (Z_to_bv 64 (ro 5)) ++ le8 (Z_to_bv 64 (rl 6)) ++ le8 (Z_to_bv 64 (rm 6)) ++ le8 (Z_to_bv 64 (ro 6)) ++ le8 (Z_to_bv 64 (rl 7)) ++ le8 (Z_to_bv 64 (rm 7)) ++ le8 (Z_to_bv 64 (ro 7)))] ++ post) -> rw_cells bsegs m A (pre ++ CB 192 (sql_ring_bytes (ring_upd rl 0 a) (ring_upd rm 0 b) (ring_upd ro 0 d)) :: post).
Proof.
  intros m A pre post rl rm ro a b d H. pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 W2]. apply cells_wf_app in W2. destruct W2 as [_ W2].
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact W1|]. split; [|exact W2]. cbn [cell_wf]. unfold sql_ring_bytes. rewrite !length_app, !length_le8. reflexivity.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. unfold sql_ring_bytes, ring_upd. cbn [Z.eqb Pos.eqb]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Lemma sql_ring_open_1 : forall (m : amem) A pre post rl rm ro a b d, a = rl 1 -> b = rm 1 -> d = ro 1 ->
  rw_cells bsegs m A (pre ++ CB 192 (sql_ring_bytes rl rm ro) :: post) -> rw_cells bsegs m A (pre ++ [CB 24 (le8 (Z_to_bv 64 (rl 0)) ++ le8 (Z_to_bv 64 (rm 0)) ++ le8 (Z_to_bv 64 (ro 0))); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 d); CB 144 (le8 (Z_to_bv 64 (rl 2)) ++ le8 (Z_to_bv 64 (rm 2)) ++ le8 (Z_to_bv 64 (ro 2)) ++ le8 (Z_to_bv 64 (rl 3)) ++ le8 (Z_to_bv 64 (rm 3)) ++ le8 (Z_to_bv 64 (ro 3)) ++ le8 (Z_to_bv 64 (rl 4)) ++ le8 (Z_to_bv 64 (rm 4)) ++ le8 (Z_to_bv 64 (ro 4)) ++ le8 (Z_to_bv 64 (rl 5)) ++ le8 (Z_to_bv 64 (rm 5)) ++ le8 (Z_to_bv 64 (ro 5)) ++ le8 (Z_to_bv 64 (rl 6)) ++ le8 (Z_to_bv 64 (rm 6)) ++ le8 (Z_to_bv 64 (ro 6)) ++ le8 (Z_to_bv 64 (rl 7)) ++ le8 (Z_to_bv 64 (rm 7)) ++ le8 (Z_to_bv 64 (ro 7)))] ++ post).
Proof.
  intros m A pre post rl rm ro a b d -> -> -> H. pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 [_ W2]].
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact W1|]. apply cells_wf_app. split; [|exact W2]. cbn [cells_wf cell_wf]. rewrite ?length_app, ?length_le8. repeat split.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. unfold sql_ring_bytes. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.
Lemma sql_ring_shut_1 : forall (m : amem) A pre post rl rm ro,
  rw_cells bsegs m A (pre ++ [CB 24 (le8 (Z_to_bv 64 (rl 0)) ++ le8 (Z_to_bv 64 (rm 0)) ++ le8 (Z_to_bv 64 (ro 0))); C8 (Z_to_bv 64 (rl 1)); C8 (Z_to_bv 64 (rm 1)); C8 (Z_to_bv 64 (ro 1)); CB 144 (le8 (Z_to_bv 64 (rl 2)) ++ le8 (Z_to_bv 64 (rm 2)) ++ le8 (Z_to_bv 64 (ro 2)) ++ le8 (Z_to_bv 64 (rl 3)) ++ le8 (Z_to_bv 64 (rm 3)) ++ le8 (Z_to_bv 64 (ro 3)) ++ le8 (Z_to_bv 64 (rl 4)) ++ le8 (Z_to_bv 64 (rm 4)) ++ le8 (Z_to_bv 64 (ro 4)) ++ le8 (Z_to_bv 64 (rl 5)) ++ le8 (Z_to_bv 64 (rm 5)) ++ le8 (Z_to_bv 64 (ro 5)) ++ le8 (Z_to_bv 64 (rl 6)) ++ le8 (Z_to_bv 64 (rm 6)) ++ le8 (Z_to_bv 64 (ro 6)) ++ le8 (Z_to_bv 64 (rl 7)) ++ le8 (Z_to_bv 64 (rm 7)) ++ le8 (Z_to_bv 64 (ro 7)))] ++ post) -> rw_cells bsegs m A (pre ++ CB 192 (sql_ring_bytes rl rm ro) :: post).
Proof.
  intros m A pre post rl rm ro H. pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 W2]. apply cells_wf_app in W2. destruct W2 as [_ W2].
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact W1|]. split; [|exact W2]. cbn [cell_wf]. unfold sql_ring_bytes. rewrite !length_app, !length_le8. reflexivity.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. unfold sql_ring_bytes. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.
Lemma sql_ring_close_1 : forall (m : amem) A pre post rl rm ro a b d,
  rw_cells bsegs m A (pre ++ [CB 24 (le8 (Z_to_bv 64 (rl 0)) ++ le8 (Z_to_bv 64 (rm 0)) ++ le8 (Z_to_bv 64 (ro 0))); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 d); CB 144 (le8 (Z_to_bv 64 (rl 2)) ++ le8 (Z_to_bv 64 (rm 2)) ++ le8 (Z_to_bv 64 (ro 2)) ++ le8 (Z_to_bv 64 (rl 3)) ++ le8 (Z_to_bv 64 (rm 3)) ++ le8 (Z_to_bv 64 (ro 3)) ++ le8 (Z_to_bv 64 (rl 4)) ++ le8 (Z_to_bv 64 (rm 4)) ++ le8 (Z_to_bv 64 (ro 4)) ++ le8 (Z_to_bv 64 (rl 5)) ++ le8 (Z_to_bv 64 (rm 5)) ++ le8 (Z_to_bv 64 (ro 5)) ++ le8 (Z_to_bv 64 (rl 6)) ++ le8 (Z_to_bv 64 (rm 6)) ++ le8 (Z_to_bv 64 (ro 6)) ++ le8 (Z_to_bv 64 (rl 7)) ++ le8 (Z_to_bv 64 (rm 7)) ++ le8 (Z_to_bv 64 (ro 7)))] ++ post) -> rw_cells bsegs m A (pre ++ CB 192 (sql_ring_bytes (ring_upd rl 1 a) (ring_upd rm 1 b) (ring_upd ro 1 d)) :: post).
Proof.
  intros m A pre post rl rm ro a b d H. pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 W2]. apply cells_wf_app in W2. destruct W2 as [_ W2].
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact W1|]. split; [|exact W2]. cbn [cell_wf]. unfold sql_ring_bytes. rewrite !length_app, !length_le8. reflexivity.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. unfold sql_ring_bytes, ring_upd. cbn [Z.eqb Pos.eqb]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Lemma sql_ring_open_2 : forall (m : amem) A pre post rl rm ro a b d, a = rl 2 -> b = rm 2 -> d = ro 2 ->
  rw_cells bsegs m A (pre ++ CB 192 (sql_ring_bytes rl rm ro) :: post) -> rw_cells bsegs m A (pre ++ [CB 48 (le8 (Z_to_bv 64 (rl 0)) ++ le8 (Z_to_bv 64 (rm 0)) ++ le8 (Z_to_bv 64 (ro 0)) ++ le8 (Z_to_bv 64 (rl 1)) ++ le8 (Z_to_bv 64 (rm 1)) ++ le8 (Z_to_bv 64 (ro 1))); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 d); CB 120 (le8 (Z_to_bv 64 (rl 3)) ++ le8 (Z_to_bv 64 (rm 3)) ++ le8 (Z_to_bv 64 (ro 3)) ++ le8 (Z_to_bv 64 (rl 4)) ++ le8 (Z_to_bv 64 (rm 4)) ++ le8 (Z_to_bv 64 (ro 4)) ++ le8 (Z_to_bv 64 (rl 5)) ++ le8 (Z_to_bv 64 (rm 5)) ++ le8 (Z_to_bv 64 (ro 5)) ++ le8 (Z_to_bv 64 (rl 6)) ++ le8 (Z_to_bv 64 (rm 6)) ++ le8 (Z_to_bv 64 (ro 6)) ++ le8 (Z_to_bv 64 (rl 7)) ++ le8 (Z_to_bv 64 (rm 7)) ++ le8 (Z_to_bv 64 (ro 7)))] ++ post).
Proof.
  intros m A pre post rl rm ro a b d -> -> -> H. pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 [_ W2]].
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact W1|]. apply cells_wf_app. split; [|exact W2]. cbn [cells_wf cell_wf]. rewrite ?length_app, ?length_le8. repeat split.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. unfold sql_ring_bytes. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.
Lemma sql_ring_shut_2 : forall (m : amem) A pre post rl rm ro,
  rw_cells bsegs m A (pre ++ [CB 48 (le8 (Z_to_bv 64 (rl 0)) ++ le8 (Z_to_bv 64 (rm 0)) ++ le8 (Z_to_bv 64 (ro 0)) ++ le8 (Z_to_bv 64 (rl 1)) ++ le8 (Z_to_bv 64 (rm 1)) ++ le8 (Z_to_bv 64 (ro 1))); C8 (Z_to_bv 64 (rl 2)); C8 (Z_to_bv 64 (rm 2)); C8 (Z_to_bv 64 (ro 2)); CB 120 (le8 (Z_to_bv 64 (rl 3)) ++ le8 (Z_to_bv 64 (rm 3)) ++ le8 (Z_to_bv 64 (ro 3)) ++ le8 (Z_to_bv 64 (rl 4)) ++ le8 (Z_to_bv 64 (rm 4)) ++ le8 (Z_to_bv 64 (ro 4)) ++ le8 (Z_to_bv 64 (rl 5)) ++ le8 (Z_to_bv 64 (rm 5)) ++ le8 (Z_to_bv 64 (ro 5)) ++ le8 (Z_to_bv 64 (rl 6)) ++ le8 (Z_to_bv 64 (rm 6)) ++ le8 (Z_to_bv 64 (ro 6)) ++ le8 (Z_to_bv 64 (rl 7)) ++ le8 (Z_to_bv 64 (rm 7)) ++ le8 (Z_to_bv 64 (ro 7)))] ++ post) -> rw_cells bsegs m A (pre ++ CB 192 (sql_ring_bytes rl rm ro) :: post).
Proof.
  intros m A pre post rl rm ro H. pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 W2]. apply cells_wf_app in W2. destruct W2 as [_ W2].
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact W1|]. split; [|exact W2]. cbn [cell_wf]. unfold sql_ring_bytes. rewrite !length_app, !length_le8. reflexivity.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. unfold sql_ring_bytes. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.
Lemma sql_ring_close_2 : forall (m : amem) A pre post rl rm ro a b d,
  rw_cells bsegs m A (pre ++ [CB 48 (le8 (Z_to_bv 64 (rl 0)) ++ le8 (Z_to_bv 64 (rm 0)) ++ le8 (Z_to_bv 64 (ro 0)) ++ le8 (Z_to_bv 64 (rl 1)) ++ le8 (Z_to_bv 64 (rm 1)) ++ le8 (Z_to_bv 64 (ro 1))); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 d); CB 120 (le8 (Z_to_bv 64 (rl 3)) ++ le8 (Z_to_bv 64 (rm 3)) ++ le8 (Z_to_bv 64 (ro 3)) ++ le8 (Z_to_bv 64 (rl 4)) ++ le8 (Z_to_bv 64 (rm 4)) ++ le8 (Z_to_bv 64 (ro 4)) ++ le8 (Z_to_bv 64 (rl 5)) ++ le8 (Z_to_bv 64 (rm 5)) ++ le8 (Z_to_bv 64 (ro 5)) ++ le8 (Z_to_bv 64 (rl 6)) ++ le8 (Z_to_bv 64 (rm 6)) ++ le8 (Z_to_bv 64 (ro 6)) ++ le8 (Z_to_bv 64 (rl 7)) ++ le8 (Z_to_bv 64 (rm 7)) ++ le8 (Z_to_bv 64 (ro 7)))] ++ post) -> rw_cells bsegs m A (pre ++ CB 192 (sql_ring_bytes (ring_upd rl 2 a) (ring_upd rm 2 b) (ring_upd ro 2 d)) :: post).
Proof.
  intros m A pre post rl rm ro a b d H. pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 W2]. apply cells_wf_app in W2. destruct W2 as [_ W2].
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact W1|]. split; [|exact W2]. cbn [cell_wf]. unfold sql_ring_bytes. rewrite !length_app, !length_le8. reflexivity.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. unfold sql_ring_bytes, ring_upd. cbn [Z.eqb Pos.eqb]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Lemma sql_ring_open_3 : forall (m : amem) A pre post rl rm ro a b d, a = rl 3 -> b = rm 3 -> d = ro 3 ->
  rw_cells bsegs m A (pre ++ CB 192 (sql_ring_bytes rl rm ro) :: post) -> rw_cells bsegs m A (pre ++ [CB 72 (le8 (Z_to_bv 64 (rl 0)) ++ le8 (Z_to_bv 64 (rm 0)) ++ le8 (Z_to_bv 64 (ro 0)) ++ le8 (Z_to_bv 64 (rl 1)) ++ le8 (Z_to_bv 64 (rm 1)) ++ le8 (Z_to_bv 64 (ro 1)) ++ le8 (Z_to_bv 64 (rl 2)) ++ le8 (Z_to_bv 64 (rm 2)) ++ le8 (Z_to_bv 64 (ro 2))); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 d); CB 96 (le8 (Z_to_bv 64 (rl 4)) ++ le8 (Z_to_bv 64 (rm 4)) ++ le8 (Z_to_bv 64 (ro 4)) ++ le8 (Z_to_bv 64 (rl 5)) ++ le8 (Z_to_bv 64 (rm 5)) ++ le8 (Z_to_bv 64 (ro 5)) ++ le8 (Z_to_bv 64 (rl 6)) ++ le8 (Z_to_bv 64 (rm 6)) ++ le8 (Z_to_bv 64 (ro 6)) ++ le8 (Z_to_bv 64 (rl 7)) ++ le8 (Z_to_bv 64 (rm 7)) ++ le8 (Z_to_bv 64 (ro 7)))] ++ post).
Proof.
  intros m A pre post rl rm ro a b d -> -> -> H. pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 [_ W2]].
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact W1|]. apply cells_wf_app. split; [|exact W2]. cbn [cells_wf cell_wf]. rewrite ?length_app, ?length_le8. repeat split.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. unfold sql_ring_bytes. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.
Lemma sql_ring_shut_3 : forall (m : amem) A pre post rl rm ro,
  rw_cells bsegs m A (pre ++ [CB 72 (le8 (Z_to_bv 64 (rl 0)) ++ le8 (Z_to_bv 64 (rm 0)) ++ le8 (Z_to_bv 64 (ro 0)) ++ le8 (Z_to_bv 64 (rl 1)) ++ le8 (Z_to_bv 64 (rm 1)) ++ le8 (Z_to_bv 64 (ro 1)) ++ le8 (Z_to_bv 64 (rl 2)) ++ le8 (Z_to_bv 64 (rm 2)) ++ le8 (Z_to_bv 64 (ro 2))); C8 (Z_to_bv 64 (rl 3)); C8 (Z_to_bv 64 (rm 3)); C8 (Z_to_bv 64 (ro 3)); CB 96 (le8 (Z_to_bv 64 (rl 4)) ++ le8 (Z_to_bv 64 (rm 4)) ++ le8 (Z_to_bv 64 (ro 4)) ++ le8 (Z_to_bv 64 (rl 5)) ++ le8 (Z_to_bv 64 (rm 5)) ++ le8 (Z_to_bv 64 (ro 5)) ++ le8 (Z_to_bv 64 (rl 6)) ++ le8 (Z_to_bv 64 (rm 6)) ++ le8 (Z_to_bv 64 (ro 6)) ++ le8 (Z_to_bv 64 (rl 7)) ++ le8 (Z_to_bv 64 (rm 7)) ++ le8 (Z_to_bv 64 (ro 7)))] ++ post) -> rw_cells bsegs m A (pre ++ CB 192 (sql_ring_bytes rl rm ro) :: post).
Proof.
  intros m A pre post rl rm ro H. pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 W2]. apply cells_wf_app in W2. destruct W2 as [_ W2].
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact W1|]. split; [|exact W2]. cbn [cell_wf]. unfold sql_ring_bytes. rewrite !length_app, !length_le8. reflexivity.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. unfold sql_ring_bytes. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.
Lemma sql_ring_close_3 : forall (m : amem) A pre post rl rm ro a b d,
  rw_cells bsegs m A (pre ++ [CB 72 (le8 (Z_to_bv 64 (rl 0)) ++ le8 (Z_to_bv 64 (rm 0)) ++ le8 (Z_to_bv 64 (ro 0)) ++ le8 (Z_to_bv 64 (rl 1)) ++ le8 (Z_to_bv 64 (rm 1)) ++ le8 (Z_to_bv 64 (ro 1)) ++ le8 (Z_to_bv 64 (rl 2)) ++ le8 (Z_to_bv 64 (rm 2)) ++ le8 (Z_to_bv 64 (ro 2))); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 d); CB 96 (le8 (Z_to_bv 64 (rl 4)) ++ le8 (Z_to_bv 64 (rm 4)) ++ le8 (Z_to_bv 64 (ro 4)) ++ le8 (Z_to_bv 64 (rl 5)) ++ le8 (Z_to_bv 64 (rm 5)) ++ le8 (Z_to_bv 64 (ro 5)) ++ le8 (Z_to_bv 64 (rl 6)) ++ le8 (Z_to_bv 64 (rm 6)) ++ le8 (Z_to_bv 64 (ro 6)) ++ le8 (Z_to_bv 64 (rl 7)) ++ le8 (Z_to_bv 64 (rm 7)) ++ le8 (Z_to_bv 64 (ro 7)))] ++ post) -> rw_cells bsegs m A (pre ++ CB 192 (sql_ring_bytes (ring_upd rl 3 a) (ring_upd rm 3 b) (ring_upd ro 3 d)) :: post).
Proof.
  intros m A pre post rl rm ro a b d H. pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 W2]. apply cells_wf_app in W2. destruct W2 as [_ W2].
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact W1|]. split; [|exact W2]. cbn [cell_wf]. unfold sql_ring_bytes. rewrite !length_app, !length_le8. reflexivity.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. unfold sql_ring_bytes, ring_upd. cbn [Z.eqb Pos.eqb]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Lemma sql_ring_open_4 : forall (m : amem) A pre post rl rm ro a b d, a = rl 4 -> b = rm 4 -> d = ro 4 ->
  rw_cells bsegs m A (pre ++ CB 192 (sql_ring_bytes rl rm ro) :: post) -> rw_cells bsegs m A (pre ++ [CB 96 (le8 (Z_to_bv 64 (rl 0)) ++ le8 (Z_to_bv 64 (rm 0)) ++ le8 (Z_to_bv 64 (ro 0)) ++ le8 (Z_to_bv 64 (rl 1)) ++ le8 (Z_to_bv 64 (rm 1)) ++ le8 (Z_to_bv 64 (ro 1)) ++ le8 (Z_to_bv 64 (rl 2)) ++ le8 (Z_to_bv 64 (rm 2)) ++ le8 (Z_to_bv 64 (ro 2)) ++ le8 (Z_to_bv 64 (rl 3)) ++ le8 (Z_to_bv 64 (rm 3)) ++ le8 (Z_to_bv 64 (ro 3))); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 d); CB 72 (le8 (Z_to_bv 64 (rl 5)) ++ le8 (Z_to_bv 64 (rm 5)) ++ le8 (Z_to_bv 64 (ro 5)) ++ le8 (Z_to_bv 64 (rl 6)) ++ le8 (Z_to_bv 64 (rm 6)) ++ le8 (Z_to_bv 64 (ro 6)) ++ le8 (Z_to_bv 64 (rl 7)) ++ le8 (Z_to_bv 64 (rm 7)) ++ le8 (Z_to_bv 64 (ro 7)))] ++ post).
Proof.
  intros m A pre post rl rm ro a b d -> -> -> H. pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 [_ W2]].
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact W1|]. apply cells_wf_app. split; [|exact W2]. cbn [cells_wf cell_wf]. rewrite ?length_app, ?length_le8. repeat split.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. unfold sql_ring_bytes. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.
Lemma sql_ring_shut_4 : forall (m : amem) A pre post rl rm ro,
  rw_cells bsegs m A (pre ++ [CB 96 (le8 (Z_to_bv 64 (rl 0)) ++ le8 (Z_to_bv 64 (rm 0)) ++ le8 (Z_to_bv 64 (ro 0)) ++ le8 (Z_to_bv 64 (rl 1)) ++ le8 (Z_to_bv 64 (rm 1)) ++ le8 (Z_to_bv 64 (ro 1)) ++ le8 (Z_to_bv 64 (rl 2)) ++ le8 (Z_to_bv 64 (rm 2)) ++ le8 (Z_to_bv 64 (ro 2)) ++ le8 (Z_to_bv 64 (rl 3)) ++ le8 (Z_to_bv 64 (rm 3)) ++ le8 (Z_to_bv 64 (ro 3))); C8 (Z_to_bv 64 (rl 4)); C8 (Z_to_bv 64 (rm 4)); C8 (Z_to_bv 64 (ro 4)); CB 72 (le8 (Z_to_bv 64 (rl 5)) ++ le8 (Z_to_bv 64 (rm 5)) ++ le8 (Z_to_bv 64 (ro 5)) ++ le8 (Z_to_bv 64 (rl 6)) ++ le8 (Z_to_bv 64 (rm 6)) ++ le8 (Z_to_bv 64 (ro 6)) ++ le8 (Z_to_bv 64 (rl 7)) ++ le8 (Z_to_bv 64 (rm 7)) ++ le8 (Z_to_bv 64 (ro 7)))] ++ post) -> rw_cells bsegs m A (pre ++ CB 192 (sql_ring_bytes rl rm ro) :: post).
Proof.
  intros m A pre post rl rm ro H. pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 W2]. apply cells_wf_app in W2. destruct W2 as [_ W2].
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact W1|]. split; [|exact W2]. cbn [cell_wf]. unfold sql_ring_bytes. rewrite !length_app, !length_le8. reflexivity.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. unfold sql_ring_bytes. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.
Lemma sql_ring_close_4 : forall (m : amem) A pre post rl rm ro a b d,
  rw_cells bsegs m A (pre ++ [CB 96 (le8 (Z_to_bv 64 (rl 0)) ++ le8 (Z_to_bv 64 (rm 0)) ++ le8 (Z_to_bv 64 (ro 0)) ++ le8 (Z_to_bv 64 (rl 1)) ++ le8 (Z_to_bv 64 (rm 1)) ++ le8 (Z_to_bv 64 (ro 1)) ++ le8 (Z_to_bv 64 (rl 2)) ++ le8 (Z_to_bv 64 (rm 2)) ++ le8 (Z_to_bv 64 (ro 2)) ++ le8 (Z_to_bv 64 (rl 3)) ++ le8 (Z_to_bv 64 (rm 3)) ++ le8 (Z_to_bv 64 (ro 3))); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 d); CB 72 (le8 (Z_to_bv 64 (rl 5)) ++ le8 (Z_to_bv 64 (rm 5)) ++ le8 (Z_to_bv 64 (ro 5)) ++ le8 (Z_to_bv 64 (rl 6)) ++ le8 (Z_to_bv 64 (rm 6)) ++ le8 (Z_to_bv 64 (ro 6)) ++ le8 (Z_to_bv 64 (rl 7)) ++ le8 (Z_to_bv 64 (rm 7)) ++ le8 (Z_to_bv 64 (ro 7)))] ++ post) -> rw_cells bsegs m A (pre ++ CB 192 (sql_ring_bytes (ring_upd rl 4 a) (ring_upd rm 4 b) (ring_upd ro 4 d)) :: post).
Proof.
  intros m A pre post rl rm ro a b d H. pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 W2]. apply cells_wf_app in W2. destruct W2 as [_ W2].
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact W1|]. split; [|exact W2]. cbn [cell_wf]. unfold sql_ring_bytes. rewrite !length_app, !length_le8. reflexivity.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. unfold sql_ring_bytes, ring_upd. cbn [Z.eqb Pos.eqb]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Lemma sql_ring_open_5 : forall (m : amem) A pre post rl rm ro a b d, a = rl 5 -> b = rm 5 -> d = ro 5 ->
  rw_cells bsegs m A (pre ++ CB 192 (sql_ring_bytes rl rm ro) :: post) -> rw_cells bsegs m A (pre ++ [CB 120 (le8 (Z_to_bv 64 (rl 0)) ++ le8 (Z_to_bv 64 (rm 0)) ++ le8 (Z_to_bv 64 (ro 0)) ++ le8 (Z_to_bv 64 (rl 1)) ++ le8 (Z_to_bv 64 (rm 1)) ++ le8 (Z_to_bv 64 (ro 1)) ++ le8 (Z_to_bv 64 (rl 2)) ++ le8 (Z_to_bv 64 (rm 2)) ++ le8 (Z_to_bv 64 (ro 2)) ++ le8 (Z_to_bv 64 (rl 3)) ++ le8 (Z_to_bv 64 (rm 3)) ++ le8 (Z_to_bv 64 (ro 3)) ++ le8 (Z_to_bv 64 (rl 4)) ++ le8 (Z_to_bv 64 (rm 4)) ++ le8 (Z_to_bv 64 (ro 4))); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 d); CB 48 (le8 (Z_to_bv 64 (rl 6)) ++ le8 (Z_to_bv 64 (rm 6)) ++ le8 (Z_to_bv 64 (ro 6)) ++ le8 (Z_to_bv 64 (rl 7)) ++ le8 (Z_to_bv 64 (rm 7)) ++ le8 (Z_to_bv 64 (ro 7)))] ++ post).
Proof.
  intros m A pre post rl rm ro a b d -> -> -> H. pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 [_ W2]].
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact W1|]. apply cells_wf_app. split; [|exact W2]. cbn [cells_wf cell_wf]. rewrite ?length_app, ?length_le8. repeat split.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. unfold sql_ring_bytes. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.
Lemma sql_ring_shut_5 : forall (m : amem) A pre post rl rm ro,
  rw_cells bsegs m A (pre ++ [CB 120 (le8 (Z_to_bv 64 (rl 0)) ++ le8 (Z_to_bv 64 (rm 0)) ++ le8 (Z_to_bv 64 (ro 0)) ++ le8 (Z_to_bv 64 (rl 1)) ++ le8 (Z_to_bv 64 (rm 1)) ++ le8 (Z_to_bv 64 (ro 1)) ++ le8 (Z_to_bv 64 (rl 2)) ++ le8 (Z_to_bv 64 (rm 2)) ++ le8 (Z_to_bv 64 (ro 2)) ++ le8 (Z_to_bv 64 (rl 3)) ++ le8 (Z_to_bv 64 (rm 3)) ++ le8 (Z_to_bv 64 (ro 3)) ++ le8 (Z_to_bv 64 (rl 4)) ++ le8 (Z_to_bv 64 (rm 4)) ++ le8 (Z_to_bv 64 (ro 4))); C8 (Z_to_bv 64 (rl 5)); C8 (Z_to_bv 64 (rm 5)); C8 (Z_to_bv 64 (ro 5)); CB 48 (le8 (Z_to_bv 64 (rl 6)) ++ le8 (Z_to_bv 64 (rm 6)) ++ le8 (Z_to_bv 64 (ro 6)) ++ le8 (Z_to_bv 64 (rl 7)) ++ le8 (Z_to_bv 64 (rm 7)) ++ le8 (Z_to_bv 64 (ro 7)))] ++ post) -> rw_cells bsegs m A (pre ++ CB 192 (sql_ring_bytes rl rm ro) :: post).
Proof.
  intros m A pre post rl rm ro H. pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 W2]. apply cells_wf_app in W2. destruct W2 as [_ W2].
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact W1|]. split; [|exact W2]. cbn [cell_wf]. unfold sql_ring_bytes. rewrite !length_app, !length_le8. reflexivity.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. unfold sql_ring_bytes. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.
Lemma sql_ring_close_5 : forall (m : amem) A pre post rl rm ro a b d,
  rw_cells bsegs m A (pre ++ [CB 120 (le8 (Z_to_bv 64 (rl 0)) ++ le8 (Z_to_bv 64 (rm 0)) ++ le8 (Z_to_bv 64 (ro 0)) ++ le8 (Z_to_bv 64 (rl 1)) ++ le8 (Z_to_bv 64 (rm 1)) ++ le8 (Z_to_bv 64 (ro 1)) ++ le8 (Z_to_bv 64 (rl 2)) ++ le8 (Z_to_bv 64 (rm 2)) ++ le8 (Z_to_bv 64 (ro 2)) ++ le8 (Z_to_bv 64 (rl 3)) ++ le8 (Z_to_bv 64 (rm 3)) ++ le8 (Z_to_bv 64 (ro 3)) ++ le8 (Z_to_bv 64 (rl 4)) ++ le8 (Z_to_bv 64 (rm 4)) ++ le8 (Z_to_bv 64 (ro 4))); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 d); CB 48 (le8 (Z_to_bv 64 (rl 6)) ++ le8 (Z_to_bv 64 (rm 6)) ++ le8 (Z_to_bv 64 (ro 6)) ++ le8 (Z_to_bv 64 (rl 7)) ++ le8 (Z_to_bv 64 (rm 7)) ++ le8 (Z_to_bv 64 (ro 7)))] ++ post) -> rw_cells bsegs m A (pre ++ CB 192 (sql_ring_bytes (ring_upd rl 5 a) (ring_upd rm 5 b) (ring_upd ro 5 d)) :: post).
Proof.
  intros m A pre post rl rm ro a b d H. pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 W2]. apply cells_wf_app in W2. destruct W2 as [_ W2].
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact W1|]. split; [|exact W2]. cbn [cell_wf]. unfold sql_ring_bytes. rewrite !length_app, !length_le8. reflexivity.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. unfold sql_ring_bytes, ring_upd. cbn [Z.eqb Pos.eqb]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Lemma sql_ring_open_6 : forall (m : amem) A pre post rl rm ro a b d, a = rl 6 -> b = rm 6 -> d = ro 6 ->
  rw_cells bsegs m A (pre ++ CB 192 (sql_ring_bytes rl rm ro) :: post) -> rw_cells bsegs m A (pre ++ [CB 144 (le8 (Z_to_bv 64 (rl 0)) ++ le8 (Z_to_bv 64 (rm 0)) ++ le8 (Z_to_bv 64 (ro 0)) ++ le8 (Z_to_bv 64 (rl 1)) ++ le8 (Z_to_bv 64 (rm 1)) ++ le8 (Z_to_bv 64 (ro 1)) ++ le8 (Z_to_bv 64 (rl 2)) ++ le8 (Z_to_bv 64 (rm 2)) ++ le8 (Z_to_bv 64 (ro 2)) ++ le8 (Z_to_bv 64 (rl 3)) ++ le8 (Z_to_bv 64 (rm 3)) ++ le8 (Z_to_bv 64 (ro 3)) ++ le8 (Z_to_bv 64 (rl 4)) ++ le8 (Z_to_bv 64 (rm 4)) ++ le8 (Z_to_bv 64 (ro 4)) ++ le8 (Z_to_bv 64 (rl 5)) ++ le8 (Z_to_bv 64 (rm 5)) ++ le8 (Z_to_bv 64 (ro 5))); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 d); CB 24 (le8 (Z_to_bv 64 (rl 7)) ++ le8 (Z_to_bv 64 (rm 7)) ++ le8 (Z_to_bv 64 (ro 7)))] ++ post).
Proof.
  intros m A pre post rl rm ro a b d -> -> -> H. pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 [_ W2]].
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact W1|]. apply cells_wf_app. split; [|exact W2]. cbn [cells_wf cell_wf]. rewrite ?length_app, ?length_le8. repeat split.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. unfold sql_ring_bytes. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.
Lemma sql_ring_shut_6 : forall (m : amem) A pre post rl rm ro,
  rw_cells bsegs m A (pre ++ [CB 144 (le8 (Z_to_bv 64 (rl 0)) ++ le8 (Z_to_bv 64 (rm 0)) ++ le8 (Z_to_bv 64 (ro 0)) ++ le8 (Z_to_bv 64 (rl 1)) ++ le8 (Z_to_bv 64 (rm 1)) ++ le8 (Z_to_bv 64 (ro 1)) ++ le8 (Z_to_bv 64 (rl 2)) ++ le8 (Z_to_bv 64 (rm 2)) ++ le8 (Z_to_bv 64 (ro 2)) ++ le8 (Z_to_bv 64 (rl 3)) ++ le8 (Z_to_bv 64 (rm 3)) ++ le8 (Z_to_bv 64 (ro 3)) ++ le8 (Z_to_bv 64 (rl 4)) ++ le8 (Z_to_bv 64 (rm 4)) ++ le8 (Z_to_bv 64 (ro 4)) ++ le8 (Z_to_bv 64 (rl 5)) ++ le8 (Z_to_bv 64 (rm 5)) ++ le8 (Z_to_bv 64 (ro 5))); C8 (Z_to_bv 64 (rl 6)); C8 (Z_to_bv 64 (rm 6)); C8 (Z_to_bv 64 (ro 6)); CB 24 (le8 (Z_to_bv 64 (rl 7)) ++ le8 (Z_to_bv 64 (rm 7)) ++ le8 (Z_to_bv 64 (ro 7)))] ++ post) -> rw_cells bsegs m A (pre ++ CB 192 (sql_ring_bytes rl rm ro) :: post).
Proof.
  intros m A pre post rl rm ro H. pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 W2]. apply cells_wf_app in W2. destruct W2 as [_ W2].
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact W1|]. split; [|exact W2]. cbn [cell_wf]. unfold sql_ring_bytes. rewrite !length_app, !length_le8. reflexivity.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. unfold sql_ring_bytes. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.
Lemma sql_ring_close_6 : forall (m : amem) A pre post rl rm ro a b d,
  rw_cells bsegs m A (pre ++ [CB 144 (le8 (Z_to_bv 64 (rl 0)) ++ le8 (Z_to_bv 64 (rm 0)) ++ le8 (Z_to_bv 64 (ro 0)) ++ le8 (Z_to_bv 64 (rl 1)) ++ le8 (Z_to_bv 64 (rm 1)) ++ le8 (Z_to_bv 64 (ro 1)) ++ le8 (Z_to_bv 64 (rl 2)) ++ le8 (Z_to_bv 64 (rm 2)) ++ le8 (Z_to_bv 64 (ro 2)) ++ le8 (Z_to_bv 64 (rl 3)) ++ le8 (Z_to_bv 64 (rm 3)) ++ le8 (Z_to_bv 64 (ro 3)) ++ le8 (Z_to_bv 64 (rl 4)) ++ le8 (Z_to_bv 64 (rm 4)) ++ le8 (Z_to_bv 64 (ro 4)) ++ le8 (Z_to_bv 64 (rl 5)) ++ le8 (Z_to_bv 64 (rm 5)) ++ le8 (Z_to_bv 64 (ro 5))); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 d); CB 24 (le8 (Z_to_bv 64 (rl 7)) ++ le8 (Z_to_bv 64 (rm 7)) ++ le8 (Z_to_bv 64 (ro 7)))] ++ post) -> rw_cells bsegs m A (pre ++ CB 192 (sql_ring_bytes (ring_upd rl 6 a) (ring_upd rm 6 b) (ring_upd ro 6 d)) :: post).
Proof.
  intros m A pre post rl rm ro a b d H. pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 W2]. apply cells_wf_app in W2. destruct W2 as [_ W2].
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact W1|]. split; [|exact W2]. cbn [cell_wf]. unfold sql_ring_bytes. rewrite !length_app, !length_le8. reflexivity.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. unfold sql_ring_bytes, ring_upd. cbn [Z.eqb Pos.eqb]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Lemma sql_ring_open_7 : forall (m : amem) A pre post rl rm ro a b d, a = rl 7 -> b = rm 7 -> d = ro 7 ->
  rw_cells bsegs m A (pre ++ CB 192 (sql_ring_bytes rl rm ro) :: post) -> rw_cells bsegs m A (pre ++ [CB 168 (le8 (Z_to_bv 64 (rl 0)) ++ le8 (Z_to_bv 64 (rm 0)) ++ le8 (Z_to_bv 64 (ro 0)) ++ le8 (Z_to_bv 64 (rl 1)) ++ le8 (Z_to_bv 64 (rm 1)) ++ le8 (Z_to_bv 64 (ro 1)) ++ le8 (Z_to_bv 64 (rl 2)) ++ le8 (Z_to_bv 64 (rm 2)) ++ le8 (Z_to_bv 64 (ro 2)) ++ le8 (Z_to_bv 64 (rl 3)) ++ le8 (Z_to_bv 64 (rm 3)) ++ le8 (Z_to_bv 64 (ro 3)) ++ le8 (Z_to_bv 64 (rl 4)) ++ le8 (Z_to_bv 64 (rm 4)) ++ le8 (Z_to_bv 64 (ro 4)) ++ le8 (Z_to_bv 64 (rl 5)) ++ le8 (Z_to_bv 64 (rm 5)) ++ le8 (Z_to_bv 64 (ro 5)) ++ le8 (Z_to_bv 64 (rl 6)) ++ le8 (Z_to_bv 64 (rm 6)) ++ le8 (Z_to_bv 64 (ro 6))); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 d)] ++ post).
Proof.
  intros m A pre post rl rm ro a b d -> -> -> H. pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 [_ W2]].
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact W1|]. apply cells_wf_app. split; [|exact W2]. cbn [cells_wf cell_wf]. rewrite ?length_app, ?length_le8. repeat split.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. unfold sql_ring_bytes. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.
Lemma sql_ring_shut_7 : forall (m : amem) A pre post rl rm ro,
  rw_cells bsegs m A (pre ++ [CB 168 (le8 (Z_to_bv 64 (rl 0)) ++ le8 (Z_to_bv 64 (rm 0)) ++ le8 (Z_to_bv 64 (ro 0)) ++ le8 (Z_to_bv 64 (rl 1)) ++ le8 (Z_to_bv 64 (rm 1)) ++ le8 (Z_to_bv 64 (ro 1)) ++ le8 (Z_to_bv 64 (rl 2)) ++ le8 (Z_to_bv 64 (rm 2)) ++ le8 (Z_to_bv 64 (ro 2)) ++ le8 (Z_to_bv 64 (rl 3)) ++ le8 (Z_to_bv 64 (rm 3)) ++ le8 (Z_to_bv 64 (ro 3)) ++ le8 (Z_to_bv 64 (rl 4)) ++ le8 (Z_to_bv 64 (rm 4)) ++ le8 (Z_to_bv 64 (ro 4)) ++ le8 (Z_to_bv 64 (rl 5)) ++ le8 (Z_to_bv 64 (rm 5)) ++ le8 (Z_to_bv 64 (ro 5)) ++ le8 (Z_to_bv 64 (rl 6)) ++ le8 (Z_to_bv 64 (rm 6)) ++ le8 (Z_to_bv 64 (ro 6))); C8 (Z_to_bv 64 (rl 7)); C8 (Z_to_bv 64 (rm 7)); C8 (Z_to_bv 64 (ro 7))] ++ post) -> rw_cells bsegs m A (pre ++ CB 192 (sql_ring_bytes rl rm ro) :: post).
Proof.
  intros m A pre post rl rm ro H. pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 W2]. apply cells_wf_app in W2. destruct W2 as [_ W2].
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact W1|]. split; [|exact W2]. cbn [cell_wf]. unfold sql_ring_bytes. rewrite !length_app, !length_le8. reflexivity.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. unfold sql_ring_bytes. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.
Lemma sql_ring_close_7 : forall (m : amem) A pre post rl rm ro a b d,
  rw_cells bsegs m A (pre ++ [CB 168 (le8 (Z_to_bv 64 (rl 0)) ++ le8 (Z_to_bv 64 (rm 0)) ++ le8 (Z_to_bv 64 (ro 0)) ++ le8 (Z_to_bv 64 (rl 1)) ++ le8 (Z_to_bv 64 (rm 1)) ++ le8 (Z_to_bv 64 (ro 1)) ++ le8 (Z_to_bv 64 (rl 2)) ++ le8 (Z_to_bv 64 (rm 2)) ++ le8 (Z_to_bv 64 (ro 2)) ++ le8 (Z_to_bv 64 (rl 3)) ++ le8 (Z_to_bv 64 (rm 3)) ++ le8 (Z_to_bv 64 (ro 3)) ++ le8 (Z_to_bv 64 (rl 4)) ++ le8 (Z_to_bv 64 (rm 4)) ++ le8 (Z_to_bv 64 (ro 4)) ++ le8 (Z_to_bv 64 (rl 5)) ++ le8 (Z_to_bv 64 (rm 5)) ++ le8 (Z_to_bv 64 (ro 5)) ++ le8 (Z_to_bv 64 (rl 6)) ++ le8 (Z_to_bv 64 (rm 6)) ++ le8 (Z_to_bv 64 (ro 6))); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 d)] ++ post) -> rw_cells bsegs m A (pre ++ CB 192 (sql_ring_bytes (ring_upd rl 7 a) (ring_upd rm 7 b) (ring_upd ro 7 d)) :: post).
Proof.
  intros m A pre post rl rm ro a b d H. pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [W1 W2]. apply cells_wf_app in W2. destruct W2 as [_ W2].
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact W1|]. split; [|exact W2]. cbn [cell_wf]. unfold sql_ring_bytes. rewrite !length_app, !length_le8. reflexivity.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. unfold sql_ring_bytes, ring_upd. cbn [Z.eqb Pos.eqb]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

End CANSEC1.
