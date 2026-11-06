(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs.
Import ListNotations.
Open Scope Z_scope.

Lemma rw_cells_rebytes : forall m A cs cs', rw_cells asegs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells asegs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] W E S. split; [split; [exact W| rewrite E; exact Hb]| rewrite S; exact Hw]. Qed.

Lemma Z_to_le_bytes_app : forall a b z, Z_to_le_bytes (a + b) z = Z_to_le_bytes a z ++ Z_to_le_bytes b (Z.shiftr z (8 * Z.of_nat a)).
Proof.
  induction a as [|a IH]; intros b z.
  - cbn [Nat.add app Z.of_nat Z.mul]. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [Nat.add Z_to_le_bytes app]. f_equal. rewrite IH. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

Lemma le8_small_split : forall v, 0 <= v < 2^32 -> le8 (wz v) = le4 (wz v) ++ le4 (wz 0).
Proof.
  intros v Hv. rewrite <- store_bytes_8. unfold le4. rewrite !unsigned_lit by lia.
  change (width_bytes 64) with (4 + 4)%nat. rewrite Z_to_le_bytes_app. f_equal.
  change (8 * Z.of_nat 4) with 32. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma rw_cells_C8_C4C4 : forall m A pre v post, 0 <= v < 2^32 ->
  rw_cells asegs m A (pre ++ C8 (wz v) :: post) -> rw_cells asegs m A (pre ++ C4 (wz v) :: C4 (wz 0) :: post).
Proof.
  intros m A pre v post Hv H. eapply rw_cells_rebytes; [exact H| | |].
  - destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [H1 [_ H3]]. apply cells_wf_app. split; [exact H1|]. cbn. tauto.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes app]. rewrite le8_small_split by lia. rewrite <- app_assoc. reflexivity.
  - rewrite !cells_size_app. reflexivity.
Qed.
Lemma rw_cells_C4C4_C8 : forall m A pre v post, 0 <= v < 2^32 ->
  rw_cells asegs m A (pre ++ C4 (wz v) :: C4 (wz 0) :: post) -> rw_cells asegs m A (pre ++ C8 (wz v) :: post).
Proof.
  intros m A pre v post Hv H. eapply rw_cells_rebytes; [exact H| | |].
  - destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [H1 [_ [_ H3]]]. apply cells_wf_app. split; [exact H1|]. cbn. tauto.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes app]. rewrite le8_small_split by lia. rewrite <- app_assoc. reflexivity.
  - rewrite !cells_size_app. reflexivity.
Qed.
