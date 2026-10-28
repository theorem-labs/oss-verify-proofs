(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Prelim Stdio.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout FX_Stdio_iface RT_iface D_iface D_defs D_kit D_libiface D_clx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition IO_FPA : list (Z * Z) := [(0x5e7168, 0x5e7250); (0x5e7348, 0x5e7430); (0xbfb550, 0xbfbda0)].
Definition OUT_repA (so : stdout_st) (m : mem) : Prop := stdout_file m so.
Definition ERR_repA (m : mem) : Prop := stderr_wfile0 m.

Lemma in_IO_FPA : forall lo hi x, In (lo, hi) IO_FPA -> lo <= x < hi -> in_ranges IO_FPA x.
Proof. intros lo hi x H1 H2. exists lo, hi. split; assumption. Qed.

Lemma OUT_locA : forall so, fp_local IO_FPA (OUT_repA so).
Proof.
  intros so m m' (flags & mode & tail & bb & FC & FL & BUF & BP & BL & INA) AG.
  exists flags, mode, tail, bb. split; [| split; [exact FL| split; [| split; [exact BP| split; [exact BL| exact INA]]]]].
  - apply (rw_cells_agree_nw bsegs m m' _ _ FC). intros a Ha. apply AG.
    apply (in_IO_FPA 0x5e7348 0x5e7430); [cbn; tauto|]. unfold file_cells in Ha. cbn [cells_size csize] in Ha. lia.
  - apply (rw_cells_agree_nw bsegs m m' _ _ BUF). intros a Ha. apply AG.
    apply (in_IO_FPA 0xbfb550 0xbfbda0); [cbn; tauto|]. cbn [cells_size csize] in Ha. lia.
Qed.

Lemma ERR_locA : fp_local IO_FPA ERR_repA.
Proof.
  intros m m' (flags & mode & e & wend & tail & FC & REST) AG.
  exists flags, mode, e, wend, tail. split; [| exact REST].
  apply (rw_cells_agree_nw bsegs m m' _ _ FC). intros a Ha. apply AG.
  apply (in_IO_FPA 0x5e7168 0x5e7250); [cbn; tauto|]. unfold file_cells in Ha. cbn [cells_size csize] in Ha. lia.
Qed.

Lemma IO_imgA : forall x, in_ranges IO_FPA x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Proof.
  intros x (lo & hi & Hin & Hx). cbn in Hin.
  split; [| split].
  - apply client_static_intro. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
  - unfold drv_cell, ERRNO_A, TP_A, SSP_GUARD, TR_INIT, g_read_stage. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
  - unfold LIB_FP. cbn. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; (repeat (split; [lia|])); try exact I.
Qed.

(* [comment removed for export] *)
Lemma stdout_file_agree : forall so m m',
  agree_on (fun x => (0x5e7348 <= x < 0x5e7430) \/ (0xbfb968 <= x < 0xbfbda0)) m m' -> wmono bsegs m m' ->
  OUT_repA so m -> OUT_repA so m'.
Proof.
  intros so m m' AG WM (flags & mode & tail & bb & FC & FL & BUF & BP & BL & INA).
  exists flags, mode, tail, bb. split; [| split; [exact FL| split; [| split; [exact BP| split; [exact BL| exact INA]]]]].
  - apply (rw_cells_agree bsegs m m' _ _ FC); [| exact WM]. intros a Ha. apply AG.
    left. unfold file_cells in Ha. cbn [cells_size csize] in Ha. lia.
  - apply (rw_cells_agree bsegs m m' _ _ BUF); [| exact WM]. intros a Ha. apply AG.
    right. cbn [cells_size csize] in Ha. lia.
Qed.

Lemma stderr_wfile0_agree : forall m m',
  agree_on (fun x => 0x5e7168 <= x < 0x5e7250) m m' -> wmono bsegs m m' -> ERR_repA m -> ERR_repA m'.
Proof.
  intros m m' AG WM (flags & mode & e & wend & tail & FC & REST).
  exists flags, mode, e, wend, tail. split; [| exact REST].
  apply (rw_cells_agree bsegs m m' _ _ FC); [| exact WM]. intros a Ha. apply AG.
  unfold file_cells in Ha. cbn [cells_size csize] in Ha. lia.
Qed.
