(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small I_qck.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma asegs_w_r : forallb (fun seg => negb (seg_writable seg) || seg_readable seg) ctasegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma find_segment_in : forall segs a n seg, find_segment segs a n = Some seg -> In seg segs.
Proof.
  induction segs as [|s segs IH]; intros a n seg H; cbn in H; [discriminate|].
  destruct (_ && _); [injection H as <-; left; reflexivity| right; eapply IH; eassumption].
Qed.

Lemma wview_mrd_A : forall (m : mem) a, wview ctasegs m a <> None -> exists b, mrd ctasegs m a = Some b.
Proof.
  intros m a H. unfold wview, mrd in *. destruct (m a) as [b|]; [exists b; reflexivity|].
  unfold seg_rom, memory_read.
  destruct (find_segment ctasegs (bv_unsigned a) 1) as [seg|] eqn:FS; [| contradiction].
  change (Z.of_N 1) with 1. rewrite FS.
  pose proof (find_segment_in _ _ _ _ FS) as IN.
  pose proof asegs_w_r as W. rewrite forallb_forall in W. specialize (W seg IN).
  destruct (seg_writable seg) eqn:SW; [| contradiction]. cbn in W. rewrite W.
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  destruct (segment_byte_at _ _) as [b|]; [| contradiction]. exists b. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma wr_at_stk : forall (m : mem) d n, wr_at ctasegs m d n -> stk ctasegs m d (d + n).
Proof.
  intros m d n (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  assert (W : wview ctasegs m (wa a) <> None) by (replace a with (d + (a - d)) by lia; apply H; lia).
  split; [exact W| exact (wview_mrd_A m _ W)].
Qed.

Lemma wr_at_rw_CB : forall (m : mem) d n, wr_at ctasegs m d n -> 0 <= n -> exists junk, rw_cells ctasegs m d [CB (Z.to_nat n) junk].
Proof.
  intros m d n W N0. pose proof (wr_at_stk m d n W) as S.
  destruct (stk_carve ctasegs m d (d + n) (Z.to_nat n) S ltac:(lia)) as [_ (junk & FR)].
  exists junk. replace (d + n - Z.of_nat (Z.to_nat n)) with d in FR by lia. exact FR.
Qed.
