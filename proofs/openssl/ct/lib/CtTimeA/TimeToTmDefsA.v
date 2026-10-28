(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge Cells Mem. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim CtTime.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeP Require Import TimeToTmDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition A_JTAB_A : Z := 0x76b18.
Definition A_MINTAB_A : Z := 0x76b40.
Definition A_MAXTAB_A : Z := 0x76ba0.
Definition A_MDAYS_A : Z := 0x76c00.
Definition A_YDAYS_A : Z := 0x76ea0.
Definition T2T_HEAD_A : Z := 0x26eeb8.       (* [comment removed for export] *)
Definition T2T_LTAIL_A : Z := 0x26f26c.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition case_pcA (i : Z) : Z :=
  if i =? 0 then 0x26f00c else if i =? 1 then 0x26f098 else if i =? 2 then 0x26f024 else if i =? 3 then 0x26f034
  else if i =? 4 then 0x26f01c else if i =? 5 then 0x26f0b8 else 0x26f0c0.
Definition jtabA (i : Z) : Z := case_pcA i - A_JTAB_A.

(* [comment removed for export] *)
Definition t2t_lowA (j0 j192 j200 : list byte) (l tm f DA GS mon year : Z) (g : nat) (junk : list byte) : list cell :=
  [CB 8 j0; C8 (Z_to_bv 64 14); C8 (Z_to_bv 64 42949672); C8 (Z_to_bv 64 l); C8 (Z_to_bv 64 l);
   C8 (Z_to_bv 64 18446744071868851347); C8 (Z_to_bv 64 1717986919); C8 (Z_to_bv 64 1374389535); C8 (Z_to_bv 64 10737419);
   C8 (Z_to_bv 64 85899344); C8 (Z_to_bv 64 18446744072678759465); C8 (Z_to_bv 64 mon); C8 (Z_to_bv 64 MASK47);
   C8 (Z_to_bv 64 tm); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 year); C8 (Z_to_bv 64 (f + 32)); C8 (Z_to_bv 64 (l - 2)); C8 (Z_to_bv 64 (l - 1));
   C8 (Z_to_bv 64 (DA + 4)); C8 (Z_to_bv 64 12); C8 (Z_to_bv 64 GS); C8 (Z_to_bv 64 7);
   C8 (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (DA + 4))) 3 + SHB));
   CB 8 j192; CB 8 j200; C8 (Z_to_bv 64 f); CB g junk].

(* [comment removed for export] *)
Definition TM_CELLS_A (sec mi hr md mo yr wd yd : Z) : list cell :=
  [C4 (Z_to_bv 64 sec); C4 (Z_to_bv 64 mi); C4 (Z_to_bv 64 hr); C4 (Z_to_bv 64 md); C4 (Z_to_bv 64 mo); C4 (Z_to_bv 64 yr);
   C4 (Z_to_bv 64 wd); C4 (Z_to_bv 64 yd); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ro_C4_of_imageA : forall m A v, mem_inv ctasegs m -> ro_bytes_b ctasegs A (le4 (Z_to_bv 64 v)) = true -> 0 <= A -> A + 4 <= 2^64 ->
  ro_cells ctasegs m A [C4 (Z_to_bv 64 v)].
Proof.
  intros m A v MI RB A0 A4. split; [cbn; tauto|]. cbn [cells_bytes cbytes app]. rewrite app_nil_r.
  apply ro_bytes_at; [exact MI| lia| rewrite length_le4; lia|]. apply ro_bytes_b_sound. exact RB.
Qed.

Local Ltac tab_tac MI := apply ro_C4_of_imageA; [exact MI| vm_compute; reflexivity| unfold A_MINTAB_A, A_MAXTAB_A, A_JTAB_A, A_MDAYS_A, A_YDAYS_A; lia| unfold A_MINTAB_A, A_MAXTAB_A, A_JTAB_A, A_MDAYS_A, A_YDAYS_A; lia].

Lemma mintabA_cell : forall m i, mem_inv ctasegs m -> 0 <= i <= 6 -> ro_cells ctasegs m (A_MINTAB_A + 4 * i) [C4 (Z_to_bv 64 (mintab i))].
Proof.
  intros m i MI Hi. assert (H : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) by lia.
  destruct H as [->|[->|[->|[->|[->|[->| ->]]]]]]; tab_tac MI.
Qed.
Lemma maxtabA_cell : forall m i, mem_inv ctasegs m -> 0 <= i <= 6 -> ro_cells ctasegs m (A_MAXTAB_A + 4 * i) [C4 (Z_to_bv 64 (maxtab i))].
Proof.
  intros m i MI Hi. assert (H : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) by lia.
  destruct H as [->|[->|[->|[->|[->|[->| ->]]]]]]; tab_tac MI.
Qed.
Lemma jtabA_cell : forall m i, mem_inv ctasegs m -> 0 <= i <= 6 -> ro_cells ctasegs m (A_JTAB_A + 4 * i) [C4 (Z_to_bv 64 (jtabA i))].
Proof.
  intros m i MI Hi. assert (H : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) by lia.
  destruct H as [->|[->|[->|[->|[->|[->| ->]]]]]]; tab_tac MI.
Qed.
Lemma mdaysA_cell : forall m k, mem_inv ctasegs m -> 0 <= k <= 11 -> ro_cells ctasegs m (4 * k + A_MDAYS_A) [C4 (Z_to_bv 64 (mdaystab k))].
Proof.
  intros m k MI Hk. assert (H : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11) by lia.
  destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]; tab_tac MI.
Qed.
Lemma ydaysA_cell : forall m k, mem_inv ctasegs m -> 0 <= k <= 11 -> ro_cells ctasegs m (4 * k + A_YDAYS_A) [C4 (Z_to_bv 64 (ydaystab k))].
Proof.
  intros m k MI Hk. assert (H : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11) by lia.
  destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]; tab_tac MI.
Qed.
