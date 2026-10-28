(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import RT_ibase Fz_W3_iface Fz_W3_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition pem_file_str : list byte := Eval vm_compute in (match image_bytes asegs LIT_FILE 20 with Some bs => bs | None => [] end).
Definition pem_func_str : list byte := Eval vm_compute in (match image_bytes asegs LIT_FUNC 15 with Some bs => bs | None => [] end).
Definition pem_getname_str : list byte := Eval vm_compute in (match image_bytes asegs LIT_GETNAME 8 with Some bs => bs | None => [] end).
Definition pem_gethd_str : list byte := Eval vm_compute in (match image_bytes asegs LIT_GETHD 19 with Some bs => bs | None => [] end).

Lemma pem_file_len : length pem_file_str = 20%nat. Proof. reflexivity. Qed.
Lemma pem_func_len : length pem_func_str = 15%nat. Proof. reflexivity. Qed.
Lemma pem_getname_len : length pem_getname_str = 8%nat. Proof. reflexivity. Qed.
Lemma pem_gethd_len : length pem_gethd_str = 19%nat. Proof. reflexivity. Qed.

Lemma pem_file_ro : ro_bytes asegs LIT_FILE (pem_file_str ++ [Z_to_bv 8 0]).
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma pem_func_ro : ro_bytes asegs LIT_FUNC (pem_func_str ++ [Z_to_bv 8 0]).
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma pem_getname_ro : ro_bytes asegs LIT_GETNAME (pem_getname_str ++ [Z_to_bv 8 0]).
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma pem_gethd_ro : ro_bytes asegs LIT_GETHD (pem_gethd_str ++ [Z_to_bv 8 0]).
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma pem_file_bytes : forall m : word -> option byte, mem_inv asegs m -> bytes_at asegs m LIT_FILE (pem_file_str ++ [Z_to_bv 8 0]).
Proof. intros m MI. apply ro_bytes_at; [exact MI| unfold LIT_FILE; lia| cbn; unfold LIT_FILE; lia| exact pem_file_ro]. Qed.
Lemma pem_func_bytes : forall m : word -> option byte, mem_inv asegs m -> bytes_at asegs m LIT_FUNC (pem_func_str ++ [Z_to_bv 8 0]).
Proof. intros m MI. apply ro_bytes_at; [exact MI| unfold LIT_FUNC; lia| cbn; unfold LIT_FUNC; lia| exact pem_func_ro]. Qed.
Lemma pem_getname_bytes : forall m : word -> option byte, mem_inv asegs m -> bytes_at asegs m LIT_GETNAME (pem_getname_str ++ [Z_to_bv 8 0]).
Proof. intros m MI. apply ro_bytes_at; [exact MI| unfold LIT_GETNAME; lia| cbn; unfold LIT_GETNAME; lia| exact pem_getname_ro]. Qed.
Lemma pem_gethd_bytes : forall m : word -> option byte, mem_inv asegs m -> bytes_at asegs m LIT_GETHD (pem_gethd_str ++ [Z_to_bv 8 0]).
Proof. intros m MI. apply ro_bytes_at; [exact MI| unfold LIT_GETHD; lia| cbn; unfold LIT_GETHD; lia| exact pem_gethd_ro]. Qed.

Local Ltac nonul D := unfold D; intros H; repeat (destruct H as [H|H]; [apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate|]); exact H.
Lemma pem_file_nonul : ~ In (Z_to_bv 8 0) pem_file_str. Proof. nonul pem_file_str. Qed.
Lemma pem_func_nonul : ~ In (Z_to_bv 8 0) pem_func_str. Proof. nonul pem_func_str. Qed.
Lemma pem_getname_nonul : ~ In (Z_to_bv 8 0) pem_getname_str. Proof. nonul pem_getname_str. Qed.
Lemma pem_gethd_nonul : ~ In (Z_to_bv 8 0) pem_gethd_str. Proof. nonul pem_gethd_str. Qed.

(* [comment removed for export] *)
Lemma rw_cells_CB0 : forall (m : word -> option byte) A, 0 <= A -> A <= 2 ^ 64 -> rw_cells asegs m A [CB 0%nat []].
Proof. intros m A H1 H2. split; [split; [cbn; tauto| split; [exact H1| split; [cbn; lia| intros i Hi; cbn in Hi; lia]]]| split; [exact H1| split; [cbn; lia| intros i Hi; cbn in Hi; lia]]]. Qed.
Lemma rw_cells_CB0_of : forall (m : word -> option byte) A n bs, rw_cells asegs m A [CB n bs] -> rw_cells asegs m A [CB 0%nat []].
Proof. intros m A n bs H. pose proof (rw_cells_bound asegs m A _ H) as [H1 H2]. apply rw_cells_CB0; [exact H1|]. cbn [cells_size csize Nat.add] in H2. lia. Qed.

(* [comment removed for export] *)
Definition pem_file_slack : list byte := Eval vm_compute in (match image_bytes asegs (LIT_FILE + 21) 3 with Some bs => bs | None => [] end).
Definition pem_getname_slack : list byte := Eval vm_compute in (match image_bytes asegs (LIT_GETNAME + 9) 7 with Some bs => bs | None => [] end).
Definition pem_gethd_slack : list byte := Eval vm_compute in (match image_bytes asegs (LIT_GETHD + 20) 4 with Some bs => bs | None => [] end).
Lemma pem_file_ro_sl : ro_bytes asegs LIT_FILE (pem_file_str ++ Z_to_bv 8 0 :: pem_file_slack).
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma pem_func_ro_sl : ro_bytes asegs LIT_FUNC (pem_func_str ++ Z_to_bv 8 0 :: []).
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma pem_getname_ro_sl : ro_bytes asegs LIT_GETNAME (pem_getname_str ++ Z_to_bv 8 0 :: pem_getname_slack).
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma pem_gethd_ro_sl : ro_bytes asegs LIT_GETHD (pem_gethd_str ++ Z_to_bv 8 0 :: pem_gethd_slack).
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.

Section Lits.
  Variable GOBJ : Z -> Z -> Prop.
  Hypothesis GO_file : GOBJ LIT_FILE LIT_FILE_SZ.
  Hypothesis GO_func : GOBJ LIT_FUNC LIT_FUNC_SZ.
  Hypothesis GO_getname : GOBJ LIT_GETNAME LIT_GETNAME_SZ.
  Hypothesis GO_gethd : GOBJ LIT_GETHD LIT_GETHD_SZ.

  Local Ltac lit_tac RO NN LEN GO :=
    do 3 eexists; split; [exact RO|]; split; [exact NN|]; split; [intros X; apply (f_equal (@length byte)) in X; rewrite LEN in X; discriminate X|];
    rewrite LEN; split; [reflexivity|]; split; [lia|]; split; [unfold LIT_FILE, LIT_FUNC, LIT_GETNAME, LIT_GETHD; vm_compute; discriminate|]; split; [exact GO|];
    unfold LIT_FILE, LIT_FILE_SZ, LIT_FUNC, LIT_FUNC_SZ, LIT_GETNAME, LIT_GETNAME_SZ, LIT_GETHD, LIT_GETHD_SZ, SEGTOP_A; cbn; lia.
  Lemma pem_file_lit : pem_lit_ok GOBJ LIT_FILE 21 pem_file_str.
  Proof. lit_tac pem_file_ro_sl pem_file_nonul pem_file_len GO_file. Qed.
  Lemma pem_func_lit : pem_lit_ok GOBJ LIT_FUNC 16 pem_func_str.
  Proof. lit_tac pem_func_ro_sl pem_func_nonul pem_func_len GO_func. Qed.
  Lemma pem_getname_lit : pem_lit_ok GOBJ LIT_GETNAME 9 pem_getname_str.
  Proof. lit_tac pem_getname_ro_sl pem_getname_nonul pem_getname_len GO_getname. Qed.
  Lemma pem_gethd_lit : pem_lit_ok GOBJ LIT_GETHD 20 pem_gethd_str.
  Proof. lit_tac pem_gethd_ro_sl pem_gethd_nonul pem_gethd_len GO_gethd. Qed.
End Lits.
