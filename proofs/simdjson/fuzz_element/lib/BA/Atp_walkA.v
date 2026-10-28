(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout Shadow RT_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import IcptSpec D_defs Sj_acps Sj_hkit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Atp_elemA Atp_arrA Atp_objdA Atp_objcA Atp_objmA Atp_objA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition esc_okA (RT : rt_sig) : Prop :=
  forall (E : aenvA) (d : nat) PMc (Σ Σ1 : rts RT) (I : objI),
    aenvA_ok E -> atp_elem_cpsA RT E d -> fdfs_only PMc -> mat_stable PMc -> octx RT E d Σ Σ1 I ->
    esc_sso_stmt RT E d PMc Σ Σ1 I /\ esc_heap_stmt RT E d PMc Σ Σ1 I.

Section WalkA.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RC2 : rt_contracts2 RT.
  Hypothesis ESC : esc_okA RT.

  Theorem atp_levelA : forall E, aenvA_ok E -> forall d, atp_elem_cpsA RT E d.
  Proof using AF RC2 ESC.
    intros E OK d. induction d as [|d IH].
    - apply (atp_elemA RT AF (rc2_rt RT RC2) E OK 0%nat); intros d' Ed; discriminate Ed.
    - apply (atp_elemA RT AF (rc2_rt RT RC2) E OK (S d)); intros d' Ed; injection Ed as <-.
      + exact (atp_objA RT AF RC2 E OK d IH
                 (fun PMc Σ Σ1 I FDO MST CTX => proj1 (ESC E d PMc Σ Σ1 I OK IH FDO MST CTX))
                 (fun PMc Σ Σ1 I FDO MST CTX => proj2 (ESC E d PMc Σ Σ1 I OK IH FDO MST CTX))).
      + exact (atp_arrA RT AF (rc2_rt RT RC2) E OK d IH).
  Qed.

  Theorem atp_obj_levelA : forall E, aenvA_ok E -> forall d, atp_obj_cpsA RT E d.
  Proof using AF RC2 ESC.
    intros E OK d.
    exact (atp_objA RT AF RC2 E OK d (atp_levelA E OK d)
             (fun PMc Σ Σ1 I FDO MST CTX => proj1 (ESC E d PMc Σ Σ1 I OK (atp_levelA E OK d) FDO MST CTX))
             (fun PMc Σ Σ1 I FDO MST CTX => proj2 (ESC E d PMc Σ Σ1 I OK (atp_levelA E OK d) FDO MST CTX))).
  Qed.

  Theorem atp_arr_levelA : forall E, aenvA_ok E -> forall d, atp_arr_cpsA RT E d.
  Proof using AF RC2 ESC. intros E OK d. exact (atp_arrA RT AF (rc2_rt RT RC2) E OK d (atp_levelA E OK d)). Qed.

  Corollary atp_obj_topA : forall E, aenvA_ok E -> atp_obj_cpsA RT E (Nat.pred TAPE_MAX_DEPTH).
  Proof using AF RC2 ESC. intros E OK. exact (atp_obj_levelA E OK _). Qed.
  Corollary atp_arr_topA : forall E, aenvA_ok E -> atp_arr_cpsA RT E (Nat.pred TAPE_MAX_DEPTH).
  Proof using AF RC2 ESC. intros E OK. exact (atp_arr_levelA E OK _). Qed.
End WalkA.
