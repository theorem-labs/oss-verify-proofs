(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec SeqExec StoreOk SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1ExitKn S1Cells.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition kn_of_cells2 (cells : list (Z * nat * Z)) : list kentry :=
  map (fun c : Z * nat * Z => match c with (a, w, v) => KWord (SA (ELit 0) a) w (ELit v) end) cells.
Definition cells_wf (cells : list (Z * nat * Z)) : bool :=
  forallb (fun c : Z * nat * Z => match c with (a, w, v) =>
    (Nat.leb w 8 && (0 <=? a) && (a + Z.of_nat w <=? 2 ^ 64) && (a <? 2 ^ 64))%bool end) cells.

Definition kn_drv_cells : list kentry := Eval cbv in kn_of_cells2 drv_cells.
Lemma kn_drv_cells_eq : kn_drv_cells = kn_of_cells2 drv_cells. Proof. reflexivity. Qed.

Section K.
  Variable E : env.
  Variable M : word -> option byte.

  Lemma know_cells2 : forall cells, cells_wf cells = true ->
    Forall (fun c : Z * nat * Z => match c with (a, w, v) =>
      rdn RSEGS M (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 v)) end) cells ->
    know_ok RSEGS E M (kn_of_cells2 cells).
  Proof.
    induction cells as [|[[a w] v] rest IH]; intros Hwf Hc; [constructor|].
    cbn [cells_wf forallb] in Hwf. apply andb_prop in Hwf as [Hwf Hrest].
    apply andb_prop in Hwf as [Hwf H3]. apply andb_prop in Hwf as [Hwf H2]. apply andb_prop in Hwf as [H0 H1].
    apply Nat.leb_le in H0. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
    apply Forall_cons_iff in Hc as [Hc1 Hc2].
    constructor; [|apply IH; assumption].
    cbn [kentry_ok a_base a_off edenot]. split; [exact H0|].
    unfold flat, estart, adenot. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia.
    split; [lia|]. unfold v_addi. rewrite (u_small 0) by lia. rewrite Z.add_0_l. exact Hc1.
  Qed.

  Lemma know_drv_cells : drv_cells_ok M -> know_ok RSEGS E M kn_drv_cells.
  Proof. intros H. rewrite kn_drv_cells_eq. apply know_cells2; [vm_compute; reflexivity | exact H]. Qed.
End K.
