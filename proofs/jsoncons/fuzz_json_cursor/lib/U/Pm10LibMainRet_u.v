(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10_code_39000_3a000_u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.

Theorem main_ret_0 : forall regs mem rom,
  getr regs 10 = Z_to_bv 64 0 ->
  exists regs',
    msteps RSEGS (mkst regs (0x393c0 : word) mem rom) (mkst regs' (0x39440 : word) mem rom)
    /\ getr regs' 8 = Z_to_bv 64 0
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ (forall r : reg, r <> 1 -> r <> 8 -> r <> 10 -> r <> 11 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom Ha0.
  destruct (c_lts (getr regs 21) (getr regs 0)) eqn:Hc.
  -
    eexists. split.
    + stepb_tk F_39088 D_39088 ltac:(exact Hc).
      stepn F_39094 D_39094.
      stepn F_391dc D_391dc.
      stepret F_391e0 D_391e0 (Z_to_bv 64 0x393d0) ltac:(reflexivity).
      stepn F_39098 D_39098.
      stepn F_3909c D_3909c.
      stepb_tk F_390a0 D_390a0 ltac:(cond_compute).
      apply mst_refl.
    + repeat split; gres; try reflexivity.
      intros r H1 H8 H10 H11. rewrite !getr_other by assumption. reflexivity.
  -
    eexists. split.
    + stepb_ft F_39088 D_39088 ltac:(exact Hc).
      stepn F_3908c D_3908c.
      stepn F_39090 D_39090.
      apply mst_refl.
    + repeat split; gres; try reflexivity; try (rewrite Ha0; reflexivity).
      intros r H1 H8 H10 H11. rewrite !getr_other by assumption. reflexivity.
Qed.
End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
