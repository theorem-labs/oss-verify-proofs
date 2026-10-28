(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import As_code_1f3d88_1f4290.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Theorem amain_ret_0 : forall regs mem rom,
  getr regs 10 = Z_to_bv 64 0 ->
  exists regs',
    msteps RSEGS (mkst regs (0x1eee98 : word) mem rom) (mkst regs' (0x1eef18 : word) mem rom)
    /\ getr regs' 8 = Z_to_bv 64 0
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ (forall r : reg, r <> 1 -> r <> 8 -> r <> 10 -> r <> 11 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom Ha0.
  destruct (c_lts (getr regs 21) (getr regs 0)) eqn:Hc.
  - (* [comment removed for export] *)
    eexists. split.
    + stepb_tk F_1f3f10 D_1f3f10 ltac:(exact Hc).
      stepn F_1f3f1c D_1f3f1c.
      stepn F_1f4068 D_1f4068.
      stepret F_1f406c D_1f406c (Z_to_bv 64 0x1eeea8) ltac:(reflexivity).
      stepn F_1f3f20 D_1f3f20.
      stepn F_1f3f24 D_1f3f24.
      stepb_tk F_1f3f28 D_1f3f28 ltac:(cond_compute).
      apply mst_refl.
    + repeat split; gres; try reflexivity.
      intros r H1 H8 H10 H11. rewrite !getr_other by assumption. reflexivity.
  - (* [comment removed for export] *)
    eexists. split.
    + stepb_ft F_1f3f10 D_1f3f10 ltac:(exact Hc).
      stepn F_1f3f14 D_1f3f14.
      stepn F_1f3f18 D_1f3f18.
      apply mst_refl.
    + repeat split; gres; try reflexivity; try (rewrite Ha0; reflexivity).
      intros r H1 H8 H10 H11. rewrite !getr_other by assumption. reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
