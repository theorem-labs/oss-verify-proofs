(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac Ref_code_2ab1c_2b108.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Theorem main_ret_0 : forall regs mem rom,
  getr regs 10 = Z_to_bv 64 0 ->
  exists regs',
    msteps RSEGS (mkst regs (0x2addc : word) mem rom) (mkst regs' (0x2ae5c : word) mem rom)
    /\ getr regs' 8 = Z_to_bv 64 0
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ (forall r : reg, r <> 1 -> r <> 8 -> r <> 10 -> r <> 11 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom Ha0.
  destruct (c_lts (getr regs 21) (getr regs 0)) eqn:Hc.
  - (* [comment removed for export] *)
    eexists. split.
    + stepb_tk F_2addc D_2addc ltac:(exact Hc).
      stepn F_2ade8 D_2ade8.
      stepn F_2af30 D_2af30.
      stepret F_2af34 D_2af34 (Z_to_bv 64 0x2adec) ltac:(reflexivity).
      stepn F_2adec D_2adec.
      stepn F_2adf0 D_2adf0.
      stepb_tk F_2adf4 D_2adf4 ltac:(cond_compute).
      apply mst_refl.
    + repeat split; gres; try reflexivity.
      intros r H1 H8 H10 H11. rewrite !getr_other by assumption. reflexivity.
  - (* [comment removed for export] *)
    eexists. split.
    + stepb_ft F_2addc D_2addc ltac:(exact Hc).
      stepn F_2ade0 D_2ade0.
      stepn F_2ade4 D_2ade4.
      apply mst_refl.
    + repeat split; gres; try reflexivity; try (rewrite Ha0; reflexivity).
      intros r H1 H8 H10 H11. rewrite !getr_other by assumption. reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
