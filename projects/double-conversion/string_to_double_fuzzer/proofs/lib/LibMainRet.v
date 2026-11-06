(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac Ref_code_323a8_33000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

#[local] Abbreviation RSEGS := ImgP.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPW_1. Context {fx : PropExec.FPState}.


Theorem main_ret_0 : forall regs mem rom,
  getr regs 10 = Z_to_bv 64 0 ->
  exists regs',
    msteps RSEGS (mkst regs (0x326e8 : word) mem rom) (mkst regs' (0x32768 : word) mem rom)
    /\ getr regs' 8 = Z_to_bv 64 0
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ (forall r : reg, r <> 1 -> r <> 8 -> r <> 10 -> r <> 11 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom Ha0.
  destruct (c_lts (getr regs 21) (getr regs 0)) eqn:Hc.
  - (* [comment removed for export] *)
    eexists. split.
    + stepb_tk F_326e8 D_326e8 ltac:(exact Hc).
      stepn F_326f4 D_326f4.
      stepn F_3283c D_3283c.
      stepret F_32840 D_32840 (Z_to_bv 64 0x326f8) ltac:(reflexivity).
      stepn F_326f8 D_326f8.
      stepn F_326fc D_326fc.
      stepb_tk F_32700 D_32700 ltac:(cond_compute).
      apply mst_refl.
    + repeat split; gres; try reflexivity.
      intros r H1 H8 H10 H11. rewrite !getr_other by assumption. reflexivity.
  - (* [comment removed for export] *)
    eexists. split.
    + stepb_ft F_326e8 D_326e8 ltac:(exact Hc).
      stepn F_326ec D_326ec.
      stepn F_326f0 D_326f0.
      apply mst_refl.
    + repeat split; gres; try reflexivity; try (rewrite Ha0; reflexivity).
      intros r H1 H8 H10 H11. rewrite !getr_other by assumption. reflexivity.
Qed.
End FPW_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
