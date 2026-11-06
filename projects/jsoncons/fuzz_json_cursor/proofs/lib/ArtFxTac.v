(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- msteps _ (mkstr ?R ?P ?MM _ ?RS) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM; idtac "RESV" RS | |- ?G => idtac "GOAL" G end; fail "SHOWST".

Ltac zclosed V := lazymatch goal with
  | |- msteps _ (mkst (regupd _ _ ?x) _ _ _) _ => replace x with (Z_to_bv 64 V : word) by (apply bv_eq; vm_compute; reflexivity)
  | |- msteps _ (mkstr (regupd _ _ ?x) _ _ _ _) _ => replace x with (Z_to_bv 64 V : word) by (apply bv_eq; vm_compute; reflexivity) end.

Ltac zwok' := idtac; lazymatch goal with |- store_ok ?sg ?mm (Z_to_bv 64 ?aa) ?nn = true => change (wok sg mm aa nn); zwok | |- wok _ _ _ _ => zwok end.
Ltac wpc0 := lazymatch goal with |- msteps _ (mkstr _ ?p _ _ _) _ => wlit p | |- msteps _ (mkst _ ?p _ _) _ => wlit p end.

Ltac zcas6 Flr Dlr Fad Dad Fx1 Dx1 Fan Dan Fx2 Dx2 Fsc Dsc A OLD T1 T2 NEW CELL WOK :=
  chain_step; [reflexivity
    | eapply (art_step_lr_w _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 A) _ (Z_to_bv 64 OLD));
      [exact Flr | reflexivity | exact Dlr | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; reflexivity
      | exact CELL | apply art_bytes4; lia ]
    | ]; wpc0; rewrite art_v_lw_small by lia;
  chain_step; [reflexivity | eapply art_step_addi_r; [exact Fad | reflexivity | exact Dad | reflexivity] | ]; wpc0; gres; rwH; zclosed (NEW - OLD);
  chain_step; [reflexivity | eapply art_step_xor_r; [exact Fx1 | reflexivity | exact Dx1 | reflexivity] | ]; wpc0; gres; zclosed T1;
  chain_step; [reflexivity | eapply art_step_and_r; [exact Fan | reflexivity | exact Dan | reflexivity] | ]; wpc0; gres; rwH; zclosed T2;
  chain_step; [reflexivity | eapply art_step_xor_r; [exact Fx2 | reflexivity | exact Dx2 | reflexivity] | ]; wpc0; gres; zclosed NEW;
  chain_step; [reflexivity
    | eapply (art_step_sc_w_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 A));
      [exact Fsc | reflexivity | exact Dsc | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; reflexivity | gres; reflexivity
      | exact WOK ]
    | ]; wpc0;
  change (wbytes ?M0 (Z_to_bv 64 A) (word_to_le_bytes 4 (Z_to_bv 64 NEW))) with (Wn 4 M0 A NEW).
Ltac wpc := lazymatch goal with |- msteps _ (mkstr _ ?p _ _ _) _ => wlit p | |- msteps _ (mkst _ ?p _ _) _ => wlit p end.

