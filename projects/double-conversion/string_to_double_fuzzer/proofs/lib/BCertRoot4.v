(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages BothPlanImages BothTableL AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs BothMainDefs BothMain StartupHSBoth MainHSBoth MainItabBoth ArgFragsBoth ArgFragsDirBoth BMain_dir_r01 BMain_dir_r2 BK0TailAll.
From Ltac2 Require Import Ltac2 Constr Std Control.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
Set Default Proof Mode "Classic".
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Definition C_dir_r01_h0 : class := root_class 4.
Definition s_dir_r01_h0 : shape := SAlt2 (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2; SPLit [10]] (SExit 2)) (SAlt2 (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 111; 117; 116; 32; 111; 102; 32; 109; 101; 109; 111; 114; 121; 10]] (SExit 2)) (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32]; SPBlob 2; SPLit [10]] (SExit 2))).
Lemma dir_r01_h0_ok : pay_check KCm BFUELm FUELm BITm TT_r5 (mcase_lo (HSA HS_main_both 0) e_r 4046) C_dir_r01_h0 (main_dir_r01) = COk s_dir_r01_h0.
Proof. ltac2:(cert_refl constr:(COk s_dir_r01_h0)). Qed.

Definition C_dir_r2_h0 : class := root_class 4.
Definition s_dir_r2_h0 : shape := SAlt2 (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2; SPLit [10]] (SExit 2)) (SAlt2 (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 111; 117; 116; 32; 111; 102; 32; 109; 101; 109; 111; 114; 121; 10]] (SExit 2)) (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32]; SPBlob 2; SPLit [10]] (SExit 2))).
Lemma dir_r2_h0_ok : pay_check KCm BFUELm FUELm BITm TT_r5 (mcase_hi (HSA HS_main_both 0) e_r 4046) C_dir_r2_h0 (main_dir_r2) = COk s_dir_r2_h0.
Proof. ltac2:(cert_refl constr:(COk s_dir_r2_h0)). Qed.
