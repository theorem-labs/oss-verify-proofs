(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages BothPlanImages BothTableL AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs BothMainDefs BothMain StartupHSBoth MainHSBoth MainItabBoth ArgFragsBoth BMainErrPlans.
From Ltac2 Require Import Ltac2 Constr Std Control.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
Set Default Proof Mode "Classic".
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Section TTS.
Variable TT : nat -> option (acs * plan * shape).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition C_u1_67_73_h0 : class := (((((root_class 1 ++ [(QL0, 0 + 1, QMAX)]) ++ [(QL0, 63 + 1, QMAX)]) ++ [(QL0, 64 + 1, QMAX)]) ++ [(QL0, 66 + 1, QMAX)]) ++ [(QL0, QMIN, 73)]).
Definition s_u1_67_73_h0 : shape := SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SEmitP 2 [] (SExit 2)).
Lemma u1_67_73_h0_ok : main_check HS_main_both KCm BFUELm FUELm BITm TT 0%nat C_u1_67_73_h0 (plan_u1_67_73_both) = COk s_u1_67_73_h0.
Proof. ltac2:(cert_refl constr:(COk s_u1_67_73_h0)). Qed.

(* [comment removed for export] *)
Definition C_u1_74_inf_h0 : class := (((((root_class 1 ++ [(QL0, 0 + 1, QMAX)]) ++ [(QL0, 63 + 1, QMAX)]) ++ [(QL0, 64 + 1, QMAX)]) ++ [(QL0, 66 + 1, QMAX)]) ++ [(QL0, 73 + 1, QMAX)]).
Definition s_u1_74_inf_h0 : shape := SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1] (SEmitP 2 [SPLit [32; 73; 78; 80; 85; 84; 10]] (SExit 2)).
Lemma u1_74_inf_h0_ok : main_check HS_main_both KCm BFUELm FUELm BITm TT 0%nat C_u1_74_inf_h0 (plan_u1_74_inf_both) = COk s_u1_74_inf_h0.
Proof. ltac2:(cert_refl constr:(COk s_u1_74_inf_h0)). Qed.

(* [comment removed for export] *)
Definition C_toolong_h0 : class := root_class 2.
Definition s_toolong_h0 : shape := SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2] (SEmitP 2 [SPLit [10]] (SExit 2)).
Lemma toolong_h0_ok : main_check HS_main_both KCm BFUELm FUELm BITm TT 0%nat C_toolong_h0 (main_toolong) = COk s_toolong_h0.
Proof. ltac2:(cert_refl constr:(COk s_toolong_h0)). Qed.

(* [comment removed for export] *)
Definition C_noent_0_h0 : class := (root_class 3 ++ [(QL1, QMIN, 0)]).
Definition s_noent_0_h0 : shape := SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 10]] (SExit 2).
Lemma noent_0_h0_ok : main_check HS_main_both KCm BFUELm FUELm BITm TT 0%nat C_noent_0_h0 (main_noent0) = COk s_noent_0_h0.
Proof. ltac2:(cert_refl constr:(COk s_noent_0_h0)). Qed.

(* [comment removed for export] *)
Definition C_noent_1_62_h0 : class := ((root_class 3 ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, QMIN, 62)]).
Definition s_noent_1_62_h0 : shape := SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2; SPLit [10]] (SExit 2).
Lemma noent_1_62_h0_ok : main_check HS_main_both KCm BFUELm FUELm BITm TT 0%nat C_noent_1_62_h0 (main_noent_1_62) = COk s_noent_1_62_h0.
Proof. ltac2:(cert_refl constr:(COk s_noent_1_62_h0)). Qed.

(* [comment removed for export] *)
Definition C_noent_63_63_h0 : class := (((root_class 3 ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, QMIN, 63)]).
Definition s_noent_63_63_h0 : shape := SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2; SPLit [10]] (SEmitP 2 [] (SExit 2)).
Lemma noent_63_63_h0_ok : main_check HS_main_both KCm BFUELm FUELm BITm TT 0%nat C_noent_63_63_h0 (main_noent_63_63) = COk s_noent_63_63_h0.
Proof. ltac2:(cert_refl constr:(COk s_noent_63_63_h0)). Qed.

(* [comment removed for export] *)
Definition C_noent_64_64_h0 : class := ((((root_class 3 ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, 63 + 1, QMAX)]) ++ [(QL1, QMIN, 64)]).
Definition s_noent_64_64_h0 : shape := SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2] (SEmitP 2 [SPLit [10]] (SExit 2)).
Lemma noent_64_64_h0_ok : main_check HS_main_both KCm BFUELm FUELm BITm TT 0%nat C_noent_64_64_h0 (main_noent_64_64) = COk s_noent_64_64_h0.
Proof. ltac2:(cert_refl constr:(COk s_noent_64_64_h0)). Qed.

(* [comment removed for export] *)
Definition C_noent_65_4095_h0 : class := ((((root_class 3 ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, 63 + 1, QMAX)]) ++ [(QL1, 64 + 1, QMAX)]).
Definition s_noent_65_4095_h0 : shape := SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2] (SEmitP 2 [SPLit [10]] (SExit 2)).
Lemma noent_65_4095_h0_ok : main_check HS_main_both KCm BFUELm FUELm BITm TT 0%nat C_noent_65_4095_h0 (main_noent_65_4095) = COk s_noent_65_4095_h0.
Proof. ltac2:(cert_refl constr:(COk s_noent_65_4095_h0)). Qed.

End TTS.