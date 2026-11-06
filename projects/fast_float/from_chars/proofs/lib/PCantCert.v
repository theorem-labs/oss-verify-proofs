(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxImg FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvData PDrvMain.
From OSSVerify.Proofs.fast_float.from_chars.lib Require POpenCert.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvCall PDrvCall2 PDrvExit PDrvSys PUsageCert POpenCert.
Import OSSVerify.Proofs.fast_float.from_chars.lib.PDrvData OSSVerify.Proofs.fast_float.from_chars.lib.PDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert.PDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvCall OSSVerify.Proofs.fast_float.from_chars.lib.PDrvCall2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvExit OSSVerify.Proofs.fast_float.from_chars.lib.PDrvSys OSSVerify.Proofs.fast_float.from_chars.lib.PUsageCert OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 cert_refl_vm (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl _ $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Set Default Proof Mode "Classic".

Definition INFO (L : sst) := (s_pc L, RET L, rget (s_regs L) (rk 2), rget (s_regs L) (rk 10), rget (s_regs L) (rk 11), rget (s_regs L) (rk 12)).
Definition CONDS (L : sst) := List.filter (fun f => match f with FCond _ _ _ _ => true | _ => false end) (s_facts L).

(* [comment removed for export] *)
Definition LC1 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U_oe [].
Set Default Proof Mode "Ltac2".
Lemma certC1 : fx_explore TBL_P IMG_P 4000 S1 U_oe [] = LC1. Proof. cert_refl_vm constr:(LC1). Qed.
Set Default Proof Mode "Classic".
Definition Lc1 : sst := Eval vm_compute in nth 0 LC1 P_main2.
Lemma LC1_one : LC1 = [Lc1]. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition U_c2 : sst := Eval vm_compute in havoc_call Lc1 0x54ab0 KEEP [(0%nat, 64384, 32)] (Some X1).
Set Default Proof Mode "Ltac2".
Lemma U_c2_eq : havoc_call Lc1 0x54ab0 KEEP [(0%nat, 64384, 32)] (Some X1) = U_c2. Proof. cert_refl_vm constr:(U_c2). Qed.
Set Default Proof Mode "Classic".
Definition LB1c := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S2 U_c2 [].
Set Default Proof Mode "Ltac2".
Lemma certB1c : fx_explore TBL_P IMG_P 4000 S2 U_c2 [] = LB1c. Proof. cert_refl_vm constr:(LB1c). Qed.
Set Default Proof Mode "Classic".
Definition L2c : sst := Eval vm_compute in nth 0 LB1c P_main2.
Lemma LB1c_one : LB1c = [L2c]. Proof. reflexivity. Qed.
Definition LB2c := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S2 L2c [].
Set Default Proof Mode "Ltac2".
Lemma certB2c : fx_explore TBL_P IMG_P 4000 S2 L2c [] = LB2c. Proof. cert_refl_vm constr:(LB2c). Qed.
Set Default Proof Mode "Classic".
Definition L3bc : sst := Eval vm_compute in nth 0 LB2c P_main2.
Definition L3ac : sst := Eval vm_compute in nth 1 LB2c P_main2.
Lemma LB2c_two : LB2c = [L3bc; L3ac]. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition U4bc : sst := Eval vm_compute in sw_template L3bc 0x55000 0 64304 5 (laddc SP0 (-560)) (lconst 80) (lvar 8).
Set Default Proof Mode "Ltac2".
Lemma U4bc_eq : sw_template L3bc 0x55000 0 64304 5 (laddc SP0 (-560)) (lconst 80) (lvar 8) = U4bc. Proof. cert_refl_vm constr:(U4bc). Qed.
Set Default Proof Mode "Classic".
Lemma hok3bc : havoc_ok L3bc [(0%nat, 64304, 112); (5%nat, 32, 16); (5%nat, 56, 8)] (Some (lvar 8)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wf4bc : state_wf U4bc = true. Proof. vm_compute. reflexivity. Qed.
Definition LCbc := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U4bc [].
Set Default Proof Mode "Ltac2".
Lemma certCbc : fx_explore TBL_P IMG_P 4000 S1 U4bc [] = LCbc. Proof. cert_refl_vm constr:(LCbc). Qed.
Set Default Proof Mode "Classic".
Definition L4bc : sst := Eval vm_compute in nth 0 LCbc P_main2.
Lemma LCbc_one : LCbc = [L4bc]. Proof. reflexivity. Qed.
Definition U5bc : sst := Eval vm_compute in sw_template L4bc 0x54410 0 64848 5 (laddc SP0 (-560)) (lconst 80) (lconst 0).
Set Default Proof Mode "Ltac2".
Lemma U5bc_eq : sw_template L4bc 0x54410 0 64848 5 (laddc SP0 (-560)) (lconst 80) (lconst 0) = U5bc. Proof. cert_refl_vm constr:(U5bc). Qed.
Set Default Proof Mode "Classic".
Lemma hok4bc : havoc_ok L4bc [(0%nat, 64848, 112); (5%nat, 32, 16); (5%nat, 56, 8)] (Some (lconst 0)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wf5bc : state_wf U5bc = true. Proof. vm_compute. reflexivity. Qed.
Definition LDbc := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U5bc [].
Set Default Proof Mode "Ltac2".
Lemma certDbc : fx_explore TBL_P IMG_P 4000 S1 U5bc [] = LDbc. Proof. cert_refl_vm constr:(LDbc). Qed.
Set Default Proof Mode "Classic".
Definition L5bc : sst := Eval vm_compute in nth 0 LDbc P_main2.
Lemma LDbc_one : LDbc = [L5bc]. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition RG3ac : list region := Eval vm_compute in split_rgs (s_rgs L3ac) 0 64993 65056.
Lemma wk3ac : weaken_ok (s_rgs L3ac) RG3ac (split_ws 22 0 65056) = true. Proof. vm_compute. reflexivity. Qed.
Definition L3ac' : sst := with_rgs L3ac RG3ac.
Lemma L3ac'_wf : state_wf L3ac' = true. Proof. vm_compute. reflexivity. Qed.
Definition U4ac : sst := Eval vm_compute in havoc_call L3ac' 0x53e98 KEEP [] (Some (laddc SP0 (-543))).
Set Default Proof Mode "Ltac2".
Lemma U4ac_eq : havoc_call L3ac' 0x53e98 KEEP [] (Some (laddc SP0 (-543))) = U4ac. Proof. cert_refl_vm constr:(U4ac). Qed.
Set Default Proof Mode "Classic".
Lemma hok3ac : havoc_ok L3ac' [] (Some (laddc SP0 (-543))) = true. Proof. vm_compute. reflexivity. Qed.
Definition LCac := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S2 U4ac [].
Set Default Proof Mode "Ltac2".
Lemma certCac : fx_explore TBL_P IMG_P 4000 S2 U4ac [] = LCac. Proof. cert_refl_vm constr:(LCac). Qed.
Set Default Proof Mode "Classic".
Definition L4ac1 : sst := Eval vm_compute in nth 0 LCac P_main2.
Definition L4ac2 : sst := Eval vm_compute in nth 1 LCac P_main2.
Lemma LCac_two : LCac = [L4ac1; L4ac2]. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition U5ac1 : sst := Eval vm_compute in sw_template L4ac1 0x545e0 0 64304 5 (laddc SP0 (-560)) (lconst 80) (lconst 1).
Set Default Proof Mode "Ltac2".
Lemma U5ac1_eq : sw_template L4ac1 0x545e0 0 64304 5 (laddc SP0 (-560)) (lconst 80) (lconst 1) = U5ac1. Proof. cert_refl_vm constr:(U5ac1). Qed.
Set Default Proof Mode "Classic".
Lemma hok4ac1 : havoc_ok L4ac1 [(0%nat, 64304, 112); (5%nat, 32, 16); (5%nat, 56, 8)] (Some (lconst 1)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wf5ac1 : state_wf U5ac1 = true. Proof. vm_compute. reflexivity. Qed.
Definition LDac1 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U5ac1 [].
Set Default Proof Mode "Ltac2".
Lemma certDac1 : fx_explore TBL_P IMG_P 4000 S1 U5ac1 [] = LDac1. Proof. cert_refl_vm constr:(LDac1). Qed.
Set Default Proof Mode "Classic".
Definition L6ac1 : sst := Eval vm_compute in nth 0 LDac1 P_main2.
Lemma LDac1_one : LDac1 = [L6ac1]. Proof. reflexivity. Qed.
Definition U6ac1 : sst := Eval vm_compute in sw_template L6ac1 0x54410 0 64848 5 (laddc SP0 (-560)) (lconst 80) (lconst 0).
Set Default Proof Mode "Ltac2".
Lemma U6ac1_eq : sw_template L6ac1 0x54410 0 64848 5 (laddc SP0 (-560)) (lconst 80) (lconst 0) = U6ac1. Proof. cert_refl_vm constr:(U6ac1). Qed.
Set Default Proof Mode "Classic".
Lemma hok6ac1 : havoc_ok L6ac1 [(0%nat, 64848, 112); (5%nat, 32, 16); (5%nat, 56, 8)] (Some (lconst 0)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wf6ac1 : state_wf U6ac1 = true. Proof. vm_compute. reflexivity. Qed.
Definition LEac1 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U6ac1 [].
Set Default Proof Mode "Ltac2".
Lemma certEac1 : fx_explore TBL_P IMG_P 4000 S1 U6ac1 [] = LEac1. Proof. cert_refl_vm constr:(LEac1). Qed.
Set Default Proof Mode "Classic".
Definition L7ac1 : sst := Eval vm_compute in nth 0 LEac1 P_main2.
Lemma LEac1_one : LEac1 = [L7ac1]. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition RES2c : lin := Eval vm_compute in rget (s_regs L4ac2) (rk 10).
Definition U5ac2 : sst := Eval vm_compute in havoc_call L4ac2 0x53e98 KEEP [] (Some RES2c).
Set Default Proof Mode "Ltac2".
Lemma U5ac2_eq : havoc_call L4ac2 0x53e98 KEEP [] (Some RES2c) = U5ac2. Proof. cert_refl_vm constr:(U5ac2). Qed.
Set Default Proof Mode "Classic".
Lemma hok4ac2 : havoc_ok L4ac2 [] (Some RES2c) = true. Proof. vm_compute. reflexivity. Qed.
Definition LDac2 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U5ac2 [].
Set Default Proof Mode "Ltac2".
Lemma certDac2 : fx_explore TBL_P IMG_P 4000 S1 U5ac2 [] = LDac2. Proof. cert_refl_vm constr:(LDac2). Qed.
Set Default Proof Mode "Classic".
Definition L6ac2 : sst := Eval vm_compute in nth 0 LDac2 P_main2.
Lemma LDac2_one : LDac2 = [L6ac2]. Proof. reflexivity. Qed.
Definition U6ac2 : sst := Eval vm_compute in sw_template L6ac2 0x54410 0 64848 5 (laddc SP0 (-560)) (lconst 80) (lconst 0).
Set Default Proof Mode "Ltac2".
Lemma U6ac2_eq : sw_template L6ac2 0x54410 0 64848 5 (laddc SP0 (-560)) (lconst 80) (lconst 0) = U6ac2. Proof. cert_refl_vm constr:(U6ac2). Qed.
Set Default Proof Mode "Classic".
Lemma hok6ac2 : havoc_ok L6ac2 [(0%nat, 64848, 112); (5%nat, 32, 16); (5%nat, 56, 8)] (Some (lconst 0)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wf6ac2 : state_wf U6ac2 = true. Proof. vm_compute. reflexivity. Qed.
Definition LEac2 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U6ac2 [].
Set Default Proof Mode "Ltac2".
Lemma certEac2 : fx_explore TBL_P IMG_P 4000 S1 U6ac2 [] = LEac2. Proof. cert_refl_vm constr:(LEac2). Qed.
Set Default Proof Mode "Classic".
Definition L7ac2 : sst := Eval vm_compute in nth 0 LEac2 P_main2.
Lemma LEac2_one : LEac2 = [L7ac2]. Proof. reflexivity. Qed.
