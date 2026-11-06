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
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import PDrvData PDrvMain PDrvCall PDrvCall2 PUsageCert.
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

(* [comment removed for export] *)
Set Default Proof Mode "Ltac2".
Lemma certCa : fx_explore TBL_P IMG_P 4000 S2 U4a [] = LCa. Proof. cert_refl_vm constr:(LCa). Qed.
Set Default Proof Mode "Classic".
Definition L4a1 : sst := Eval vm_compute in nth 0 LCa P_main1.
Definition L4a2 : sst := Eval vm_compute in nth 1 LCa P_main1.
Lemma LCa_two : LCa = [L4a1; L4a2]. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition U5a1 : sst := Eval vm_compute in sw_template L4a1 0x545e0 0 64304 5 (laddc SP0 (-560)) (lconst 80) (lconst 7).
Set Default Proof Mode "Ltac2".
Lemma U5a1_eq : sw_template L4a1 0x545e0 0 64304 5 (laddc SP0 (-560)) (lconst 80) (lconst 7) = U5a1. Proof. cert_refl_vm constr:(U5a1). Qed.
Set Default Proof Mode "Classic".
Lemma hok4a1 : havoc_ok L4a1 [(0%nat, 64304, 112); (5%nat, 32, 16); (5%nat, 56, 8)] (Some (lconst 7)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wf5a1 : state_wf U5a1 = true. Proof. vm_compute. reflexivity. Qed.
Definition LDa1 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U5a1 [].
Set Default Proof Mode "Ltac2".
Lemma certDa1 : fx_explore TBL_P IMG_P 4000 S1 U5a1 [] = LDa1. Proof. cert_refl_vm constr:(LDa1). Qed.
Set Default Proof Mode "Classic".
Definition L6a1 : sst := Eval vm_compute in nth 0 LDa1 P_main1.
Lemma LDa1_one : LDa1 = [L6a1]. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Definition U6a1 : sst := Eval vm_compute in sw_template L6a1 0x54410 0 64848 5 (laddc SP0 (-560)) (lconst 80) (lconst 0).
Set Default Proof Mode "Ltac2".
Lemma U6a1_eq : sw_template L6a1 0x54410 0 64848 5 (laddc SP0 (-560)) (lconst 80) (lconst 0) = U6a1. Proof. cert_refl_vm constr:(U6a1). Qed.
Set Default Proof Mode "Classic".
Lemma hok6a1 : havoc_ok L6a1 [(0%nat, 64848, 112); (5%nat, 32, 16); (5%nat, 56, 8)] (Some (lconst 0)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wf6a1 : state_wf U6a1 = true. Proof. vm_compute. reflexivity. Qed.
Definition LEa1 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U6a1 [].
Set Default Proof Mode "Ltac2".
Lemma certEa1 : fx_explore TBL_P IMG_P 4000 S1 U6a1 [] = LEa1. Proof. cert_refl_vm constr:(LEa1). Qed.
Set Default Proof Mode "Classic".
Definition L7a1 : sst := Eval vm_compute in nth 0 LEa1 P_main1.
Lemma LEa1_one : LEa1 = [L7a1]. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition RES2 : lin := Eval vm_compute in rget (s_regs L4a2) (rk 10).
Definition U5a2 : sst := Eval vm_compute in havoc_call L4a2 0x53e98 KEEP [] (Some RES2).
Set Default Proof Mode "Ltac2".
Lemma U5a2_eq : havoc_call L4a2 0x53e98 KEEP [] (Some RES2) = U5a2. Proof. cert_refl_vm constr:(U5a2). Qed.
Set Default Proof Mode "Classic".
Lemma hok4a2 : havoc_ok L4a2 [] (Some RES2) = true. Proof. vm_compute. reflexivity. Qed.
Definition LDa2 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U5a2 [].
Set Default Proof Mode "Ltac2".
Lemma certDa2 : fx_explore TBL_P IMG_P 4000 S1 U5a2 [] = LDa2. Proof. cert_refl_vm constr:(LDa2). Qed.
Set Default Proof Mode "Classic".
Definition L6a2 : sst := Eval vm_compute in nth 0 LDa2 P_main1.
Lemma LDa2_one : LDa2 = [L6a2]. Proof. reflexivity. Qed.
Definition U6a2 : sst := Eval vm_compute in sw_template L6a2 0x54410 0 64848 5 (laddc SP0 (-560)) (lconst 80) (lconst 0).
Set Default Proof Mode "Ltac2".
Lemma U6a2_eq : sw_template L6a2 0x54410 0 64848 5 (laddc SP0 (-560)) (lconst 80) (lconst 0) = U6a2. Proof. cert_refl_vm constr:(U6a2). Qed.
Set Default Proof Mode "Classic".
Lemma hok6a2 : havoc_ok L6a2 [(0%nat, 64848, 112); (5%nat, 32, 16); (5%nat, 56, 8)] (Some (lconst 0)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wf6a2 : state_wf U6a2 = true. Proof. vm_compute. reflexivity. Qed.
Definition LEa2 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U6a2 [].
Set Default Proof Mode "Ltac2".
Lemma certEa2 : fx_explore TBL_P IMG_P 4000 S1 U6a2 [] = LEa2. Proof. cert_refl_vm constr:(LEa2). Qed.
Set Default Proof Mode "Classic".
Definition L7a2 : sst := Eval vm_compute in nth 0 LEa2 P_main1.
Lemma LEa2_one : LEa2 = [L7a2]. Proof. reflexivity. Qed.
