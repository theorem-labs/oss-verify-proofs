(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxImg FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UDrvData UDrvMain UDrvCall UDrvCall2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 cert_refl_vm (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl _ $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Set Default Proof Mode "Classic".

Definition rk (r : Z) : positive := bv_key (Z_to_bv 5 r).
Definition S1 := [0x607e8; 0x55e08; 0x52be0; 0x60c2c; 0x530c8; 0x52f88; 0x22e0c].
Definition S2 := 0x600a8 :: S1.
Definition XP (s : sst) (st : list Z) := fx_explore TBL_P IMG_P 4000 st s [].
Definition RET (L : sst) : Z := l_c (rget (s_regs L) (rk 1)).

(* [comment removed for export] *)
Definition LA := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 P_main1 [].
Set Default Proof Mode "Ltac2".
Lemma certA : fx_explore TBL_P IMG_P 4000 S1 P_main1 [] = LA. Proof. cert_refl_vm constr:(LA). Qed.
Set Default Proof Mode "Classic".
Definition L1 : sst := Eval vm_compute in nth 0 LA P_main1.
Lemma LA_one : LA = [L1]. Proof. reflexivity. Qed.
Definition L1_R0 : region := Eval vm_compute in nth 0 (s_rgs L1) (RGz lc0 0 RW TEmpty).
Lemma L1_R0_eq : nth_error (s_rgs L1) 0 = Some L1_R0. Proof. vm_compute. reflexivity. Qed.
Lemma L1_R0_base : rg_base L1_R0 = laddc SP0 (-65536). Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition U2 : sst := Eval vm_compute in havoc_call L1 0x56868 KEEP [(0%nat, 64384, 32)] (Some X0).
Set Default Proof Mode "Ltac2".
Lemma U2_eq : havoc_call L1 0x56868 KEEP [(0%nat, 64384, 32)] (Some X0) = U2. Proof. cert_refl_vm constr:(U2). Qed.
Set Default Proof Mode "Classic".

(* [comment removed for export] *)
Definition LB1 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S2 U2 [].
Set Default Proof Mode "Ltac2".
Lemma certB1 : fx_explore TBL_P IMG_P 4000 S2 U2 [] = LB1. Proof. cert_refl_vm constr:(LB1). Qed.
Set Default Proof Mode "Classic".
Definition L2 : sst := Eval vm_compute in nth 0 LB1 P_main1.
Lemma LB1_one : LB1 = [L2]. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Definition LB2 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S2 L2 [].
Set Default Proof Mode "Ltac2".
Lemma certB2 : fx_explore TBL_P IMG_P 4000 S2 L2 [] = LB2. Proof. cert_refl_vm constr:(LB2). Qed.
Set Default Proof Mode "Classic".
Definition L3b : sst := Eval vm_compute in nth 0 LB2 P_main1.
Definition L3a : sst := Eval vm_compute in nth 1 LB2 P_main1.
Lemma LB2_two : LB2 = [L3b; L3a]. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition RG3a : list region := Eval vm_compute in split_rgs (s_rgs L3a) 0 64983 65056.
Lemma wk3a : weaken_ok (s_rgs L3a) RG3a (split_ws 22 0 65056) = true. Proof. vm_compute. reflexivity. Qed.
Definition L3a' : sst := with_rgs L3a RG3a.
Lemma L3a'_wf : state_wf L3a' = true. Proof. vm_compute. reflexivity. Qed.
Definition U4a : sst := Eval vm_compute in havoc_call L3a' 0x55c50 KEEP [] (Some (laddc SP0 (-553))).
Set Default Proof Mode "Ltac2".
Lemma U4a_eq : havoc_call L3a' 0x55c50 KEEP [] (Some (laddc SP0 (-553))) = U4a. Proof. cert_refl_vm constr:(U4a). Qed.
Set Default Proof Mode "Classic".
Lemma hok3a : havoc_ok L3a' [] (Some (laddc SP0 (-553))) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition U4b : sst := Eval vm_compute in sw_template L3b 0x56db8 0 64304 5 (laddc SP0 (-560)) (lconst 80) (lvar 7).
Set Default Proof Mode "Ltac2".
Lemma U4b_eq : sw_template L3b 0x56db8 0 64304 5 (laddc SP0 (-560)) (lconst 80) (lvar 7) = U4b. Proof. cert_refl_vm constr:(U4b). Qed.
Set Default Proof Mode "Classic".
Lemma hok3b : havoc_ok L3b [(0%nat, 64304, 112); (5%nat, 32, 16); (5%nat, 56, 8)] (Some (lvar 7)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wf3b : state_wf U4b = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition L3b_R0 : region := Eval vm_compute in nth 0 (s_rgs L3b) (RGz lc0 0 RW TEmpty).
Lemma L3b_R0_eq : nth_error (s_rgs L3b) 0 = Some L3b_R0. Proof. vm_compute. reflexivity. Qed.
Definition L3b_R3 : region := Eval vm_compute in nth 3 (s_rgs L3b) (RGz lc0 0 RW TEmpty).
Lemma L3b_R3_eq : nth_error (s_rgs L3b) 3 = Some L3b_R3. Proof. vm_compute. reflexivity. Qed.
Definition L3b_R5 : region := Eval vm_compute in nth 5 (s_rgs L3b) (RGz lc0 0 RW TEmpty).
Lemma L3b_R5_eq : nth_error (s_rgs L3b) 5 = Some L3b_R5. Proof. vm_compute. reflexivity. Qed.
Definition L3b_R8 : region := Eval vm_compute in nth 8 (s_rgs L3b) (RGz lc0 0 RW TEmpty).
Lemma L3b_R8_eq : nth_error (s_rgs L3b) 8 = Some L3b_R8. Proof. vm_compute. reflexivity. Qed.

Definition L3a_R0 : region := Eval vm_compute in nth 0 (s_rgs L3a) (RGz lc0 0 RW TEmpty).
Lemma L3a_R0_eq : nth_error (s_rgs L3a) 0 = Some L3a_R0. Proof. vm_compute. reflexivity. Qed.
Lemma L3a_R0_base : rg_base L3a_R0 = laddc SP0 (-65536). Proof. vm_compute. reflexivity. Qed.
Lemma L3a_R0_size : rg_size L3a_R0 = lconst 65536. Proof. vm_compute. reflexivity. Qed.
Lemma L3a_R0_kind : rg_kind L3a_R0 = RW. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition LCa := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S2 U4a [].
(* [comment removed for export] *)
Definition LCb := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U4b [].
Definition L4b : sst := Eval vm_compute in nth 0 LCb P_main1.
Set Default Proof Mode "Ltac2".
Lemma certCb : fx_explore TBL_P IMG_P 4000 S1 U4b [] = LCb. Proof. cert_refl_vm constr:(LCb). Qed.
Set Default Proof Mode "Classic".
Lemma LCb_one : LCb = [L4b]. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Definition U5b : sst := Eval vm_compute in sw_template L4b 0x561c8 0 64848 5 (laddc SP0 (-560)) (lconst 80) (lconst 0).
Set Default Proof Mode "Ltac2".
Lemma U5b_eq : sw_template L4b 0x561c8 0 64848 5 (laddc SP0 (-560)) (lconst 80) (lconst 0) = U5b. Proof. cert_refl_vm constr:(U5b). Qed.
Set Default Proof Mode "Classic".
Definition LDb := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U5b [].
Set Default Proof Mode "Ltac2".
Lemma certDb : fx_explore TBL_P IMG_P 4000 S1 U5b [] = LDb. Proof. cert_refl_vm constr:(LDb). Qed.
Set Default Proof Mode "Classic".
Definition L5b : sst := Eval vm_compute in nth 0 LDb P_main1.
Lemma LDb_one : LDb = [L5b]. Proof. reflexivity. Qed.
Definition L5b_R0 : region := Eval vm_compute in nth 0 (s_rgs L5b) (RGz lc0 0 RW TEmpty).
Lemma L5b_R0_eq : nth_error (s_rgs L5b) 0 = Some L5b_R0. Proof. vm_compute. reflexivity. Qed.
Definition L5b_R3 : region := Eval vm_compute in nth 3 (s_rgs L5b) (RGz lc0 0 RW TEmpty).
Lemma L5b_R3_eq : nth_error (s_rgs L5b) 3 = Some L5b_R3. Proof. vm_compute. reflexivity. Qed.
Definition L5b_R5 : region := Eval vm_compute in nth 5 (s_rgs L5b) (RGz lc0 0 RW TEmpty).
Lemma L5b_R5_eq : nth_error (s_rgs L5b) 5 = Some L5b_R5. Proof. vm_compute. reflexivity. Qed.
Definition L5b_R6 : region := Eval vm_compute in nth 6 (s_rgs L5b) (RGz lc0 0 RW TEmpty).
Lemma L5b_R6_eq : nth_error (s_rgs L5b) 6 = Some L5b_R6. Proof. vm_compute. reflexivity. Qed.
Definition L5b_R7 : region := Eval vm_compute in nth 7 (s_rgs L5b) (RGz lc0 0 RW TEmpty).
Lemma L5b_R7_eq : nth_error (s_rgs L5b) 7 = Some L5b_R7. Proof. vm_compute. reflexivity. Qed.
Definition L4b_R0 : region := Eval vm_compute in nth 0 (s_rgs L4b) (RGz lc0 0 RW TEmpty).
Lemma L4b_R0_eq : nth_error (s_rgs L4b) 0 = Some L4b_R0. Proof. vm_compute. reflexivity. Qed.
Definition L4b_R5 : region := Eval vm_compute in nth 5 (s_rgs L4b) (RGz lc0 0 RW TEmpty).
Lemma L4b_R5_eq : nth_error (s_rgs L4b) 5 = Some L4b_R5. Proof. vm_compute. reflexivity. Qed.
Definition L4b_R3 : region := Eval vm_compute in nth 3 (s_rgs L4b) (RGz lc0 0 RW TEmpty).
Lemma L4b_R3_eq : nth_error (s_rgs L4b) 3 = Some L4b_R3. Proof. vm_compute. reflexivity. Qed.
Definition L4b_R8 : region := Eval vm_compute in nth 8 (s_rgs L4b) (RGz lc0 0 RW TEmpty).
Lemma L4b_R8_eq : nth_error (s_rgs L4b) 8 = Some L4b_R8. Proof. vm_compute. reflexivity. Qed.
Lemma hok4b : havoc_ok L4b [(0%nat, 64848, 112); (5%nat, 32, 16); (5%nat, 56, 8)] (Some (lconst 0)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wf5b : state_wf U5b = true. Proof. vm_compute. reflexivity. Qed.
