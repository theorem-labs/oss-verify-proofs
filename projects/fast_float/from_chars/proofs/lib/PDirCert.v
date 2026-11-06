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
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvCall PDrvCall2 PDrvExit PDrvSys PDrvHeap PUsageCert POpenCert.
Import OSSVerify.Proofs.fast_float.from_chars.lib.PDrvData OSSVerify.Proofs.fast_float.from_chars.lib.PDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert.PDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvCall OSSVerify.Proofs.fast_float.from_chars.lib.PDrvCall2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvExit OSSVerify.Proofs.fast_float.from_chars.lib.PDrvSys OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeap OSSVerify.Proofs.fast_float.from_chars.lib.PUsageCert OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert.
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
Definition RPATH : region := RGz P1 1 RW (put_bytes TEmpty 0 [BK 46]).
Definition U_od : sst := Eval vm_compute in add_fact (add_rg U_ofd RPATH) (FRange X1 1 1).
Set Default Proof Mode "Ltac2".
Lemma U_od_eq : add_fact (add_rg U_ofd RPATH) (FRange X1 1 1) = U_od. Proof. cert_refl_vm constr:(U_od). Qed.
Set Default Proof Mode "Classic".
Definition LD1 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U_od [].
Set Default Proof Mode "Ltac2".
Lemma cert_LD1 : fx_explore TBL_P IMG_P 4000 S1 U_od [] = LD1. Proof. cert_refl_vm constr:(LD1). Qed.
Set Default Proof Mode "Classic".
Definition Ld1 : sst := Eval vm_compute in nth 0 LD1 P_main2.
Lemma LD1_eq : LD1 = [Ld1]. Proof. reflexivity. Qed.
Definition NXD1 : positive := Eval vm_compute in s_next Ld1.
Definition U_d2 : sst := Eval vm_compute in add_fact (havoc_call Ld1 0x2268c KEEPH [(0%nat, 57216, 8192); (7%nat, 4, 4)] None) (FRange (lvar (NXD1 + 10)) 16 140737488355328).
Set Default Proof Mode "Ltac2".
Lemma U_d2_eq : add_fact (havoc_call Ld1 0x2268c KEEPH [(0%nat, 57216, 8192); (7%nat, 4, 4)] None) (FRange (lvar (NXD1 + 10)) 16 140737488355328) = U_d2. Proof. cert_refl_vm constr:(U_d2). Qed.
Set Default Proof Mode "Classic".
Definition LD2 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U_d2 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LD2 : fx_explore TBL_P IMG_P 4000 S1 U_d2 [] = LD2. Proof. cert_refl_vm constr:(LD2). Qed.
Set Default Proof Mode "Classic".
Definition Ld2 : sst := Eval vm_compute in nth 0 LD2 P_main2.
Lemma LD2_eq : LD2 = [Ld2]. Proof. reflexivity. Qed.
Definition U_d3 : sst := Eval vm_compute in havoc_call Ld2 0x5ee78 KEEPALL [] (Some (lconst 18446744073709551595)).
Set Default Proof Mode "Ltac2".
Lemma U_d3_eq : havoc_call Ld2 0x5ee78 KEEPALL [] (Some (lconst 18446744073709551595)) = U_d3. Proof. cert_refl_vm constr:(U_d3). Qed.
Set Default Proof Mode "Classic".
Definition LD3 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U_d3 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LD3 : fx_explore TBL_P IMG_P 4000 S1 U_d3 [] = LD3. Proof. cert_refl_vm constr:(LD3). Qed.
Set Default Proof Mode "Classic".
Definition Ld3 : sst := Eval vm_compute in nth 0 LD3 P_main2.
Lemma LD3_eq : LD3 = [Ld3]. Proof. reflexivity. Qed.
Definition U_d4 : sst := Eval vm_compute in havoc_call Ld3 0x54ab0 KEEP [(0%nat, 64384, 32)] (Some X1).
Set Default Proof Mode "Ltac2".
Lemma U_d4_eq : havoc_call Ld3 0x54ab0 KEEP [(0%nat, 64384, 32)] (Some X1) = U_d4. Proof. cert_refl_vm constr:(U_d4). Qed.
Set Default Proof Mode "Classic".
Definition LD4 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S2 U_d4 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LD4 : fx_explore TBL_P IMG_P 4000 S2 U_d4 [] = LD4. Proof. cert_refl_vm constr:(LD4). Qed.
Set Default Proof Mode "Classic".
Definition Ld4 : sst := Eval vm_compute in nth 0 LD4 P_main2.
Lemma LD4_eq : LD4 = [Ld4]. Proof. reflexivity. Qed.
Definition LD4b := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S2 Ld4 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LD4b : fx_explore TBL_P IMG_P 4000 S2 Ld4 [] = LD4b. Proof. cert_refl_vm constr:(LD4b). Qed.
Set Default Proof Mode "Classic".
Definition Ld4b : sst := Eval vm_compute in nth 0 LD4b P_main2.
Lemma LD4b_eq : LD4b = [Ld4b]. Proof. reflexivity. Qed.
Definition U_d5 : sst := Eval vm_compute in havoc_call Ld4b 0x53e98 KEEP [(0%nat, 64995, 1)] (Some (laddc SP0 (-541))).
Set Default Proof Mode "Ltac2".
Lemma U_d5_eq : havoc_call Ld4b 0x53e98 KEEP [(0%nat, 64995, 1)] (Some (laddc SP0 (-541))) = U_d5. Proof. cert_refl_vm constr:(U_d5). Qed.
Set Default Proof Mode "Classic".
Definition U_d5t : sst := Eval vm_compute in upd_rg U_d5 0 (track (rgn U_d5 0) 64995 [BK 46]).
Set Default Proof Mode "Ltac2".
Lemma U_d5t_eq : upd_rg U_d5 0 (track (rgn U_d5 0) 64995 [BK 46]) = U_d5t. Proof. cert_refl_vm constr:(U_d5t). Qed.
Set Default Proof Mode "Classic".
Definition LD5 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S2 U_d5t [].
Set Default Proof Mode "Ltac2".
Lemma cert_LD5 : fx_explore TBL_P IMG_P 4000 S2 U_d5t [] = LD5. Proof. cert_refl_vm constr:(LD5). Qed.
Set Default Proof Mode "Classic".
Definition Ld5a : sst := Eval vm_compute in nth 0 LD5 P_main2.
Lemma LD5_eq : LD5 = [Ld5a]. Proof. reflexivity. Qed.
Definition U_d5h : sst := Eval vm_compute in havoc_call Ld5a 0x53e98 KEEP [(0%nat, 64996, 1)] (Some (laddc SP0 (-540))).
Set Default Proof Mode "Ltac2".
Lemma U_d5h_eq : havoc_call Ld5a 0x53e98 KEEP [(0%nat, 64996, 1)] (Some (laddc SP0 (-540))) = U_d5h. Proof. cert_refl_vm constr:(U_d5h). Qed.
Set Default Proof Mode "Classic".
Definition U_d5b : sst := Eval vm_compute in upd_rg U_d5h 0 (track (rgn U_d5h 0) 64996 [BK 10]).
Set Default Proof Mode "Ltac2".
Lemma U_d5b_eq : upd_rg U_d5h 0 (track (rgn U_d5h 0) 64996 [BK 10]) = U_d5b. Proof. cert_refl_vm constr:(U_d5b). Qed.
Set Default Proof Mode "Classic".
Definition LD5b := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U_d5b [].
Set Default Proof Mode "Ltac2".
Lemma cert_LD5b : fx_explore TBL_P IMG_P 4000 S1 U_d5b [] = LD5b. Proof. cert_refl_vm constr:(LD5b). Qed.
Set Default Proof Mode "Classic".
Definition Ld5 : sst := Eval vm_compute in nth 0 LD5b P_main2.
Lemma LD5b_eq : LD5b = [Ld5]. Proof. reflexivity. Qed.
Definition U_d6 : sst := Eval vm_compute in sw_template Ld5 0x54410 0 64848 5 (laddc SP0 (-560)) (lconst 80) (lconst 0).
Set Default Proof Mode "Ltac2".
Lemma U_d6_eq : sw_template Ld5 0x54410 0 64848 5 (laddc SP0 (-560)) (lconst 80) (lconst 0) = U_d6. Proof. cert_refl_vm constr:(U_d6). Qed.
Set Default Proof Mode "Classic".
Definition LD6 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U_d6 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LD6 : fx_explore TBL_P IMG_P 4000 S1 U_d6 [] = LD6. Proof. cert_refl_vm constr:(LD6). Qed.
Set Default Proof Mode "Classic".
Definition Ld6 : sst := Eval vm_compute in nth 0 LD6 P_main2.
Lemma LD6_eq : LD6 = [Ld6]. Proof. reflexivity. Qed.
Lemma hok_d2 : havoc_ok Ld1 [(0%nat, 57216, 8192); (7%nat, 4, 4)] None = true. Proof. vm_compute. reflexivity. Qed.
Lemma hok_d3 : havoc_ok Ld2 [] (Some (lconst 18446744073709551595)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma hok_d4 : havoc_ok Ld3 [(0%nat, 64384, 32)] (Some X1) = true. Proof. vm_compute. reflexivity. Qed.
Lemma hok_d5 : havoc_ok Ld4b [(0%nat, 64995, 1)] (Some (laddc SP0 (-541))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma hok_d5h : havoc_ok Ld5a [(0%nat, 64996, 1)] (Some (laddc SP0 (-540))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma hok_d6 : havoc_ok Ld5 [(0%nat, 64848, 112); (5%nat, 32, 16); (5%nat, 56, 8)] (Some (lconst 0)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wf_d5t : state_wf U_d5t = true. Proof. vm_compute. reflexivity. Qed.
Lemma wf_d5b : state_wf U_d5b = true. Proof. vm_compute. reflexivity. Qed.
Lemma wf_d6 : state_wf U_d6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wf_od : state_wf (add_rg U_ofd RPATH) = true. Proof. vm_compute. reflexivity. Qed.
