(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxImg FxEnt FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvData PDrvMain.
From OSSVerify.Proofs.fast_float.from_chars.lib Require POpenCert.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvCall PDrvCall2 PDrvExit PDrvSys PDrvHeap PUsageCert POpenCert PLoopCert.
Import OSSVerify.Proofs.fast_float.from_chars.lib.PDrvData OSSVerify.Proofs.fast_float.from_chars.lib.PDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert.PDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvCall OSSVerify.Proofs.fast_float.from_chars.lib.PDrvCall2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvExit OSSVerify.Proofs.fast_float.from_chars.lib.PDrvSys OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeap OSSVerify.Proofs.fast_float.from_chars.lib.PUsageCert OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert OSSVerify.Proofs.fast_float.from_chars.lib.PLoopCert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 cert_refl_vm (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl _ $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Set Default Proof Mode "Classic".

(* [comment removed for export] *)
Lemma hok_c : havoc_ok Lc [] (Some (lconst 0)) = true. Proof. vm_compute. reflexivity. Qed.
Definition U_c : sst := Eval vm_compute in havoc_call Lc 0x5ee78 KEEPALL [] (Some (lconst 0)).
Set Default Proof Mode "Ltac2".
Lemma U_c_eq : havoc_call Lc 0x5ee78 KEEPALL [] (Some (lconst 0)) = U_c. Proof. cert_refl_vm constr:(U_c). Qed.
Set Default Proof Mode "Classic".
Definition SHD := 0x2273c :: S1.
Definition LC1 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 SHD U_c [].
Set Default Proof Mode "Ltac2".
Lemma cert_LC1 : fx_explore TBL_P IMG_P 4000 SHD U_c [] = LC1. Proof. cert_refl_vm constr:(LC1). Qed.
Set Default Proof Mode "Classic".
Definition Lhd : sst := Eval vm_compute in nth 0 LC1 P_main2.
Definition Lsh : sst := Eval vm_compute in nth 1 LC1 P_main2.
Lemma LC1_eq : LC1 = [Lhd; Lsh]. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition SWFP : list fpr := [(0%nat, 65232, 112); (5%nat, 32, 16); (5%nat, 56, 8)].
Lemma hok_sh : havoc_ok Lsh SWFP (Some (lconst 31)) = true. Proof. vm_compute. reflexivity. Qed.
Definition U_sh2 : sst := Eval vm_compute in sw_template Lsh 0x53f54 0 65232 5 (lconst 0x962a0) (lconst 0) (lconst 31).
Set Default Proof Mode "Ltac2".
Lemma U_sh2_eq : sw_template Lsh 0x53f54 0 65232 5 (lconst 0x962a0) (lconst 0) (lconst 31) = U_sh2. Proof. cert_refl_vm constr:(U_sh2). Qed.
Set Default Proof Mode "Classic".
Lemma wf_sh2 : state_wf U_sh2 = true. Proof. vm_compute. reflexivity. Qed.
Definition LSH2 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U_sh2 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LSH2 : fx_explore TBL_P IMG_P 4000 S1 U_sh2 [] = LSH2. Proof. cert_refl_vm constr:(LSH2). Qed.
Set Default Proof Mode "Classic".
Definition Lsh3 : sst := Eval vm_compute in nth 0 LSH2 P_main2.
Lemma LSH2_eq : LSH2 = [Lsh3]. Proof. reflexivity. Qed.
Lemma hok_sh3 : havoc_ok Lsh3 HFP None = true. Proof. vm_compute. reflexivity. Qed.
Definition U_sh4 : sst := Eval vm_compute in havoc_call Lsh3 0x22834 KEEPH HFP None.
Set Default Proof Mode "Ltac2".
Lemma U_sh4_eq : havoc_call Lsh3 0x22834 KEEPH HFP None = U_sh4. Proof. cert_refl_vm constr:(U_sh4). Qed.
Set Default Proof Mode "Classic".
Definition LSH4 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U_sh4 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LSH4 : fx_explore TBL_P IMG_P 4000 S1 U_sh4 [] = LSH4. Proof. cert_refl_vm constr:(LSH4). Qed.
Set Default Proof Mode "Classic".
Definition Lsh5 : sst := Eval vm_compute in nth 0 LSH4 P_main2.
Lemma LSH4_eq : LSH4 = [Lsh5]. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition KEEPH5 : list positive := [2;3;4;5;6;7;8;9;10;13;14;15;16;17;18;20;21;23;24;25;26;27;28;29;30;31;32]%positive.
Lemma hok_hd : havoc_ok Lhd [] None = true. Proof. vm_compute. reflexivity. Qed.
Definition NXH : positive := Eval vm_compute in s_next Lhd.
Definition CLV : positive := Eval vm_compute in (NXH + 18)%positive.
Definition BMR : region := RGz (LIN 2 [(BUF, 1); (CLV, 1)]) 4 RW TEmpty.
Definition U_h0 : sst := Eval vm_compute in havoc_call Lhd 0x22750 KEEPH5 [] None.
Set Default Proof Mode "Ltac2".
Lemma U_h0_eq : havoc_call Lhd 0x22750 KEEPH5 [] None = U_h0. Proof. cert_refl_vm constr:(U_h0). Qed.
Set Default Proof Mode "Classic".
Definition U_h : sst := Eval vm_compute in add_rg (add_fact U_h0 (FRange (lvar CLV) 0 32767)) BMR.
Lemma U_h_eq : add_rg (add_fact U_h0 (FRange (lvar CLV) 0 32767)) BMR = U_h. Proof. vm_compute. reflexivity. Qed.
Lemma wf_h : state_wf U_h = true. Proof. vm_compute. reflexivity. Qed.
Definition STR := 0x22908 :: S1.
Definition LH1 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 STR U_h [].
Set Default Proof Mode "Ltac2".
Lemma cert_LH1 : fx_explore TBL_P IMG_P 4000 STR U_h [] = LH1. Proof. cert_refl_vm constr:(LH1). Qed.
Set Default Proof Mode "Classic".
Definition Ltr0 : sst := Eval vm_compute in nth 0 LH1 P_main2.
Definition Lov0 : sst := Eval vm_compute in nth 1 LH1 P_main2.
Lemma LH1_eq : LH1 = [Ltr0; Lov0]. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Definition WS21 : list (nat * Z) := List.map (fun k => (k, 0)) (seq 0 22).
Definition Ltr : sst := Eval vm_compute in with_rgs Ltr0 (firstn 22 (s_rgs Ltr0)).
Definition Lov : sst := Eval vm_compute in with_rgs Lov0 (firstn 22 (s_rgs Lov0)).
Lemma Ltr_eq : with_rgs Ltr0 (firstn 22 (s_rgs Ltr0)) = Ltr. Proof. vm_compute. reflexivity. Qed.
Lemma Lov_eq : with_rgs Lov0 (firstn 22 (s_rgs Lov0)) = Lov. Proof. vm_compute. reflexivity. Qed.
Lemma wk_tr : weaken_ok (s_rgs Ltr0) (firstn 22 (s_rgs Ltr0)) WS21 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wk_ov : weaken_ok (s_rgs Lov0) (firstn 22 (s_rgs Lov0)) WS21 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wf_tr : state_wf Ltr = true. Proof. vm_compute. reflexivity. Qed.
Lemma wf_ov : state_wf Lov = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma hok_ov : havoc_ok Lov SWFP (Some (lconst 31)) = true. Proof. vm_compute. reflexivity. Qed.
Definition U_ov2 : sst := Eval vm_compute in sw_template Lov 0x53f54 0 65232 5 (lconst 0x962a0) (lconst 0) (lconst 31).
Set Default Proof Mode "Ltac2".
Lemma U_ov2_eq : sw_template Lov 0x53f54 0 65232 5 (lconst 0x962a0) (lconst 0) (lconst 31) = U_ov2. Proof. cert_refl_vm constr:(U_ov2). Qed.
Set Default Proof Mode "Classic".
Lemma wf_ov2 : state_wf U_ov2 = true. Proof. vm_compute. reflexivity. Qed.
Definition LOV2 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U_ov2 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LOV2 : fx_explore TBL_P IMG_P 4000 S1 U_ov2 [] = LOV2. Proof. cert_refl_vm constr:(LOV2). Qed.
Set Default Proof Mode "Classic".
Definition Lov3 : sst := Eval vm_compute in nth 0 LOV2 P_main2.
Lemma LOV2_eq : LOV2 = [Lov3]. Proof. reflexivity. Qed.
Lemma hok_ov3 : havoc_ok Lov3 HFP None = true. Proof. vm_compute. reflexivity. Qed.
Definition U_ov4 : sst := Eval vm_compute in havoc_call Lov3 0x22834 KEEPH HFP None.
Set Default Proof Mode "Ltac2".
Lemma U_ov4_eq : havoc_call Lov3 0x22834 KEEPH HFP None = U_ov4. Proof. cert_refl_vm constr:(U_ov4). Qed.
Set Default Proof Mode "Classic".
Definition LOV4 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U_ov4 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LOV4 : fx_explore TBL_P IMG_P 4000 S1 U_ov4 [] = LOV4. Proof. cert_refl_vm constr:(LOV4). Qed.
Set Default Proof Mode "Classic".
Definition Lov5 : sst := Eval vm_compute in nth 0 LOV4 P_main2.
Lemma LOV4_eq : LOV4 = [Lov5]. Proof. reflexivity. Qed.
