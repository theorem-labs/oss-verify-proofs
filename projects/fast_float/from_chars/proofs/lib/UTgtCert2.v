(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFold FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxImg FxEnt FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFold OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib Require UDrvData UDrvMain.
From OSSVerify.Proofs.fast_float.from_chars.lib Require UOpenCert.
From OSSVerify.Proofs.fast_float.from_chars.lib Require UDrvCall UDrvCall2 UDrvExit UDrvSys UDrvHeap UUsageCert UOpenCert ULoopCert ULoopInv UEofCert UTgtCert UTgt3 UTgt4.
Import OSSVerify.Proofs.fast_float.from_chars.lib.UDrvData OSSVerify.Proofs.fast_float.from_chars.lib.UDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.UOpenCert.UDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.UDrvCall OSSVerify.Proofs.fast_float.from_chars.lib.UDrvCall2 OSSVerify.Proofs.fast_float.from_chars.lib.UDrvExit OSSVerify.Proofs.fast_float.from_chars.lib.UDrvSys OSSVerify.Proofs.fast_float.from_chars.lib.UDrvHeap OSSVerify.Proofs.fast_float.from_chars.lib.UUsageCert OSSVerify.Proofs.fast_float.from_chars.lib.UOpenCert OSSVerify.Proofs.fast_float.from_chars.lib.ULoopCert OSSVerify.Proofs.fast_float.from_chars.lib.ULoopInv OSSVerify.Proofs.fast_float.from_chars.lib.UEofCert OSSVerify.Proofs.fast_float.from_chars.lib.UTgtCert OSSVerify.Proofs.fast_float.from_chars.lib.UTgt3 OSSVerify.Proofs.fast_float.from_chars.lib.UTgt4.
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
Definition X1 : sst := Eval vm_compute in nth 0 LSW1 P_main2.
Lemma fr_x1 : fr_tmpl X1 0x22c94 (-208) (lvar OV) FFP1 = true. Proof. vm_compute. reflexivity. Qed.
Definition TL1 : sst := Eval vm_compute in havoc_call X1 0x22c94 KEEPH FFP1 None.
Set Default Proof Mode "Ltac2".
Lemma TL1_eq : havoc_call X1 0x22c94 KEEPH FFP1 None = TL1. Proof. cert_refl_vm constr:(TL1). Qed.
Set Default Proof Mode "Classic".
Definition LTL1 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 TL1 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LTL1 : fx_explore TBL_P IMG_P 4000 S1 TL1 [] = LTL1. Proof. cert_refl_vm constr:(LTL1). Qed.
Set Default Proof Mode "Classic".
Definition B1a : sst := Eval vm_compute in nth 0 LTL1 P_main2.
Definition B1b : sst := Eval vm_compute in nth 1 LTL1 P_main2.
Lemma LTL1_eq : LTL1 = [B1a; B1b]. Proof. reflexivity. Qed.
Lemma tl1_chk : shape (s_rgs TL1) = shape (s_rgs P_main2) /\ cells_tmpl TL1 = true /\ (502 <= s_next TL1)%positive.
Proof. split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | vm_compute; congruence]]. Qed.
Lemma cells_b1a : cells_tmpl B1a = true. Proof. vm_compute. reflexivity. Qed.
Lemma cells_b1b : cells_tmpl B1b = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition BJ1 : sst := Eval vm_compute in SST (s_pc B1a) (rset (s_regs B1a) (rk 11) (lvar (s_next B1a))) (s_rgs B1a) (tl (s_facts B1a)) (s_next B1a + 1) RNone.
Lemma wf_bj1 : state_wf BJ1 = true. Proof. vm_compute. reflexivity. Qed.
Definition sig_b1a : tree lin := Eval vm_compute in match_st B1a BJ1.
Lemma ent_b1a : entails B1a BJ1 sig_b1a = true. Proof. vm_compute. reflexivity. Qed.
Lemma sid_b1a : sig_id_below sig_b1a 502 = true. Proof. vm_compute. reflexivity. Qed.
Definition sig_b1b : tree lin := Eval vm_compute in match_st B1b BJ1.
Lemma ent_b1b : entails B1b BJ1 sig_b1b = true. Proof. vm_compute. reflexivity. Qed.
Lemma sid_b1b : sig_id_below sig_b1b 502 = true. Proof. vm_compute. reflexivity. Qed.
Lemma fr_bj1 : fr_tmpl BJ1 0x22ac8 (-128) (lvar BUF) HFP = true. Proof. vm_compute. reflexivity. Qed.
Definition EX1 : sst := Eval vm_compute in havoc_call BJ1 0x22ac8 KEEPH HFP None.
Set Default Proof Mode "Ltac2".
Lemma EX1_eq : havoc_call BJ1 0x22ac8 KEEPH HFP None = EX1. Proof. cert_refl_vm constr:(EX1). Qed.
Set Default Proof Mode "Classic".
Definition LEX1 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 EX1 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LEX1 : fx_explore TBL_P IMG_P 4000 S1 EX1 [] = LEX1. Proof. cert_refl_vm constr:(LEX1). Qed.
Set Default Proof Mode "Classic".
Definition XL1 : sst := Eval vm_compute in nth 0 LEX1 P_main2.
Lemma LEX1_eq : LEX1 = [XL1]. Proof. reflexivity. Qed.
Lemma ex1_chk : shape (s_rgs EX1) = shape (s_rgs P_main2) /\ (502 <= s_next EX1)%positive.
Proof. split; [vm_compute; reflexivity | vm_compute; congruence]. Qed.

(* [comment removed for export] *)
Definition F2 : sst := Eval vm_compute in nth 1 LSW1 P_main2.
Lemma LSW1_eq : LSW1 = [X1; F2]. Proof. reflexivity. Qed.
Lemma lp1_chk : shape (s_rgs U_sw1) = shape (s_rgs P_main2) /\ cells_tmpl U_sw1 = true /\ cells_tmpl X1 = true /\
  cells_tmpl F2 = true /\ (502 <= s_next U_sw1)%positive.
Proof. split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | vm_compute; congruence]]]]. Qed.
Definition FCx1 : fact := Eval vm_compute in nth 0 (s_facts X1) (FRange (lconst 0) 0 0).
Lemma FCx1_in : In FCx1 (s_facts X1). Proof. vm_compute. tauto. Qed.
Lemma FCx1_eq : FCx1 = FCond BC_NE (LIN 18446744073709551615 [(RV, 1)]) (lconst 0) false. Proof. vm_compute. reflexivity. Qed.
Lemma fz_f2 : fz_tmpl F2 = true. Proof. vm_compute. reflexivity. Qed.
Definition U_z2 : sst := Eval vm_compute in havoc_call F2 0x22c68 KEEPH ZFP (Some (lconst 0)).
Set Default Proof Mode "Ltac2".
Lemma U_z2_eq : havoc_call F2 0x22c68 KEEPH ZFP (Some (lconst 0)) = U_z2. Proof. cert_refl_vm constr:(U_z2). Qed.
Set Default Proof Mode "Classic".
Definition LZ2 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U_z2 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LZ2 : fx_explore TBL_P IMG_P 4000 S1 U_z2 [] = LZ2. Proof. cert_refl_vm constr:(LZ2). Qed.
Set Default Proof Mode "Classic".

(* [comment removed for export] *)
Definition X2 : sst := Eval vm_compute in nth 0 LZ2 P_main2.
Lemma fr_x2 : fr_tmpl X2 0x22c94 (-208) (lvar OV) FFP1 = true. Proof. vm_compute. reflexivity. Qed.
Definition TL2 : sst := Eval vm_compute in havoc_call X2 0x22c94 KEEPH FFP1 None.
Set Default Proof Mode "Ltac2".
Lemma TL2_eq : havoc_call X2 0x22c94 KEEPH FFP1 None = TL2. Proof. cert_refl_vm constr:(TL2). Qed.
Set Default Proof Mode "Classic".
Definition LTL2 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 TL2 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LTL2 : fx_explore TBL_P IMG_P 4000 S1 TL2 [] = LTL2. Proof. cert_refl_vm constr:(LTL2). Qed.
Set Default Proof Mode "Classic".
Definition B2a : sst := Eval vm_compute in nth 0 LTL2 P_main2.
Definition B2b : sst := Eval vm_compute in nth 1 LTL2 P_main2.
Lemma LTL2_eq : LTL2 = [B2a; B2b]. Proof. reflexivity. Qed.
Lemma tl2_chk : shape (s_rgs TL2) = shape (s_rgs P_main2) /\ cells_tmpl TL2 = true /\ (502 <= s_next TL2)%positive.
Proof. split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | vm_compute; congruence]]. Qed.
Lemma cells_b2a : cells_tmpl B2a = true. Proof. vm_compute. reflexivity. Qed.
Lemma cells_b2b : cells_tmpl B2b = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition BJ2 : sst := Eval vm_compute in SST (s_pc B2a) (rset (s_regs B2a) (rk 11) (lvar (s_next B2a))) (s_rgs B2a) (tl (s_facts B2a)) (s_next B2a + 1) RNone.
Lemma wf_bj2 : state_wf BJ2 = true. Proof. vm_compute. reflexivity. Qed.
Definition sig_b2a : tree lin := Eval vm_compute in match_st B2a BJ2.
Lemma ent_b2a : entails B2a BJ2 sig_b2a = true. Proof. vm_compute. reflexivity. Qed.
Lemma sid_b2a : sig_id_below sig_b2a 502 = true. Proof. vm_compute. reflexivity. Qed.
Definition sig_b2b : tree lin := Eval vm_compute in match_st B2b BJ2.
Lemma ent_b2b : entails B2b BJ2 sig_b2b = true. Proof. vm_compute. reflexivity. Qed.
Lemma sid_b2b : sig_id_below sig_b2b 502 = true. Proof. vm_compute. reflexivity. Qed.
Lemma fr_bj2 : fr_tmpl BJ2 0x22ac8 (-128) (lvar BUF) HFP = true. Proof. vm_compute. reflexivity. Qed.
Definition EX2 : sst := Eval vm_compute in havoc_call BJ2 0x22ac8 KEEPH HFP None.
Set Default Proof Mode "Ltac2".
Lemma EX2_eq : havoc_call BJ2 0x22ac8 KEEPH HFP None = EX2. Proof. cert_refl_vm constr:(EX2). Qed.
Set Default Proof Mode "Classic".
Definition LEX2 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 EX2 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LEX2 : fx_explore TBL_P IMG_P 4000 S1 EX2 [] = LEX2. Proof. cert_refl_vm constr:(LEX2). Qed.
Set Default Proof Mode "Classic".
Definition XL2 : sst := Eval vm_compute in nth 0 LEX2 P_main2.
Lemma LEX2_eq : LEX2 = [XL2]. Proof. reflexivity. Qed.
Lemma ex2_chk : shape (s_rgs EX2) = shape (s_rgs P_main2) /\ (502 <= s_next EX2)%positive.
Proof. split; [vm_compute; reflexivity | vm_compute; congruence]. Qed.

(* [comment removed for export] *)
Definition F3 : sst := Eval vm_compute in nth 1 LZ2 P_main2.
Lemma LZ2_eq : LZ2 = [X2; F3]. Proof. reflexivity. Qed.
Lemma lp2_chk : shape (s_rgs U_z2) = shape (s_rgs P_main2) /\ cells_tmpl U_z2 = true /\ cells_tmpl X2 = true /\
  cells_tmpl F3 = true /\ (502 <= s_next U_z2)%positive.
Proof. split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | vm_compute; congruence]]]]. Qed.
Definition FCx2 : fact := Eval vm_compute in nth 0 (s_facts X2) (FRange (lconst 0) 0 0).
Lemma FCx2_in : In FCx2 (s_facts X2). Proof. vm_compute. tauto. Qed.
Lemma FCx2_eq : FCx2 = FCond BC_NE (LIN 18446744073709551614 [(RV, 1)]) (lconst 0) false. Proof. vm_compute. reflexivity. Qed.
Lemma fz_f3 : fz_tmpl F3 = true. Proof. vm_compute. reflexivity. Qed.
Definition U_z3 : sst := Eval vm_compute in havoc_call F3 0x22c68 KEEPH ZFP (Some (lconst 0)).
Set Default Proof Mode "Ltac2".
Lemma U_z3_eq : havoc_call F3 0x22c68 KEEPH ZFP (Some (lconst 0)) = U_z3. Proof. cert_refl_vm constr:(U_z3). Qed.
Set Default Proof Mode "Classic".
Definition LZ3 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U_z3 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LZ3 : fx_explore TBL_P IMG_P 4000 S1 U_z3 [] = LZ3. Proof. cert_refl_vm constr:(LZ3). Qed.
Set Default Proof Mode "Classic".

(* [comment removed for export] *)
Definition X3 : sst := Eval vm_compute in nth 0 LZ3 P_main2.
Lemma fr_x3 : fr_tmpl X3 0x22c94 (-208) (lvar OV) FFP1 = true. Proof. vm_compute. reflexivity. Qed.
Definition TL3 : sst := Eval vm_compute in havoc_call X3 0x22c94 KEEPH FFP1 None.
Set Default Proof Mode "Ltac2".
Lemma TL3_eq : havoc_call X3 0x22c94 KEEPH FFP1 None = TL3. Proof. cert_refl_vm constr:(TL3). Qed.
Set Default Proof Mode "Classic".
Definition LTL3 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 TL3 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LTL3 : fx_explore TBL_P IMG_P 4000 S1 TL3 [] = LTL3. Proof. cert_refl_vm constr:(LTL3). Qed.
Set Default Proof Mode "Classic".
Definition B3a : sst := Eval vm_compute in nth 0 LTL3 P_main2.
Definition B3b : sst := Eval vm_compute in nth 1 LTL3 P_main2.
Lemma LTL3_eq : LTL3 = [B3a; B3b]. Proof. reflexivity. Qed.
Lemma tl3_chk : shape (s_rgs TL3) = shape (s_rgs P_main2) /\ cells_tmpl TL3 = true /\ (502 <= s_next TL3)%positive.
Proof. split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | vm_compute; congruence]]. Qed.
Lemma cells_b3a : cells_tmpl B3a = true. Proof. vm_compute. reflexivity. Qed.
Lemma cells_b3b : cells_tmpl B3b = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition BJ3 : sst := Eval vm_compute in SST (s_pc B3a) (rset (s_regs B3a) (rk 11) (lvar (s_next B3a))) (s_rgs B3a) (tl (s_facts B3a)) (s_next B3a + 1) RNone.
Lemma wf_bj3 : state_wf BJ3 = true. Proof. vm_compute. reflexivity. Qed.
Definition sig_b3a : tree lin := Eval vm_compute in match_st B3a BJ3.
Lemma ent_b3a : entails B3a BJ3 sig_b3a = true. Proof. vm_compute. reflexivity. Qed.
Lemma sid_b3a : sig_id_below sig_b3a 502 = true. Proof. vm_compute. reflexivity. Qed.
Definition sig_b3b : tree lin := Eval vm_compute in match_st B3b BJ3.
Lemma ent_b3b : entails B3b BJ3 sig_b3b = true. Proof. vm_compute. reflexivity. Qed.
Lemma sid_b3b : sig_id_below sig_b3b 502 = true. Proof. vm_compute. reflexivity. Qed.
Lemma fr_bj3 : fr_tmpl BJ3 0x22ac8 (-128) (lvar BUF) HFP = true. Proof. vm_compute. reflexivity. Qed.
Definition EX3 : sst := Eval vm_compute in havoc_call BJ3 0x22ac8 KEEPH HFP None.
Set Default Proof Mode "Ltac2".
Lemma EX3_eq : havoc_call BJ3 0x22ac8 KEEPH HFP None = EX3. Proof. cert_refl_vm constr:(EX3). Qed.
Set Default Proof Mode "Classic".
Definition LEX3 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 EX3 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LEX3 : fx_explore TBL_P IMG_P 4000 S1 EX3 [] = LEX3. Proof. cert_refl_vm constr:(LEX3). Qed.
Set Default Proof Mode "Classic".
Definition XL3 : sst := Eval vm_compute in nth 0 LEX3 P_main2.
Lemma LEX3_eq : LEX3 = [XL3]. Proof. reflexivity. Qed.
Lemma ex3_chk : shape (s_rgs EX3) = shape (s_rgs P_main2) /\ (502 <= s_next EX3)%positive.
Proof. split; [vm_compute; reflexivity | vm_compute; congruence]. Qed.

(* [comment removed for export] *)
Definition F4 : sst := Eval vm_compute in nth 1 LZ3 P_main2.
Lemma LZ3_eq : LZ3 = [X3; F4]. Proof. reflexivity. Qed.
Lemma lp3_chk : shape (s_rgs U_z3) = shape (s_rgs P_main2) /\ cells_tmpl U_z3 = true /\ cells_tmpl X3 = true /\
  cells_tmpl F4 = true /\ (502 <= s_next U_z3)%positive.
Proof. split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | vm_compute; congruence]]]]. Qed.
Definition FCx3 : fact := Eval vm_compute in nth 0 (s_facts X3) (FRange (lconst 0) 0 0).
Lemma FCx3_in : In FCx3 (s_facts X3). Proof. vm_compute. tauto. Qed.
Lemma FCx3_eq : FCx3 = FCond BC_NE (LIN 18446744073709551613 [(RV, 1)]) (lconst 0) false. Proof. vm_compute. reflexivity. Qed.
Lemma fz_f4 : fz_tmpl F4 = true. Proof. vm_compute. reflexivity. Qed.
Definition U_z4 : sst := Eval vm_compute in havoc_call F4 0x22c68 KEEPH ZFP (Some (lconst 0)).
Set Default Proof Mode "Ltac2".
Lemma U_z4_eq : havoc_call F4 0x22c68 KEEPH ZFP (Some (lconst 0)) = U_z4. Proof. cert_refl_vm constr:(U_z4). Qed.
Set Default Proof Mode "Classic".
Definition LZ4 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U_z4 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LZ4 : fx_explore TBL_P IMG_P 4000 S1 U_z4 [] = LZ4. Proof. cert_refl_vm constr:(LZ4). Qed.
Set Default Proof Mode "Classic".

(* [comment removed for export] *)
Definition X4 : sst := Eval vm_compute in nth 0 LZ4 P_main2.
Lemma fr_x4 : fr_tmpl X4 0x22c94 (-208) (lvar OV) FFP1 = true. Proof. vm_compute. reflexivity. Qed.
Definition TL4 : sst := Eval vm_compute in havoc_call X4 0x22c94 KEEPH FFP1 None.
Set Default Proof Mode "Ltac2".
Lemma TL4_eq : havoc_call X4 0x22c94 KEEPH FFP1 None = TL4. Proof. cert_refl_vm constr:(TL4). Qed.
Set Default Proof Mode "Classic".
Definition LTL4 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 TL4 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LTL4 : fx_explore TBL_P IMG_P 4000 S1 TL4 [] = LTL4. Proof. cert_refl_vm constr:(LTL4). Qed.
Set Default Proof Mode "Classic".
Definition B4a : sst := Eval vm_compute in nth 0 LTL4 P_main2.
Definition B4b : sst := Eval vm_compute in nth 1 LTL4 P_main2.
Lemma LTL4_eq : LTL4 = [B4a; B4b]. Proof. reflexivity. Qed.
Lemma tl4_chk : shape (s_rgs TL4) = shape (s_rgs P_main2) /\ cells_tmpl TL4 = true /\ (502 <= s_next TL4)%positive.
Proof. split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | vm_compute; congruence]]. Qed.
Lemma cells_b4a : cells_tmpl B4a = true. Proof. vm_compute. reflexivity. Qed.
Lemma cells_b4b : cells_tmpl B4b = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition BJ4 : sst := Eval vm_compute in SST (s_pc B4a) (rset (s_regs B4a) (rk 11) (lvar (s_next B4a))) (s_rgs B4a) (tl (s_facts B4a)) (s_next B4a + 1) RNone.
Lemma wf_bj4 : state_wf BJ4 = true. Proof. vm_compute. reflexivity. Qed.
Definition sig_b4a : tree lin := Eval vm_compute in match_st B4a BJ4.
Lemma ent_b4a : entails B4a BJ4 sig_b4a = true. Proof. vm_compute. reflexivity. Qed.
Lemma sid_b4a : sig_id_below sig_b4a 502 = true. Proof. vm_compute. reflexivity. Qed.
Definition sig_b4b : tree lin := Eval vm_compute in match_st B4b BJ4.
Lemma ent_b4b : entails B4b BJ4 sig_b4b = true. Proof. vm_compute. reflexivity. Qed.
Lemma sid_b4b : sig_id_below sig_b4b 502 = true. Proof. vm_compute. reflexivity. Qed.
Lemma fr_bj4 : fr_tmpl BJ4 0x22ac8 (-128) (lvar BUF) HFP = true. Proof. vm_compute. reflexivity. Qed.
Definition EX4 : sst := Eval vm_compute in havoc_call BJ4 0x22ac8 KEEPH HFP None.
Set Default Proof Mode "Ltac2".
Lemma EX4_eq : havoc_call BJ4 0x22ac8 KEEPH HFP None = EX4. Proof. cert_refl_vm constr:(EX4). Qed.
Set Default Proof Mode "Classic".
Definition LEX4 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 EX4 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LEX4 : fx_explore TBL_P IMG_P 4000 S1 EX4 [] = LEX4. Proof. cert_refl_vm constr:(LEX4). Qed.
Set Default Proof Mode "Classic".
Definition XL4 : sst := Eval vm_compute in nth 0 LEX4 P_main2.
Lemma LEX4_eq : LEX4 = [XL4]. Proof. reflexivity. Qed.
Lemma ex4_chk : shape (s_rgs EX4) = shape (s_rgs P_main2) /\ (502 <= s_next EX4)%positive.
Proof. split; [vm_compute; reflexivity | vm_compute; congruence]. Qed.

(* [comment removed for export] *)
Lemma LZ4_eq : LZ4 = [X4]. Proof. reflexivity. Qed.
Lemma lp4_chk : shape (s_rgs U_z4) = shape (s_rgs P_main2) /\ cells_tmpl U_z4 = true /\ cells_tmpl X4 = true /\
  (502 <= s_next U_z4)%positive.
Proof. split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | vm_compute; congruence]]]. Qed.
(* [comment removed for export] *)
Definition FCx4_1 : fact := FCond BC_NE (LIN 18446744073709551615 [(RV, 1)]) (lconst 0) true.
Definition FCx4_2 : fact := FCond BC_NE (LIN 18446744073709551614 [(RV, 1)]) (lconst 0) true.
Definition FCx4_3 : fact := FCond BC_NE (LIN 18446744073709551613 [(RV, 1)]) (lconst 0) true.
Lemma fact_in_of_existsb : forall f l, existsb (fact_eqb f) l = true -> In f l.
Proof. intros f l H. apply existsb_exists in H as (g & Hg & Heq). apply fact_eqb_eq in Heq. subst g. exact Hg. Qed.
Lemma FCx4_in : In FCx4_1 (s_facts X4) /\ In FCx4_2 (s_facts X4) /\ In FCx4_3 (s_facts X4).
Proof. split; [|split]; apply fact_in_of_existsb; vm_compute; reflexivity. Qed.

