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
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxImg FxEnt FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib Require UDrvData UDrvMain.
From OSSVerify.Proofs.fast_float.from_chars.lib Require UOpenCert.
From OSSVerify.Proofs.fast_float.from_chars.lib Require UDrvCall UDrvCall2 UDrvExit UDrvSys UDrvHeap UUsageCert UOpenCert.
Import OSSVerify.Proofs.fast_float.from_chars.lib.UDrvData OSSVerify.Proofs.fast_float.from_chars.lib.UDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.UOpenCert.UDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.UDrvCall OSSVerify.Proofs.fast_float.from_chars.lib.UDrvCall2 OSSVerify.Proofs.fast_float.from_chars.lib.UDrvExit OSSVerify.Proofs.fast_float.from_chars.lib.UDrvSys OSSVerify.Proofs.fast_float.from_chars.lib.UDrvHeap OSSVerify.Proofs.fast_float.from_chars.lib.UUsageCert OSSVerify.Proofs.fast_float.from_chars.lib.UOpenCert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 cert_refl_vm (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl _ $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Set Default Proof Mode "Classic".

Definition LOOPPC : Z := 0x22998.
Definition SL1 := LOOPPC :: S1.
Definition SL2 := LOOPPC :: S2.
(* [comment removed for export] *)
Definition HFP : list fpr := [(0%nat, 57216, 8192); (7%nat, 4, 4)].

(* [comment removed for export] *)
Definition LF1 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U_ofd [].
Set Default Proof Mode "Ltac2".
Lemma cert_LF1 : fx_explore TBL_P IMG_P 4000 S1 U_ofd [] = LF1. Proof. cert_refl_vm constr:(LF1). Qed.
Set Default Proof Mode "Classic".
Definition Lf1 : sst := Eval vm_compute in nth 0 LF1 P_main2.
Lemma LF1_eq : LF1 = [Lf1]. Proof. reflexivity. Qed.
Lemma hok_f1 : havoc_ok Lf1 HFP None = true. Proof. vm_compute. reflexivity. Qed.
Definition NXF1 : positive := Eval vm_compute in s_next Lf1.
Definition U_f2 : sst := Eval vm_compute in add_fact (havoc_call Lf1 0x22920 KEEPH HFP None) (FRange (lvar (NXF1 + 10)) 16 140737488355328).
Set Default Proof Mode "Ltac2".
Lemma U_f2_eq : add_fact (havoc_call Lf1 0x22920 KEEPH HFP None) (FRange (lvar (NXF1 + 10)) 16 140737488355328) = U_f2. Proof. cert_refl_vm constr:(U_f2). Qed.
Set Default Proof Mode "Classic".
Definition LF2 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 SL1 U_f2 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LF2 : fx_explore TBL_P IMG_P 4000 SL1 U_f2 [] = LF2. Proof. cert_refl_vm constr:(LF2). Qed.
Set Default Proof Mode "Classic".
Definition Lfirst : sst := Eval vm_compute in nth 0 LF2 P_main2.
Lemma LF2_eq : LF2 = [Lfirst]. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint gen_regs (t : tree lin) (ks : list Z) (nx : positive) : tree lin :=
  match ks with [] => t | k :: ks' => gen_regs (rset t (rk k) (lvar nx)) ks' (Pos.succ nx) end.
(* [comment removed for export] *)
Definition GENK : list Z := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31].
Definition N0 : positive := Eval vm_compute in s_next Lfirst.
Definition C0 : positive := Eval vm_compute in (s_next Lfirst + 1)%positive.
Definition BUF : positive := 242.
Definition LOOPT : sst := Eval vm_compute in
  SST (s_pc Lfirst) (gen_regs (rset (rset (s_regs Lfirst) (rk 19) (lvar N0)) (rk 21) (lvar C0)) GENK (s_next Lfirst + 2))
      (s_rgs Lfirst) (s_facts Lfirst) (s_next Lfirst + 2 + 17) (s_resv Lfirst).
Lemma LOOPT_wf : state_wf LOOPT = true. Proof. vm_compute. reflexivity. Qed.
Definition sig_first : tree lin := Eval vm_compute in match_st Lfirst LOOPT.
Lemma ent_first : entails Lfirst LOOPT sig_first = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition LI := Eval vm_compute in fx_explore TBL_P IMG_P 4000 SL1 LOOPT [].
Set Default Proof Mode "Ltac2".
Lemma cert_LI : fx_explore TBL_P IMG_P 4000 SL1 LOOPT [] = LI. Proof. cert_refl_vm constr:(LI). Qed.
Set Default Proof Mode "Classic".
Definition Lra : sst := Eval vm_compute in nth 0 LI P_main2.
Definition Lrb : sst := Eval vm_compute in nth 1 LI P_main2.
Lemma LI_eq : LI = [Lra; Lrb]. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Definition NXR : positive := Eval vm_compute in s_next Lra.
Definition Lr : sst := Eval vm_compute in
  SST (s_pc Lra) (rset (s_regs Lra) (rk 12) (lvar NXR)) (s_rgs Lra) (s_facts LOOPT) (NXR + 1) (s_resv Lra).
Lemma Lr_wf : state_wf Lr = true. Proof. vm_compute. reflexivity. Qed.
Definition sig_ra : tree lin := Eval vm_compute in match_st Lra Lr.
Definition sig_rb : tree lin := Eval vm_compute in match_st Lrb Lr.
Lemma ent_ra : entails Lra Lr sig_ra = true. Proof. vm_compute. reflexivity. Qed.
Lemma ent_rb : entails Lrb Lr sig_rb = true. Proof. vm_compute. reflexivity. Qed.
Lemma hok_r : havoc_ok Lr [] None = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition NR : positive := Eval vm_compute in (s_next Lr + 10)%positive.
Definition U_r : sst := Eval vm_compute in add_fact (havoc_call Lr 0x60c30 KEEPALL [] None) (FRange (lvar NR) 0 65536).
Set Default Proof Mode "Ltac2".
Lemma U_r_eq : add_fact (havoc_call Lr 0x60c30 KEEPALL [] None) (FRange (lvar NR) 0 65536) = U_r. Proof. cert_refl_vm constr:(U_r). Qed.
Set Default Proof Mode "Classic".
Definition LR := Eval vm_compute in fx_explore TBL_P IMG_P 4000 SL2 U_r [].
Set Default Proof Mode "Ltac2".
Lemma cert_LR : fx_explore TBL_P IMG_P 4000 SL2 U_r [] = LR. Proof. cert_refl_vm constr:(LR). Qed.
Set Default Proof Mode "Classic".
Definition Lc : sst := Eval vm_compute in nth 0 LR P_main2.
Definition Lm : sst := Eval vm_compute in nth 1 LR P_main2.
Lemma LR_eq : LR = [Lc; Lm]. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Definition U_m : sst := Eval vm_compute in havoc_call Lm 0x2294c KEEP [] (Some (rget (s_regs Lm) (rk 10))).
Set Default Proof Mode "Ltac2".
Lemma U_m_eq : havoc_call Lm 0x2294c KEEP [] (Some (rget (s_regs Lm) (rk 10))) = U_m. Proof. cert_refl_vm constr:(U_m). Qed.
Set Default Proof Mode "Classic".
Lemma hok_m : havoc_ok Lm [] (Some (rget (s_regs Lm) (rk 10))) = true. Proof. vm_compute. reflexivity. Qed.
Definition SLG := 0x22960 :: SL1.
Definition LM := Eval vm_compute in fx_explore TBL_P IMG_P 4000 SLG U_m [].
Set Default Proof Mode "Ltac2".
Lemma cert_LM : fx_explore TBL_P IMG_P 4000 SLG U_m [] = LM. Proof. cert_refl_vm constr:(LM). Qed.
Set Default Proof Mode "Classic".
Definition Lh : sst := Eval vm_compute in nth 0 LM P_main2.
Definition Lq : sst := Eval vm_compute in nth 1 LM P_main2.
Lemma LM_eq : LM = [Lh; Lq]. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Definition LENP : lin := LIN 0 [(N0, 1); (NR, 1)].
Definition Lq9 : sst := Eval vm_compute in add_fact Lq (FRange LENP 65536 33554432).
Definition Lq10 : sst := Eval vm_compute in add_fact Lq (FRange LENP 67108864 67108864).
Lemma Lq9_eq : add_fact Lq (FRange LENP 65536 33554432) = Lq9. Proof. vm_compute. reflexivity. Qed.
Lemma Lq10_eq : add_fact Lq (FRange LENP 67108864 67108864) = Lq10. Proof. vm_compute. reflexivity. Qed.
Definition LQ9 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 SLG Lq9 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LQ9 : fx_explore TBL_P IMG_P 4000 SLG Lq9 [] = LQ9. Proof. cert_refl_vm constr:(LQ9). Qed.
Set Default Proof Mode "Classic".
Definition Lg : sst := Eval vm_compute in nth 0 LQ9 P_main2.
Lemma LQ9_eq : LQ9 = [Lg]. Proof. reflexivity. Qed.
Definition LQ10 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 SLG Lq10 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LQ10 : fx_explore TBL_P IMG_P 4000 SLG Lq10 [] = LQ10. Proof. cert_refl_vm constr:(LQ10). Qed.
Set Default Proof Mode "Classic".
Definition Lrf : sst := Eval vm_compute in nth 0 LQ10 P_main2.
Lemma LQ10_eq : LQ10 = [Lrf]. Proof. reflexivity. Qed.
Definition sig_h : tree lin := Eval vm_compute in match_st Lh LOOPT.
Lemma ent_h : entails Lh LOOPT sig_h = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma hok_g : havoc_ok Lg HFP None = true. Proof. vm_compute. reflexivity. Qed.
Definition NXG : positive := Eval vm_compute in s_next Lg.
Definition U_g1 : sst := Eval vm_compute in add_fact (havoc_call Lg 0x22974 KEEPH HFP None) (FRange (lvar (NXG + 10)) 16 140737488355328).
Set Default Proof Mode "Ltac2".
Lemma U_g1_eq : add_fact (havoc_call Lg 0x22974 KEEPH HFP None) (FRange (lvar (NXG + 10)) 16 140737488355328) = U_g1. Proof. cert_refl_vm constr:(U_g1). Qed.
Set Default Proof Mode "Classic".
Definition LG1 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 SL2 U_g1 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LG1 : fx_explore TBL_P IMG_P 4000 SL2 U_g1 [] = LG1. Proof. cert_refl_vm constr:(LG1). Qed.
Set Default Proof Mode "Classic".
Definition Lg1 : sst := Eval vm_compute in nth 0 LG1 P_main2.
Lemma LG1_eq : LG1 = [Lg1]. Proof. reflexivity. Qed.
Definition U_g2 : sst := Eval vm_compute in havoc_call Lg1 0x22990 KEEP [] (Some (rget (s_regs Lg1) (rk 10))).
Set Default Proof Mode "Ltac2".
Lemma U_g2_eq : havoc_call Lg1 0x22990 KEEP [] (Some (rget (s_regs Lg1) (rk 10))) = U_g2. Proof. cert_refl_vm constr:(U_g2). Qed.
Set Default Proof Mode "Classic".
Lemma hok_g1 : havoc_ok Lg1 [] (Some (rget (s_regs Lg1) (rk 10))) = true. Proof. vm_compute. reflexivity. Qed.
Definition LG2 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 SL2 U_g2 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LG2 : fx_explore TBL_P IMG_P 4000 SL2 U_g2 [] = LG2. Proof. cert_refl_vm constr:(LG2). Qed.
Set Default Proof Mode "Classic".
Definition Lg2 : sst := Eval vm_compute in nth 0 LG2 P_main2.
Lemma LG2_eq : LG2 = [Lg2]. Proof. reflexivity. Qed.
Lemma hok_g2 : havoc_ok Lg2 HFP None = true. Proof. vm_compute. reflexivity. Qed.
Definition U_g3 : sst := Eval vm_compute in havoc_call Lg2 0x22998 KEEPH HFP None.
Set Default Proof Mode "Ltac2".
Lemma U_g3_eq : havoc_call Lg2 0x22998 KEEPH HFP None = U_g3. Proof. cert_refl_vm constr:(U_g3). Qed.
Set Default Proof Mode "Classic".
Definition sig_g : tree lin := Eval vm_compute in match_st U_g3 LOOPT.
Lemma ent_g : entails U_g3 LOOPT sig_g = true. Proof. vm_compute. reflexivity. Qed.
