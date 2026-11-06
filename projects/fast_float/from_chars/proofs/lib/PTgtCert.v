(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFold FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxImg FxEnt FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFold OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvData PDrvMain.
From OSSVerify.Proofs.fast_float.from_chars.lib Require POpenCert.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvCall PDrvCall2 PDrvExit PDrvSys PDrvHeap PUsageCert POpenCert PLoopCert PEofCert.
Import OSSVerify.Proofs.fast_float.from_chars.lib.PDrvData OSSVerify.Proofs.fast_float.from_chars.lib.PDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert.PDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvCall OSSVerify.Proofs.fast_float.from_chars.lib.PDrvCall2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvExit OSSVerify.Proofs.fast_float.from_chars.lib.PDrvSys OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeap OSSVerify.Proofs.fast_float.from_chars.lib.PUsageCert OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert OSSVerify.Proofs.fast_float.from_chars.lib.PLoopCert OSSVerify.Proofs.fast_float.from_chars.lib.PEofCert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 cert_refl_vm (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl _ $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Set Default Proof Mode "Classic".

Definition STG : list Z := 0x22964 :: 0x229b0 :: S1.

(* [comment removed for export] *)
Definition sig_id_below (σ : tree lin) (n : positive) : bool :=
  tforall (fun x l => if Pos.ltb x n then lin_eqb l (lvar x) else true) σ.
Lemma ecomp_agree : forall E σ n, sig_id_below σ n = true -> agree n E (ecomp E σ).
Proof.
  intros E σ n H x Hx. unfold ecomp, svar. destruct (tget x σ) as [l|] eqn:Hl; [|rewrite lden_lvar; reflexivity].
  pose proof (tforall_spec _ _ H x l Hl) as X. cbv beta in X. rewrite (proj2 (Pos.ltb_lt x n) Hx) in X.
  apply lin_eqb_eq in X. subst l. rewrite lden_lvar. reflexivity.
Qed.
Lemma ecomp_at : forall E σ x l, svar σ x = l -> ecomp E σ x = lden E l.
Proof. intros E σ x l H. unfold ecomp. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Definition STGL : list Z := 0x5eb5c :: STG.
Definition LT0 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 STGL Ltr [].
Set Default Proof Mode "Ltac2".
Lemma cert_LT0 : fx_explore TBL_P IMG_P 4000 STGL Ltr [] = LT0. Proof. cert_refl_vm constr:(LT0). Qed.
Set Default Proof Mode "Classic".
Definition Llk : sst := Eval vm_compute in nth 0 LT0 P_main2.
Lemma LT0_eq : LT0 = [Llk]. Proof. reflexivity. Qed.
Lemma hok_lk : havoc_ok Llk [] None = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition U_lk : sst := Eval vm_compute in havoc_call Llk 0x50d40 KEEPN [] None.
Set Default Proof Mode "Ltac2".
Lemma U_lk_eq : havoc_call Llk 0x50d40 KEEPN [] None = U_lk. Proof. cert_refl_vm constr:(U_lk). Qed.
Set Default Proof Mode "Classic".
Lemma wf_lk : state_wf U_lk = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition LT1 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 STG U_lk [].
Set Default Proof Mode "Ltac2".
Lemma cert_LT1 : fx_explore TBL_P IMG_P 4000 STG U_lk [] = LT1. Proof. cert_refl_vm constr:(LT1). Qed.
Set Default Proof Mode "Classic".
Definition Lcf : sst := Eval vm_compute in nth 0 LT1 P_main2.
Definition J0a : sst := Eval vm_compute in nth 1 LT1 P_main2.
Definition J1a : sst := Eval vm_compute in nth 2 LT1 P_main2.
Lemma LT1_eq : LT1 = [Lcf; J0a; J1a]. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition JV : positive := Eval vm_compute in s_next Lcf.
Definition HV : positive := Eval vm_compute in (s_next Lcf + 1)%positive.
Definition CFGR : region := RGz (laddc (lvar BUF) 2) 1 RW (put_bytes TEmpty 0 [BV (LIN 0 [(JV, 1); (HV, 4)]) 0]).
Definition U_cf : sst := Eval vm_compute in
  add_rg (add_fact (add_fact (add_var (add_var Lcf)) (FRange (lvar JV) 0 3)) (FRange (lvar HV) 0 63)) CFGR.
Lemma U_cf_eq : add_rg (add_fact (add_fact (add_var (add_var Lcf)) (FRange (lvar JV) 0 3)) (FRange (lvar HV) 0 63)) CFGR = U_cf.
Proof. vm_compute. reflexivity. Qed.
Lemma wf_cf : state_wf U_cf = true. Proof. vm_compute. reflexivity. Qed.
Definition LCF := Eval vm_compute in fx_explore TBL_P IMG_P 4000 STG U_cf [].
Set Default Proof Mode "Ltac2".
Lemma cert_LCF : fx_explore TBL_P IMG_P 4000 STG U_cf [] = LCF. Proof. cert_refl_vm constr:(LCF). Qed.
Set Default Proof Mode "Classic".
Definition J1b0 : sst := Eval vm_compute in nth 0 LCF P_main2.
Definition J0b0 : sst := Eval vm_compute in nth 1 LCF P_main2.
Lemma LCF_eq : LCF = [J1b0; J0b0]. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Definition J1b : sst := Eval vm_compute in with_rgs J1b0 (firstn 22 (s_rgs J1b0)).
Definition J0b : sst := Eval vm_compute in with_rgs J0b0 (firstn 22 (s_rgs J0b0)).
Lemma J1b_eq : with_rgs J1b0 (firstn 22 (s_rgs J1b0)) = J1b. Proof. vm_compute. reflexivity. Qed.
Lemma J0b_eq : with_rgs J0b0 (firstn 22 (s_rgs J0b0)) = J0b. Proof. vm_compute. reflexivity. Qed.
Lemma wk_j1b : weaken_ok (s_rgs J1b0) (firstn 22 (s_rgs J1b0)) WS21 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wk_j0b : weaken_ok (s_rgs J0b0) (firstn 22 (s_rgs J0b0)) WS21 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wf_j1b : state_wf J1b = true. Proof. vm_compute. reflexivity. Qed.
Lemma wf_j0b : state_wf J0b = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition RV : positive := 400.
Definition GENKT : list Z := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31].
Definition J1 : sst := Eval vm_compute in
  SST 0x22964 (gen_regs (rset (s_regs J1a) (rk 21) (lvar RV)) GENKT 401) (s_rgs J1a) (FRange (lvar RV) 1 4 :: s_facts P_main2) 420 RNone.
Definition J0 : sst := Eval vm_compute in
  SST 0x229b0 (gen_regs (rset (s_regs J0a) (rk 21) (lvar RV)) GENKT 401) (s_rgs J0a) (FRange (lvar RV) 1 4 :: s_facts P_main2) 420 RNone.
Lemma wf_j1 : state_wf J1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wf_j0 : state_wf J0 = true. Proof. vm_compute. reflexivity. Qed.
Definition sig_j1a : tree lin := Eval vm_compute in match_st J1a J1.
Definition sig_j1b : tree lin := Eval vm_compute in match_st J1b J1.
Definition sig_j0a : tree lin := Eval vm_compute in match_st J0a J0.
Definition sig_j0b : tree lin := Eval vm_compute in match_st J0b J0.
Lemma ent_j1a : entails J1a J1 sig_j1a = true. Proof. vm_compute. reflexivity. Qed.
Lemma ent_j1b : entails J1b J1 sig_j1b = true. Proof. vm_compute. reflexivity. Qed.
Lemma ent_j0a : entails J0a J0 sig_j0a = true. Proof. vm_compute. reflexivity. Qed.
Lemma ent_j0b : entails J0b J0 sig_j0b = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition LJ0 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 J0 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LJ0 : fx_explore TBL_P IMG_P 4000 S1 J0 [] = LJ0. Proof. cert_refl_vm constr:(LJ0). Qed.
Set Default Proof Mode "Classic".
(* [comment removed for export] *)
Definition LJ1 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 J1 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LJ1 : fx_explore TBL_P IMG_P 4000 S1 J1 [] = LJ1. Proof. cert_refl_vm constr:(LJ1). Qed.
Set Default Proof Mode "Classic".
Definition F0 : sst := Eval vm_compute in nth 0 LJ0 P_main2.
Lemma LJ0_eq : LJ0 = [F0]. Proof. reflexivity. Qed.
Definition Lm : sst := Eval vm_compute in nth 0 LJ1 P_main2.
Lemma LJ1_eq : LJ1 = [Lm]. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition MFP : list fpr := [(0%nat, 57136, 8192); (7%nat, 4, 4)].
Lemma hok_m : havoc_ok Lm MFP None = true. Proof. vm_compute. reflexivity. Qed.
Definition PV : positive := Eval vm_compute in (s_next Lm + 10)%positive.
Definition U_m : sst := Eval vm_compute in add_fact (havoc_call Lm 0x2296c KEEPH MFP None) (FRange (lvar PV) 16 140737488355328).
Set Default Proof Mode "Ltac2".
Lemma U_m_eq : add_fact (havoc_call Lm 0x2296c KEEPH MFP None) (FRange (lvar PV) 16 140737488355328) = U_m. Proof. cert_refl_vm constr:(U_m). Qed.
Set Default Proof Mode "Classic".
Definition LM1 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S2 U_m [].
Set Default Proof Mode "Ltac2".
Lemma cert_LM1 : fx_explore TBL_P IMG_P 4000 S2 U_m [] = LM1. Proof. cert_refl_vm constr:(LM1). Qed.
Set Default Proof Mode "Classic".
Definition INFO (L : sst) := (s_pc L, RET L, rget (s_regs L) (rk 2), rget (s_regs L) (rk 10), rget (s_regs L) (rk 11), rget (s_regs L) (rk 12), s_next L).
Definition Lmc : sst := Eval vm_compute in nth 0 LM1 P_main2.
Lemma LM1_eq : LM1 = [Lmc]. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma hok_mc : havoc_ok Lmc [] (Some (lvar PV)) = true. Proof. vm_compute. reflexivity. Qed.
Definition U_mc : sst := Eval vm_compute in havoc_call Lmc 0x22980 KEEP [] (Some (lvar PV)).
Set Default Proof Mode "Ltac2".
Lemma U_mc_eq : havoc_call Lmc 0x22980 KEEP [] (Some (lvar PV)) = U_mc. Proof. cert_refl_vm constr:(U_mc). Qed.
Set Default Proof Mode "Classic".
Definition LM2 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S2 U_mc [].
Set Default Proof Mode "Ltac2".
Lemma cert_LM2 : fx_explore TBL_P IMG_P 4000 S2 U_mc [] = LM2. Proof. cert_refl_vm constr:(LM2). Qed.
Set Default Proof Mode "Classic".
Definition Fm : sst := Eval vm_compute in nth 0 LM2 P_main2.
Lemma LM2_eq : LM2 = [Fm]. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition rg_meet (R1 R2 : region) : region :=
  match rg_kind R1 with
  | RW => RG (rg_base R1) (rg_size R1) RW
            (tfilter (fun p => match tget p (rg_cont R1), tget p (rg_cont R2) with Some v, Some v' => bval_eqb v v' | _, _ => false end) (rg_cont R1))
  | _ => R1
  end.
Definition rgs_meet (r1 r2 : list region) : list region := List.map (fun '(R1, R2) => rg_meet R1 R2) (List.combine r1 r2).
Definition AV : positive := 500.
Definition OV : positive := 501.
Definition GENKF : list Z := [5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31].
Definition G0 : sst := Eval vm_compute in
  SST 0x22b18 (gen_regs (rset (rset (rset (s_regs F0) (rk 9) (lvar AV)) (rk 10) (lvar AV)) (rk 18) (lvar OV)) GENKF 502)
      (rgs_meet (s_rgs F0) (s_rgs Fm)) (FRange (lvar RV) 1 4 :: s_facts P_main2) 520 RNone.
Lemma wf_g0 : state_wf G0 = true. Proof. vm_compute. reflexivity. Qed.
Definition sig_f0 : tree lin := Eval vm_compute in match_st F0 G0.
Definition sig_fm : tree lin := Eval vm_compute in match_st Fm G0.
Lemma ent_f0 : entails F0 G0 sig_f0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma sid_j0a : sig_id_below sig_j0a 390 = true. Proof. vm_compute. reflexivity. Qed.
Lemma sid_j1a : sig_id_below sig_j1a 390 = true. Proof. vm_compute. reflexivity. Qed.
Lemma sid_j0b : sig_id_below sig_j0b 390 = true. Proof. vm_compute. reflexivity. Qed.
Lemma sid_j1b : sig_id_below sig_j1b 390 = true. Proof. vm_compute. reflexivity. Qed.
Lemma sid_f0 : sig_id_below sig_f0 420 = true. Proof. vm_compute. reflexivity. Qed.
Lemma sid_fm : sig_id_below sig_fm 420 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ent_fm : entails Fm G0 sig_fm = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition ZFP : list fpr := [(0%nat, 56832, 8496); (7%nat, 4, 4)].
Lemma hok_z1 : havoc_ok G0 ZFP (Some (lconst 0)) = true. Proof. vm_compute. reflexivity. Qed.
Definition U_z1 : sst := Eval vm_compute in havoc_call G0 0x229d4 KEEPH ZFP (Some (lconst 0)).
Set Default Proof Mode "Ltac2".
Lemma U_z1_eq : havoc_call G0 0x229d4 KEEPH ZFP (Some (lconst 0)) = U_z1. Proof. cert_refl_vm constr:(U_z1). Qed.
Set Default Proof Mode "Classic".
Definition LZ1 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U_z1 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LZ1 : fx_explore TBL_P IMG_P 4000 S1 U_z1 [] = LZ1. Proof. cert_refl_vm constr:(LZ1). Qed.
Set Default Proof Mode "Classic".
Definition Lio1 : sst := Eval vm_compute in nth 0 LZ1 P_main2.
Lemma LZ1_eq : LZ1 = [Lio1]. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma hok_io1 : havoc_ok Lio1 [] (Some (lconst 18446744073709551591)) = true. Proof. vm_compute. reflexivity. Qed.
Definition U_io1 : sst := Eval vm_compute in havoc_call Lio1 0x54248 KEEPALL [] (Some (lconst 18446744073709551591)).
Set Default Proof Mode "Ltac2".
Lemma U_io1_eq : havoc_call Lio1 0x54248 KEEPALL [] (Some (lconst 18446744073709551591)) = U_io1. Proof. cert_refl_vm constr:(U_io1). Qed.
Set Default Proof Mode "Classic".
Definition LIO1 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U_io1 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LIO1 : fx_explore TBL_P IMG_P 4000 S1 U_io1 [] = LIO1. Proof. cert_refl_vm constr:(LIO1). Qed.
Set Default Proof Mode "Classic".
Definition Lsw1 : sst := Eval vm_compute in nth 0 LIO1 P_main2.
Lemma LIO1_eq : LIO1 = [Lsw1]. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Definition SWFP1 : list fpr := [(0%nat, 64128, 112); (6%nat, 32, 16); (6%nat, 56, 8)].
Lemma hok_sw1 : havoc_ok Lsw1 SWFP1 (Some (lconst 1)) = true. Proof. vm_compute. reflexivity. Qed.
Definition U_sw1 : sst := Eval vm_compute in sw_template Lsw1 0x54268 0 64128 6 (lconst 0x962a8) (lconst 1024) (lconst 1).
Set Default Proof Mode "Ltac2".
Lemma U_sw1_eq : sw_template Lsw1 0x54268 0 64128 6 (lconst 0x962a8) (lconst 1024) (lconst 1) = U_sw1. Proof. cert_refl_vm constr:(U_sw1). Qed.
Set Default Proof Mode "Classic".
Lemma wf_sw1 : state_wf U_sw1 = true. Proof. vm_compute. reflexivity. Qed.
Definition LSW1 := Eval vm_compute in fx_explore TBL_P IMG_P 4000 S1 U_sw1 [].
Set Default Proof Mode "Ltac2".
Lemma cert_LSW1 : fx_explore TBL_P IMG_P 4000 S1 U_sw1 [] = LSW1. Proof. cert_refl_vm constr:(LSW1). Qed.
Set Default Proof Mode "Classic".
