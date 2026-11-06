(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxMem FxStep FxSubst FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChAdd FxChStart FxChain FxChDir FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require Import AsanImgScan AsanImg AsanTbl AsanEntry AsanPlan AsanStart AsanFinC AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxDirConv AsanRdErr.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChWv.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxDirConvOwn.

Module AsanRdConv.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxMem FxStep FxSubst FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChAdd FxChStart FxChain FxChDir FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require Import AsanImgScan AsanImg AsanTbl AsanEntry AsanPlan AsanStart AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import FxDirConv AsanRdErr.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition R0 : region := Eval vm_compute in List.hd (RG (lconst 0) (lconst 0) RW TEmpty) (List.filter drop_rand (s_rgs S1)).
Lemma R0_only : List.filter drop_rand (s_rgs S1) = [R0]. Proof. vm_compute. reflexivity. Qed.
Lemma R0_base : rg_base R0 = laddc RANDP16 (-16). Proof. vm_compute. reflexivity. Qed.
Lemma R0_size : rg_size R0 = lconst 16. Proof. vm_compute. reflexivity. Qed.
Definition FRZ : lin * lin := Eval vm_compute in List.nth 1 (sm_frz M1) (lconst 0, lconst 0).
Lemma FRZ_in : In FRZ (sm_frz M1). Proof. vm_compute. right. left. reflexivity. Qed.
Lemma FRZ_size : lin_eqb (snd FRZ) (lsub (laddc RANDP16 (-16)) (fst FRZ)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma own_M1 : sm_own M1 = []. Proof. vm_compute. reflexivity. Qed.
Lemma FSR_wf : forallb (fwf (s_next S1)) FSR = true. Proof. vm_compute. reflexivity. Qed.
Lemma PV_wf : lwf (s_next S1) PV = true. Proof. vm_compute. reflexivity. Qed.
Lemma SZR_wf : lwf (s_next S1) SZR = true. Proof. vm_compute. reflexivity. Qed.
Lemma SR0_next : s_next SR0 = s_next S1.
Proof. unfold SR0. apply conv_post_next. Qed.

(* [comment removed for export] *)
Lemma u_lsub_eq : forall E a b, uE E b + bv_unsigned (lden E (lsub a b)) < two64 ->
  uE E a = uE E b + bv_unsigned (lden E (lsub a b)).
Proof.
  intros E a b H. rewrite lden_lsub, bv_sub_unsigned in *. unfold uE in *.
  pose proof (bv_unsigned_in_range _ (lden E a)) as Ra. pose proof (bv_unsigned_in_range _ (lden E b)) as Rb.
  unfold bv_modulus in *. change (2 ^ Z.of_N 64) with two64 in *. unfold bv_wrap, bv_modulus in *. change (2 ^ Z.of_N 64) with two64 in *.
  set (ua := bv_unsigned (lden E a)) in *. set (ub := bv_unsigned (lden E b)) in *.
  destruct (Z_le_gt_dec ub ua) as [Hle|Hgt].
  - rewrite Z.mod_small by lia. lia.
  - assert (Hm : (ua - ub) mod two64 = ua - ub + two64).
    { replace (ua - ub) with ((ua - ub + two64) + (-1) * two64) at 1 by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
    rewrite Hm in H. lia.
Qed.
Lemma u_laddc_neg : forall E a c, 0 <= c <= uE E a -> uE E (laddc a (- c)) = uE E a - c.
Proof.
  intros E a c H. unfold uE in *. rewrite lden_laddc, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with two64. pose proof (bv_unsigned_in_range _ (lden E a)) as Ra. unfold bv_modulus in Ra.
  change (2 ^ Z.of_N 64) with two64 in Ra. apply Z.mod_small. lia.
Qed.
Lemma u_lconst_small : forall E z, 0 <= z < two64 -> uE E (lconst z) = z.
Proof. intros E z H. unfold uE. rewrite lden_lconst, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. exact H. Qed.

Section Conv.
Variables (model0 : Model) (mem0 : word -> option byte) (E : valu) (ms : machine_state) (model : Model).
Hypothesis Hd : DEN ASEGS LIM model0 mem0 E S1 M1 ms model.
Hypothesis HF : Forall (fact_ok E) FSR.
Hypothesis HP0 : uE E (fst FRZ) <= uE E PV.
Hypothesis HM : forall w, uE E PV <= w < uE E PV + uE E SZR - 16 -> mem0 (Z_to_bv 64 w) <> None.
Hypothesis HB : mem0 (Z_to_bv 64 (uE E PV)) = Some (Z_to_bv 8 46) /\ mem0 (Z_to_bv 64 (uE E PV + 1)) = Some (Z_to_bv 8 0).

#[using="Hd HF HP0 HM HB"] Theorem den_conv_rd : DEN ASEGS LIM model0 mem0 E SR0 MR0 ms model.
Proof. LiaFast.lf_pins (fun (Hd HF HP0 HM HB : LiaFast.U) => LiaFast.u0).
  pose proof HF as HF0. inversion HF0 as [|? ? HARGC HF1]; subst. inversion HF1 as [|? ? HV8 HF2]; subst.
  inversion HF2 as [|? ? HV8SP HF3]; subst. inversion HF3 as [|? ? HRND _]; subst.
  unfold FARGC, FV8, FV8SP, FRND in *. cbn [fact_ok] in HARGC, HV8, HV8SP, HRND. fold (uE E PV) in HV8.
  (* [comment removed for export] *)
  pose proof (dn_sp _ _ _ _ _ _ _ _ _ Hd) as HspE. pose proof (dn_spok _ _ _ _ _ _ _ _ _ Hd) as (_ & Hsphi).
  rewrite HspE in Hsphi. fold (uE E (sm_sp M1)) in Hsphi. unfold sp_window_hi in Hsphi.
  assert (Hsp : uE E PV = uE E (sm_sp M1) + bv_unsigned (lden E (lsub PV (sm_sp M1)))) by (apply u_lsub_eq; unfold two64; lia).
  fold (uE E SZR) in HRND.
  assert (Hrp : uE E RANDP16 = uE E PV + uE E SZR).
  { pose proof (u_lsub_eq E RANDP16 PV) as H1. change (lsub RANDP16 PV) with SZR in H1. fold (uE E SZR) in H1. apply H1. unfold two64. lia. }
  assert (Hb0 : uE E (rg_base R0) = uE E RANDP16 - 16) by (rewrite R0_base; apply (u_laddc_neg E RANDP16 16); lia).
  assert (Hs0 : rsz E R0 = 16) by (unfold rsz; rewrite R0_size; fold (uE E (lconst 16)); apply u_lconst_small; unfold two64; lia).
  assert (Hfz : uE E (snd FRZ) = uE E (rg_base R0) - uE E (fst FRZ)).
  { rewrite (lin_eqb_eq _ _ FRZ_size). rewrite <- R0_base.
    assert (Rb : uE E (rg_base R0) < two64).
    { unfold uE. pose proof (bv_unsigned_in_range _ (lden E (rg_base R0))) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with two64 in R. lia. }
    assert (Rf : 0 <= uE E (fst FRZ)) by (unfold uE; pose proof (bv_unsigned_in_range _ (lden E (fst FRZ))) as R; lia).
    unfold uE at 1. rewrite lden_lsub, bv_sub_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
    fold (uE E (rg_base R0)). fold (uE E (fst FRZ)). apply Z.mod_small. lia. }
  unfold SR0, MR0.
  apply (den_conv_rt ASEGS LIM model0 mem0 E S1 M1 ms model drop_rand R0 FSR PV SZR [46; 0] Hd own_M1).
  - assert (H : In R0 (List.filter drop_rand (s_rgs S1))) by (rewrite R0_only; left; reflexivity). apply filter_In in H. exact (proj1 H).
  - vm_compute. reflexivity.
  - intros R HR Hf w Hw.
    assert (H : In R (List.filter drop_rand (s_rgs S1))) by (apply filter_In; split; assumption). rewrite R0_only in H.
    destruct H as [<-|[]]. unfold in_shadow, SH_LO, SH_HI. apply andb_false_iff. right. apply Z.ltb_ge. lia.
  - pose proof FSR_wf as Hw. rewrite forallb_forall in Hw. apply Forall_forall. intros g Hg. split; [exact (Hw g Hg)|].
    rewrite Forall_forall in HF. exact (HF g Hg).
  - exact PV_wf.
  - exact SZR_wf.
  - lia.
  - cbn [length]. lia.
  - repeat constructor; lia.
  - lia.
  - intros w Hw. destruct (Z_lt_le_dec w (uE E (rg_base R0))) as [Hlt|Hge].
    + left. exists FRZ. split; [exact FRZ_in|]. split; [lia|]. apply HM. lia.
    + right. lia.
  - intros k Hk. cbn [length] in Hk. split.
    + exists FRZ. split; [exact FRZ_in|]. lia.
    + destruct k as [|[|k]]; [| |lia].
      * replace (uE E PV + Z.of_nat 0) with (uE E PV) by lia. exact (proj1 HB).
      * replace (uE E PV + Z.of_nat 1) with (uE E PV + 1) by lia. exact (proj2 HB).
Qed.
End Conv.

(* [comment removed for export] *)
Lemma INV_conv_rd : forall path0 fs0 mem0 E S S' M M' FS model0, s_next S' = s_next S ->
  INV PV path0 [] fs0 true None mem0 E S M FS model0 -> INV PV path0 [] fs0 true None mem0 E S' M' FS model0.
Proof.
  intros path0 fs0 mem0 E S S' M M' FS model0 Hn Hi.
  destruct Hi as (H1 & H2 & _ & _ & H5 & _ & H7 & H8 & H9 & H10 & _).
  unfold INV. rewrite Hn. split; [exact H1|]. split; [exact H2|].
  split; [intros Hc; discriminate Hc|]. split; [split; intros Hc; discriminate Hc|]. split; [exact H5|].      (* [comment removed for export] *)
  split; [intros Hc; discriminate Hc|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|].
  unfold hv_inv. exact I.
Qed.
(* [comment removed for export] *)
End AsanRdConv.

From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxSFam AsanUsageT AsanRdErrT.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxDirConv OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanRdErr OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChWv.FxDropOwn OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxDirConvOwn OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanRdConvT.AsanRdConv OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxSFam OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanUsageT OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanRdErrT.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition R0T : region := Eval vm_compute in List.hd (RG (lconst 0) (lconst 0) RW TEmpty) (List.filter drop_rand (s_rgs TMAIN)).
Lemma R0_onlyT : List.filter drop_rand (s_rgs TMAIN) = [R0T]. Proof. vm_compute. reflexivity. Qed.
Lemma R0_baseT : rg_base R0T = laddc RANDP16 (-16). Proof. vm_compute. reflexivity. Qed.
Lemma R0_sizeT : rg_size R0T = lconst 16. Proof. vm_compute. reflexivity. Qed.
Definition FRZT : lin * lin := Eval vm_compute in List.nth 1 (sm_frz MMAIN) (lconst 0, lconst 0).
Lemma FRZ_inT : In FRZT (sm_frz MMAIN). Proof. vm_compute. right. left. reflexivity. Qed.
Lemma FRZ_sizeT : lin_eqb (snd FRZT) (lsub (laddc RANDP16 (-16)) (fst FRZT)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma drop_chkT : drop_own_ok TMAIN MMAIN drop_rand = true. Proof. vm_compute. reflexivity. Qed.
Lemma FSR_wfT : forallb (fwf (s_next TMAIN)) FSRT = true. Proof. vm_compute. reflexivity. Qed.
Lemma PV_wfT : lwf (s_next TMAIN) PV = true. Proof. vm_compute. reflexivity. Qed.
Lemma SZR_wfT : lwf (s_next TMAIN) SZR = true. Proof. vm_compute. reflexivity. Qed.
Lemma SRT_next : s_next SRT = s_next TMAIN.
Proof. unfold SRT. apply conv_post_next. Qed.

Section ConvT.
Variables (model0 : Model) (mem0 : word -> option byte) (E : valu) (ms : machine_state) (model : Model).
Hypothesis Hd : DEN ASEGS LIM model0 mem0 E TMAIN MMAIN ms model.
Hypothesis HF : Forall (fact_ok E) FSRT.
Hypothesis HP0 : uE E (fst FRZT) <= uE E PV.
Hypothesis HM : forall w, uE E PV <= w < uE E PV + uE E SZR - 16 -> mem0 (Z_to_bv 64 w) <> None.
Hypothesis HB : mem0 (Z_to_bv 64 (uE E PV)) = Some (Z_to_bv 8 46) /\ mem0 (Z_to_bv 64 (uE E PV + 1)) = Some (Z_to_bv 8 0).

#[using="Hd HF HP0 HM HB"] Theorem den_conv_rdT : DEN ASEGS LIM model0 mem0 E SRT MRT ms model.
Proof. LiaFast.lf_pins (fun (Hd HF HP0 HM HB : LiaFast.U) => LiaFast.u0).
  pose proof HF as HF0. inversion HF0 as [|? ? HARGC HF1]; subst. inversion HF1 as [|? ? HV8 HF2]; subst.
  inversion HF2 as [|? ? HV8SP HF3]; subst. inversion HF3 as [|? ? HRND _]; subst.
  unfold FARGC, FV8, FV8SPT, FRND in *. cbn [fact_ok] in HARGC, HV8, HV8SP, HRND. fold (uE E PV) in HV8.
  (* [comment removed for export] *)
  pose proof (dn_sp _ _ _ _ _ _ _ _ _ Hd) as HspE. pose proof (dn_spok _ _ _ _ _ _ _ _ _ Hd) as (_ & Hsphi).
  rewrite HspE in Hsphi. fold (uE E (sm_sp MMAIN)) in Hsphi. unfold sp_window_hi in Hsphi.
  assert (Hsp : uE E PV = uE E (sm_sp MMAIN) + bv_unsigned (lden E (lsub PV (sm_sp MMAIN)))) by (apply u_lsub_eq; unfold two64; lia).
  fold (uE E SZR) in HRND.
  assert (Hrp : uE E RANDP16 = uE E PV + uE E SZR).
  { pose proof (u_lsub_eq E RANDP16 PV) as H1. change (lsub RANDP16 PV) with SZR in H1. fold (uE E SZR) in H1. apply H1. unfold two64. lia. }
  assert (Hb0 : uE E (rg_base R0T) = uE E RANDP16 - 16) by (rewrite R0_baseT; apply (u_laddc_neg E RANDP16 16); lia).
  assert (Hs0 : rsz E R0T = 16) by (unfold rsz; rewrite R0_sizeT; fold (uE E (lconst 16)); apply u_lconst_small; unfold two64; lia).
  assert (Hfz : uE E (snd FRZT) = uE E (rg_base R0T) - uE E (fst FRZT)).
  { rewrite (lin_eqb_eq _ _ FRZ_sizeT). rewrite <- R0_baseT.
    assert (Rb : uE E (rg_base R0T) < two64).
    { unfold uE. pose proof (bv_unsigned_in_range _ (lden E (rg_base R0T))) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with two64 in R. lia. }
    assert (Rf : 0 <= uE E (fst FRZT)) by (unfold uE; pose proof (bv_unsigned_in_range _ (lden E (fst FRZT))) as R; lia).
    unfold uE at 1. rewrite lden_lsub, bv_sub_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
    fold (uE E (rg_base R0T)). fold (uE E (fst FRZT)). apply Z.mod_small. lia. }
  unfold SRT, MRT.
  apply (den_conv_rt_own ASEGS LIM model0 mem0 E TMAIN MMAIN ms model drop_rand R0T FSRT PV SZR [46; 0] Hd drop_chkT).
  - assert (H : In R0T (List.filter drop_rand (s_rgs TMAIN))) by (rewrite R0_onlyT; left; reflexivity). apply filter_In in H. exact (proj1 H).
  - vm_compute. reflexivity.
  - intros R HR Hf w Hw.
    assert (H : In R (List.filter drop_rand (s_rgs TMAIN))) by (apply filter_In; split; assumption). rewrite R0_onlyT in H.
    destruct H as [<-|[]]. unfold in_shadow, SH_LO, SH_HI. apply andb_false_iff. right. apply Z.ltb_ge. lia.
  - pose proof FSR_wfT as Hw. rewrite forallb_forall in Hw. apply Forall_forall. intros g Hg. split; [exact (Hw g Hg)|].
    rewrite Forall_forall in HF. exact (HF g Hg).
  - exact PV_wfT.
  - exact SZR_wfT.
  - lia.
  - cbn [length]. lia.
  - repeat constructor; lia.
  - lia.
  - intros w Hw. destruct (Z_lt_le_dec w (uE E (rg_base R0T))) as [Hlt|Hge].
    + left. exists FRZT. split; [exact FRZ_inT|]. split; [lia|]. apply HM. lia.
    + right. lia.
  - intros k Hk. cbn [length] in Hk. split.
    + exists FRZT. split; [exact FRZ_inT|]. lia.
    + destruct k as [|[|k]]; [| |lia].
      * replace (uE E PV + Z.of_nat 0) with (uE E PV) by lia. exact (proj1 HB).
      * replace (uE E PV + Z.of_nat 1) with (uE E PV + 1) by lia. exact (proj2 HB).
Qed.
End ConvT.
(* [comment removed for export] *)
