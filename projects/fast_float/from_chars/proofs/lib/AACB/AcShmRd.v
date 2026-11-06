(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec AsanAcct FxLin FxCore FxSound FxMem FxStep FxSubst FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_put AXG_np AXG_nf1 AXG_npf.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcPri AcHA.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma outside_or_in : forall E rgs (w : word), outside E rgs w \/
  exists R, In R rgs /\ bv_unsigned (lden E (rg_base R)) <= bv_unsigned w < bv_unsigned (lden E (rg_base R)) + rsz E R.
Proof.
  intros E rgs w. induction rgs as [|R r IH]; [left; constructor|].
  destruct (Z_lt_le_dec (bv_unsigned w) (bv_unsigned (lden E (rg_base R)))) as [H1|H1].
  - destruct IH as [IH|(R' & HR' & Hin)]; [left; constructor; [left; exact H1 | exact IH] | right; exists R'; split; [right; exact HR' | exact Hin]].
  - destruct (Z_lt_le_dec (bv_unsigned w) (bv_unsigned (lden E (rg_base R)) + rsz E R)) as [H2|H2].
    + right. exists R. split; [left; reflexivity | lia].
    + destruct IH as [IH|(R' & HR' & Hin)]; [left; constructor; [right; exact H2 | exact IH] | right; exists R'; split; [right; exact HR' | exact Hin]].
Qed.
(* [comment removed for export] *)
Lemma rg_ok_rd1 : forall E m R i, rg_ok ASEGS E m R -> 0 <= i < rsz E R -> rd1 ASEGS m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) <> None.
Proof.
  intros E m R i (_ & _ & HB & _) Hi. specialize (HB i Hi). destruct (rg_kind R).
  - exact (proj1 HB).
  - destruct HB as [H1 H2]. unfold rd1. rewrite H1. exact H2.
  - exact (proj1 (proj1 HB)).
  - exact (proj1 (proj1 HB)).
  - exact HB.
Qed.

Theorem cls_shadow_readable : forall LIMIT model0 mem0 E S M ms model a, DEN ASEGS LIMIT model0 mem0 E S M ms model -> HA_on E M a mem0 -> a_pri a <> [] ->
  forall c, In c CLS -> 1 <= z_j (pden E a) c ->
  forall x, z_sh (pden E a) + 536870912 * c <= x < z_sh (pden E a) + 536870912 * c + 32768 ->
  rd1 ASEGS (mrestrict (Hof E M model) (ms_mem ms)) (Z_to_bv 64 x) <> None.
Proof.
  intros LIMIT model0 mem0 E S M ms model a Hd HA Hne c Hc Hj x Hx.
  pose proof (ha_pri _ _ _ _ HA Hne) as HP. pose proof (po_inv _ _ _ _ HP) as HI. unfold INV_A in HI.
  assert (Hf : pri_foot E a x) by (unfold pri_foot, pri_foot_z; right; right; right; exists c; split; [exact Hc|]; right; right; left; exact Hx).
  pose proof (pri_foot_rng E a mem0 HI x Hf) as Hx47.
  assert (Hu : bv_unsigned (Z_to_bv 64 x) = x) by (apply u_small64; unfold two64; lia).
  destruct (outside_or_in E (s_rgs S) (Z_to_bv 64 x)) as [Hout|(R & HR & Hin)].
  - destruct (po_own _ _ _ _ HP x ltac:(lia) Hf) as (p & Hp & Hpw).
    destruct (dn_own _ _ _ _ _ _ _ _ _ Hd p Hp x Hpw) as [Hv Hm]. unfold rd1, mrestrict. rewrite Hv, (Hm Hout).
    destruct (iz_cls _ _ HI c Hc) as [(J0 & _)|(_ & _ & _ & _ & HPo)]; [lia|].
    pose proof (pc_shm _ _ _ _ _ _ HPo x ltac:(unfold SHX; exact Hx)) as Hnn. change (Z_to_bv 64 x) with (wa x).
    destruct (mem0 (wa x)); [discriminate | exact (False_ind _ (Hnn eq_refl))].
  - pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & HG & _). rewrite Forall_forall in HG.
    rewrite Hu in Hin. pose proof (rg_ok_rd1 E _ R (x - bv_unsigned (lden E (rg_base R))) (HG R HR) ltac:(lia)) as X.
    replace (bv_unsigned (lden E (rg_base R)) + (x - bv_unsigned (lden E (rg_base R)))) with x in X by ring. exact X.
Qed.
(* [comment removed for export] *)
