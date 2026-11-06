(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec FxLin FxCore FxSubst FxSound FxMem FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxEnt FxRgs FxFacts FxPlan FxFrame FxWork FxWorkX.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWorkX.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Cells Exec Frame Arr Step Image RegsEquiv MState.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require Import KxBridge KxRun.
From OSSVerify.Proofs.fast_float.from_chars.lib.HX Require Import HxGen.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXB Require Import HxGenFp HxSemB HxBaseB HxIntB HxDefsB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Theorem R_NOFRAC_ok : hand_okx_fp BSEGS xok_spd R_NOFRAC.
Proof.
  apply hx_rule_ok_fp. intros L XL E ms m0 _ _ _ _ _ _. constructor; [|constructor].
  unfold xfact_ok. cbn [xf_tag xf_args List.map xok_spd]. left. rewrite !lden_lconst. split; reflexivity.
Qed.

Theorem R_DIG0_ok : hand_okx_fp BSEGS xok_spd R_DIG0.
Proof.
  apply hx_rule_ok_fp. intros L XL E ms m0 Hpc Hchk Hw Hd HxF Hm0.
  unfold dig0_chk in Hchk. cbn [xs_st xs_x] in Hchk.
  apply andb_prop in Hchk as [Hrg Hfx]. rewrite forallb_app in Hfx. apply andb_prop in Hfx as [Hfx HfS].
  pose proof (txt_bounds E ms L Hd Hfx) as (B1 & B2 & B3 & B4 & B5 & B6).
  destruct (txt_bytes E ms L Hd Hrg Hfx) as (bs & TXT & Hlen).
  destruct (sden_0 _ _ _ _ Hd) as (Hpc0 & Hsvc0 & Hresv0 & HR & HG & HD & HF & Hfrm).
  set (Tz := bv_unsigned (E 1%positive)) in *. set (Lz := bv_unsigned (E 2%positive)) in *.
  set (Xl := rgl L 12) in *. set (Xz := bv_unsigned (lden E Xl)).
  pose proof (bv_unsigned_in_range _ (lden E Xl)) as BX. unfold bv_modulus in BX. change (2 ^ Z.of_N 64) with two64 in BX.
  cbn [forallb] in HfS. apply andb_prop in HfS as [F1 HfS]. apply andb_prop in HfS as [F2 _].
  pose proof (fact_implied_ok E _ _ HF F1) as X1. pose proof (fact_implied_ok E _ _ HF F2) as X2. cbn [fact_ok] in X1, X2.
  rewrite (u_sub E) in X1, X2. unfold TXT_TL, TXT_T, TXT_L in X1, X2. rewrite (u_add E) in X2.
  rewrite !lden_lvar in X1. rewrite !lden_lvar in X2. fold Tz Lz Xz in X1, X2.
  assert (M3 : (Tz + Lz) mod two64 = Tz + Lz) by (apply Z.mod_small; unfold two64 in *; lia).
  rewrite M3 in X2.
  assert (HS : Tz <= Xz <= Tz + Lz) by (clear -X1 X2 BX B1 B2; unfold two64 in *; split; Z.div_mod_to_equations; lia).
  clear X1 X2.
  constructor; [|constructor]. unfold xfact_ok. cbn [xf_tag xf_args List.map xok_spd]. fold Xl Xz.
  exists Tz, bs. split.
  - apply (bytes_at_transport (ms_mem ms)); [exact TXT|]. intros i Hi.
    unfold txt_rgs_ok in Hrg. destruct (s_rgs L) as [|R0 [|R1 rs]] eqn:Hr; try discriminate.
    apply andb_prop in Hrg as [H0 _]. unfold rg_is in H0. apply andb_prop in H0 as [H0 _]. apply andb_prop in H0 as [H0 Hk0].
    apply andb_prop in H0 as [Hb0 Hs0]. apply lin_eqb_eq in Hb0, Hs0. destruct (rg_kind R0) eqn:Hk; cbn in Hk0; try discriminate.
    rewrite <- Hr in Hm0. exact (txt_frame E L ms m0 R0 (R1 :: rs) i Hr Hb0 Hs0 Hk Hm0 ltac:(lia) ltac:(unfold two64 in *; lia)).
  - split; [lia|]. split; [lia|]. apply digs_nil.
Qed.

Theorem R_FRAC_ok : hand_okx_fp BSEGS xok_spd R_FRAC.
Proof.
  apply hx_rule_ok_fp. intros L XL E ms m0 Hpc Hchk Hw Hd HxF Hm0.
  unfold frac_chk in Hchk. cbn [xs_st xs_x] in Hchk.
  apply andb_prop in Hchk as [Hchk Hx0]. apply andb_prop in Hchk as [Hchk Hx2]. apply andb_prop in Hchk as [Hchk Hfx].
  apply andb_prop in Hchk as [Hrg Ha2]. apply lin_eqb_eq in Ha2.
  rewrite forallb_app in Hfx. apply andb_prop in Hfx as [Hfx HfS].
  pose proof (txt_bounds E ms L Hd Hfx) as (B1 & B2 & B3 & B4 & B5 & B6).
  destruct (txt_bytes E ms L Hd Hrg Hfx) as (bs & TXT & Hlen).
  destruct (sden_0 _ _ _ _ Hd) as (Hpc0 & Hsvc0 & Hresv0 & HR & HG & HD & HF & Hfrm).
  set (Tz := bv_unsigned (E 1%positive)) in *. set (Lz := bv_unsigned (E 2%positive)) in *.
  set (IEl := rgl L 10) in *. set (FPl := rgl L 29) in *. set (FEl := rgl L 24) in *.
  set (IEz := bv_unsigned (lden E IEl)). set (FPz := bv_unsigned (lden E FPl)). set (FEz := bv_unsigned (lden E FEl)).
  pose proof (bv_unsigned_in_range _ (lden E IEl)) as BIE. pose proof (bv_unsigned_in_range _ (lden E FPl)) as BFP.
  pose proof (bv_unsigned_in_range _ (lden E FEl)) as BFE.
  unfold bv_modulus in BIE, BFP, BFE. change (2 ^ Z.of_N 64) with two64 in BIE, BFP, BFE.
  cbn [forallb] in HfS.
  repeat match type of HfS with (?a && ?b)%bool = true => apply andb_prop in HfS as [?F HfS] end.
  pose proof (fact_implied_ok E _ _ HF F) as X1. pose proof (fact_implied_ok E _ _ HF F0) as X2.
  pose proof (fact_implied_ok E _ _ HF F1) as X3.
  cbn [fact_ok] in X1, X2, X3. rewrite (u_sub E) in X1, X2, X3. rewrite lden_laddc, u_Z_to_bv in X1.
  unfold TXT_TL, TXT_T, TXT_L in X2, X3. rewrite (u_add E) in X3. rewrite !lden_lvar in X2. rewrite !lden_lvar in X3.
  fold Tz Lz IEz FPz FEz in X1, X2, X3.
  assert (M3 : (Tz + Lz) mod two64 = Tz + Lz) by (apply Z.mod_small; unfold two64 in *; lia).
  rewrite M3 in X3.
  apply existsb_exists in Hx2 as (f2 & Hf2 & Hq2). apply xf_eqb_eq in Hq2. subst f2.
  apply existsb_exists in Hx0 as (f0 & Hf0 & Hq0). apply xf_eqb_eq in Hq0. subst f0.
  rewrite Forall_forall in HxF. pose proof (HxF _ Hf2) as XT. pose proof (HxF _ Hf0) as XD.
  unfold xfact_ok in XT, XD. cbn [xf_tag xf_args List.map xok_spd] in XT, XD. fold IEl FPl FEl in XT, XD. fold IEz FPz FEz in XT, XD.
  destruct XT as (Tt & bst & TXt & Dt1 & Dt2). destruct XD as (Td & bsd & TXd & (Dd1 & Dd1') & Dd2 & DGd).
  assert (HIE : Tz <= IEz <= Tz + 128) by (clear -X2 BIE B2; unfold two64 in *; Z.div_mod_to_equations; lia).
  assert (HFP : FPz = IEz + 1).
  { clear -X1 BIE BFP HIE B2. unfold two64 in *. rewrite (Z.mod_small (IEz + 1)) in X1 by lia. Z.div_mod_to_equations. lia. }
  assert (HS : Tz <= IEz /\ FPz <= FEz /\ FEz <= Tz + Lz) by (clear -X2 X3 Dd1' BIE BFE B1 B2; unfold two64 in *; split; [|split]; try exact Dd1'; Z.div_mod_to_equations; lia).
  assert (TXT0 : bytes_at BSEGS m0 Tz bs).
  { apply (bytes_at_transport (ms_mem ms)); [exact TXT|]. intros i Hi.
    unfold txt_rgs_ok in Hrg. destruct (s_rgs L) as [|R0 [|R1 rs]] eqn:Hr; try discriminate.
    apply andb_prop in Hrg as [H0 _]. unfold rg_is in H0. apply andb_prop in H0 as [H0 _]. apply andb_prop in H0 as [H0 Hk0].
    apply andb_prop in H0 as [Hb0 Hs0]. apply lin_eqb_eq in Hb0, Hs0. destruct (rg_kind R0) eqn:Hk; cbn in Hk0; try discriminate.
    rewrite <- Hr in Hm0. exact (txt_frame E L ms m0 R0 (R1 :: rs) i Hr Hb0 Hs0 Hk Hm0 ltac:(lia) ltac:(unfold two64 in *; lia)). }
  constructor; [|constructor]. unfold xfact_ok. cbn [xf_tag xf_args List.map xok_spd]. fold IEl FPl. fold IEz FPz.
  rewrite Ha2, lden_lsub, bv_sub_unsigned. fold FEl FPl. fold FEz FPz. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
  rewrite (Z.mod_small (FEz - FPz)) by (unfold two64 in *; lia).
  unfold TXT_TL, TXT_T, TXT_L. rewrite lden_ladd, bv_add_unsigned, !lden_lvar. fold Tz Lz. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with two64. rewrite M3.
  unfold spansp. right. split; [exact HFP|]. split; [lia|].
  exists Tz, bs. split; [exact TXT0|]. split; [lia|]. split; [lia|]. split.
  - rewrite (tx_transport m0 Tz bs Tt bst IEz TXT0 TXt ltac:(lia) ltac:(lia)). exact Dt2.
  - replace (IEz + 1 + (FEz - FPz) - Tz) with (FEz - Tz) by lia. replace (IEz + 1 - Tz) with (FPz - Tz) by lia.
    apply (digs_transport m0 Tz bs Td bsd FPz FEz TXT0 TXd); [lia | lia | lia | lia | exact DGd].
Qed.
