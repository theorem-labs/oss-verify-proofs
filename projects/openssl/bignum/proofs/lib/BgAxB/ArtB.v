(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From OSSVerify.Proofs.openssl.bignum.lib.AS Require Import AsanAcct.
From OSSVerify.Proofs.openssl.bignum.lib.Common Require Import RegEqv.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Mem Frame. 
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require RzCPS.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Stdio.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout RT_iface RT_state RT_main_shape RT_rep R_depot_defs R_glue_defs RT_main RT_main_clx D_defs D_libiface I_iodefs X_xdefs.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import FastWord.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import ExTrie AxLazy AxLin AxVal AxMem AxZZ AxState AxSys AxLz AxEntryS AxFd AxModelRel.
From OSSVerify.Proofs.openssl.bignum.lib.BgAxBdB Require Import BdBParams.
From OSSVerify.Proofs.openssl.bignum.lib.AxA Require Import AxExport AxExportH AxExportV AxExportI FinMain1 FinMain2.
From OSSVerify.Proofs.openssl.bignum.lib.BgAxB Require Import AxExportS AxExportF AxExportL AxExportT AxExportP FinMain3 BridgeB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Definition BK_C0 : list Z := Eval vm_compute in (map (fun tr => bkt (depot_hash tr)) (firstn 4000 (skipn 0 T_MAIN))).
Definition BK_C1 : list Z := Eval vm_compute in (map (fun tr => bkt (depot_hash tr)) (firstn 4000 (skipn 4000 T_MAIN))).
Definition BK_C2 : list Z := Eval vm_compute in (map (fun tr => bkt (depot_hash tr)) (firstn 4000 (skipn 8000 T_MAIN))).
Definition BK_C3 : list Z := Eval vm_compute in (map (fun tr => bkt (depot_hash tr)) (firstn 4000 (skipn 12000 T_MAIN))).
Definition BK_C4 : list Z := Eval vm_compute in (map (fun tr => bkt (depot_hash tr)) (firstn 4000 (skipn 16000 T_MAIN))).
Definition BK_C5 : list Z := Eval vm_compute in (map (fun tr => bkt (depot_hash tr)) (firstn 4000 (skipn 20000 T_MAIN))).
Definition BK_C6 : list Z := Eval vm_compute in (map (fun tr => bkt (depot_hash tr)) (skipn 24000 T_MAIN)).
Definition BK_TAIL : list Z := BK_C0 ++ BK_C1 ++ BK_C2 ++ BK_C3 ++ BK_C4 ++ BK_C5 ++ BK_C6.

Lemma DEP_BK_eq (h1 : Z) : DEP_BK h1 = bkt h1 :: BK_TAIL.
Proof.
  unfold DEP_BK. apply (f_equal (cons (bkt h1))).

  vm_cast_no_check (eq_refl BK_TAIL).
Qed.

Definition h1_of (F : bforms) (B : AST) : Z :=
  match ld_form bgbsegs B (laddc (bf_DNB F) 16) with Some (c, []) => c | _ => -1 end.

Definition dep_rw (h1 : Z) : list (saddr * list scell) :=
  (SA LB_DNB 16, [SC_lit 8 h1]) :: map (fun b => (SA LB_lit (d_tab + 4 * b), [SC_lit 4 (tab_of [h1] b)])) (bkt h1 :: BK_TAIL).

Lemma dep_rw_eq (h1 : Z) : DEP_RW h1 = dep_rw h1.
Proof. unfold DEP_RW, dep_rw. rewrite DEP_BK_eq. reflexivity. Qed.

Definition fin_art (F : bforms) (B : AST) : bool :=
  let W := win_of B in let h1 := h1_of F B in
  forallb (chk_rw B W F SEGTOP_A) MAIN_RW && forallb (chk_ro B W F SEGTOP_A) MAIN_RO
  && forallb (chk_zero B W F SEGTOP_A) MAIN_ZERO && forallb (chk_stk B W F SEGTOP_A) MAIN_STK
  && (0 <=? h1) && (h1 <? 18446744073709551616) && forallb (fun b => (0 <=? b) && (b <? 1048576)) (bkt h1 :: BK_TAIL)
  && forallb (chk_rw B W F SEGTOP_A) (dep_rw h1) && forallb (chk_zero B W F SEGTOP_A) (SSB_ZERO (bf_f0 F))
  && chk_pristine B W SEGTOP_A (RELRO_LO, RELRO_HI)
  && forallb (chk_ro B W F SEGTOP_A) LIBSH_RO.

Section Art.
Variable fs0 : Fs.Fs.
Variable ρ : valuation.
Variable B : AST.
Variable ms : machine_state.
Variable model : Model.
Hypothesis HR : R bgbsegs amodel (MR bgbsegs fs0 ρ) target_alloc_limit ρ B (mkCfg ms model).
Variable F : bforms.

Local Notation W := (win_of B).
Local Notation L := (Lm ρ W JUNK F (vm_maps (m_vmmaps model))).
Local Notation m := (mM ρ ms model W JUNK F (vm_maps (m_vmmaps model))).

Hypothesis Hcore : fin_core F B = true.
Hypothesis Hart : fin_art F B = true.
Hypothesis Hlay : layout_ok L.

Theorem fin_art_sound : main_facts L (h1_of F B) m.
Proof.

  assert (Hc := Hcore). unfold fin_core in Hc. do 6 (apply andb_prop in Hc as [Hc _]).
  apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc Kss]. apply andb_prop in Hc as [Hc Klay]. apply andb_prop in Hc as [Kfm Kfw].
  destruct (ex_layout_ok fs0 _ ρ B ms model HR W JUNK F RES_B RES_B_ok eq_refl Klay) as (_ & Hat & _ & _).
  destruct (sp0_bounds ρ B model F Hlay) as [(S1 & S2) EAC].
  destruct (hz_parts B a_main Kfm Kfw) as (Hpos & HwL & HwH).
  assert (Hsp : 0x7fff80000000 <= l_sp0 L <= 2 ^ 47) by lia.

  assert (Ha := Hart). unfold fin_art in Ha. cbv zeta in Ha.
  apply andb_prop in Ha as [Ha Ksh]. apply andb_prop in Ha as [Ha Krel]. apply andb_prop in Ha as [Ha Kssb]. apply andb_prop in Ha as [Ha Kdep].
  apply andb_prop in Ha as [Ha Kbk]. apply andb_prop in Ha as [Ha Kh2]. apply andb_prop in Ha as [Ha Kh1]. apply andb_prop in Ha as [Ha Kstk].
  apply andb_prop in Ha as [Ha Kz]. apply andb_prop in Ha as [Krw Kro].
  apply Z.leb_le in Kh1. apply Z.ltb_lt in Kh2.
  constructor.
  - exact Hlay.
  - exact (chk_rw_all fs0 _ ρ B ms model HR W JUNK F _ Hsp SEGTOP_A _ Krw).
  - exact (chk_ro_all fs0 _ ρ B ms model HR W JUNK F _ Hsp SEGTOP_A _ Kro).
  - exact (chk_zero_all fs0 _ ρ B ms model HR W JUNK F _ Hsp SEGTOP_A _ Kz).
  - exact (chk_stk_all bsegs_low fs0 _ ρ B ms model HR W JUNK F _ HwL HwH Hsp SEGTOP_A _ Kstk).
  - exact (ex_stack_shadow bsegs_low fs0 ρ B ms model HR F a_main Kfm Kfw Hlay Hat Kss).
  - change (2 ^ 64) with 18446744073709551616. lia.
  - rewrite DEP_BK_eq. apply Forall_forall. intros b Hb. rewrite forallb_forall in Kbk. specialize (Kbk b Hb).
    apply andb_prop in Kbk as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2. change (2 ^ 20) with 1048576. lia.
  - rewrite dep_rw_eq. exact (chk_rw_all fs0 _ ρ B ms model HR W JUNK F _ Hsp SEGTOP_A _ Kdep).
  - exact (chk_zero_all fs0 _ ρ B ms model HR W JUNK F _ Hsp SEGTOP_A _ Kssb).
  - intros a Ha'. pose proof (chk_pristine_sound BDB_PC bdb_img_ok fs0 _ ρ B ms model HR W JUNK F (vm_maps (m_vmmaps model)) SEGTOP_A (RELRO_LO, RELRO_HI) Krel (bv_unsigned a) Ha') as X.
    unfold wa in X. rewrite Z_to_bv_bv_unsigned in X. exact X.
  - exact (chk_ro_all fs0 _ ρ B ms model HR W JUNK F _ Hsp SEGTOP_A _ Ksh).
  -
    intros a Hs Hal _ _.
    assert (Hss : in_ss (bv_unsigned a)).
    { unfold shreg, SHB, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in Hs. unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi. lia. }
    assert (Hv : RzCPS.HID (AFull ρ W JUNK F (vm_maps (m_vmmaps model))) model (wz (bv_unsigned a)) = false).
    { unfold wz. rewrite Z_to_bv_bv_unsigned. unfold RzCPS.HID, mkH. change (l_al0 L ++ allow_main L) with (AFull ρ W JUNK F (vm_maps (m_vmmaps model))) in Hal.
      rewrite Hal, andb_false_r. cbn [orb]. apply Z.leb_gt. unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi in Hss. lia. }
    destruct (sh_vis bgbsegs bsegs_low fs0 _ ρ B ms model HR W JUNK (allow_main L) HwL HwH (bv_unsigned a) Hss Hv) as (_ & _ & X).
    unfold wz in X. rewrite Z_to_bv_bv_unsigned in X. exact X.
Qed.

Corollary fin_art_ART : ART_A (sigma0 L (h1_of F B)) m.
Proof. exact (main_art L (h1_of F B) m fin_art_sound). Qed.

End Art.

Definition fin_clx (F : bforms) (B : AST) : bool :=
  let W := win_of B in forallb (chk_pristine B W SEGTOP_A) CLX_PRISTINE && forallb (chk_rw B W F SEGTOP_A) CLX_RW.

Section Clx.
Variable fs0 : Fs.Fs.
Variable ρ : valuation.
Variable B : AST.
Variable ms : machine_state.
Variable model : Model.
Hypothesis HR : R bgbsegs amodel (MR bgbsegs fs0 ρ) target_alloc_limit ρ B (mkCfg ms model).
Variable F : bforms.

Local Notation W := (win_of B).
Local Notation L := (Lm ρ W JUNK F (vm_maps (m_vmmaps model))).
Local Notation m := (mM ρ ms model W JUNK F (vm_maps (m_vmmaps model))).

Hypothesis Hcore : fin_core F B = true.
Hypothesis Hclx : fin_clx F B = true.
Hypothesis Hlay : layout_ok L.

Theorem fin_clx_sound : clx_facts L m.
Proof.
  assert (Hc := Hcore). unfold fin_core in Hc. do 9 (apply andb_prop in Hc as [Hc _]). apply andb_prop in Hc as [Kfm Kfw].
  destruct (sp0_bounds ρ B model F Hlay) as [(S1 & S2) EAC]. destruct (hz_parts B a_main Kfm Kfw) as (Hpos & HwL & HwH).
  assert (Hsp : 0x7fff80000000 <= l_sp0 L <= 2 ^ 47) by lia.
  unfold fin_clx in Hclx. cbv zeta in Hclx. apply andb_prop in Hclx as [Kp Krw].
  constructor.
  - destruct Hlay as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htid & _). exact Htid.
  - apply Forall_forall. intros r Hr. rewrite forallb_forall in Kp. intros a Ha.
    exact (chk_pristine_sound BDB_PC bdb_img_ok fs0 _ ρ B ms model HR W JUNK F (vm_maps (m_vmmaps model)) SEGTOP_A r (Kp r Hr) a Ha).
  - exact (chk_rw_all fs0 _ ρ B ms model HR W JUNK F _ Hsp SEGTOP_A _ Krw).
Qed.

End Clx.

Definition fin_rt (F : bforms) (B : AST) : bool := fin_art F B && fin_clx F B.

Definition fin_mainB : AST -> bool := fin_main fin_rt.

Lemma fin_mainB_out (B : AST) : fin_mainB B = true -> am_out (a_model B) = [].
Proof. exact (fin_main_out fin_rt B). Qed.

Theorem bridgeB_final (fs0 : Fs.Fs) (B : AST) : fin_mainB B = true ->
  forall ρ c, R bgbsegs amodel (MR bgbsegs fs0 ρ) target_alloc_limit ρ B c ->
  exists c', cfg_eqv c' c /\ START RTA OUT_repA ERR_repA XENVA lib_startA (dec_argvB ρ) fs0 c'.
Proof.
  apply (bridgeB OUT_repA ERR_repA XENVA lib_startA sigma0 h1_of sigma0_lay sigma0_aw sigma0_maps).
  - intros L h. unfold sigma0, sigma_init, rt_eager. cbn. lia.
  - intros L h. destruct (sigma0_live L h) as (L1 & L2 & L3). split; [exact L1|]. split; [exact L2|]. rewrite L3. unfold CREDIT_DRV, CREDIT0. lia.
  - intros fs1 ρ B' ms model F HR Hcore Hrt Hlay. unfold fin_rt in Hrt. apply andb_prop in Hrt as [Ha Hc]. split.
    + exact (fin_art_ART fs1 ρ B' ms model HR F Hcore Ha Hlay).
    + exact (main_clx _ _ (fin_clx_sound fs1 ρ B' ms model HR F Hcore Hc Hlay)).
Qed.
