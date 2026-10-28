(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common Require Import RegEqv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Mem Frame ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Stdio.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface RT_state RT_main_shape RT_rep R_depot_defs R_glue_defs RT_main RT_main_clx D_defs D_libiface I_iodefs X_xdefs.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.VCommon Require Import FastWord.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExTrie AxLazy AxLin AxVal AxMem AxZZ AxState AxSys AxLz AxEntryS AxFd AxModelRel.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AxBdB Require Import BdAParams.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AxA Require Import AxExport AxExportH AxExportV. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AxB Require Import AxExportS AxExportF AxExportI AxExportL AxExportT AxExportP. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AxA Require Import FinMain1 FinMain2. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AxB Require Import FinMain3 BridgeA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
Definition BK_TAIL : list Z := Eval vm_compute in (map (fun tr => bkt (depot_hash tr)) T_MAIN).

Lemma DEP_BK_eq (h1 : Z) : DEP_BK h1 = bkt h1 :: BK_TAIL.
Proof.
  unfold DEP_BK. apply (f_equal (cons (bkt h1))).
  (* [comment removed for export] *)
  vm_cast_no_check (eq_refl BK_TAIL).
Qed.

(* [comment removed for export] *)
Definition h1_of (F : bforms) (B : AST) : Z :=
  match ld_form bsegs B (laddc (bf_DNB F) 16) with Some (c, []) => c | _ => -1 end.

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
Hypothesis HR : R bsegs amodel (MR bsegs fs0 ρ) target_alloc_limit ρ B (mkCfg ms model).
Variable F : bforms.

Local Notation W := (win_of B).
Local Notation L := (Lm ρ W JUNK F (vm_maps (m_vmmaps model))).
Local Notation m := (mM ρ ms model W JUNK F (vm_maps (m_vmmaps model))).

Hypothesis Hcore : fin_core F B = true.
Hypothesis Hart : fin_art F B = true.
Hypothesis Hlay : layout_ok L.

Theorem fin_art_sound : main_facts L (h1_of F B) m.
Proof.
  (* [comment removed for export] *)
  assert (Hc := Hcore). unfold fin_core in Hc. do 6 (apply andb_prop in Hc as [Hc _]).
  apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc Kss]. apply andb_prop in Hc as [Hc Klay]. apply andb_prop in Hc as [Kfm Kfw].
  destruct (ex_layout_ok fs0 _ ρ B ms model HR W JUNK F RES_A RES_A_ok eq_refl Klay) as (_ & Hat & _ & _).
  destruct (sp0_bounds ρ B model F Hlay) as [(S1 & S2) EAC].
  destruct (hz_parts B a_main Kfm Kfw) as (Hpos & HwL & HwH).
  assert (Hsp : 0x7fff80000000 <= l_sp0 L <= 2 ^ 47) by lia.
  (* [comment removed for export] *)
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
  - exact (chk_stk_all asegs_low fs0 _ ρ B ms model HR W JUNK F _ HwL HwH Hsp SEGTOP_A _ Kstk).
  - exact (ex_stack_shadow asegs_low fs0 ρ B ms model HR F a_main Kfm Kfw Hlay Hat Kss).
  - change (2 ^ 64) with 18446744073709551616. lia.
  - rewrite DEP_BK_eq. apply Forall_forall. intros b Hb. rewrite forallb_forall in Kbk. specialize (Kbk b Hb).
    apply andb_prop in Kbk as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2. change (2 ^ 20) with 1048576. lia.
  - rewrite dep_rw_eq. exact (chk_rw_all fs0 _ ρ B ms model HR W JUNK F _ Hsp SEGTOP_A _ Kdep).
  - exact (chk_zero_all fs0 _ ρ B ms model HR W JUNK F _ Hsp SEGTOP_A _ Kssb).
  - intros a Ha'. pose proof (chk_pristine_sound BDA_PC bda_img_ok fs0 _ ρ B ms model HR W JUNK F (vm_maps (m_vmmaps model)) SEGTOP_A (RELRO_LO, RELRO_HI) Krel (bv_unsigned a) Ha') as X.
    unfold wa in X. rewrite Z_to_bv_bv_unsigned in X. exact X.
  - exact (chk_ro_all fs0 _ ρ B ms model HR W JUNK F _ Hsp SEGTOP_A _ Ksh).
  - (* [comment removed for export] *)
    intros a Hs Hal _ _.
    assert (Hss : in_ss (bv_unsigned a)).
    { unfold shreg, SHB, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in Hs. unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi. lia. }
    assert (Hv : RzCPS.HID (AFull ρ W JUNK F (vm_maps (m_vmmaps model))) model (wz (bv_unsigned a)) = false).
    { unfold wz. rewrite Z_to_bv_bv_unsigned. unfold RzCPS.HID, mkH. change (l_al0 L ++ allow_main L) with (AFull ρ W JUNK F (vm_maps (m_vmmaps model))) in Hal.
      rewrite Hal, andb_false_r. cbn [orb]. apply Z.leb_gt. unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi in Hss. lia. }
    destruct (sh_vis bsegs asegs_low fs0 _ ρ B ms model HR W JUNK (allow_main L) HwL HwH (bv_unsigned a) Hss Hv) as (_ & _ & X).
    unfold wz in X. rewrite Z_to_bv_bv_unsigned in X. exact X.
Qed.

Corollary fin_art_ART : ART_A (sigma0 L (h1_of F B)) m.
Proof. exact (main_art L (h1_of F B) m fin_art_sound). Qed.

End Art.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fin_clx (F : bforms) (B : AST) : bool :=
  let W := win_of B in forallb (chk_pristine B W SEGTOP_A) CLX_PRISTINE && forallb (chk_rw B W F SEGTOP_A) CLX_RW.

Section Clx.
Variable fs0 : Fs.Fs.
Variable ρ : valuation.
Variable B : AST.
Variable ms : machine_state.
Variable model : Model.
Hypothesis HR : R bsegs amodel (MR bsegs fs0 ρ) target_alloc_limit ρ B (mkCfg ms model).
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
    exact (chk_pristine_sound BDA_PC bda_img_ok fs0 _ ρ B ms model HR W JUNK F (vm_maps (m_vmmaps model)) SEGTOP_A r (Kp r Hr) a Ha).
  - exact (chk_rw_all fs0 _ ρ B ms model HR W JUNK F _ Hsp SEGTOP_A _ Krw).
Qed.

End Clx.

Definition fin_rt (F : bforms) (B : AST) : bool := fin_art F B && fin_clx F B.

(* [comment removed for export] *)
Definition fin_mainA : AST -> bool := fin_main fin_rt.

Lemma fin_mainA_out (B : AST) : fin_mainA B = true -> am_out (a_model B) = [].
Proof. exact (fin_main_out fin_rt B). Qed.

(* [comment removed for export] *)
Theorem bridgeA_final (fs0 : Fs.Fs) (B : AST) : fin_mainA B = true ->
  forall ρ c, R bsegs amodel (MR bsegs fs0 ρ) target_alloc_limit ρ B c ->
  exists c', cfg_eqv c' c /\ START RTA OUT_repA ERR_repA XENVA lib_startA (dec_argvB ρ) fs0 c'.
Proof.
  apply (bridgeA OUT_repA ERR_repA XENVA lib_startA sigma0 h1_of sigma0_lay sigma0_aw sigma0_maps).
  - intros L h. unfold sigma0, sigma_init, rt_eager. cbn. lia.
  - intros L h. destruct (sigma0_live L h) as (L1 & L2 & L3). split; [exact L1|]. split; [exact L2|]. rewrite L3. unfold CREDIT_DRV, CREDIT0. lia.
  - intros fs1 ρ B' ms model F HR Hcore Hrt Hlay. unfold fin_rt in Hrt. apply andb_prop in Hrt as [Ha Hc]. split.
    + exact (fin_art_ART fs1 ρ B' ms model HR F Hcore Ha Hlay).
    + exact (main_clx _ _ (fin_clx_sound fs1 ρ B' ms model HR F Hcore Hc Hlay)).
Qed.
