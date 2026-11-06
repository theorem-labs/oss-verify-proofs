(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib BgArith.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX BnArith.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA W_topA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR Require W_bndiv.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import BnAKitAF BnCallAF W_callsAF W_expandAF W_lshiftAF W_div_tailAF W_divAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac fix_ret :=
  lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

Notation octop := OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_bndiv.octop.
Notation div_fin_eq := OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_bndiv.div_fin_eq.
Local Notation ops := (tree_ops bptr).

Definition BN_DIV : Z := 0x233440.
Definition BN_DIV_TOP_STACK : Z := 64 + BN_DIV_FT_STACK.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_dv_ft := (E_BN_div_233370 : uk_call BN_DIV 0x233558 BN_DIV_FIXED_TOP).

Lemma BN_div_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (dv rm : option bnref) (num dvs : bnref) (adv arm anum advs ac : Z) (qc : bptr),
  bn_preA Σ ls m OW LB PL EA sp lo BN_DIV_TOP_STACK BN_DIV_FT_COST ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_DIV (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> pl_ctx PL = Some (ac, qc) ->
  oref_at ls OW PL dv adv -> oref_at ls OW PL rm arm -> ref_at ls OW PL num anum -> ref_at ls OW PL dvs advs ->
  (forall d, dv = Some d -> wref PL d) -> (forall r, rm = Some r -> hpl PL r) -> num <> ROne -> dvs <> ROne -> nbuf PL num ->
  a0 = wz adv -> a1 = wz arm -> a2 = wz anum -> a3 = wz advs -> a4 = wz ac ->
  implA (BN_div ops dv rm num dvs ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA BN_DIV_FT_COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_DIV) fc None m (seg_rom bgasegs)).
Proof.
  intros until qc. intros PRE UW CTX -> EC HAdv HArm HAnum HAdvs WRdv HPrm NROn NROd NBn -> -> -> -> ->.
  change (not_one num) in NROn. change (not_one dvs) in NROd.
  pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
  pose proof LO as LO'.
  unfold BN_DIV_TOP_STACK, BN_DIV_FT_STACK, BN_LSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO.
  unfold BN_DIV_FT_COST in *. unfold BN_DIV, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  unfold BN_div. rewrite W_div_tail.bbind_get.
  set (bd := getbn dvs ls) in *.

  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAdvs) as HVdvs.
  destruct (lib_state_open [] ls m OW PL EA dvs advs LS ND HAdvs ltac:(intros []) NROd) as ((Dd & BNd & ARRd) & (OKd1 & OKd2 & OKd3 & OKd4) & _).
  fold bd in BNd, ARRd, OKd1, OKd2, OKd3, OKd4.
  destruct (bn_arr_facts_lin Σ OW LB m HEAP ls PL EA (bv_unsigned sp) USTACK_TOP PARTS FROK dvs Dd HVdvs NROd ARRd) as (Ud & _ & Dd0 & DdC & DdI & DSEPd).
  fold bd in Ud, DdC, DdI, DSEPd. pose proof (DSEPd dvs advs HAdvs) as SEPd. clear DSEPd.
  destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP PARTS NOFR HAdvs NROd) as (qd & Ad & nd & Hind & Rd1 & Rd2).
  pose proof (AH_range_in _ _ _ _ _ _ _ HEAP Hind) as (DA0 & _ & _ & DAC & DAI).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HAdvs NROd) as (ACDV & ALDV & OFDV).
  destruct (bn_arr_sh Σ OW LB m ls PL EA (bv_unsigned sp) USTACK_TOP dvs Dd HEAP PARTS FROK (proj2 NOFR) HVdvs NROd ARRd) as (ACV & ALV & OFV). fold bd in ACV, OFV.
  destruct (proj1 (limbarr_limbs_at bgasegs m Dd (bn_buf bd)) Ud) as (LAd & _).
  unfold BG_DMAX in OKd3. unfold bn_cells in BNd. unfold MallocRep.wz in BNd. clear Ud.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 80, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  assert (ASD : 0 < advs /\ advs + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - DA0 Rd1 Rd2 DAC CEIL LO SPR SPT; lia).
  assert (BDD : 0 <= Dd /\ Dd + 8 * Z.of_nat (bn_dmax bd) <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - Dd0 DdC CEIL LO SPR SPT; lia).
  apply implA_from_evt.
  carve_frame 64%nat ST. do 10 step. do 4 step. do 3 step. do 3 step.

  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  eapply evt_cut.
  { match goal with STx : stk _ m1 _ _, MIx : mem_inv _ m1 |- _ =>
      eapply BN_is_zero_specA with (lo := lo) (A := advs) (D := Dd) (b := bd);
        [exact BNd | unfold bn_dmax in *; lia | rewrite ESP; exact STx | rewrite ESP; lia | exact MIx | rewrite ESP; left; unfold BnHeapA.ACEIL in *; lia
        | exact (conj SHB1 SHB2) | exact (acc_munch bgasegs _ m m1 _ _ ACDV MU OFF ltac:(lia) ltac:(lia)) | exact ALDV | unfold SHHI; lia | exact OFDV | reflexivity] end. }
  intros ms' PO. unfold bn_small_postA in PO.
  destruct PO as (? & ? & ? & a0z & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & E & MUc & WMc & MIc & STc & ->).
  subst ms'. rewrite ESP in *.
  fix_ret.
  assert (LAd2 : limbs_at bgasegs m2 Dd (bn_buf bd)).
  { eapply limbs_at_transport; [eapply limbs_at_transport; [exact LAd | exact MU |] | exact MUc |];
      cbn [disjoint_from]; fold (bn_dmax bd); (split; [left; unfold BnHeapA.ACEIL in *; lia| exact I]). }
  match goal with STx : stk _ m1 _ _, MIx : mem_inv _ m1 |- _ => clear STx MIx end.
  transport_after_call bgasegs m1 m2 MUc WMc. clear MUc WMc.
  apply hide_intro in OFDV. apply hide_intro in OFV. apply hide_intro in DAI. apply hide_intro in DdI. apply hide_intro in SEPd.
  zstep. if_cases KZ; zify_cond KZ.
  2:{
      apply evt_done.
      replace (bn_top bd =? 0)%nat with true by (destruct (bn_top bd =? 0)%nat; [reflexivity| exfalso; cbn in KZ; rewrite ?unsigned_lit in KZ by lia; lia]).
      unfold bunr. cbn [unreachable tree_ops]. apply implA_unr. }
  apply Nat.eqb_neq in KZ.

  do 2 zstep.
  shl_with ACDV ALDV. chk0.
  do 3 zstep.
  shl_with ACDV ALDV.
  step.
  chk0.
  step. rewrite (sx32_small (Z.of_nat (bn_top bd))) by (unfold bn_dmax in *; lia).
  do 3 zstep.
  set (dtop := nth (bn_top bd - 1) (bn_buf bd) 0) in *.
  assert (Ntop : nth_error (bn_buf bd) (bn_top bd - 1) = Some dtop) by (apply nth_error_nth'; unfold bn_dmax in *; lia).
  assert (Rdtop : 0 <= dtop < 18446744073709551616).
  { assert (L : limb dtop) by (apply limbs_nth; exact OKd1). unfold limb in L. rewrite BW_lit in L. lia. }
  replace (Z.of_nat (bn_top bd) ≪ 3) with (8 * Z.of_nat (bn_top bd)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  do 2 zstep.
  shl_with ACV ALV. chk0.
  let ad := cur_mem_addr in
    pose proof (limbs_at_read_nth bgasegs m2 Dd (bn_buf bd) (bn_top bd - 1) dtop ad LAd2 Ntop ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. clear RD.
  zstep. if_cases KT; zify_cond KT.
  {
    apply evt_done.
    replace (bn_top bd =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; exact KZ).
    replace (dtop =? 0) with true by (symmetry; apply Z.eqb_eq; rewrite ?unsigned_lit in KT by lia; lia).
    unfold bunr. cbn [unreachable tree_ops]. apply implA_unr. }
  do 5 zstep. step.

  assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp - 80, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp - 80, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]).
  pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m m2 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
  match goal with FRx : rw_cells _ m2 (bv_unsigned sp + -64) ?fr, STx : stk _ m2 _ _, MIx : mem_inv _ m2 |- _ =>
    let pre := drop2 fr in
    assert (ENV : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre 0 Σ ls m2 OW);
    [ unfold cenvA; split;
      [ unfold cenv_ok; split; [exact CEIL|]; split; [clear - LO; lia|]; split; [clear; lia|]; split; [unfold USTACK_TOP; clear - SPT; lia|]; split; [exact SP16|];
        split; [clear - SP16; Z.div_mod_to_equations; lia|]; split; [exact CNT|]; split; [exact CRED|]; split; [exact FROK|]; split; [exact FAL| exact NOFR] |];
      split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; clear - SPT; lia))|];
      split; [exact STx|]; split; [exact MIx|];
      split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL CEIL ltac:(clear - LO; lia))|];
      split; [lia|]; split; [apply cnt_eq_refl|]; split; [apply refs_stable_refl|];
      split; [cbn [app]; exact FRx|]; split; [cbn; lia|]; unfold uw_opt;
      eapply uw_chain_munch_nw; [exact UW | exact MU |]; constructor; [cbn; lia | constructor]
    | ] end.
  pose proof ENV as (OK & HEAP1 & _).
  apply evt_done.
  replace (bn_top bd =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; exact KZ).
  replace (dtop =? 0) with false by (symmetry; apply Z.eqb_neq; exact KT).
  unfold bbind at 1. cbn [bind tree_ops].
  eapply implA_bind.
  { eapply (bn_div_fixed_top_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW) (LB := LB) (PL := PL) (EA := EA)
             (dv := dv) (rm := rm) (num := num) (dvs := dvs) (adv := adv) (arm := arm) (anum := anum) (advs := advs) (ac := ac) (qc := qc);
      [| | | reflexivity | exact EC | exact HAdv | exact HArm | exact HAnum | exact HAdvs | exact WRdv | exact HPrm | exact NROn | exact NROd | exact NBn
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | fold bd; clear - KZ; lia | fold bd; exact KT].
    - eapply cenv_preA; [exact ENV | exact LS1 | unfold BN_DIV_FT_STACK, BN_LSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_dv_ft CTX). }
  cbv beta. intros [u1 ls1] Σ1 ms1 PO.
  apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) BN_DIV_FT_COST Σ ls OW) in PO; [| exact OK | exact HEAP1].
  cbn [fst snd] in *.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F1 & fc1 & m3 & OW1 & PL1 & -> & CP1 & (EPL1 & ->)).
  subst PL1. specialize (CP1 eq_refl).
  lazymatch type of ENV with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?pre _ _ _ _ _ =>
    assert (E1 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre (0 + BN_DIV_FT_COST) Σ1 ls1 m3 OW1 /\ lib_state ls1 m3 OW1 PL EA)
      by (eapply cenv_postA; [exact ENV | exact CP1]) end.
  destruct E1 as (ENV1 & LS1').
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP1) as RS1.
  fix_ret. unfold MallocRep.wz.
  clear CP1.

  pose proof (oref_at_stable _ _ _ _ _ _ _ RS1 HAdv) as HAdv1. pose proof (oref_at_stable _ _ _ _ _ _ _ RS1 HArm) as HArm1.
  rewrite div_fin_eq. apply implA_ret_evt.
  unfold MallocRep.wz.
  assert (LOFB16 : lo <= bv_unsigned sp + -64 - 16) by (clear - LO; lia).
  clear ENV LS1 LS HEAP LAd LAd2 BNd ARRd MU WM HWL WOK HAdv HArm HAnum HAdvs RS1 PARTS WFS PWF IDS PLB ERRB ND HVdvs HEAP1.

  lazymatch type of ENV1 with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?pre ?u _ _ _ _ =>
  assert (EPI : forall lsE mE (FE : bvmap 5 word) (fcE : bv 32) y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y28 y29 y30 y31,
             cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre u Σ1 lsE mE OW1 -> lib_state lsE mE OW1 PL EA ->
             evt bgasegs (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA BN_DIV_FT_COST
                            (fun _ _ _ PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 1) (tt, lsE) Σ1)
               (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 TP_A) y5 y6 y7 sp y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 1) y19 y20 y21 y22 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                   FE (Z_to_bv 64 0x2334c4) fcE None mE (seg_rom bgasegs)))
  end.
  { intros lsE mE FE fcE y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y28 y29 y30 y31 ENVE LSE.
    pose proof (cenv_finalA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ENVE LSE ltac:(clear; lia)) as (F1' & F2 & F3 & F4 & F5 & F6 & F7).
    env_openA ENVE.
    zstep. do 8 step.
    release_frame FRe STe (bv_unsigned sp). step. step.
    apply evt_done. unfold bn_postA. do 17 eexists. exists mE, OW1, PL. split; [reflexivity|]. cbn [fst snd].
    split; [exact F1'|]. split; [exact F2|]. split; [exact STe|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
    split; [exact F6|]. split; [exact F7|]. split; reflexivity. }

  lazymatch type of ENV1 with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?pre ?u _ _ _ _ =>
  assert (MID : forall lsM mM (FM : bvmap 5 word) (fcM : bv 32) y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y28 y29 y30 y31,
             cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre u Σ1 lsM mM OW1 -> lib_state lsM mM OW1 PL EA ->
             oref_at lsM OW1 PL rm arm ->
             evt bgasegs (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA BN_DIV_FT_COST
                            (fun _ _ _ PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 1) (tt, octop rm lsM) Σ1)
               (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 TP_A) y5 y6 y7 sp (Z_to_bv 64 arm) y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                   FM (Z_to_bv 64 0x233568) fcM None mM (seg_rom bgasegs)))
  end.
  { intros lsM mM FM fcM y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y28 y29 y30 y31 ENVM LSM HArmM.
    destruct rm as [r|]; cbn [octop oref_at] in *.
    - pose proof (HPrm r eq_refl) as HPr.
      pose proof (lib_state_h_parts _ _ _ _ _ _ LSM) as PARTSM.
      pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENVM)) PARTSM HArmM HPr) as (RA0 & RAC & _ & _).
      assert (ARM : 0 < arm < 18446744073709551616) by (unfold BnHeapA.ACEIL in *; clear - RA0 RAC CEIL LO SPR; lia).
      zstep.
      zstep. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by (clear - ARM; lia). clear - K3 ARM. lia. }
      clear K3.
      zstep. step.
      eapply (ctop_callA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m LOFB16);
        [exact ENVM | exact LSM | exact HArmM | exact (hpl_wref PL r HPr) |].
      intros m5 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 ls5 ENV3 LS3.
      fix_ret.
      step.
      eapply EPI; [exact ENV3 | exact LS3].
    - subst arm.
      zstep.
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite ?unsigned_lit in K3 by lia. clear - K3. lia. }
      clear K3.
      eapply EPI; [exact ENVM | exact LSM]. }
  destruct dv as [d|]; cbn [octop oref_at] in *.
  - pose proof (WRdv d eq_refl) as WRd.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS1') as PARTS1.
    destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENV1)) PARTS1 NOFR HAdv1 (proj1 WRd)) as (qv & Av & nv & Hinv & Rv1 & Rv2).
    pose proof (AH_range_in _ _ _ _ _ _ _ (proj1 (proj2 ENV1)) Hinv) as (VA0 & _ & _ & VAC & _).
    assert (ADV : 0 < adv < 18446744073709551616) by (unfold BnHeapA.ACEIL in *; clear - VA0 Rv1 Rv2 VAC CEIL LO SPR; lia).
    clear VAC PARTS1.
    zstep. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. clear - K1. lia. }
    clear K1.
    zstep. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by (clear - ADV; lia). clear - K2 ADV. lia. }
    clear K2.
    zstep. step.
    eapply (ctop_callA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m LOFB16);
      [exact ENV1 | exact LS1' | exact HAdv1 | exact WRd |].
    intros m4 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 ls4 ENV2 LS2.
    fix_ret.
    eapply MID; [exact ENV2 | exact LS2 | apply oref_at_setbn; exact HArm1].
  - subst adv.
    zstep. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. clear - K1. lia. }
    clear K1.
    zstep. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. clear - K2. lia. }
    clear K2.
    eapply MID; [exact ENV1 | exact LS1' | exact HArm1].
Qed.

End WithRT.
