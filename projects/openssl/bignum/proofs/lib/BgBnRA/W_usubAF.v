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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnAddSpec BnMInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnA Require W_usub_core W_usub.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA UnwindA EdgesA AsStruct RtCallA W_cryptoA W_usub_coreA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR Require W_usub.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import BnAKitAF W_expandAF W_uaddAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BN_USUB : Z := 0x234e70.
Definition BN_USUB_STACK : Z := 80 + BN_WEXPAND_STACK.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_us_wexpand := (E_BN_usub_234d10 : uk_call BN_USUB 0x234ef8 BN_WEXPAND).

Lemma BN_usub_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (rr x y : bnref) (R X Y : Z),
  bn_preA Σ ls m OW LB PL EA sp lo BN_USUB_STACK MC ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_USUB (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> ref_at ls OW PL rr R -> hpl PL rr -> ref_at ls OW PL x X -> x <> ROne -> ref_at ls OW PL y Y -> y <> ROne ->
  a0 = wz R -> a1 = wz X -> a2 = wz Y ->
  implA (BN_usub (tree_ops bptr) rr x y ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC (uarith_res rr ls OW PL))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_USUB) fc None m (seg_rom bgasegs)).
Proof.
  intros until Y. intros PRE UW CTX -> HR HP HX NROx HY NROy -> -> ->.
  pose proof (proj1 (hpl_wref PL rr HP) : not_one rr) as NRO. change (not_one x) in NROx. change (not_one y) in NROy.
  pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
  unfold BN_USUB_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO.
  unfold BN_USUB, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  destruct (open_ro_sh Σ OW LB m ls PL EA _ x X HEAP LS FROK NOFR HX NROx) as (Dx0 & SX & OKX & _ & X0 & XC & _ & _ & ACX0 & ALX0 & _ & _).
  destruct (open_ro_sh Σ OW LB m ls PL EA _ y Y HEAP LS FROK NOFR HY NROy) as (Dy0 & SY & OKY & _ & Y0 & YC & _ & _ & ACY0 & ALY0 & _ & _).
  pose proof OKX as (_ & TDX & DMX & _). pose proof OKY as (_ & TDY & DMY & _). unfold BG_DMAX in DMX, DMY.
  unfold bn_cells, MallocRep.wz in SX, SY.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 80, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  rewrite OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_usub.BN_usub_eq.
  set (max := bn_top (getbn x ls)) in *. set (min := bn_top (getbn y ls)) in *.
  apply implA_from_evt.
  carve_frame 80%nat ST.
  apply (rw_cells_split_CB bgasegs _ _ [] 80 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 11 step. do 4 step.
  do 4 step. shl. step. chk0.
  do 3 step. shl. step. rewrite (sx32_small (Z.of_nat max)) by (clear - TDX DMX; unfold bn_dmax in *; lia). chk0.
  step. rewrite (sx32_small (Z.of_nat min)) by (clear - TDY DMY; unfold bn_dmax in *; lia).
  step. rewrite !unsigned_lit by (clear - TDX DMX TDY DMY; unfold bn_dmax in *; lia).
  rewrite (bn_swrap32_small (Z.of_nat max - Z.of_nat min)) by (clear - TDX DMX TDY DMY; unfold bn_dmax in *; lia).
  step. rewrite lts_signed by (clear - TDX DMX TDY DMY; unfold bn_dmax in *; lia).
  if_cases K; zify_cond K.
  {
    replace (max <? min)%nat with true by (symmetry; apply Nat.ltb_lt; clear - K; lia).
    apply evt_done. apply implA_unr. }
  replace (max <? min)%nat with false by (symmetry; apply Nat.ltb_ge; clear - K; lia).
  assert (HTOPS : (min <= max)%nat) by (clear - K; lia). clear K.
  do 3 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (HWL0 : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -80, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK0 : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -80, bv_unsigned sp)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  pose proof (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL0 CEIL ltac:(unfold USTACK_TOP; lia)) as HEAP1.
  pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m m1 OW PL EA _ HEAP LS MU WM FROK WOK0) as LS1.
  assert (AXP1 : ax_pres LB (bv_unsigned sp) (XW PL) m m1) by (exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL0 CEIL ltac:(lia))).
  assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp + -80) (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { apply (uw_push_frame m1 _ (bv_unsigned sp) 80 [CB 8 (take 8 junk); C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1]
             (bv_unsigned ra) (bv_unsigned s0) ras);
      [reflexivity | lia | clear - SP16; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | apply bv_unsigned_in_range | |].
    - rewrite !Z_to_bv_bv_unsigned. exact FR.
    - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
  clear SX SY OKX OKY Dx0 Dy0 ACX0 ACY0 MU WM OFF HWL0 WOK0 SHB1 SHB2 HEAP LS PRE PARTS.

  apply evt_done.
  eapply implA_bind.
  { eapply (bn_wexpand_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (r := rr) (a := R) (words := max)
                                   (OW := OW) (LB := LB) (PL := PL) (EA := EA);
      [| | | reflexivity | exact HR | exact (hpl_wref PL rr HP) | reflexivity | reflexivity | clear - TDX DMX; unfold bn_dmax in *; lia].
    - unfold bn_preA. rewrite ESP.
      split; [exact HEAP1|]. split; [exact LS1|]. split; [eapply frames_ok_call; [exact FROK| exact CEIL| lia| lia]|]. split; [exact ST|]. split; [exact CEIL|].
      split; [unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; lia|].
      split; [unfold USTACK_TOP; lia|]. split; [clear - SP16; Z.div_mod_to_equations; lia|]. split; [exact MI|]. split; [exact CNT|]. split; [exact CRED|]. split; [exact FAL| exact NOFR].
    - rewrite ESP. exact UW1.
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_us_wexpand CTX). }
  cbv beta. intros [u ls1] Σ1 ms1 PO. unfold bn_postA in PO. cbn [fst snd] in *.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & PL2 & -> & HEAP2 & LS2 & ST2
                  & MI2 & AXP2 & CR2 & CNT2 & RST2 & -> & -> & HDM & WRES & BST).
  rewrite ESP in *.
  rewrite (ret_pc_even 2313976) by lia.
  pose proof (ref_at_stable _ _ _ _ _ _ _ RST2 HR) as HR1. pose proof (ref_at_stable _ _ _ _ _ _ _ RST2 HX) as HX1. pose proof (ref_at_stable _ _ _ _ _ _ _ RST2 HY) as HY1.
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS1 HR) as HVR.
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HR1) as HVR1.
  assert (ETX : bn_top (getbn x ls1) = max) by (apply (wexpand_res_topA rr max ls ls1 x WRES HVR)).
  assert (ETY : bn_top (getbn y ls1) = min) by (apply (wexpand_res_topA rr max ls ls1 y WRES HVR)).
  clear TDX TDY.

  assert (FR2 : rw_cells bgasegs m2 (bv_unsigned sp + -80) [CB 8 (take 8 junk); C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_agree; [exact AXP2 | exact FR |].
    intros a Ha. cbn in Ha. xw_client_stack FROK. }

  pose proof (AH_nodup_l _ _ _ _ HEAP2) as ND2.
  pose proof (AH_ceil _ _ _ _ HEAP2) as (C1' & C2' & C3').
  destruct (lib_state_open [] ls1 m2 OW2 PL EA rr R LS2 ND2 HR1 ltac:(intros []) NRO) as ((Dr & SR & ARR) & OKR' & LSH). pose proof (bg_okm _ OKR') as OKR.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS1. pose proof PARTS1 as (WFS1 & PWF1 & IDS1 & PLB1 & ERRB1).
  destruct (bn_arr_factsA Σ1 OW2 LB m2 ls1 PL EA _ rr Dr HEAP2 PARTS1 FROK NOFR HVR1 NRO ARR) as (UR & LENR & DR0 & DRC & _ & DSEPR).
  pose proof ARR as ARRP. apply (fun ARRnb__ => bn_arr_nofr PL rr m2 OW2 Dr _ PWF1 NOFR NRO ARRnb__ ltac:(solve_nbuf)) in ARR.
  destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 NOFR HR1 NRO) as (qs & As & ns & Hins & Ra1 & Ra2).
  pose proof (AH_range_in _ _ _ _ _ _ _ HEAP2 Hins) as (SA0 & _ & _ & SAC & SAI).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HX1) as HVX1. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HY1) as HVY1.
  pose proof (st_wf_ok x ls1 WFS1 HVX1 NROx) as (LMX & TDX & _). pose proof (st_wf_ok y ls1 WFS1 HVY1 NROy) as (LMY & TDY & _).
  destruct (operand_view_sh Σ1 OW2 LB m2 ls1 PL EA _ rr R Dr x X max HEAP2 LS2 FROK NOFR HR1 NRO SR ARR HX1 NROx ltac:(rewrite ETX; lia))
    as (Dx & (ACDX & ALDX) & HXd & HLX & X0' & XC' & DX0 & DXC & SXR & SXA & ALIX).
  destruct (operand_view_sh Σ1 OW2 LB m2 ls1 PL EA _ rr R Dr y Y min HEAP2 LS2 FROK NOFR HR1 NRO SR ARR HY1 NROy ltac:(rewrite ETY; lia))
    as (Dy & (ACDY & ALDY) & HYd & HLY & Y0' & YC' & DY0 & DYC & SYR & SYA & ALIY).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP2 LS2 NOFR HR1 NRO) as (ACR & ALR & OFR).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP2 LS2 NOFR HX1 NROx) as (ACX & ALX2 & _).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP2 LS2 NOFR HY1 NROy) as (ACY & ALY2 & _).
  destruct (arr_shA _ _ _ _ _ _ HEAP2 ARR) as (ACDR & ALDR & OFDR).
  set (br := getbn rr ls1) in *.
  set (la := firstn max (bn_buf (getbn x ls1))) in *. set (lb := firstn min (bn_buf (getbn y ls1))) in *.
  assert (LLA : length la = max) by (subst la; apply firstn_length_le; rewrite <- ETX; exact TDX).
  assert (LLB : length lb = min) by (subst lb; apply firstn_length_le; rewrite <- ETY; exact TDY).

  rewrite (OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_usub.usub_rest_eq rr x y ls1 max min HVR1 HTOPS) by (unfold bn_dmax in *; lia). fold br la lb.
  change (OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_usub_core.usub_bn br la lb) with (BgBnA.W_usub_core.usub_bn br la lb).
  apply implA_ret_evt.
  assert (PREc : usub_preA sp lo R X Y Dr Dx Dy br la lb).
  { unfold usub_preA. rewrite LLA, LLB. specialize (DSEPR rr R HR1). fold br in DSEPR.
    split; [subst la; apply limbs_firstn; exact LMX|]. split; [subst lb; apply limbs_firstn; exact LMY|].
    split; [exact HTOPS|]. split; [exact OKR|]. split; [exact HDM|].
    split; [unfold BnHeapA.ACEIL in *; lia|]. split; [lia|]. split; [lia|]. split; [exact DSEPR|]. split; [exact SXA|]. split; [exact SYA|].
    split; [exact ALIX|]. split; [exact ALIY|].
    split; [repeat split; assumption|].
    unfold SHLO, SHHI in *. unfold BnHeapA.ACEIL in *. repeat split; lia. }
  replace (Z_to_bv 64 (Z.of_nat max)) with (Z_to_bv 64 (Z.of_nat (length la))) by (rewrite LLA; reflexivity).
  replace (Z_to_bv 64 (Z.of_nat min)) with (Z_to_bv 64 (Z.of_nat (length lb))) by (rewrite LLB; reflexivity).
  replace (Z_to_bv 64 (Z.of_nat max - Z.of_nat min)) with (Z_to_bv 64 (Z.of_nat (length la) - Z.of_nat (length lb))) by (rewrite LLA, LLB; reflexivity).
  eapply evt_mono.
  { eapply (usub_coreA ra sp gp (Z_to_bv 64 TP_A) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F2 fc2 (take 8 junk)) with (lo := lo) (R := R) (A := X) (B := Y)
      (Dr := Dr) (Da := Dx) (Db := Dy) (br := br) (la := la) (lb := lb).
    - exact PREc.
    - unfold core_memA. rewrite LLA, LLB. split; [exact SR|]. split; [exact UR|]. split; [exact HXd|]. split; [exact HYd|].
      split; [exact HLX|]. split; [exact HLY|]. split; [exact FR2|]. split; [exact ST2|]. split; [exact MI2|].
      split; [exact (AH_shb _ _ _ _ HEAP2)|]. split; [exact ACR|].
      split; [eapply acc_sub; [exact ACX | lia | lia]|]. split; [eapply acc_sub; [exact ACY | lia | lia]|].
      split; [exact ACDR|]. split; [exact ACDX | exact ACDY]. }

  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> & MU & WM & MI3 & SR3 & UR3 & ST3).
  pose proof (P_plain sp lo R X Y Dr Dx Dy br la lb PREc) as PREp.
  pose proof (BgBnA.W_usub_core.usub_buf_len sp lo R X Y Dr Dx Dy br la lb PREp) as LU.
  pose proof (BgBnA.W_usub_core.usub_bn_okm sp lo R X Y Dr Dx Dy br la lb PREp) as OKF.

  assert (CLOSE : forall W, munch W m2 m3 -> Forall (w_lib ls1 OW2 PL lo (bv_unsigned sp)) W -> Forall (w_ok OW2 LB ls1 PL EA (bv_unsigned sp) [rr]) W ->
            BnRepDefs.bn_arr m3 OW2 Dr (BgBnA.W_usub_core.usub_bn br la lb) -> bn_blocks (BgBnA.W_usub_core.usub_bn br la lb) = bn_blocks br ->
            bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC (uarith_res rr ls OW PL)
              ((), setbn rr (BgBnA.W_usub_core.usub_bn br la lb) ls1) Σ1
              (MS (mkR ra sp gp (Z_to_bv 64 TP_A) t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F2 (ret_pc ra) fc2 None m3 (seg_rom bgasegs))).
  { intros W MUW HWL WOK ARR3 EBL.
    unfold bn_postA. exists t0', t1', t2', (Z_to_bv 64 1), a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F2, fc2, m3, OW2, PL.
    split; [reflexivity|]. cbn [fst snd].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 FROK MUW WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|].
    split.
    { assert (OKF' : bg_ok (BgBnA.W_usub_core.usub_bn br la lb)).
      { destruct OKF as (K1 & K2 & _ & K4). destruct OKR' as (_ & _ & K3 & _). split; [exact K1|]. split; [exact K2|]. split; [|exact K4].
        unfold bn_dmax, BgBnA.W_usub_core.usub_bn in *. cbn [bn_buf] in *. rewrite LU. exact K3. }
      unfold lib_state. eapply (lib_state_close [] ls1 m3 OW2 PL EA rr R); [| exact ND2 | exact HR1 | exact NRO | | exact OKF' |].
      - eapply (lib_state_frame Σ1 LB (bv_unsigned sp) USTACK_TOP); [exact HEAP2 | exact LSH | exact MUW | exact WM | exact FROK | exact WOK].
      - exists Dr. split; [exact SR3|]. apply (fun ARRnb__ => bn_arr_of_nofr PL rr m3 OW2 Dr _ PWF1 NOFR NRO ARRnb__ ltac:(solve_nbuf)). exact ARR3.
      - apply ids_ok_setbn_same; [exact IDS1 | exact HVR1 | exact EBL]. }
    split; [exact ST3|]. split; [exact MI3|].
    split. { eapply ax_pres_trans; [exact AXP1|]. eapply ax_pres_trans; [eapply ax_pres_weaken; [exact AXP2 | lia]|].
             exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 FROK MUW HWL CEIL ltac:(lia)). }
    split; [exact CR2|].
    split. { unfold cnt_eq in *. rewrite (cnt_bal_setbn rr _ ls1 OW2 OW2 HVR1). fold br. rewrite CNT2, EBL. lia. }
    split. { eapply refs_stable_trans; [exact RST2| apply refs_stable_setbn]. }
    unfold uarith_res. split; [reflexivity|]. split; [reflexivity | exact BST]. }
  assert (HS : w_lib ls1 OW2 PL lo (bv_unsigned sp) (R, R + 24) /\ w_ok OW2 LB ls1 PL EA (bv_unsigned sp) [rr] (R, R + 24)).
  { split; [w_lib_ref HR1 NRO|].
    eapply (w_struct OW2 LB ls1 PL EA (bv_unsigned sp) false [rr] _ rr R); [left; reflexivity | exact HR1 | exact NRO | cbn; lia | cbn; lia]. }
  assert (HK : w_lib ls1 OW2 PL lo (bv_unsigned sp) (bv_unsigned sp - 128, bv_unsigned sp) /\ w_ok OW2 LB ls1 PL EA (bv_unsigned sp) [rr] (bv_unsigned sp - 128, bv_unsigned sp)).
  { split; [left; cbn [fst snd]; lia | apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia]. }
  rewrite LLA in MU.
  unfold BnRepDefs.bn_arr in ARR. destruct (bn_d br) as [pr|] eqn:Edr.
  - destruct ARR as [HinR _].
    eapply (CLOSE _ MU).
    + constructor; [right; left; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn [blk_addr blk_size fst snd]; split; [exact HinR | lia]|].
      constructor; [apply HS | constructor; [apply HK | constructor]].
    + constructor; [eapply (w_limbs OW2 LB ls1 PL EA (bv_unsigned sp) false [rr] _ rr pr Dr); [left; reflexivity | exact HVR1 | exact Edr | exact HinR | cbn [fst snd]; lia | cbn [fst snd]; fold br; lia]|].
      constructor; [apply HS | constructor; [apply HK | constructor]].
    + unfold BnRepDefs.bn_arr, BgBnA.W_usub_core.usub_bn. cbn [bn_d]. rewrite Edr. unfold bn_dmax at 1. cbn [bn_buf]. rewrite LU. split; [exact HinR | exact UR3].
    + unfold bn_blocks, BgBnA.W_usub_core.usub_bn, bn_dmax. cbn [bn_d bn_buf]. rewrite LU. reflexivity.
  -
    destruct ARR as [ED Eb].
    assert (EM0 : max = 0%nat) by (unfold bn_dmax in HDM; rewrite Eb in HDM; cbn [length] in HDM; lia).
    rewrite EM0 in MU. change (8 * Z.of_nat 0) with 0 in MU. rewrite Z.add_0_r in MU.
    assert (MU' : munch [(R, R + 24); (bv_unsigned sp - 128, bv_unsigned sp)] m2 m3).
    { eapply munch_weaken; [|exact MU]. unfold sub_fp. cbn [outside]. intros a Ha. split; [lia | exact Ha]. }
    eapply (CLOSE _ MU').
    + constructor; [apply HS | constructor; [apply HK | constructor]].
    + constructor; [apply HS | constructor; [apply HK | constructor]].
    + unfold BnRepDefs.bn_arr, BgBnA.W_usub_core.usub_bn. cbn [bn_d]. rewrite Edr. cbn [bn_buf].
      split; [exact ED|]. unfold BgBnA.W_usub_core.usub_buf. rewrite LLA, EM0. cbn [Nat.eqb]. exact Eb.
    + unfold bn_blocks, BgBnA.W_usub_core.usub_bn. cbn [bn_d]. rewrite Edr. reflexivity.
Qed.

End WithRT.
