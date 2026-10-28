(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA ZBridge RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnAddSpec BnMInv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem BnTacX.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnA Require W_usub_core W_usub.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA BnRepX ImplA BnIfaceA UnwindA EdgesA AsStruct RtCallA W_cryptoA W_expandA BnAKitA W_usub_coreA W_uaddA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit UbStruct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2438944 => 2
  | 2438956 => 1
  | 2438960 => 2
  | 2439000 => 2
  | 2439004 => 1
  | 2439008 => 2
  | 2439048 => 2
  | 2439076 => 2
  | 2439080 => 1
  | 2439084 => 2
  | 2439172 => 1
  | 2439176 => 1
  | 2439180 => 2
  | 2439184 => 1
  | 2439188 => 1
  | 2439192 => 1
  | 2439196 => 1
  | 2439200 => 2
  | 2439208 => 1
  | 2439212 => 1
  | 2439216 => 2
  | 2439220 => 1
  | 2439224 => 1
  | 2439228 => 1
  | 2439232 => 2
  | 2439240 => 1
  | 2439244 => 1
  | 2439272 => 1
  | 2439288 => 1
  | 2439292 => 2
  | 2439300 => 2
  | 2439304 => 2
  | 2439320 => 1
  | 2439324 => 2
  | 2439332 => 2
  | 2439336 => 2
  | 2439404 => 1
  | 2439412 => 1
  | 2439416 => 2
  | 2439420 => 2
  | 2439448 => 1
  | 2439460 => 2
  | 2439536 => 1
  | 2439540 => 1
  | 2439544 => 2
  | 2439548 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Open Scope Z_scope.

Definition BN_USUB : Z := 0x2536f4.
Definition BN_USUB_STACK : Z := 80 + BN_WEXPAND_STACK.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_us_wexpand := (E_BN_usub_24ff74 : uk_call BN_USUB 0x25379c BN_WEXPAND).

Lemma BN_usub_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
    (lo : Z) (ras : list Z) (rr x y : bnref) (R X Y : Z),
  bn_preA Σ ls m OW LB AD EA sp lo BN_USUB_STACK MC ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_USUB (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> ref_at ls OW AD rr R -> ref_at ls OW AD x X -> ref_at ls OW AD y Y ->
  a0 = wz R -> a1 = wz X -> a2 = wz Y ->
  implA (BN_usub (tree_ops bptr) rr x y ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA MC (uarith_res rr ls OW))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_USUB) fc None m (seg_rom bsegs)).
Proof.
  intros until Y. intros PRE UW CTX -> HR HX HY -> -> ->.
  pose proof PRE as (HEAP & LS & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED).
  unfold BN_USUB_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO.
  unfold BN_USUB, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  destruct (open_ro_sh Σ OW LB m ls AD EA x X HEAP LS HX) as (Dx0 & SX & OKX & _ & X0 & XC & _ & _ & ACX0 & ALX0 & _ & _).
  destruct (open_ro_sh Σ OW LB m ls AD EA y Y HEAP LS HY) as (Dy0 & SY & OKY & _ & Y0 & YC & _ & _ & ACY0 & ALY0 & _ & _).
  pose proof OKX as (_ & TDX & DMX & _). pose proof OKY as (_ & TDY & DMY & _). unfold BN_WORDS_MAX in DMX, DMY.
  unfold bn_cells, MallocRep.wz in SX, SY.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 80, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  rewrite W_usub.BN_usub_eq.
  set (max := bn_top (getbn x ls)) in *. set (min := bn_top (getbn y ls)) in *.
  apply implA_from_evt.
  carve_frame 80%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 80 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 11 (ub; step). do 3 (ub; step). do 4 (ub; step).
  do 2 (ub; step). ub; shl. ub; chk0.
  ub; step. do 2 (ub; step). ub; shl. ub; step. rewrite (sx32_small (Z.of_nat max)) by (clear - TDX DMX; unfold bn_dmax in *; lia). ub; chk0.
  ub; step. rewrite (sx32_small (Z.of_nat min)) by (clear - TDY DMY; unfold bn_dmax in *; lia).
  ub; step. rewrite !unsigned_lit by (clear - TDX DMX TDY DMY; unfold bn_dmax in *; lia).
  rewrite (bn_swrap32_small (Z.of_nat max - Z.of_nat min)) by (clear - TDX DMX TDY DMY; unfold bn_dmax in *; lia).
  ub; step.
  ub; step. rewrite lts_signed by (clear - TDX DMX TDY DMY; unfold bn_dmax in *; lia).
  if_cases K; zify_cond K.
  { (* [comment removed for export] *)
    replace (max <? min)%nat with true by (symmetry; apply Nat.ltb_lt; clear - K; lia).
    apply evt_done. apply implA_unr. }
  replace (max <? min)%nat with false by (symmetry; apply Nat.ltb_ge; clear - K; lia).
  assert (HTOPS : (min <= max)%nat) by (clear - K; lia). clear K.
  do 3 (ub; step).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (HWL0 : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -80, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK0 : Forall (w_ok OW LB ls AD EA []) [(bv_unsigned sp + -80, bv_unsigned sp)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  pose proof (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL0 CEIL ltac:(unfold USTACK_TOP; lia)) as HEAP1.
  pose proof (lib_state_frame Σ LB [] ls m m1 OW AD EA _ HEAP LS MU WM WOK0) as LS1.
  assert (AXP1 : ax_pres LB (bv_unsigned sp) LIBW_A m m1) by (exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP MU HWL0 CEIL ltac:(lia))).
  assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp + -80) (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { apply (uw_push_frame m1 _ (bv_unsigned sp) 80 [CB 8 (take 8 junk); C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1]
             (bv_unsigned ra) (bv_unsigned s0) ras);
      [reflexivity | lia | clear - SP16; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | apply bv_unsigned_in_range | |].
    - rewrite !Z_to_bv_bv_unsigned. exact FR.
    - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
  clear SX SY OKX OKY Dx0 Dy0 ACX0 ACY0 MU WM OFF HWL0 WOK0 SHB1 SHB2 HEAP LS PRE.
  (* [comment removed for export] *)
  apply evt_done.
  eapply implA_bind.
  { eapply (bn_wexpand_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (r := rr) (a := R) (words := max)
                                   (OW := OW) (LB := LB) (AD := AD) (EA := EA);
      [| | | reflexivity | exact HR | reflexivity | reflexivity | clear - TDX DMX; unfold bn_dmax in *; lia].
    - unfold bn_preA. rewrite ESP.
      split; [exact HEAP1|]. split; [exact LS1|]. split; [exact ST|]. split; [exact CEIL|].
      split; [unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; lia|].
      split; [unfold USTACK_TOP; lia|]. split; [clear - SP16; Z.div_mod_to_equations; lia|]. split; [exact MI|]. split; [exact CNT| exact CRED].
    - rewrite ESP. exact UW1.
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_us_wexpand CTX). }
  cbv beta. intros [u ls1] Σ1 ms1 PO. unfold bn_postA in PO. cbn [fst snd] in *.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & -> & HEAP2 & LS2 & ST2
                  & MI2 & AXP2 & CR2 & CNT2 & RST2 & -> & HDM & WRES & BST).
  rewrite ESP in *.
  rewrite (ret_pc_even 2439068) by lia.
  pose proof (RST2 _ _ HR) as HR1. pose proof (RST2 _ _ HX) as HX1. pose proof (RST2 _ _ HY) as HY1.
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS1 HR) as HVR.
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HR1) as HVR1.
  assert (ETX : bn_top (getbn x ls1) = max) by (apply (wexpand_res_topA rr max ls ls1 x WRES HVR)).
  assert (ETY : bn_top (getbn y ls1) = min) by (apply (wexpand_res_topA rr max ls ls1 y WRES HVR)).
  clear TDX TDY.
  (* [comment removed for export] *)
  assert (FR2 : rw_cells bsegs m2 (bv_unsigned sp + -80) [CB 8 (take 8 junk); C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_agree; [exact AXP2 | exact FR |].
    intros a Ha. cbn in Ha. split; [|left; unfold USTACK_TOP; lia]. unfold LIBW_A. cbn [rin_ivs fst snd]. unfold BnHeapA.ACEIL in *. lia. }
  (* [comment removed for export] *)
  pose proof (AH_nodup_l _ _ _ _ HEAP2) as ND2.
  pose proof (AH_ceil _ _ _ _ HEAP2) as (C1' & C2' & C3').
  destruct (lib_state_open [] ls1 m2 OW2 AD EA rr R LS2 ND2 HR1 ltac:(intros [])) as ((Dr & SR & ARR) & OKR & LSH).
  destruct (lib_state_h_parts _ _ _ _ _ _ LS2) as (IDS1 & ADB1 & ERRB1 & SOK1).
  destruct (bn_arr_facts Σ1 OW2 LB m2 HEAP2 ls1 AD EA IDS1 ADB1 rr Dr HVR1 ARR) as (UR & LENR & DR0 & DRC & _ & DSEPR).
  destruct (ref_at_inb _ _ _ _ _ ADB1 HR1) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP2 Hins) as (SA0 & _ & _ & SAC & SAI).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HX1) as HVX1. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HY1) as HVY1.
  pose proof (st_okm_getbn x ls1 SOK1 HVX1) as (LMX & TDX & _). pose proof (st_okm_getbn y ls1 SOK1 HVY1) as (LMY & TDY & _).
  destruct (operand_view_shu Σ1 OW2 LB m2 ls1 AD EA rr R Dr x X max HEAP2 LS2 HR1 SR ARR HX1 ltac:(rewrite ETX; lia))
    as (Dx & (ACDX & ALDX) & HXd & HLX & X0' & XC' & DX0 & DXC & SXR & SXA & ALIX & UBX).
  destruct (operand_view_shu Σ1 OW2 LB m2 ls1 AD EA rr R Dr y Y min HEAP2 LS2 HR1 SR ARR HY1 ltac:(rewrite ETY; lia))
    as (Dy & (ACDY & ALDY) & HYd & HLY & Y0' & YC' & DY0 & DYC & SYR & SYA & ALIY & UBY).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP2 LS2 HR1) as (ACR & ALR & OFR).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP2 LS2 HX1) as (ACX & ALX2 & _).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP2 LS2 HY1) as (ACY & ALY2 & _).
  destruct (arr_shA _ _ _ _ _ _ HEAP2 ARR) as (ACDR & ALDR & OFDR).
  set (br := getbn rr ls1) in *.
  set (la := firstn max (bn_buf (getbn x ls1))) in *. set (lb := firstn min (bn_buf (getbn y ls1))) in *.
  assert (LLA : length la = max) by (subst la; apply firstn_length_le; rewrite <- ETX; exact TDX).
  assert (LLB : length lb = min) by (subst lb; apply firstn_length_le; rewrite <- ETY; exact TDY).
  (* [comment removed for export] *)
  rewrite (W_usub.usub_rest_eq rr x y ls1 max min HVR1 HTOPS) by (unfold bn_dmax in *; lia). fold br la lb.
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
    - unfold usub_upreA. rewrite LLA, LLB. split; [|split; [exact UBX | exact UBY]].
      apply (arr_ub_okA Σ1 OW2 LB m2 Dr br _ HEAP2 ARR). unfold bn_dmax in *. lia.
    - unfold core_memA. rewrite LLA, LLB. split; [exact SR|]. split; [exact UR|]. split; [exact HXd|]. split; [exact HYd|].
      split; [exact HLX|]. split; [exact HLY|]. split; [exact FR2|]. split; [exact ST2|]. split; [exact MI2|].
      split; [exact (AH_shb _ _ _ _ HEAP2)|]. split; [exact ACR|].
      split; [eapply acc_sub; [exact ACX | lia | lia]|]. split; [eapply acc_sub; [exact ACY | lia | lia]|].
      split; [exact ACDR|]. split; [exact ACDX | exact ACDY]. }
  (* [comment removed for export] *)
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> & MU & WM & MI3 & SR3 & UR3 & ST3).
  pose proof (P_plain sp lo R X Y Dr Dx Dy br la lb PREc) as PREp.
  pose proof (W_usub_core.usub_buf_len sp lo R X Y Dr Dx Dy br la lb PREp) as LU.
  pose proof (W_usub_core.usub_bn_okm sp lo R X Y Dr Dx Dy br la lb PREp) as OKF.
  (* [comment removed for export] *)
  assert (CLOSE : forall W, munch W m2 m3 -> Forall (w_lib OW2 lo (bv_unsigned sp)) W -> Forall (w_ok OW2 LB ls1 AD EA [rr]) W ->
            bn_arr m3 OW2 Dr (W_usub_core.usub_bn br la lb) -> bn_blocks (W_usub_core.usub_bn br la lb) = bn_blocks br ->
            bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA MC (uarith_res rr ls OW)
              ((), setbn rr (W_usub_core.usub_bn br la lb) ls1) Σ1
              (MS (mkR ra sp gp (Z_to_bv 64 TP_A) t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F2 (ret_pc ra) fc2 None m3 (seg_rom bsegs))).
  { intros W MUW HWL WOK ARR3 EBL.
    unfold bn_postA. exists t0', t1', t2', (Z_to_bv 64 1), a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F2, fc2, m3, OW2.
    split; [reflexivity|]. cbn [fst snd].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP2 MUW WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|].
    split.
    { unfold lib_state. eapply (lib_state_close [] ls1 m3 OW2 AD EA rr R); [| exact ND2 | exact HR1 | | exact OKF |].
      - eapply lib_state_frame; [exact HEAP2 | exact LSH | exact MUW | exact WM | exact WOK].
      - exists Dr. split; [exact SR3 | exact ARR3].
      - apply ids_ok_setbn_same; [exact IDS1 | exact HVR1 | exact EBL]. }
    split; [exact ST3|]. split; [exact MI3|].
    split. { eapply ax_pres_trans; [exact AXP1|]. eapply ax_pres_trans; [eapply ax_pres_weaken; [exact AXP2 | lia]|].
             exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP2 MUW HWL CEIL ltac:(lia)). }
    split; [exact CR2|].
    split. { unfold cnt_eq in *. rewrite (cnt_bal_setbn rr _ ls1 OW2 OW2 HVR1). fold br. rewrite CNT2, EBL. lia. }
    split. { intros r0 a0' H0. apply ref_at_setbn. apply RST2. exact H0. }
    unfold uarith_res. split; [reflexivity | exact BST]. }
  assert (HS : w_lib OW2 lo (bv_unsigned sp) (R, R + 24) /\ w_ok OW2 LB ls1 AD EA [rr] (R, R + 24)).
  { split; [right; exists (qs, As, ns); cbn [blk_addr blk_size fst snd]; split; [exact Hins | lia]|].
    eapply (w_struct OW2 LB ls1 AD EA false [rr] _ rr R); [left; reflexivity | exact HR1 | cbn; lia | cbn; lia]. }
  assert (HK : w_lib OW2 lo (bv_unsigned sp) (bv_unsigned sp - 192, bv_unsigned sp) /\ w_ok OW2 LB ls1 AD EA [rr] (bv_unsigned sp - 192, bv_unsigned sp)).
  { split; [left; cbn [fst snd]; lia | apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia]. }
  rewrite LLA in MU.
  unfold bn_arr in ARR. destruct (bn_d br) as [pr|] eqn:Edr.
  - destruct ARR as [HinR _].
    eapply (CLOSE _ MU).
    + constructor; [right; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn [blk_addr blk_size fst snd]; split; [exact HinR | lia]|].
      constructor; [apply HS | constructor; [apply HK | constructor]].
    + constructor; [eapply (w_limbs OW2 LB ls1 AD EA false [rr] _ rr pr Dr); [left; reflexivity | exact HVR1 | exact Edr | exact HinR | cbn [fst snd]; lia | cbn [fst snd]; fold br; lia]|].
      constructor; [apply HS | constructor; [apply HK | constructor]].
    + unfold bn_arr, W_usub_core.usub_bn. cbn [bn_d]. rewrite Edr. unfold bn_dmax at 1. cbn [bn_buf]. rewrite LU. split; [exact HinR | exact UR3].
    + unfold bn_blocks, W_usub_core.usub_bn, bn_dmax. cbn [bn_d bn_buf]. rewrite LU. reflexivity.
  - (* [comment removed for export] *)
    destruct ARR as [ED Eb].
    assert (EM0 : max = 0%nat) by (unfold bn_dmax in HDM; rewrite Eb in HDM; cbn [length] in HDM; lia).
    rewrite EM0 in MU. change (8 * Z.of_nat 0) with 0 in MU. rewrite Z.add_0_r in MU.
    assert (MU' : munch [(R, R + 24); (bv_unsigned sp - 192, bv_unsigned sp)] m2 m3).
    { eapply munch_weaken; [|exact MU]. unfold sub_fp. cbn [outside]. intros a Ha. split; [lia | exact Ha]. }
    eapply (CLOSE _ MU').
    + constructor; [apply HS | constructor; [apply HK | constructor]].
    + constructor; [apply HS | constructor; [apply HK | constructor]].
    + unfold bn_arr, W_usub_core.usub_bn. cbn [bn_d]. rewrite Edr. cbn [bn_buf].
      split; [exact ED|]. unfold W_usub_core.usub_buf. rewrite LLA, EM0. cbn [Nat.eqb]. exact Eb.
    + unfold bn_blocks, W_usub_core.usub_bn. cbn [bn_d]. rewrite Edr. reflexivity.
Qed.

End WithRT.
