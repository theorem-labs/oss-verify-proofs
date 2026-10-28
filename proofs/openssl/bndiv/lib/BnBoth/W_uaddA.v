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
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnA Require W_uadd_core W_uadd.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA BnRepX ImplA BnIfaceA UnwindA EdgesA AsStruct RtCallA W_cryptoA W_expandA BnAKitA W_uadd_coreA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit UbStruct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2437992 => 2
  | 2438004 => 1
  | 2438008 => 2
  | 2438012 => 2
  | 2438016 => 1
  | 2438020 => 2
  | 2438156 => 1
  | 2438160 => 2
  | 2438168 => 2
  | 2438184 => 2
  | 2438188 => 1
  | 2438192 => 2
  | 2438308 => 1
  | 2438312 => 1
  | 2438316 => 2
  | 2438320 => 1
  | 2438324 => 1
  | 2438328 => 1
  | 2438332 => 1
  | 2438336 => 2
  | 2438344 => 1
  | 2438348 => 1
  | 2438352 => 2
  | 2438356 => 1
  | 2438360 => 1
  | 2438364 => 1
  | 2438368 => 2
  | 2438380 => 1
  | 2438384 => 1
  | 2438408 => 1
  | 2438420 => 1
  | 2438428 => 2
  | 2438436 => 1
  | 2438440 => 2
  | 2438448 => 2
  | 2438452 => 2
  | 2438468 => 1
  | 2438472 => 2
  | 2438480 => 2
  | 2438484 => 2
  | 2438548 => 2
  | 2438552 => 1
  | 2438556 => 2
  | 2438600 => 1
  | 2438604 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma wexpand_res_topA : forall r words (ls ls' : lstate bptr) x, wexpand_res r words ls ls' -> valid_refm r ls ->
  bn_top (getbn x ls') = bn_top (getbn x ls).
Proof.
  intros r words ls ls' x [[_ ->]|[_ [pn ->]]] HV; [reflexivity|].
  destruct (bnref_eq_dec r x) as [->|NE]; [rewrite getbn_setbn_same_m by exact HV; reflexivity | rewrite getbn_setbn_other by exact NE; reflexivity].
Qed.

Definition BN_UADD : Z := 0x253334.
Definition BN_UADD_STACK : Z := 96 + BN_WEXPAND_STACK.

(* [comment removed for export] *)
Definition uarith_res (rr : bnref) (ls : lstate bptr) (OW : list block) : unit -> lstate bptr -> list block -> word -> Prop :=
  fun _ ls' OW' a0' => a0' = wz 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rr ls) <> Some q -> In (q, A, n) OW').

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_ua_wexpand := (E_BN_uadd_24fcdc : uk_call BN_UADD 0x253424 BN_WEXPAND).

(* [comment removed for export] *)
Lemma uadd_tailA : forall
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (jb : list byte)
    (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo : Z) (ras : list Z)
    (m1 : mem) (rr x y : bnref) (R X Y : Z)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x21 x23 x24 x25 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  AHEAP Σ OW LB m1 -> lib_state ls m1 OW AD EA -> stk bsegs m1 lo (bv_unsigned sp + -96) -> mem_inv bsegs m1 ->
  ax_pres LB (bv_unsigned sp) LIBW_A m m1 ->
  rw_cells bsegs m1 (bv_unsigned sp + -96) [CB 8 jb; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  uw_chain USTACK_TOP m1 (bv_unsigned sp + -96) (bv_unsigned sp) (bv_unsigned ra :: ras) ->
  uk_ctx BN_UADD (bv_unsigned ra :: ras) ->
  ACEIL <= lo -> lo <= bv_unsigned sp - BN_UADD_STACK -> bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  cnt_ok ls OW LB -> MC <= rt_credit RT Σ ->
  ref_at ls OW AD rr R -> ref_at ls OW AD x X -> ref_at ls OW AD y Y ->
  (bn_top (getbn y ls) <= bn_top (getbn x ls))%nat ->
  implA (uadd_body rr x y ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA MC (uarith_res rr ls OW))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 R) a0 a1 a2 a3 a4 a5 a6 a7
             x18 (Z_to_bv 64 X) (Z_to_bv 64 Y) x21 (Z_to_bv 64 SHB) x23 x24 x25 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2533d8) fc None m1 (seg_rom bsegs)).
Proof.
  intros until fc. intros HEAP LS ST MI AXP1 FR UW1 CTX CEIL LO SPT SP16 CNT CRED HR HX HY HTOPS.
  unfold BN_UADD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  destruct (open_ro_sh Σ OW LB m1 ls AD EA x X HEAP LS HX) as (Dx0 & SX & OKX & _ & X0 & XC & _ & _ & ACX & ALX & _ & _).
  destruct (open_ro_sh Σ OW LB m1 ls AD EA y Y HEAP LS HY) as (Dy0 & SY & OKY & _ & Y0 & YC & _ & _ & ACY & ALY & _ & _).
  pose proof OKX as (_ & TDX & DMX & _). pose proof OKY as (_ & TDY & DMY & _). unfold BN_WORDS_MAX in DMX, DMY.
  unfold bn_cells, MallocRep.wz in SX, SY.
  set (max := bn_top (getbn x ls)) in *. set (min := bn_top (getbn y ls)) in *.
  pose proof (munch_refl (@nil (Z * Z)) m1) as MU.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
  apply implA_from_evt.
  do 3 (ub; step). ub; shl. ub; chk0.
  do 3 (ub; step). ub; shl. ub; step. rewrite (sx32_small (Z.of_nat max)) by (clear - TDX DMX; unfold bn_dmax in *; lia). ub; chk0.
  ub; step. rewrite (sx32_small (Z.of_nat min)) by (clear - TDY DMY; unfold bn_dmax in *; lia).
  ub; step.
  ub; step. rewrite (unsigned_lit (Z.of_nat max)) by (clear - TDX DMX; unfold bn_dmax in *; lia).
  rewrite (bn_swrap32_small (Z.of_nat max + 1)) by (clear - TDX DMX; unfold bn_dmax in *; lia).
  ub; step. ub; step.
  (* [comment removed for export] *)
  apply evt_done.
  rewrite W_uadd.uadd_body_eq. fold max min.
  eapply implA_bind.
  { eapply (bn_wexpand_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (r := rr) (a := R) (words := (max + 1)%nat)
                                   (OW := OW) (LB := LB) (AD := AD) (EA := EA);
      [| | | reflexivity | exact HR | reflexivity | unfold MallocRep.wz; f_equal; lia | clear - TDX DMX; unfold bn_dmax in *; lia].
    - unfold bn_preA. rewrite ESP.
      split; [exact HEAP|]. split; [exact LS|]. split; [exact ST|]. split; [exact CEIL|].
      split; [unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; lia|].
      split; [unfold USTACK_TOP; lia|]. split; [clear - SP16; Z.div_mod_to_equations; lia|]. split; [exact MI|]. split; [exact CNT| exact CRED].
    - rewrite ESP. exact UW1.
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_ua_wexpand CTX). }
  cbv beta. intros [u ls1] Σ1 ms1 PO. unfold bn_postA in PO. cbn [fst snd] in *.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & -> & HEAP2 & LS2 & ST2
                  & MI2 & AXP2 & CR2 & CNT2 & RST2 & -> & HDM & WRES & BST).
  rewrite ESP in *.
  rewrite (ret_pc_even 2438180) by lia.
  pose proof (RST2 _ _ HR) as HR1. pose proof (RST2 _ _ HX) as HX1. pose proof (RST2 _ _ HY) as HY1.
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR.
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HR1) as HVR1.
  assert (ETX : bn_top (getbn x ls1) = max) by (apply (wexpand_res_topA rr (max + 1) ls ls1 x WRES HVR)).
  assert (ETY : bn_top (getbn y ls1) = min) by (apply (wexpand_res_topA rr (max + 1) ls ls1 y WRES HVR)).
  clear SX SY OKX OKY TDX TDY Dx0 Dy0 ACX ACY MU.
  (* [comment removed for export] *)
  assert (FR2 : rw_cells bsegs m2 (bv_unsigned sp + -96) [CB 8 jb; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
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
  rewrite (W_uadd.uadd_rest_eq rr x y ls1 max min HVR1 HTOPS) by (unfold bn_dmax in *; lia). fold br la lb.
  apply implA_ret_evt.
  replace (Z.of_nat max) with (Z.of_nat (length la)) by (rewrite LLA; reflexivity).
  replace (Z.of_nat min) with (Z.of_nat (length lb)) by (rewrite LLB; reflexivity).
  eapply evt_mono.
  { eapply (uadd_coreA ra sp gp (Z_to_bv 64 TP_A) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F2 fc2 jb) with (lo := lo) (R := R) (A := X) (B := Y)
      (Dr := Dr) (Da := Dx) (Db := Dy) (br := br) (la := la) (lb := lb).
    - unfold uadd_preA. rewrite LLA, LLB. specialize (DSEPR rr R HR1). fold br in DSEPR.
      split; [subst la; apply limbs_firstn; exact LMX|]. split; [subst lb; apply limbs_firstn; exact LMY|].
      split; [exact HTOPS|]. split; [exact OKR|]. split; [exact HDM|].
      split; [unfold BnHeapA.ACEIL in *; lia|]. split; [lia|]. split; [lia|]. split; [exact DSEPR|]. split; [exact SXA|]. split; [exact SYA|].
      split; [exact ALIX|]. split; [exact ALIY|].
      split; [repeat split; assumption|].
      unfold SHLO, SHHI in *. unfold BnHeapA.ACEIL in *. repeat split; lia.
    - unfold uadd_upreA. rewrite LLA, LLB. split; [|split; [exact UBX | exact UBY]].
      apply (arr_ub_okA Σ1 OW2 LB m2 Dr br _ HEAP2 ARR). unfold bn_dmax in *. lia.
    - unfold core_memA. rewrite LLA, LLB. split; [exact SR|]. split; [exact UR|]. split; [exact HXd|]. split; [exact HYd|].
      split; [exact HLX|]. split; [exact HLY|]. split; [exact FR2|]. split; [exact ST2|]. split; [exact MI2|].
      split; [exact (AH_shb _ _ _ _ HEAP2)|]. split; [exact ACR|].
      split; [eapply acc_sub; [exact ACX | lia | lia]|]. split; [eapply acc_sub; [exact ACY | lia | lia]|].
      split; [exact ACDR|]. split; [exact ACDX | exact ACDY]. }
  (* [comment removed for export] *)
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> & MU & WM & MI3 & SR3 & UR3 & ST3).
  assert (HLla : limbs la) by (subst la; apply limbs_firstn; exact LMX).
  assert (HLlb : limbs lb) by (subst lb; apply limbs_firstn; exact LMY).
  assert (HMM : (length lb <= length la)%nat) by (rewrite LLA, LLB; exact HTOPS).
  assert (HDD : (length la + 1 <= bn_dmax br)%nat) by (rewrite LLA; exact HDM).
  pose proof (W_uadd_core.uadd_buf_length br la lb HLla HLlb HMM HDD) as LU.
  pose proof (W_uadd_core.uadd_bn_okm br la lb HLla HLlb HMM HDD OKR) as OKF.
  (* [comment removed for export] *)
  unfold bn_arr in ARR. destruct (bn_d br) as [pr|] eqn:Edr.
  2:{ exfalso. destruct ARR as [_ Eb]. unfold bn_dmax in HDD. rewrite Eb in HDD. cbn [length] in HDD. lia. }
  destruct ARR as [HinR _].
  pose proof (AH_range _ _ _ _ _ _ _ HEAP2 HinR) as (_ & _ & _ & _ & DRI).
  rewrite LLA in MU.
  assert (HWL : Forall (w_lib OW2 lo (bv_unsigned sp)) [(Dr, Dr + 8 * (Z.of_nat max + 1)); (R, R + 24); (bv_unsigned sp - 208, bv_unsigned sp)]).
  { constructor; [right; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn [blk_addr blk_size fst snd]; split; [exact HinR | lia]|].
    constructor; [right; exists (qs, As, ns); cbn [blk_addr blk_size fst snd]; split; [exact Hins | lia]|].
    constructor; [left; cbn [fst snd]; lia | constructor]. }
  assert (WOK : Forall (w_ok OW2 LB ls1 AD EA [rr]) [(Dr, Dr + 8 * (Z.of_nat max + 1)); (R, R + 24); (bv_unsigned sp - 208, bv_unsigned sp)]).
  { constructor; [eapply (w_limbs OW2 LB ls1 AD EA false [rr] _ rr pr Dr); [left; reflexivity | exact HVR1 | exact Edr | exact HinR | cbn [fst snd]; lia | cbn [fst snd]; fold br; lia]|].
    constructor; [eapply (w_struct OW2 LB ls1 AD EA false [rr] _ rr R); [left; reflexivity | exact HR1 | cbn; lia | cbn; lia]|].
    constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia | constructor]. }
  unfold bn_postA. exists t0', t1', t2', (Z_to_bv 64 1), a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F2, fc2, m3, OW2.
  split; [reflexivity|]. cbn [fst snd].
  split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP2 MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|].
  split.
  { unfold lib_state. eapply (lib_state_close [] ls1 m3 OW2 AD EA rr R); [| exact ND2 | exact HR1 | | exact OKF |].
    - eapply lib_state_frame; [exact HEAP2 | exact LSH | exact MU | exact WM | exact WOK].
    - exists Dr. split; [exact SR3|]. unfold bn_arr, W_uadd_core.uadd_bn. cbn [bn_d]. rewrite Edr. unfold bn_dmax at 1. cbn [bn_buf]. rewrite LU.
      split; [exact HinR | exact UR3].
    - apply ids_ok_setbn_same; [exact IDS1 | exact HVR1 |]. unfold bn_blocks, W_uadd_core.uadd_bn, bn_dmax. cbn [bn_d bn_buf]. rewrite LU. reflexivity. }
  split; [exact ST3|]. split; [exact MI3|].
  split. { eapply ax_pres_trans; [exact AXP1|]. eapply ax_pres_trans; [eapply ax_pres_weaken; [exact AXP2 | lia]|].
           exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP2 MU HWL CEIL ltac:(lia)). }
  split; [exact CR2|].
  split. { unfold cnt_eq in *. rewrite (cnt_bal_setbn rr _ ls1 OW2 OW2 HVR1). fold br. rewrite CNT2.
           unfold bn_blocks, W_uadd_core.uadd_bn. cbn [bn_d]. rewrite Edr. cbn [length]. lia. }
  split. { intros r0 a0' H0. apply ref_at_setbn. apply RST2. exact H0. }
  unfold uarith_res. split; [reflexivity | exact BST].
Qed.

Lemma BN_uadd_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
    (lo : Z) (ras : list Z) (rr ra_ rb_ : bnref) (R A Bb : Z),
  bn_preA Σ ls m OW LB AD EA sp lo BN_UADD_STACK MC ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_UADD (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> ref_at ls OW AD rr R -> ref_at ls OW AD ra_ A -> ref_at ls OW AD rb_ Bb ->
  a0 = wz R -> a1 = wz A -> a2 = wz Bb ->
  implA (BN_uadd (tree_ops bptr) rr ra_ rb_ ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA MC (uarith_res rr ls OW))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_UADD) fc None m (seg_rom bsegs)).
Proof.
  intros until Bb. intros PRE UW CTX -> HR HA HB -> -> ->.
  pose proof PRE as (HEAP & LS & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED).
  pose proof LO as LO'. unfold BN_UADD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO'.
  unfold BN_UADD, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  destruct (open_ro_sh Σ OW LB m ls AD EA ra_ A HEAP LS HA) as (Da0 & SA & OKA & _ & A0 & AC & _ & _ & ACA & ALA & _ & _).
  destruct (open_ro_sh Σ OW LB m ls AD EA rb_ Bb HEAP LS HB) as (Db0 & SB & OKB & _ & B0 & BC & _ & _ & ACB & ALB & _ & _).
  pose proof OKA as (_ & TDA & DMA & _). pose proof OKB as (_ & TDB & DMB & _). unfold BN_WORDS_MAX in DMA, DMB.
  unfold bn_cells, MallocRep.wz in SA, SB.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 96, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  rewrite BN_uadd_unfold.
  apply implA_from_evt.
  carve_frame 96%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 96 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 12 (ub; step). ub; step.
  ub; step. ub; step. do 4 (ub; step).
  do 2 (ub; step). ub; shl. ub; chk0.
  do 3 (ub; step). ub; shl. ub; step. rewrite (sx32_small (Z.of_nat (bn_top (getbn ra_ ls)))) by (clear - TDA DMA; unfold bn_dmax in *; lia). ub; chk0.
  ub; step. rewrite (sx32_small (Z.of_nat (bn_top (getbn rb_ ls)))) by (clear - TDB DMB; unfold bn_dmax in *; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -96, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK : Forall (w_ok OW LB ls AD EA []) [(bv_unsigned sp + -96, bv_unsigned sp)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  pose proof (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia)) as HEAP1.
  pose proof (lib_state_frame Σ LB [] ls m m1 OW AD EA _ HEAP LS MU WM WOK) as LS1.
  assert (AXP1 : ax_pres LB (bv_unsigned sp) LIBW_A m m1) by (exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP MU HWL CEIL ltac:(lia))).
  assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp + -96) (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { apply (uw_push_frame m1 _ (bv_unsigned sp) 96 [CB 8 (take 8 junk); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1]
             (bv_unsigned ra) (bv_unsigned s0) ras);
      [reflexivity | lia | clear - SP16; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | apply bv_unsigned_in_range | |].
    - rewrite !Z_to_bv_bv_unsigned. exact FR.
    - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  ub; step. rewrite lts_small by (clear - TDA DMA TDB DMB; unfold bn_dmax in *; lia).
  if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    replace (bn_top (getbn ra_ ls) <? bn_top (getbn rb_ ls))%nat with true by (symmetry; apply Nat.ltb_lt; clear - K; lia).
    ub; step. ub; step.
    apply evt_done.
    eapply (uadd_tailA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (take 8 junk) m Σ ls OW LB AD EA lo ras m1 rr rb_ ra_ R Bb A);
      [exact HEAP1 | exact LS1 | exact ST | exact MI | exact AXP1 | exact FR | exact UW1 | exact CTX | exact CEIL | exact LO
      | unfold USTACK_TOP; lia | exact SP16 | exact CNT | exact CRED | exact HR | exact HB | exact HA | clear - K; lia].
  - replace (bn_top (getbn ra_ ls) <? bn_top (getbn rb_ ls))%nat with false by (symmetry; apply Nat.ltb_ge; clear - K; lia).
    ub; step. ub; step.
    apply evt_done.
    eapply (uadd_tailA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (take 8 junk) m Σ ls OW LB AD EA lo ras m1 rr ra_ rb_ R A Bb);
      [exact HEAP1 | exact LS1 | exact ST | exact MI | exact AXP1 | exact FR | exact UW1 | exact CTX | exact CEIL | exact LO
      | unfold USTACK_TOP; lia | exact SP16 | exact CNT | exact CRED | exact HR | exact HA | exact HB | clear - K; lia].
Qed.

End WithRT.
