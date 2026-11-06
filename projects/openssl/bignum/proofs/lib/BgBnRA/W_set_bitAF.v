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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR2 Require W_set_bit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import BnAKitAF BnCallAF W_expandAF ShiftKitAF W_div_padAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BN_SET_BIT : Z := 0x225d1c.
Definition BN_SET_BIT_STACK : Z := 80 + BN_EXPAND2_STACK.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Local Notation set_bit_ext := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_set_bit.set_bit_ext.
Local Notation set_bit_bn := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_set_bit.set_bit_bn.
Local Notation wlimbs_nth := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_set_bit.wlimbs_nth.
Local Notation wlimbs_upd := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_set_bit.wlimbs_upd.

Lemma BN_set_bit_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (rx : bnref) (ax n : Z),
  bn_preA Σ ls m OW LB PL EA sp lo BN_SET_BIT_STACK MC ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_SET_BIT (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> ref_at ls OW PL rx ax -> wref PL rx -> a0 = wz ax -> a1 = Z_to_bv 64 n -> -2^31 <= n < 2^31 ->
  implA (BN_set_bit (tree_ops bptr) rx n ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC
              (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = wz 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx ls) <> Some q -> In (q, A, n) OW')))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_SET_BIT) fc None m (seg_rom bgasegs)).
Proof.
  intros until n. intros PRE UW CTX -> HAx WRx -> -> HN.
  pose proof (proj1 WRx : not_one rx) as NROx.
  change (2 ^ 31) with 2147483648 in HN.

  destruct (Z.ltb_spec n 0) as [NNEG|NNEG].
  { unfold BN_set_bit. replace (n <? 0) with true by (symmetry; apply Z.ltb_lt; exact NNEG). unfold bunr. cbn [unreachable tree_ops]. apply implA_unr. }
  pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  pose proof LO as LO'. unfold BN_SET_BIT_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO'.
  unfold BN_SET_BIT, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  destruct (open_ro_sh Σ OW LB m ls PL EA _ rx ax HEAP LS FROK NOFR HAx NROx) as (Dx0 & BNx0 & (OKx1 & OKx2 & OKx3 & OKx4) & _ & X0 & XC & _ & _ & ACX & ALX & _ & _).
  set (bx := getbn rx ls) in *.
  unfold bn_cells, BnRepDefs.bn_cells, MallocRep.wz in BNx0. unfold BN_WORDS_MAX, BG_DMAX in OKx3.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 80, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAx) as HVx.
  set (i := Z.to_nat (n / 64)). set (j := n mod 64).
  assert (Ei : n / 64 = Z.of_nat i) by (subst i; clear - NNEG; Z.div_mod_to_equations; lia).
  assert (HI : 0 <= Z.of_nat i <= n) by (clear - Ei NNEG; Z.div_mod_to_equations; lia).
  assert (HJ : 0 <= j < 64) by (subst j; clear; Z.div_mod_to_equations; lia).
  assert (TOPZ : 0 <= Z.of_nat (bn_top bx) <= Z.of_nat (bn_dmax bx) /\ Z.of_nat (bn_dmax bx) <= 512) by (clear - OKx2 OKx3; unfold bn_dmax in *; lia).
  unfold BN_set_bit. replace (n <? 0) with false by (symmetry; apply Z.ltb_ge; exact NNEG).
  cbv zeta. fold i j. unfold bbind, bget, bset, bret. cbn [bind ret tree_ops tbind fst snd]. fold bx.
  apply implA_from_evt.
  carve_frame 80%nat ST.
  do 12 step.
  step. rewrite lts_signed by (clear - HN; lia). if_cases KN; zify_cond KN; [exfalso; clear - KN NNEG; lia|]. clear KN.
  do 2 step. do 3 step. do 3 step. shl_with ACX ALX. chk0.
  step. rewrite (sx32_small (Z.of_nat (bn_top bx))) by (clear - TOPZ; lia).
  step. setreg 22%Z (Z_to_bv 64 (Z.of_nat i))
          ltac:(rewrite <- Ei; f_equal; rewrite (unsigned_lit n) by (clear - HN NNEG; lia); unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 32)%Z with 4294967296%Z;
                rewrite (Z.mod_small n 4294967296) by (clear - HN NNEG; lia); rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 6) with 64;
                symmetry; apply bn_swrap32_small; clear - HN NNEG; Z.div_mod_to_equations; lia).
  step. rewrite (unsigned_lit ax) by (clear - X0 XC C1 C2 C3; unfold BnHeapA.ACEIL in *; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
  assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -80, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -80, bv_unsigned sp)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
  assert (EV : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -80) s0 ra (Some ras) MC Σ ls OW m
                 [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] 0 Σ ls m1 OW).
  { unfold cenvA, cenv_ok.
    split; [split; [exact CEIL|]; split; [lia|]; split; [lia|]; split; [unfold USTACK_TOP; lia|]; split; [exact SP16|];
            split; [clear - SP16; Z.div_mod_to_equations; lia|]; split; [exact CNT|]; split; [exact CRED|]; split; [exact FROK|]; split; [exact FAL| exact NOFR]|].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|].
    split; [exact ST|]. split; [exact MI|].
    split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL CEIL ltac:(lia))|].
    split; [lia|]. split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|].
    split; [cbn [app]; exact FR|]. split; [cbn; lia|]. unfold uw_opt.
    eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  pose proof EV as (OK & HEAP1 & _).

  assert (FIN : forall (Σ1 : rts RT) (ls1 : bstate bptr) (m2 : mem) (OW2 : list block) (used : Z) (FT : bvmap 5 word) (fcT : bv 32)
                       (q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q19 q20 q23 q28 q29 q30 q31 : word),
      cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -80) s0 ra (Some ras) MC Σ ls OW m
            [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] used Σ1 ls1 m2 OW2 ->
      lib_state ls1 m2 OW2 PL EA -> used <= MC ->
      (forall q A n, In (q, A, n) OW -> bn_d (getbn rx ls) <> Some q -> In (q, A, n) OW2) ->
      ref_at ls1 OW2 PL rx ax -> (i < bn_top (getbn rx ls1))%nat ->
      implA (TRet (tt, setbn rx (set_bit_bn (getbn rx ls1) i j) ls1)) Σ1
        (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC
                  (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx ls) <> Some q -> In (q, A, n) OW')))
        (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 TP_A) q5 q6 q7 sp (Z_to_bv 64 n) q10 q11 q12 q13 q14 q15 q16 q17
                 (Z_to_bv 64 ax) q19 q20 (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.of_nat i)) q23 (Z_to_bv 64 (Z.shiftr ax 3)) s9 s10 s11 q28 q29 q30 q31)
            FT (Z_to_bv 64 0x225e04) fcT None m2 (seg_rom bgasegs))).
  { intros Σ1 ls1 m2 OW2 used FT fcT q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q19 q20 q23 q28 q29 q30 q31 EV1 LS2 USED BST HAx2 HIT.
    clear BNx0 MU WM ST MI FR HWL WOK LS1 HEAP1 EV OK ACX OFF SHB1 SHB2 Dx0 HEAP LS PARTS PRE UW HVx C1 C2 C3 OKx1 OKx2 OKx3 OKx4 TOPZ.
    pose proof EV1 as (OK1 & HEAP2 & ST2 & MI2 & AXP2 & CR2 & CNT2 & RS2 & FR2 & FSZ2 & UW2).
    cbn [app] in FR2.
    pose proof (AH_nodup_l _ _ _ _ HEAP2) as ND2.
    pose proof (AH_ceil _ _ _ _ HEAP2) as (C1' & C2' & C3'). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS2; pose proof PARTS2 as (WFS2 & PWF2 & IDS2 & PLB2 & ERRB2).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAx2) as HVx2.
    destruct (lib_state_open [] ls1 m2 OW2 PL EA rx ax LS2 ND2 HAx2 ltac:(intros []) NROx) as ((Dr & BNr & ARRr) & (OKq1 & OKq2 & OKq3 & OKq4) & LSH).
    destruct (bn_arr_facts_w ls1 OW2 PL EA (bv_unsigned sp) USTACK_TOP Σ1 LB m2 rx Dr HEAP2 PARTS2 FROK HVx2 WRx ARRr) as (Ur & LENr & Dr0 & DrC & DrI & DSEPr).
    set (br := getbn rx ls1) in *.
    pose proof (DSEPr rx ax HAx2) as SEPrr. fold br in SEPrr.
    destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 NOFR HAx2 NROx) as (qr2 & Ar2 & nr2 & Hinr2 & Rr21 & Rr22).
    pose proof (AH_range_in _ _ _ _ _ _ _ HEAP2 Hinr2) as (SA0 & _ & _ & SAC & _).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP2 LS2 NOFR HAx2 NROx) as (ACR & ALR & OFR).
    pose proof ARRr as ARRo. apply (fun ARRnb__ => bn_arr_nofr PL rx m2 OW2 Dr _ PWF2 NOFR NROx ARRnb__ ltac:(solve_nbuf)) in ARRo.
    destruct (arr_shA _ _ _ _ _ _ HEAP2 ARRo) as (ACDR & ALDR & OFDR). fold br in ACDR, OFDR.
    unfold bn_cells, BnRepDefs.bn_cells in BNr. unfold BG_DMAX in OKq3. unfold MallocRep.wz in *. unfold SHLO, SHHI in *.
    apply implA_ret_evt.

    assert (HDr : exists pr, bn_d br = Some pr /\ In (pr, Dr, 8 * Z.of_nat (bn_dmax br)) OW2).
    { unfold BnRepDefs.bn_arr in ARRo. fold br in ARRo. destruct (bn_d br) as [pr|]; [exists pr; split; [reflexivity| exact (proj1 ARRo)]|].
      exfalso. destruct ARRo as [_ E]. unfold bn_dmax in OKq2. rewrite E in OKq2. cbn in OKq2. clear - OKq2 HIT. lia. }
    destruct HDr as (pr & Edr & Hinpr).
    assert (LBR : length (bn_buf br) = bn_dmax br) by reflexivity.
    pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m2) as MU3.
    pose proof (wmono_refl bgasegs m2) as WM3.
    assert (OFF3 : offshW [(bv_unsigned sp + -80, bv_unsigned sp); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
    { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. clear - OFDR SPR LO' CEIL C1' C2' C3'. lia. }
    assert (BDR : 0 <= Dr /\ Dr + 8 * Z.of_nat (bn_dmax br) <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - Dr0 DrC C1' C2' C3'; lia).
    assert (HIDZ : Z.of_nat i < Z.of_nat (bn_top br) <= Z.of_nat (bn_dmax br) /\ Z.of_nat (bn_dmax br) <= 512) by (clear - HIT OKq2 OKq3; unfold bn_dmax in *; lia).
    assert (LENW : Z.of_nat (length (wlimbs (bn_buf br))) = Z.of_nat (bn_dmax br)) by (rewrite wlimbs_len; reflexivity).
    clear DSEPr DrI OFR OFDR.

    step. shl_with ACR ALR. chk0.
    step. step.
    step. setreg 10%Z (Z_to_bv 64 (Dr + 8 * Z.of_nat i)) ltac:(f_equal; rewrite (unsigned_lit (Z.of_nat i)) by (clear - HIDZ; lia); rewrite Z.shiftl_mul_pow2 by (clear; lia); clear; lia).
    do 2 step. shl_limb ACDR ALDR BDR (Z.of_nat i). chk0.
    assert (NTH : nth_error (wlimbs (bn_buf br)) (Z.to_nat (Z.of_nat i)) = Some (Z_to_bv 64 (nth i (bn_buf br) 0))) by (apply wlimbs_nth; rewrite LBR; clear - HIDZ; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (u64arr_read bgasegs mx Dr (wlimbs (bn_buf br)) (Z.of_nat i) (Z_to_bv 64 (nth i (bn_buf br) 0)) (wa (Dr + 8 * Z.of_nat i)) Ur NTH ltac:(clear - HIDZ; lia) eq_refl) as RD end.
    step. clear RD.
    pose proof (limbs_nth (bn_buf br) i OKq1) as LN. unfold limb, BW in LN.
    set (x := nth i (bn_buf br) 0) in *.

    step. step. step. step.
    assert (P2J : 0 < 2 ^ j < 18446744073709551616) by (split; [apply Z.pow_pos_nonneg; [clear; lia| clear - HJ; lia]|]; change 18446744073709551616 with (2 ^ 64); apply Z.pow_lt_mono_r; clear - HJ; lia).
    setreg 11%Z (Z_to_bv 64 (Z.lor x (2 ^ j)))
            ltac:(f_equal; rewrite (unsigned_lit n) by (clear - HN NNEG; lia); replace (Z.land n 63) with j by (change 63 with (Z.ones 6); rewrite Z.land_ones by (clear; lia); reflexivity);
                  rewrite (unsigned_lit j) by (clear - HJ; lia); rewrite (Z.mod_small j 64) by (clear - HJ; lia); rewrite Z.shiftl_1_l, (unsigned_lit (2 ^ j)) by (clear - P2J; lia);
                  rewrite (unsigned_lit x) by (clear - LN; lia); reflexivity).
    assert (LOR : 0 <= Z.lor x (2 ^ j) < 18446744073709551616) by (apply (ZBridge.zr_lor x (2 ^ j)); unfold ZBridge.inr64; clear - LN P2J; lia).
    assert (IDX : 0 <= Z.of_nat i < Z.of_nat (length (wlimbs (bn_buf br)))) by (rewrite wlimbs_len, LBR; clear - HIDZ; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (u64arr_store_ok bgasegs mx Dr _ (Z.of_nat i) (wa (Dr + 8 * Z.of_nat i)) Ur IDX eq_refl) as SOKW;
      pose proof (u64arr_write bgasegs mx Dr _ (Z.of_nat i) (Z_to_bv 64 (Z.lor x (2 ^ j))) Ur IDX) as U2 end.
    rewrite Nat2Z.id, (wlimbs_upd (bn_buf br) i) in U2 by (rewrite LBR; clear - HIDZ; lia).
    clear Ur. step. store_done.

    step. step.
    do 10 step. release_frame FR2 ST2 (bv_unsigned sp). step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mG end.
    apply evt_done.
    set (nb := upd (bn_buf br) i (Z.lor x (2 ^ j))) in *.
    assert (Lnb : length nb = bn_dmax br) by (subst nb; rewrite upd_length by (rewrite LBR; clear - HIDZ; lia); exact LBR).
    assert (LMnb : limbs nb) by (subst nb; apply upd_limbs; [exact OKq1| unfold limb, BW; exact LOR]).
    assert (HWL3 : Forall (w_lib ls1 OW2 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -80, bv_unsigned sp); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
    { constructor; [left; cbn; clear - LO'; lia|].
      constructor; [right; left; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn [blk_addr blk_size fst snd]; split; [exact Hinpr| clear; lia]| constructor]. }
    assert (WOK3 : Forall (w_ok OW2 LB ls1 PL EA (bv_unsigned sp) [rx]) [(bv_unsigned sp + -80, bv_unsigned sp); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; clear - LO' CEIL; lia|].
      constructor; [eapply (w_limbs OW2 LB ls1 PL EA (bv_unsigned sp) false [rx] _ rx pr Dr); [left; reflexivity| exact HVx2| exact Edr| exact Hinpr| cbn [fst snd]; clear; lia| cbn [fst snd]; fold br; clear; lia]| constructor]. }
    unfold bn_postA. do 17 eexists. exists mG, OW2, PL. split; [reflexivity|]. cbn [fst snd].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROK MU3 WM3 HWL3 CEIL ltac:(unfold USTACK_TOP; clear - SPT; lia))|].
    split.
    { unfold lib_state. eapply (lib_state_close [] ls1 mG OW2 PL EA rx ax); [| exact ND2| exact HAx2| exact NROx| | |].
      - eapply (lib_state_frame Σ1 LB (bv_unsigned sp) USTACK_TOP); [exact HEAP2| exact LSH| exact MU3| exact WM3| exact FROK| exact WOK3].
      - exists Dr. split.
        + unfold bn_cells, BnRepDefs.bn_cells, bn_dmax, set_bit_bn, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_set_bit.set_bit_bn, bn_with_buf, MallocRep.wz. cbn [bn_top bn_buf bn_neg bn_flags bn_d]. fold br x nb. rewrite Lnb. exact BNr.
        + apply (fun ARRnb__ => bn_arr_of_nofr PL rx mG OW2 Dr _ PWF2 NOFR NROx ARRnb__ ltac:(solve_nbuf)). unfold BnRepDefs.bn_arr, bn_dmax, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_set_bit.set_bit_bn, bn_with_buf. cbn [bn_d bn_buf]. fold br x nb. rewrite Edr, Lnb. split; [exact Hinpr| exact U2].
      - unfold bg_ok, bn_dmax, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_set_bit.set_bit_bn, bn_with_buf. cbn [bn_buf bn_top bn_flags]. fold br x nb. rewrite Lnb. unfold BG_DMAX in *.
        split; [exact LMnb|]. split; [exact OKq2|]. split; [clear - OKq3; unfold bn_dmax in *; lia| exact OKq4].
      - apply ids_ok_setbn_same; [exact IDS2| exact HVx2|]. unfold bn_blocks, bn_dmax, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_set_bit.set_bit_bn, bn_with_buf. cbn [bn_d bn_buf]. fold br x nb. rewrite Lnb. reflexivity. }
    split; [exact ST2|]. split; [assumption|].
    split; [eapply ax_pres_trans; [exact AXP2|]; exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROK MU3 HWL3 CEIL ltac:(clear - LO'; lia))|].
    split; [clear - CR2 USED; lia|].
    split. { unfold cnt_eq in *. rewrite (cnt_bal_setbn rx _ ls1 OW2 OW2 HVx2). fold br. rewrite CNT2.
             unfold bn_blocks, bn_dmax, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_set_bit.set_bit_bn, bn_with_buf. cbn [bn_d bn_buf]. fold x nb. rewrite Edr. cbn [length]. clear. lia. }
    split. { eapply refs_stable_trans; [exact RS2| apply refs_stable_setbn]. }
    split; [reflexivity|]. split; [reflexivity| exact BST]. }

  assert (MID : forall (Σ1 : rts RT) (ls1 : bstate bptr) (m2 : mem) (OW2 : list block) (used : Z) (FT : bvmap 5 word) (fcT : bv 32)
                       (q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word),
      cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -80) s0 ra (Some ras) MC Σ ls OW m
            [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] used Σ1 ls1 m2 OW2 ->
      lib_state ls1 m2 OW2 PL EA -> used <= MC ->
      (forall q A n, In (q, A, n) OW -> bn_d (getbn rx ls) <> Some q -> In (q, A, n) OW2) ->
      ref_at ls1 OW2 PL rx ax -> (bn_top (getbn rx ls1) <= i)%nat -> (i + 1 <= bn_dmax (getbn rx ls1))%nat ->
      implA (TRet (tt, setbn rx (set_bit_bn (getbn rx (setbn rx (set_bit_ext (getbn rx ls1) i) ls1)) i j) (setbn rx (set_bit_ext (getbn rx ls1) i) ls1))) Σ1
        (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC
                  (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx ls) <> Some q -> In (q, A, n) OW')))
        (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 TP_A) q5 q6 q7 sp (Z_to_bv 64 n) q10 q11 q12 q13 q14 q15 q16 q17
                 (Z_to_bv 64 ax) (Z_to_bv 64 (ax + 8)) (Z_to_bv 64 (Z.of_nat i + 1)) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.of_nat i))
                 (Z_to_bv 64 (Z.shiftr (ax + 8) 3 + SHB)) (Z_to_bv 64 (Z.shiftr ax 3)) s9 s10 s11 q28 q29 q30 q31)
            FT (Z_to_bv 64 0x225db8) fcT None m2 (seg_rom bgasegs))).
  { intros Σ1 ls1 m2 OW2 used FT fcT q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 EV1 LS2 USED BST HAx2 HTI HID.
    clear BNx0 MU WM ST MI FR HWL WOK LS1 HEAP1 EV OK ACX OFF SHB1 SHB2 Dx0 HEAP LS PARTS PRE UW HVx C1 C2 C3 OKx1 OKx2 OKx3 OKx4 TOPZ.
    pose proof EV1 as (OK1 & HEAP2 & ST2 & MI2 & AXP2 & CR2 & CNT2 & RS2 & FR2 & FSZ2 & UW2).
    cbn [app] in FR2.
    pose proof (AH_nodup_l _ _ _ _ HEAP2) as ND2.
    pose proof (AH_ceil _ _ _ _ HEAP2) as (C1' & C2' & C3'). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS2; pose proof PARTS2 as (WFS2 & PWF2 & IDS2 & PLB2 & ERRB2).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAx2) as HVx2.
    destruct (lib_state_open [] ls1 m2 OW2 PL EA rx ax LS2 ND2 HAx2 ltac:(intros []) NROx) as ((Dr & BNr & ARRr) & (OKq1 & OKq2 & OKq3 & OKq4) & LSH).
    destruct (bn_arr_facts_w ls1 OW2 PL EA (bv_unsigned sp) USTACK_TOP Σ1 LB m2 rx Dr HEAP2 PARTS2 FROK HVx2 WRx ARRr) as (Ur & LENr & Dr0 & DrC & DrI & DSEPr).
    set (br := getbn rx ls1) in *.
    pose proof (DSEPr rx ax HAx2) as SEPrr. fold br in SEPrr.
    destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 NOFR HAx2 NROx) as (qr2 & Ar2 & nr2 & Hinr2 & Rr21 & Rr22).
    pose proof (AH_range_in _ _ _ _ _ _ _ HEAP2 Hinr2) as (SA0 & _ & _ & SAC & _).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP2 LS2 NOFR HAx2 NROx) as (ACR & ALR & OFR).
    pose proof ARRr as ARRo. apply (fun ARRnb__ => bn_arr_nofr PL rx m2 OW2 Dr _ PWF2 NOFR NROx ARRnb__ ltac:(solve_nbuf)) in ARRo.
    unfold bn_cells, BnRepDefs.bn_cells in BNr. unfold BG_DMAX in OKq3. unfold MallocRep.wz in *. unfold SHLO, SHHI in *.

    assert (HDr : exists pr, bn_d br = Some pr /\ In (pr, Dr, 8 * Z.of_nat (bn_dmax br)) OW2).
    { unfold BnRepDefs.bn_arr in ARRo. fold br in ARRo. destruct (bn_d br) as [pr|]; [exists pr; split; [reflexivity| exact (proj1 ARRo)]|].
      exfalso. destruct ARRo as [_ E]. unfold bn_dmax in HID. fold br in HID. rewrite E in HID. cbn in HID. clear - HID. lia. }
    destruct HDr as (pr & Edr & Hinpr).
    assert (LBR : length (bn_buf br) = bn_dmax br) by reflexivity.
    fold br in HTI, HID.
    pose proof (munch_refl (@nil (Z * Z)) m2) as MU3.
    assert (HIDZ : 0 <= Z.of_nat (bn_top br) <= Z.of_nat i /\ Z.of_nat i + 1 <= Z.of_nat (bn_dmax br) /\ Z.of_nat (bn_dmax br) <= 512) by (clear - HTI HID OKq3; unfold bn_dmax in *; lia).
    assert (BDR : 0 <= Dr /\ Dr + 8 * Z.of_nat (bn_dmax br) <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - Dr0 DrC C1' C2' C3'; lia).
    clear DSEPr DrI.
    apply implA_from_evt.
    shl_with ACR ALR. chk0.
    step. rewrite (sx32_small (Z.of_nat (bn_top br))) by (clear - HIDZ; lia).
    step. rewrite lts_signed by (clear - HIDZ; lia). if_cases KT; zify_cond KT; [exfalso; clear - KT HIDZ; lia|]. clear KT.

    step. shl_with ACR ALR. chk0.
    step. step. step. step. step. step.
    setreg 10%Z (Z_to_bv 64 (Dr + 8 * Z.of_nat (bn_top br))) ltac:(f_equal; rewrite (unsigned_lit (Z.of_nat (bn_top br))) by (clear - HIDZ; lia); rewrite Z.shiftl_mul_pow2 by (clear; lia); clear; lia).
    set (cnt := (i + 1 - bn_top br)%nat).
    assert (Ecnt : Z.of_nat cnt = Z.of_nat i + 1 - Z.of_nat (bn_top br)) by (subst cnt; clear - HIDZ; lia).
    step.
    setreg 12%Z (Z_to_bv 64 (8 * Z.of_nat cnt))
            ltac:(f_equal; rewrite (unsigned_lit (Z.of_nat i)), (unsigned_lit (Z.of_nat (bn_top br))) by (clear - HIDZ; lia); rewrite bn_swrap32_small by (clear - HIDZ; lia);
                  rewrite (unsigned_lit (Z.of_nat i - Z.of_nat (bn_top br))) by (clear - HIDZ; lia); rewrite Z.shiftl_mul_pow2 by (clear; lia);
                  change (2 ^ 32) with 4294967296; rewrite unsigned_lit by (clear - HIDZ; lia); rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 29) with 536870912;
                  clear - Ecnt HIDZ; Z.div_mod_to_equations; lia).
    step. step.

    pose proof Ur as Ur'.
    apply (proj1 (limbarr_split bgasegs _ Dr (bn_buf br) (bn_top br) ltac:(rewrite LBR; clear - HIDZ; lia))) in Ur'. destruct Ur' as [U1 U23].
    apply (proj1 (limbarr_split bgasegs _ _ (skipn (bn_top br) (bn_buf br)) cnt ltac:(rewrite length_skipn, LBR; clear - Ecnt HIDZ; lia))) in U23. destruct U23 as [_ U3].
    rewrite skipn_skipn in U3. replace (cnt + bn_top br)%nat with (i + 1)%nat in U3 by (clear - Ecnt HIDZ; lia).
    replace (Dr + 8 * Z.of_nat (bn_top br) + 8 * Z.of_nat cnt) with (Dr + 8 * (Z.of_nat i + 1)) in U3 by (clear - Ecnt; lia).
    assert (LU1 : Z.of_nat (length (wlimbs (firstn (bn_top br) (bn_buf br)))) = Z.of_nat (bn_top br)) by (rewrite wlimbs_len, firstn_length_le by (rewrite LBR; clear - HIDZ; lia); reflexivity).
    assert (LU3 : Z.of_nat (length (wlimbs (skipn (i + 1) (bn_buf br)))) = Z.of_nat (bn_dmax br) - (Z.of_nat i + 1)) by (rewrite wlimbs_len, length_skipn, LBR; clear - HIDZ; lia).
    apply evt_done.
    eapply implA_step_same.
    { eapply (asan_memset_cpsA) with (d := Dr + 8 * Z.of_nat (bn_top br)) (n := 8 * Z.of_nat cnt) (c := Z_to_bv 8 0) (bd := (pr, Dr, 8 * Z.of_nat (bn_dmax br))) (lo := lo) (OW := OW2) (LB := LB); try reflexivity.
      - exact HEAP2.
      - rewrite ESP. exact ST2.
      - exact CEIL.
      - rewrite ESP. unfold RT_STACK. clear - LO'. lia.
      - rewrite ESP. unfold USTACK_TOP. clear - SPT. lia.
      - rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
      - exact MI2.
      - apply in_or_app. left. exact Hinpr.
      - cbn [blk_addr blk_size fst snd]. clear - HIDZ. lia.
      - cbn [blk_addr blk_size fst snd]. clear - Ecnt HIDZ. lia.
      - clear - Ecnt HIDZ. lia. }
    intros msM PO. unfold icall_post in PO. rewrite ?ESP in PO.
    destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F3 & fc3 & mM & -> & MIM & STM & HEAPM & WMM & AGM & BZ & WRM).
    rewrite (ret_pc_even 2252280) by (clear; lia). unfold MallocRep.wz.
    assert (INR : In (qr2, Ar2, nr2) (OW2 ++ LB)) by (exact Hinr2).
    assert (INP : In (pr, Dr, 8 * Z.of_nat (bn_dmax br)) (OW2 ++ LB)) by (apply in_or_app; left; exact Hinpr).
    apply (rw_cells_agree _ _ _ _ _ AGM) in BNr.
    2:{ intros x Hx. cbn in Hx. split; [right; right; exists (qr2, Ar2, nr2); split; [exact INR| cbn [blk_addr blk_size fst snd]; clear - Hx Rr21 Rr22; lia]| clear - Hx SEPrr HIDZ Ecnt; lia]. }
    assert (U1M : u64arr bgasegs mM Dr (wlimbs (firstn (bn_top br) (bn_buf br)))).
    { eapply (LibKitA.u64arr_agree _ _ _ _ _ AGM); [exact U1|]. intros x Hx. rewrite LU1 in Hx.
      split; [right; right; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); split; [exact INP| cbn [blk_addr blk_size fst snd]; clear - Hx HIDZ; lia]| clear - Hx; lia]. }
    assert (U3M : u64arr bgasegs mM (Dr + 8 * (Z.of_nat i + 1)) (wlimbs (skipn (i + 1) (bn_buf br)))).
    { eapply (LibKitA.u64arr_agree _ _ _ _ _ AGM); [exact U3|]. intros x Hx. rewrite LU3 in Hx.
      split; [right; right; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); split; [exact INP| cbn [blk_addr blk_size fst snd]; clear - Hx HIDZ; lia]| clear - Hx Ecnt; lia]. }
    assert (LSHM : lib_state_hc false [rx] ls1 mM OW2 PL EA).
    { eapply (lib_state_h_icall Σ1 LB [rx] ls1 m2 mM OW2 PL EA (bv_unsigned sp + -80) (bv_unsigned sp) (Dr + 8 * Z.of_nat (bn_top br)) (8 * Z.of_nat cnt) HEAP2 LSH FROK ltac:(clear; lia) AGM).
      eapply (w_limbs OW2 LB ls1 PL EA (bv_unsigned sp) false [rx] _ rx pr Dr); [left; reflexivity| exact HVx2| exact Edr| exact Hinpr| cbn [fst snd]; clear - HIDZ; lia| cbn [fst snd]; fold br; clear - Ecnt HIDZ; lia]. }
    pose proof (cenv_icallA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -80) s0 ra (Some ras) MC Σ ls OW m _ _ _ _ _ _ _ (Dr + 8 * Z.of_nat (bn_top br)) (8 * Z.of_nat cnt) _
                  EV1 Hinpr ltac:(cbn [blk_addr blk_size fst snd]; clear - HIDZ; lia) ltac:(cbn [blk_addr blk_size fst snd]; clear - Ecnt HIDZ; lia) HEAPM STM MIM AGM) as EVM.
    assert (PZ : rw_cells bgasegs mM (Dr + 8 * Z.of_nat (bn_top br)) [CB (8 * cnt) (repeat (Z_to_bv 8 0) (8 * cnt))]).
    { replace (Z.to_nat (8 * Z.of_nat cnt)) with (8 * cnt)%nat in BZ by (clear; lia).
      split; [split; [cbn [cells_wf cell_wf]; rewrite repeat_length; clear; tauto| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BZ]|].
      cbn [cells_size csize Nat.add]. replace (Z.of_nat (8 * cnt + 0)) with (8 * Z.of_nat cnt) by (clear; lia). exact WRM. }
    set (nb := splice (bn_buf br) (bn_top br) (repeat 0 cnt)).
    assert (Lnb : length nb = bn_dmax br) by (subst nb; rewrite splice_length; [exact LBR| rewrite repeat_length, LBR; clear - Ecnt HIDZ; lia]).
    assert (LMnb : limbs nb) by (subst nb; apply splice_limbs; [exact OKq1| apply limbs_repeat; unfold limb, BW; clear; lia]).
    assert (UFM : u64arr bgasegs mM Dr (wlimbs nb)).
    { subst nb. unfold splice. rewrite repeat_length. replace (bn_top br + cnt)%nat with (i + 1)%nat by (clear - Ecnt HIDZ; lia).
      apply limbarr_app. split; [exact U1M|]. rewrite firstn_length_le by (rewrite LBR; clear - HIDZ; lia). apply limbarr_app. rewrite repeat_length. split.
      - eapply CB_u64arr. rewrite lbytes_repeat0. exact PZ.
      - replace (Dr + 8 * Z.of_nat (bn_top br) + 8 * Z.of_nat cnt) with (Dr + 8 * (Z.of_nat i + 1)) by (clear - Ecnt; lia). exact U3M. }
    assert (LENnb : Z.of_nat (length (wlimbs nb)) = Z.of_nat (bn_dmax br)) by (rewrite wlimbs_len, Lnb; reflexivity).
    clear U1 U3 Ur U1M U3M PZ BZ WRM AGM ACR MU3 HEAP2 ST2 MI2 LSH FR2 EV1 LS2 AXP2 UW2 WMM.
    pose proof EVM as (_ & _ & _ & _ & _ & _ & _ & _ & FRM & _ & _). cbn [app] in FRM.
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAPM LSHM NOFR HAx2 NROx) as (ACRM & _ & OFRM).
    pose proof (munch_refl [(ax, ax + 24)]%Z mM) as MU5. pose proof (wmono_refl bgasegs mM) as WM5.
    assert (OFF5 : offshW [(ax, ax + 24)]%Z) by (cbn [offshW]; unfold SHLO, SHHI in *; clear - OFRM; lia).
    apply implA_from_evt.

    shl_with ACRM ALR. chk0.
    step. replace (Z.of_nat i + 1) with (Z.of_nat (i + 1)) in BNr by (clear; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    apply evt_done.
    assert (HWL5 : Forall (w_lib ls1 OW2 PL lo (bv_unsigned sp)) [(ax, ax + 24)]).
    { constructor; [w_lib_ref HAx2 NROx| constructor]. }
    assert (WOK5 : Forall (w_ok OW2 LB ls1 PL EA (bv_unsigned sp) [rx]) [(ax, ax + 24)]).
    { constructor; [eapply (w_struct OW2 LB ls1 PL EA (bv_unsigned sp) false [rx] _ rx ax); [left; reflexivity| exact HAx2| exact NROx| cbn; clear; lia| cbn; clear; lia]| constructor]. }
    assert (EBL : length (bn_blocks (set_bit_ext br i)) = length (bn_blocks (getbn rx ls1))).
    { fold br. unfold bn_blocks, bn_dmax, set_bit_ext, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_set_bit.set_bit_ext. cbn [bn_d bn_buf]. rewrite Edr. reflexivity. }
    assert (LS4 : lib_state (setbn rx (set_bit_ext br i) ls1) m4 OW2 PL EA).
    { unfold lib_state. eapply (lib_state_close [] ls1 m4 OW2 PL EA rx ax); [| exact ND2| exact HAx2| exact NROx| | |].
      - eapply (lib_state_frame Σ1 LB (bv_unsigned sp) USTACK_TOP); [exact HEAPM| exact LSHM| exact MU5| exact WM5| exact FROK| exact WOK5].
      - exists Dr. split.
        + unfold bn_cells, BnRepDefs.bn_cells, bn_dmax, set_bit_ext, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_set_bit.set_bit_ext, MallocRep.wz. cbn [bn_top bn_buf bn_neg bn_flags bn_d]. fold cnt nb. rewrite Lnb. exact BNr.
        + apply (fun ARRnb__ => bn_arr_of_nofr PL rx m4 OW2 Dr _ PWF2 NOFR NROx ARRnb__ ltac:(solve_nbuf)). unfold BnRepDefs.bn_arr, bn_dmax, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_set_bit.set_bit_ext. cbn [bn_d bn_buf]. fold cnt nb. rewrite Edr, Lnb. split; [exact Hinpr| assumption].
      - unfold bg_ok, bn_dmax, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_set_bit.set_bit_ext. cbn [bn_buf bn_top bn_flags]. fold cnt nb. rewrite Lnb. unfold BG_DMAX in *.
        split; [exact LMnb|]. split; [clear - HIDZ; lia|]. split; [clear - OKq3; unfold bn_dmax in *; lia| exact OKq4].
      - apply ids_ok_setbn_same; [exact IDS2| exact HVx2|]. unfold bn_blocks, bn_dmax, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_set_bit.set_bit_ext. cbn [bn_d bn_buf]. fold cnt nb. rewrite Lnb. reflexivity. }
    eapply (FIN Σ1 (setbn rx (set_bit_ext br i) ls1) m4 OW2 used);
      [ apply cenv_setbnA; [| exact HVx2 | exact EBL];
        eapply (cenv_silentA_p LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -80) s0 ra (Some ras) MC Σ ls OW m); [exact EVM | exact PARTS2 | exact MU5 | exact WM5 | exact HWL5 | assumption | assumption | cbn [app]; eassumption | exact FSZ2]
      | exact LS4 | exact USED | exact BST
      | apply ref_at_setbn; exact HAx2
      | rewrite getbn_setbn_same by exact HVx2; unfold set_bit_ext, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_set_bit.set_bit_ext; cbn [bn_top]; clear; lia ]. }
  step. rewrite lts_signed by (clear - HI HN TOPZ; lia). if_cases KT; zify_cond KT.
  -
    replace (bn_top bx <=? i)%nat with false by (symmetry; apply Nat.leb_gt; clear - KT; lia).
    apply evt_done. cbn [tbind fst snd]. fold bx.
    eapply (FIN Σ ls m1 OW 0 F fc);
      [ exact EV | exact LS1 | unfold MC; clear; lia | intros q0 A0 n0 Hq0 _; exact Hq0 | exact HAx | fold bx; clear - KT; lia ].
  -
    replace (bn_top bx <=? i)%nat with true by (symmetry; apply Nat.leb_le; clear - KT; lia).
    do 3 step. shl_with ACX ALX. chk0.
    step. rewrite (sx32_small (Z.of_nat (bn_dmax bx))) by (clear - TOPZ; lia).
    step.
    step. rewrite lts_signed by (clear - HI HN TOPZ; lia). if_cases KD; zify_cond KD.
    +
      apply evt_done. unfold bn_wexpand, bbind, bget, bret, bset. cbn [bind ret tree_ops tbind fst snd]. fold bx.
      replace (i + 1 <=? bn_dmax bx)%nat with true by (symmetry; apply Nat.leb_le; clear - KD; lia).
      cbn [tbind fst snd]. fold bx.
      eapply (MID Σ ls m1 OW 0 F fc);
        [ exact EV | exact LS1 | unfold MC; clear; lia | intros q0 A0 n0 Hq0 _; exact Hq0 | exact HAx | fold bx; clear - KT; lia | fold bx; clear - KD; lia ].
    +
      do 3 step.
      apply evt_done.
      apply implA_assoc.
      eapply implA_bind.
      { eapply (bn_expand2_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (r := rx) (a := ax) (words := (i + 1)%nat) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
          [| | | reflexivity | exact HAx | exact WRx | reflexivity | unfold MallocRep.wz; f_equal; clear; lia | clear - HI HN; lia].
        - eapply cenv_preA; [exact EV | exact LS1 | unfold BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO'; lia | clear; lia].
        - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV).
        - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ (E_BN_set_bit_225bcc : uk_call BN_SET_BIT 0x225db4 BN_EXPAND2) CTX). }
      cbv beta. intros [u ls1] Σ1 ms1 PO.
      apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -80) MC Σ ls OW) in PO; [| exact OK | exact HEAP1].
      cbn [fst snd] in *.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & PL2 & -> & CP & (EPL & -> & HDM & WRES & BST)).
      subst PL2. specialize (CP eq_refl).
      assert (E1 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -80) s0 ra (Some ras) MC Σ ls OW m
                     [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] (0 + MC) Σ1 ls1 m2 OW2 /\ lib_state ls1 m2 OW2 PL EA)
        by (eapply cenv_postA; [exact EV | exact CP]).
      destruct E1 as (EV1 & LS2).
      pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP) as RST2.
      rewrite (ret_pc_even 2252212) by (clear; lia).
      pose proof (ref_at_stable _ _ _ _ _ _ _ RST2 HAx) as HAx2.
      assert (ETX : bn_top (getbn rx ls1) = bn_top bx) by (apply (wexpand_keeps_topA rx (i + 1) ls ls1 rx WRES HVx)).
      apply implA_from_evt.
      zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by (clear - X0 XC C1 C2 C3; unfold BnHeapA.ACEIL in *; lia). clear - KZ X0. lia. }
      clear KZ.
      apply evt_done. unfold bbind, bget, bset, bret. cbn [bind ret tree_ops tbind fst snd].
      eapply (MID Σ1 ls1 m2 OW2 (0 + MC) F2 fc2);
        [ exact EV1 | exact LS2 | clear; lia | exact BST | exact HAx2 | rewrite ETX; clear - KT; lia | exact HDM ].
Qed.

End WithRT.
