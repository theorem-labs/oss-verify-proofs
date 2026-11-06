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
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AsStruct2 AW_mul_words.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR2 Require W_mul_word.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import BnAKitAF BnCallAF W_expandAF ShiftKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BN_MUL_WORD : Z := 0x235bd4.
Definition BN_MUL_WORD_STACK : Z := 80 + BN_WEXPAND_STACK.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Local Notation mul_word_lo := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_mul_word.mul_word_lo.
Local Notation mul_word_hi := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_mul_word.mul_word_hi.
Local Notation wlimbs_upd := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_mul_word.wlimbs_upd.

Lemma BN_mul_word_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (rx : bnref) (ax w : Z),
  bn_preA Σ ls m OW LB PL EA sp lo BN_MUL_WORD_STACK MC ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_MUL_WORD (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> ref_at ls OW PL rx ax -> wref PL rx -> a0 = wz ax -> a1 = wz w -> 0 <= w < 2^64 ->
  implA (BN_mul_word (tree_ops bptr) rx w ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC
              (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = wz 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx ls) <> Some q -> In (q, A, n) OW')))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_MUL_WORD) fc None m (seg_rom bgasegs)).
Proof.
  intros until w. intros PRE UW CTX -> HAx WRx -> -> HW.
  pose proof (proj1 WRx : not_one rx) as NROx.
  pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  pose proof LO as LO'. unfold BN_MUL_WORD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO'.
  unfold BN_MUL_WORD, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  change (2 ^ 64) with 18446744073709551616 in HW.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  destruct (open_ro_sh Σ OW LB m ls PL EA _ rx ax HEAP LS FROK NOFR HAx NROx) as (Dx0 & BNx0 & (OKx1 & OKx2 & OKx3 & OKx4) & _ & X0 & XC & _ & _ & ACX & ALX & _ & _).
  set (bx := getbn rx ls) in *.
  unfold bn_cells, BnRepDefs.bn_cells, MallocRep.wz in BNx0. unfold BN_WORDS_MAX, BG_DMAX in OKx3.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 80, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAx) as HVx.
  assert (LBX : length (bn_buf bx) = bn_dmax bx) by reflexivity.
  unfold BN_mul_word, BN_zero, bbind, bget, bset, bret. cbn [bind ret tree_ops tbind fst snd]. fold bx.
  apply implA_from_evt.
  carve_frame 80%nat ST.
  do 11 step. do 3 step. do 4 step. shl_with ACX ALX. step. chk0.
  step. rewrite (sx32_small (Z.of_nat (bn_top bx))) by (clear - OKx2 OKx3; unfold bn_dmax in *; lia).
  step.
  lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: _) => set (jfr := j) in *; clearbody jfr end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
  assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -80, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -80, bv_unsigned sp)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
  assert (EV : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -80) s0 ra (Some ras) MC Σ ls OW m
                 [CB 8 jfr; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] 0 Σ ls m1 OW).
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

  assert (EPI : forall (Σ1 : rts RT) (ls1 : bstate bptr) (m2 : mem) (OW2 : list block) (used : Z) (FT : bvmap 5 word) (fcT : bv 32)
                       (q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q28 q29 q30 q31 : word),
      cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -80) s0 ra (Some ras) MC Σ ls OW m
            [CB 8 jfr; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] used Σ1 ls1 m2 OW2 ->
      lib_state ls1 m2 OW2 PL EA -> used <= MC ->
      (forall q A n, In (q, A, n) OW -> bn_d (getbn rx ls) <> Some q -> In (q, A, n) OW2) ->
      implA (TRet (tt, ls1)) Σ1
        (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC
                  (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx ls) <> Some q -> In (q, A, n) OW')))
        (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 TP_A) q5 q6 q7 sp (Z_to_bv 64 1) q10 q11 q12 q13 q14 q15 q16 q17
                 q18 q19 q20 q21 q22 q23 s8 s9 s10 s11 q28 q29 q30 q31)
            FT (Z_to_bv 64 0x235cc8) fcT None m2 (seg_rom bgasegs))).
  { intros Σ1 ls1 m2 OW2 used FT fcT q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q28 q29 q30 q31 EV1 LS2 USED BST.
    clear BNx0 MU WM ST MI FR HWL WOK LS1 HEAP1 EV OK ACX OFF SHB1 SHB2 HEAP LS PARTS PRE UW HVx OKx1 OKx2 OKx3 OKx4.
    pose proof EV1 as (OK1 & HEAP2 & ST2 & MI2 & AXP2 & CR2 & CNT2 & RS2 & FR2 & FSZ2 & UW2).
    cbn [app] in FR2.
    apply implA_ret_evt.
    step. do 9 step. release_frame FR2 ST2 (bv_unsigned sp). step. step.
    apply evt_done.
    unfold bn_postA. do 17 eexists. exists m2, OW2, PL. split; [reflexivity|]. cbn [fst snd].
    split; [exact HEAP2|]. split; [exact LS2|]. split; [exact ST2|]. split; [exact MI2|]. split; [exact AXP2|].
    split; [clear - CR2 USED; lia|]. split; [exact CNT2|]. split; [exact RS2|].
    split; [reflexivity|]. split; [reflexivity| exact BST]. }
  step. if_cases KT; zify_cond KT.
  -
    assert (ET : bn_top bx = 0%nat) by (rewrite ?unsigned_lit in KT by (clear - OKx2 OKx3; unfold bn_dmax in *; lia); clear - KT; lia).
    replace (bn_top bx =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; exact ET).
    apply evt_done.
    eapply (EPI Σ ls m1 OW 0 F fc); [exact EV | exact LS1 | unfold MC; clear; lia | intros q0 A0 n0 Hq0 _; exact Hq0].
  -
    assert (NT : bn_top bx <> 0%nat) by (rewrite ?unsigned_lit in KT by (clear - OKx2 OKx3; unfold bn_dmax in *; lia); clear - KT; lia).
    replace (bn_top bx =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; exact NT).

    clear BNx0 ACX MU WM OFF SHB1 SHB2 HEAP LS PARTS ST MI.
    pose proof EV as (_ & _ & ST1 & MI1 & _ & _ & _ & _ & FR1 & FSZ1 & _). cbn [app] in FR1. clear FR.
    pose proof (AH_nodup_l _ _ _ _ HEAP1) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS1) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    destruct (lib_state_open [] ls m1 OW PL EA rx ax LS1 ND HAx ltac:(intros []) NROx) as ((Dx & BNx & ARRx) & _ & LSH).
    destruct (bn_arr_facts_w ls OW PL EA (bv_unsigned sp) USTACK_TOP Σ LB m1 rx Dx HEAP1 PARTS FROK HVx WRx ARRx) as (Ux & LENx & Dx0' & DxC & DxI & DSEPx).
    fold bx in BNx, ARRx, Ux, LENx, DxC, DxI, DSEPx.
    pose proof (DSEPx rx ax HAx) as SEPxx.
    destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP1 PARTS NOFR HAx NROx) as (qx & Ax & nx & Hinx & Rx1 & Rx2).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP1 LS1 NOFR HAx NROx) as (ACX & ALX' & OFX).
    pose proof ARRx as ARRo. apply (fun ARRnb__ => bn_arr_nofr PL rx m1 OW Dx _ PWF NOFR NROx ARRnb__ ltac:(solve_nbuf)) in ARRo.
    destruct (arr_shA _ _ _ _ _ _ HEAP1 ARRo) as (ACDX & ALDX & OFDX).
    unfold bn_cells, BnRepDefs.bn_cells, MallocRep.wz in BNx. unfold SHLO, SHHI in *.

    assert (HDx : exists px, bn_d bx = Some px /\ In (px, Dx, 8 * Z.of_nat (bn_dmax bx)) OW).
    { unfold BnRepDefs.bn_arr in ARRo. destruct (bn_d bx) as [px|]; [exists px; split; [reflexivity| exact (proj1 ARRo)]|].
      exfalso. destruct ARRo as [_ E]. unfold bn_dmax in OKx2. rewrite E in OKx2. cbn in OKx2. clear - OKx2 NT. lia. }
    destruct HDx as (px & Edx & Hinpx).
    assert (PX0 : 0 < Dx) by (pose proof (AH_range _ _ _ _ _ _ _ HEAP1 Hinpx) as (P0 & _); exact P0).
    pose proof (munch_refl (@nil (Z * Z)) m1) as MU1.
    assert (OFF1 : offshW (@nil (Z * Z))) by exact I.
    destruct (AH_shb _ _ _ _ HEAP1) as (SHB1 & SHB2).
    step. if_cases KW; zify_cond KW.
    +
      assert (EW : w = 0) by (rewrite ?unsigned_lit in KW by (clear - HW; lia); clear - KW; lia).
      replace (w =? 0) with true by (symmetry; apply Z.eqb_eq; exact EW). cbn [tbind fst snd]. fold bx.
      step. step.
      eapply evt_cut.
      { eapply (BN_zero_ex_specA (Z_to_bv 64 2317504) (Z_to_bv 64 (bv_unsigned sp + -80))) with (A := ax) (D := Dx) (b := bx) (lo := lo);
          [ unfold bn_cells, BnRepDefs.bn_cells, MallocRep.wz; exact BNx | rewrite ESP; exact ST1 | rewrite ESP; clear - LO'; lia | exact MI1
          | rewrite ESP; unfold BnHeapA.ACEIL in *; clear - XC CEIL LO'; lia
          | exact (AH_shb _ _ _ _ HEAP1) | exact ACX | exact ALX | unfold SHHI, BnHeapA.ACEIL in *; clear - CEIL C1 C2 C3; lia | exact OFX | reflexivity]. }
      intros ms' (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m3 & -> & MUz & WMz & MIz & STz & SRz).
      rewrite ESP in MUz, STz.
      rewrite (ret_pc_even 2317504) by (clear; lia).
      assert (FR3 : rw_cells bgasegs m3 (bv_unsigned sp + -80) ([CB 8 jfr; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra])).
      { eapply rw_cells_transport; [exact FR1 | exact MUz | exact WMz |]. cbn. unfold BnHeapA.ACEIL in *. clear - XC CEIL LO'. lia. }
      step. apply evt_done.
      assert (HWLz : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -80 - 16, bv_unsigned sp + -80); (ax, ax + 24)]).
      { constructor; [left; cbn [fst snd]; clear - LO'; lia|]. constructor; [|constructor].
        w_lib_ref HAx NROx. }
      assert (WOKz : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) [rx]) [(bv_unsigned sp + -80 - 16, bv_unsigned sp + -80); (ax, ax + 24)]).
      { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; clear - CEIL LO'; lia|]. constructor; [|constructor].
        eapply (w_struct OW LB ls PL EA (bv_unsigned sp) false [rx] _ rx ax); [left; reflexivity | exact HAx | exact NROx | cbn; clear; lia | cbn; clear; lia]. }
      eapply (EPI Σ (setbn rx (bn_zero_pure bx) ls) m3 OW 0);
        [ apply cenv_setbnA; [| exact HVx | reflexivity];
          eapply cenv_silentA; [exact EV | exact LS1 | exact MUz | exact WMz | exact HWLz | exact STz | exact MIz | exact FR3 | exact FSZ1]
        | | unfold MC; clear; lia | intros q0 A0 n0 Hq0 _; exact Hq0 ].
      unfold lib_state. eapply (lib_state_close [] ls m3 OW PL EA rx ax); [| exact ND | exact HAx | exact NROx | | |].
      * eapply (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP); [exact HEAP1 | exact LSH | exact MUz | exact WMz | exact FROK | exact WOKz].
      * exists Dx. split; [exact SRz|]. eapply bn_arr_of_u64arr; [exact ARRx|].
        eapply u64arr_transport; [exact Ux | exact MUz | exact WMz |]. cbn [disjoint_from]. rewrite LENx. unfold BnHeapA.ACEIL in *. clear - SEPxx DxC Dx0' CEIL LO'. lia.
      * unfold bg_ok, bn_zero_pure, bn_dmax in *. cbn [bn_top bn_buf bn_flags]. unfold BG_DMAX. repeat split; [exact OKx1 | clear; lia | exact OKx3 | exact OKx4].
      * apply ids_ok_setbn_same; [exact IDS | exact HVx | reflexivity].
    +
      assert (NW : w <> 0) by (rewrite ?unsigned_lit in KW by (clear - HW; lia); clear - KW; lia).
      replace (w =? 0) with false by (symmetry; apply Z.eqb_neq; exact NW).
      pose proof (mul_words_spec (firstn (bn_top bx) (bn_buf bx)) w (limbs_firstn _ _ OKx1) ltac:(unfold limb, BW; exact HW)) as MWS.
      destruct (mul_words (firstn (bn_top bx) (bn_buf bx)) w) as [l ll] eqn:EMW.
      destruct MWS as (Ll & LENl & Lll & _). rewrite firstn_length_le in LENl by (clear - OKx2 LBX; lia). unfold limb, BW in Lll.
      cbn [tbind fst snd]. fold bx.
      assert (TOPZ : 0 < Z.of_nat (bn_top bx) <= Z.of_nat (bn_dmax bx) /\ Z.of_nat (bn_dmax bx) <= 512) by (clear - NT OKx2 OKx3; unfold bn_dmax in *; lia).
      assert (BDX : 0 <= Dx /\ Dx + 8 * Z.of_nat (bn_dmax bx) <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - Dx0' DxC C1 C2 C3; lia).
      do 2 step. shl_with ACX ALX. chk0.
      step. step.
      assert (EDx : bv_unsigned (Z_to_bv 64 Dx) = Dx) by (apply unsigned_lit; clear - BDX; lia).
      assert (ETP : bv_unsigned (Z_to_bv 64 (Z.of_nat (bn_top bx))) = Z.of_nat (bn_top bx)) by (apply unsigned_lit; clear - TOPZ; lia).
      assert (EWW : bv_unsigned (Z_to_bv 64 w) = w) by (apply unsigned_lit; clear - HW; lia).

      pose proof Ux as Ux'. apply (proj1 (limbarr_split bgasegs _ Dx (bn_buf bx) (bn_top bx) ltac:(clear - OKx2 LBX; lia))) in Ux'. destruct Ux' as [U1 U2].
      assert (LU2 : Z.of_nat (length (wlimbs (skipn (bn_top bx) (bn_buf bx)))) = Z.of_nat (bn_dmax bx) - Z.of_nat (bn_top bx))
        by (rewrite wlimbs_len, length_skipn, LBX; clear - OKx2; lia).
      pose proof (limbs_at_of_u64arr bgasegs _ _ _ U1) as RA1. pose proof (proj2 U1) as WR1. rewrite wlimbs_len, firstn_length_le in WR1 by (clear - OKx2 LBX; lia).
      step.
      eapply evt_cut.
      { eapply bn_mul_words_aspec with (a := firstn (bn_top bx) (bn_buf bx)) (lo := lo) (m := m1);
          rewrite ?EDx, ?ETP, ?ESP, ?EWW, ?firstn_length_le by (clear - OKx2 LBX; lia);
          [ apply limbs_firstn; exact OKx1 | clear - TOPZ; lia | reflexivity | exact RA1 | exact WR1 | left; reflexivity | exact ST1
          | clear - LO'; lia | unfold BnHeapA.ACEIL in *; clear - DxC TOPZ CEIL LO'; lia | unfold BnHeapA.ACEIL in *; clear - DxC TOPZ CEIL LO'; lia | exact MI1
          | exact (AH_shb _ _ _ _ HEAP1)
          | eapply acc_sub; [exact ACDX | clear; lia | clear - TOPZ; lia]
          | eapply acc_sub; [exact ACDX | clear; lia | clear - TOPZ; lia]
          | unfold aptrs3; split; [exact ALDX|]; split; [exact ALDX|]; split; [exact ALDX|]; split; [unfold SHLO, SHHI; clear - OFDX TOPZ; lia | unfold SHHI, BnHeapA.ACEIL in *; clear - CEIL C1 C2 C3; lia] ]. }
      intros ms' PO. unfold mw_apost, OSSVerify.Proofs.openssl.bignum.lib.BnW.BnLoop.wl_post in PO.
      destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & RES & STc).
      subst ms'. rewrite ?EDx, ?ESP, ?EWW, ?firstn_length_le, ?EMW in * by (clear - OKx2 LBX; lia). cbn [fst snd] in RES, MUc |- *.
      rewrite (ret_pc_even 2317396) by (clear; lia).
      assert (FR2 : rw_cells bgasegs m2 (bv_unsigned sp + -80) ([CB 8 jfr; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra])).
      { eapply rw_cells_transport; [exact FR1 | exact MUc | exact WMc |]. cbn. unfold BnHeapA.ACEIL in *. clear - DxC TOPZ CEIL LO'. lia. }
      lazymatch type of BNx with rw_cells _ _ ?adr ?cells => assert (BNx2 : rw_cells bgasegs m2 adr cells) end.
      { eapply rw_cells_transport; [exact BNx | exact MUc | exact WMc |]. cbn. unfold BnHeapA.ACEIL in *. clear - SEPxx XC TOPZ CEIL LO'. lia. }
      assert (U22 : u64arr bgasegs m2 (Dx + 8 * Z.of_nat (bn_top bx)) (wlimbs (skipn (bn_top bx) (bn_buf bx)))).
      { eapply u64arr_transport; [exact U2| exact MUc| exact WMc|]. cbn [disjoint_from]. unfold BnHeapA.ACEIL in *. clear - LU2 DxC TOPZ CEIL LO'. lia. }
      pose proof (wr_at_transport bgasegs m1 m2 _ _ WR1 WMc) as WR2.

      set (nb := splice (bn_buf bx) 0 l).
      assert (Enb : nb = l ++ skipn (bn_top bx) (bn_buf bx)) by (subst nb; unfold splice; rewrite firstn_O, LENl; reflexivity).
      assert (Lnb : length nb = bn_dmax bx) by (subst nb; rewrite splice_length; [exact LBX| rewrite LENl, LBX; clear - OKx2; lia]).
      assert (LMnb : limbs nb) by (subst nb; apply splice_limbs; [exact OKx1| exact Ll]).
      assert (UF : u64arr bgasegs m2 Dx (wlimbs nb)).
      { rewrite Enb. apply limbarr_app. rewrite LENl. split; [| exact U22]. apply u64arr_of_limbs_at; [exact RES| rewrite LENl; exact WR2]. }
      assert (MUT : munch [(bv_unsigned sp + -80 - 80, bv_unsigned sp + -80); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]%Z m1 m2).
      { eapply munch_weaken; [|exact MUc]. unfold sub_fp. intros x Hx. cbn [outside] in *. clear - Hx TOPZ. lia. }
      assert (HWLT : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -80 - 80, bv_unsigned sp + -80); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]).
      { constructor; [left; cbn; clear - LO'; lia|]. constructor; [| constructor]. right; left; exists (px, Dx, 8 * Z.of_nat (bn_dmax bx)); cbn; split; [exact Hinpx| clear; lia]. }
      assert (WOKc : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) [rx]) [(bv_unsigned sp + -80 - 80, bv_unsigned sp + -80); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]).
      { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; clear - CEIL LO'; lia|]. constructor; [| constructor].
        eapply (w_limbs OW LB ls PL EA (bv_unsigned sp) false [rx] _ rx px Dx); [left; reflexivity| exact HVx| exact Edx| exact Hinpx| cbn [fst snd]; fold bx; clear; lia| cbn [fst snd]; fold bx; clear; lia]. }
      set (ls2 := setbn rx (mul_word_lo bx w) ls).
      assert (EBL : length (bn_blocks (mul_word_lo bx w)) = length (bn_blocks bx)).
      { unfold bn_blocks, bn_dmax, mul_word_lo, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_mul_word.mul_word_lo, bn_with_buf. cbn [bn_d bn_buf]. rewrite EMW. cbn [fst]. destruct (bn_d bx); reflexivity. }
      assert (EV2 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -80) s0 ra (Some ras) MC Σ ls OW m
                      [CB 8 jfr; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] 0 Σ ls2 m2 OW).
      { subst ls2. apply cenv_setbnA; [| exact HVx | exact EBL].
        eapply cenv_silentA; [exact EV | exact LS1 | exact MUT | exact WMc | exact HWLT | exact STc | exact MIc | exact FR2 | exact FSZ1]. }
      assert (LS2 : lib_state ls2 m2 OW PL EA).
      { unfold lib_state. eapply (lib_state_close [] ls m2 OW PL EA rx ax); [| exact ND| exact HAx| exact NROx| | |].
        - eapply (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP); [exact HEAP1 | exact LSH | exact MUT | exact WMc | exact FROK | exact WOKc].
        - exists Dx. split.
          + unfold bn_cells, BnRepDefs.bn_cells, bn_dmax, mul_word_lo, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_mul_word.mul_word_lo, bn_with_buf, MallocRep.wz. cbn [bn_top bn_buf bn_neg bn_flags bn_d]. rewrite EMW. cbn [fst]. fold nb. rewrite Lnb. exact BNx2.
          + apply (fun ARRnb__ => bn_arr_of_nofr PL rx m2 OW Dx _ PWF NOFR NROx ARRnb__ ltac:(solve_nbuf)). unfold BnRepDefs.bn_arr, bn_dmax, mul_word_lo, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_mul_word.mul_word_lo, bn_with_buf. cbn [bn_d bn_buf]. rewrite EMW. cbn [fst]. fold nb. rewrite Edx, Lnb. split; [exact Hinpx| exact UF].
        - unfold bg_ok, bn_dmax, mul_word_lo, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_mul_word.mul_word_lo, bn_with_buf. cbn [bn_buf bn_top bn_flags]. rewrite EMW. cbn [fst]. fold nb. rewrite Lnb. unfold BG_DMAX in *.
          split; [exact LMnb|]. split; [exact OKx2|]. split; [clear - OKx3; unfold bn_dmax in *; lia| exact OKx4].
        - apply ids_ok_setbn_same; [exact IDS| exact HVx|]. unfold bn_blocks, bn_dmax, mul_word_lo, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_mul_word.mul_word_lo, bn_with_buf. cbn [bn_d bn_buf]. rewrite EMW. cbn [fst]. fold nb. rewrite Lnb. reflexivity. }
      assert (Els2 : setbn rx (bn_with_buf bx (splice (bn_buf bx) 0 l)) ls = ls2) by (subst ls2; unfold mul_word_lo, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_mul_word.mul_word_lo; rewrite EMW; reflexivity).
      rewrite Els2.
      assert (RST2 : refs_stable ls OW ls2 OW) by (apply refs_stable_setbn).
      pose proof (ref_at_stable _ _ _ _ _ _ _ RST2 HAx) as HAx2.
      pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAx2) as HVx2.
      assert (ETOP2 : bn_top (getbn rx ls2) = bn_top bx) by (subst ls2; rewrite getbn_setbn_same by exact HVx; reflexivity).
      pose proof EV2 as (OK2 & HEAP2 & _).
      destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP2 LS2 NOFR HAx2 NROx) as (ACX2 & _ & _).
      clear U1 U2 U22 WR1 WR2 RA1 RES UF LSH MUT HWLT WOKc MUc WMc ACX ACDX MU1 Ux ARRx ARRo BNx FR1 ST1 MI1 HEAP1 LS1 EV OK SHB1 SHB2 LENx DxI DSEPx.
      pose proof (munch_refl (@nil (Z * Z)) m2) as MU2.
      destruct (AH_shb _ _ _ _ HEAP2) as (SHB1 & SHB2).
      step. if_cases KL; zify_cond KL.
      *
        assert (EL : ll = 0) by (rewrite ?unsigned_lit in KL by (clear - Lll; lia); clear - KL; lia).
        replace (ll =? 0) with true by (symmetry; apply Z.eqb_eq; exact EL).
        apply evt_done.
        eapply (EPI Σ ls2 m2 OW 0); [exact EV2 | exact LS2 | unfold MC; clear; lia | intros q0 A0 n0 Hq0 _; exact Hq0].
      *
        assert (NL : ll <> 0) by (rewrite ?unsigned_lit in KL by (clear - Lll; lia); clear - KL; lia).
        replace (ll =? 0) with false by (symmetry; apply Z.eqb_neq; exact NL).
        step. shl_with ACX2 ALX. chk0.
        step. rewrite (sx32_small (Z.of_nat (bn_top bx))) by (clear - TOPZ; lia).
        do 3 step.
        clear BNx2 ACX2 MU2 SHB1 SHB2.
        apply evt_done.
        eapply implA_bind.
        { eapply (bn_wexpand_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (r := rx) (a := ax) (words := (bn_top bx + 1)%nat) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
            [| | | reflexivity | exact HAx2 | exact WRx | reflexivity
             | unfold MallocRep.wz; f_equal; rewrite ?(unsigned_lit (Z.of_nat (bn_top bx))) by (clear - TOPZ; lia); rewrite ?bn_swrap32_small by (clear - TOPZ; lia); clear; lia
             | clear - TOPZ; lia].
          - eapply cenv_preA; [exact EV2 | exact LS2 | unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO'; lia | clear; lia].
          - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV2).
          - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ (E_BN_mul_word_235a8c : uk_call BN_MUL_WORD 0x235c74 BN_WEXPAND) CTX). }
        cbv beta. intros [u ls3] Σ3 ms3 PO.
        apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -80) MC Σ ls OW) in PO; [| exact OK2 | exact HEAP2].
        cbn [fst snd] in *.
        destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F3 & fc3 & m4 & OW4 & PL4 & -> & CP & (EPL & -> & HDM & WRES & BST4)).
        subst PL4. specialize (CP eq_refl).
        assert (E3 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -80) s0 ra (Some ras) MC Σ ls OW m
                       [CB 8 jfr; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] (0 + MC) Σ3 ls3 m4 OW4 /\ lib_state ls3 m4 OW4 PL EA)
          by (eapply cenv_postA; [exact EV2 | exact CP]).
        destruct E3 as (EV3 & LS4).
        pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP) as RST4.
        rewrite (ret_pc_even 2317428) by (clear; lia).
        pose proof (ref_at_stable _ _ _ _ _ _ _ RST4 HAx2) as HAx4.
        assert (ETX : bn_top (getbn rx ls3) = bn_top bx) by (rewrite <- ETOP2; apply (wexpand_keeps_topA rx (bn_top bx + 1) ls2 ls3 rx WRES HVx2)).
        clear CP EV2 LS2 HEAP2 OK2 WRES.
        unfold bbind, bget, bset, bret. cbn [bind ret tree_ops tbind fst snd].

        pose proof EV3 as (OK3 & HEAP4 & ST4 & MI4 & _ & _ & _ & _ & FR4 & FSZ4 & _). cbn [app] in FR4.
        pose proof (AH_nodup_l _ _ _ _ HEAP4) as ND4.
        pose proof (AH_ceil _ _ _ _ HEAP4) as (C1' & C2' & C3'). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
        pose proof (lib_state_h_parts _ _ _ _ _ _ LS4) as PARTS4; pose proof PARTS4 as (WFS4 & PWF4 & IDS4 & PLB4 & ERRB4).
        pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS4 HAx4) as HVx4.
        destruct (lib_state_open [] ls3 m4 OW4 PL EA rx ax LS4 ND4 HAx4 ltac:(intros []) NROx) as ((Dr & BNr & ARRr) & (OKq1 & OKq2 & OKq3 & OKq4) & LSH4).
        destruct (bn_arr_facts_w ls3 OW4 PL EA (bv_unsigned sp) USTACK_TOP Σ3 LB m4 rx Dr HEAP4 PARTS4 FROK HVx4 WRx ARRr) as (Ur & LENr & Dr0 & DrC & DrI & DSEPr).
        set (br := getbn rx ls3) in *.
        pose proof (DSEPr rx ax HAx4) as SEPrr. fold br in SEPrr.
        destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP4 PARTS4 NOFR HAx4 NROx) as (qr4 & Ar4 & nr4 & Hinr4 & Rr41 & Rr42).
        destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP4 LS4 NOFR HAx4 NROx) as (ACR & ALR & OFR).
        pose proof ARRr as ARRq. apply (fun ARRnb__ => bn_arr_nofr PL rx m4 OW4 Dr _ PWF4 NOFR NROx ARRnb__ ltac:(solve_nbuf)) in ARRq.
        destruct (arr_shA _ _ _ _ _ _ HEAP4 ARRq) as (ACDR & ALDR & OFDR). fold br in ACDR, OFDR.
        unfold bn_cells, BnRepDefs.bn_cells in BNr. unfold BG_DMAX in OKq3. unfold MallocRep.wz in *. unfold SHLO, SHHI in *. rewrite ETX in BNr.
        assert (HDr : exists pr, bn_d br = Some pr /\ In (pr, Dr, 8 * Z.of_nat (bn_dmax br)) OW4).
        { unfold BnRepDefs.bn_arr in ARRq. fold br in ARRq. destruct (bn_d br) as [pr|]; [exists pr; split; [reflexivity| exact (proj1 ARRq)]|].
          exfalso. destruct ARRq as [_ E]. unfold bn_dmax in HDM. fold br in HDM. rewrite E in HDM. cbn in HDM. clear - HDM. lia. }
        destruct HDr as (pr & Edr & Hinpr).
        assert (LBR : length (bn_buf br) = bn_dmax br) by reflexivity.
        fold br in HDM.
        pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m4) as MU5.
        pose proof (wmono_refl bgasegs m4) as WM5.
        assert (OFF5 : offshW [(bv_unsigned sp + -80, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
        { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. clear - OFR OFDR SPR LO' CEIL C1' C2' C3'. lia. }
        assert (BDR : 0 <= Dr /\ Dr + 8 * Z.of_nat (bn_dmax br) <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - Dr0 DrC C1' C2' C3'; lia).
        assert (HDMZ : Z.of_nat (bn_top bx) + 1 <= Z.of_nat (bn_dmax br)) by (clear - HDM; lia).
        assert (LENW : Z.of_nat (length (wlimbs (bn_buf br))) = Z.of_nat (bn_dmax br)) by (rewrite wlimbs_len; reflexivity).
        destruct (AH_shb _ _ _ _ HEAP4) as (SHB1 & SHB2).
        clear DSEPr DrI OFR OFDR SEPxx DxC Dx0' BDX Hinpx Edx Rx1 Rx2 Hinx LU2 Lnb LMnb Enb EDx.
        apply implA_from_evt.
        zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by (clear - X0 XC C1 C2 C3; unfold BnHeapA.ACEIL in *; lia). clear - KZ X0. lia. }
        clear KZ.

        shl_with ACR ALR. chk0.
        shl_with ACR ALR. step. chk0.
        step. rewrite (sx32_small (Z.of_nat (bn_top bx))) by (clear - TOPZ; lia).
        step. step.
        step. replace (Z.of_nat (bn_top bx) + 1) with (Z.of_nat (bn_top bx + 1)) in BNr by (clear; lia).
        step. setreg 10%Z (Z_to_bv 64 (Dr + 8 * Z.of_nat (bn_top bx))) ltac:(f_equal; rewrite (unsigned_lit (Z.of_nat (bn_top bx))) by (clear - TOPZ; lia); rewrite Z.shiftl_mul_pow2 by (clear; lia); clear; lia).
        do 2 step. shl_limb ACDR ALDR BDR (Z.of_nat (bn_top bx)). chk0.
        assert (IDX : 0 <= Z.of_nat (bn_top bx) < Z.of_nat (length (wlimbs (bn_buf br)))) by (rewrite wlimbs_len, LBR; clear - HDMZ; lia).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          pose proof (u64arr_store_ok bgasegs mx Dr _ (Z.of_nat (bn_top bx)) (wa (Dr + 8 * Z.of_nat (bn_top bx))) ltac:(eassumption) IDX eq_refl) as SOKW;
          pose proof (u64arr_write bgasegs mx Dr _ (Z.of_nat (bn_top bx)) (Z_to_bv 64 ll) ltac:(eassumption) IDX) as U6 end.
        rewrite Nat2Z.id, (wlimbs_upd (bn_buf br) (bn_top bx)) in U6 by (rewrite LBR; clear - HDM; lia).
        clear Ur. step. store_done.
        step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
        apply evt_done.
        set (nb2 := upd (bn_buf br) (bn_top bx) ll) in *.
        assert (Lnb2 : length nb2 = bn_dmax br) by (subst nb2; rewrite upd_length by (rewrite LBR; clear - HDM; lia); exact LBR).
        assert (LMnb2 : limbs nb2) by (subst nb2; apply upd_limbs; [exact OKq1| unfold limb, BW; exact Lll]).
        assert (HWL5 : Forall (w_lib ls3 OW4 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -80, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
        { constructor; [left; cbn; clear - LO'; lia|]. constructor; [w_lib_ref HAx4 NROx|].
          constructor; [right; left; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn [blk_addr blk_size fst snd]; split; [exact Hinpr| clear; lia]| constructor]. }
        assert (WOK5 : Forall (w_ok OW4 LB ls3 PL EA (bv_unsigned sp) [rx]) [(bv_unsigned sp + -80, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
        { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; clear - LO' CEIL; lia|].
          constructor; [eapply (w_struct OW4 LB ls3 PL EA (bv_unsigned sp) false [rx] _ rx ax); [left; reflexivity| exact HAx4| exact NROx| cbn; clear; lia| cbn; clear; lia]|].
          constructor; [eapply (w_limbs OW4 LB ls3 PL EA (bv_unsigned sp) false [rx] _ rx pr Dr); [left; reflexivity| exact HVx4| exact Edr| exact Hinpr| cbn [fst snd]; clear; lia| cbn [fst snd]; fold br; clear; lia]| constructor]. }
        change (mkBN (bn_d br) (upd (bn_buf br) (bn_top bx) ll) (bn_top bx + 1) (bn_neg br) (bn_flags br)) with (mul_word_hi br (bn_top bx) ll).
        assert (EBL5 : length (bn_blocks (mul_word_hi br (bn_top bx) ll)) = length (bn_blocks (getbn rx ls3))).
        { fold br. unfold bn_blocks, bn_dmax, mul_word_hi, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_mul_word.mul_word_hi. cbn [bn_d bn_buf]. rewrite Edr. reflexivity. }
        eapply (EPI Σ3 (setbn rx (mul_word_hi br (bn_top bx) ll) ls3) m6 OW4 (0 + MC));
          [ apply cenv_setbnA; [| exact HVx4 | exact EBL5];
            eapply cenv_silentA; [exact EV3 | exact LS4 | exact MU5 | exact WM5 | exact HWL5 | assumption | assumption | cbn [app]; eassumption | exact FSZ4]
          | | clear; lia
          | intros q0 A0 n0 Hq0 Hne; apply BST4; [exact Hq0|]; subst ls2; rewrite getbn_setbn_same by exact HVx;
            unfold mul_word_lo, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_mul_word.mul_word_lo, bn_with_buf; cbn [bn_d]; exact Hne ].
        unfold lib_state. eapply (lib_state_close [] ls3 m6 OW4 PL EA rx ax); [| exact ND4| exact HAx4| exact NROx| | |].
        -- eapply (lib_state_frame Σ3 LB (bv_unsigned sp) USTACK_TOP); [exact HEAP4| exact LSH4| exact MU5| exact WM5| exact FROK| exact WOK5].
        -- exists Dr. split.
           ++ unfold bn_cells, BnRepDefs.bn_cells, bn_dmax, mul_word_hi, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_mul_word.mul_word_hi, MallocRep.wz. cbn [bn_top bn_buf bn_neg bn_flags bn_d]. fold nb2. rewrite Lnb2. exact BNr.
           ++ apply (fun ARRnb__ => bn_arr_of_nofr PL rx m6 OW4 Dr _ PWF4 NOFR NROx ARRnb__ ltac:(solve_nbuf)). unfold BnRepDefs.bn_arr, bn_dmax, mul_word_hi, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_mul_word.mul_word_hi. cbn [bn_d bn_buf]. fold nb2. rewrite Edr, Lnb2. split; [exact Hinpr| exact U6].
        -- unfold bg_ok, bn_dmax, mul_word_hi, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_mul_word.mul_word_hi. cbn [bn_buf bn_top bn_flags]. fold nb2. rewrite Lnb2. unfold BG_DMAX in *.
           split; [exact LMnb2|]. split; [clear - HDM; lia|]. split; [clear - OKq3; unfold bn_dmax in *; lia| exact OKq4].
        -- apply ids_ok_setbn_same; [exact IDS4| exact HVx4|]. unfold bn_blocks, bn_dmax, mul_word_hi, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_mul_word.mul_word_hi. cbn [bn_d bn_buf]. fold nb2. rewrite Lnb2. reflexivity.
Qed.

End WithRT.
