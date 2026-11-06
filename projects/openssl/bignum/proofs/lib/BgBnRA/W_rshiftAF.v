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
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AW_lshift_arr AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR Require W_lshift W_rshift.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import BnAKitAF BnCallAF W_expandAF AShiftArr ARShiftArr ShiftKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BN_RSHIFT : Z := 0x234780.
Definition BN_RSHIFT_STACK : Z := 64 + BN_WEXPAND_STACK.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_rs_wexpand := (E_bn_rshift_fixed_top_234618 : uk_call BN_RSHIFT 0x234800 BN_WEXPAND).

Local Notation rshift_rest := OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_rshift.rshift_rest.

Lemma bn_rshift_fixed_top_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (rr rx : bnref) (ar ax : Z) (n : Z),
  bn_preA Σ ls m OW LB PL EA sp lo BN_RSHIFT_STACK MC ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_RSHIFT (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> ref_at ls OW PL rr ar -> hpl PL rr -> ref_at ls OW PL rx ax -> rx <> ROne -> nbuf PL rx ->
  a0 = wz ar -> a1 = wz ax -> a2 = wz n -> 0 <= n < 2^30 ->
  implA (bn_rshift_fixed_top (tree_ops bptr) rr rx n ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC (shift_res rr ls OW PL))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_RSHIFT) fc None m (seg_rom bgasegs)).
Proof.
  intros until n. intros PRE UW CTX -> HAr HP HAx NROx NBx -> -> -> Hn.
  pose proof (proj1 (hpl_wref PL rr HP) : not_one rr) as NRO. change (not_one rx) in NROx.
  pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  pose proof LO as LO'. unfold BN_RSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO'.
  unfold BN_RSHIFT, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  set (nw := Z.to_nat (n / 64)). set (rb := n mod 64).
  assert (Hnw : 0 <= n / 64 < 2^24). { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  assert (Enw : Z.of_nat nw = n / 64) by (subst nw; apply Z2Nat.id; lia).
  assert (Hrb : 0 <= rb < 64) by (subst rb; apply Z.mod_pos_bound; lia).

  destruct (open_ro_sh Σ OW LB m ls PL EA _ rx ax HEAP LS FROK NOFR HAx NROx) as (Dx & BNx & (OKx1 & OKx2 & OKx3 & OKx4) & _ & X0 & XC & _ & _ & ACX & ALX & _ & _).
  set (topx := bn_top (getbn rx ls)) in *.
  unfold bn_cells, BnRepDefs.bn_cells, MallocRep.wz in BNx. unfold BN_WORDS_MAX, BG_DMAX in OKx3.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 64, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  apply implA_from_evt.
  carve_frame 64%nat ST.
  do 10 step. do 4 step. do 4 step. shl_with ACX ALX. step. chk0.
  zstep.
  step. rewrite (sx32_small (Z.of_nat topx)) by (unfold bn_dmax in *; lia).
  do 3 zstep.
  setreg 22%Z (Z_to_bv 64 (Z.of_nat nw)) ltac:(rewrite Enw; f_equal; symmetry; apply (OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_lshift.nw_m_eq n); lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -64, bv_unsigned sp)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
  assert (EV : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MC Σ ls OW m
                 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] 0 Σ ls m1 OW).
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
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAr) as HVr. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAx) as HVx.
  zstep. if_cases KT; zify_cond KT; rewrite !OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_rshift.signed_lit63 in KT by (clear - Hnw Enw OKx2 OKx3; unfold bn_dmax in *; lia).
  -
    apply evt_done.
    rewrite (OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_rshift.rshift_eq_zero rr rx n ls) by (fold topx nw; clear - KT Hn; lia).
    unfold BN_zero, bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
    apply implA_ret_evt.

    pose proof EV as (_ & _ & ST1 & MI1 & AXP1 & _ & _ & _ & FR1 & _ & _). cbn [app] in FR1.
    destruct (lib_state_open [] ls m1 OW PL EA rr ar LS1 ND HAr ltac:(intros []) NRO) as ((Dr & BNr & ARRr) & OKR' & LSH).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP1 LS1 NOFR HAr NRO) as (ACR & ALR & OFR).
    destruct (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP1 PARTS HAr HP) as (SA0 & SAC & SAI & (qr & Ar & nr & Hinr & Rr1 & Rr2)).
    destruct (bn_arr_facts_w ls OW PL EA (bv_unsigned sp) USTACK_TOP Σ LB m1 rr Dr HEAP1 PARTS FROK HVr (hpl_wref PL rr HP) ARRr) as (Ur & LENr & Dr0 & DrC & DrI & DSEPr).
    pose proof (DSEPr rr ar HAr) as SEPrr.
    set (br := getbn rr ls) in *.
    unfold bn_cells, BnRepDefs.bn_cells in BNr.
    clear BNx ST MI FR.
    do 2 step.
    eapply evt_cut.
    { eapply (BN_zero_ex_specA (Z_to_bv 64 2312424) (Z_to_bv 64 (bv_unsigned sp + -64))) with (lo := lo) (A := ar) (D := Dr) (b := br);
        [exact BNr | rewrite ESP; exact ST1 | rewrite ESP; clear - LO'; lia | exact MI1 | rewrite ESP; unfold BnHeapA.ACEIL in *; clear - SAC CEIL LO'; lia
        | exact (AH_shb _ _ _ _ HEAP1) | exact ACR | exact ALR | unfold SHHI, BnHeapA.ACEIL in *; clear - CEIL C1 C2 C3; lia | exact OFR | reflexivity]. }
    intros ms' PO. unfold bn_small_postA in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & STc & BNr2).
    subst ms'. rewrite ESP in *.
    rewrite (ret_pc_even 2312424) by (clear; lia).
    eapply (rw_cells_transport bgasegs _ m1 m2) in FR1; [| exact MUc | exact WMc | cbn; unfold BnHeapA.ACEIL in *; clear - SAC CEIL LO'; lia].
    eapply (u64arr_transport bgasegs _ m1 m2) in Ur; [| exact MUc | exact WMc | cbn [disjoint_from]; rewrite wlimbs_len; unfold bn_dmax, BnHeapA.ACEIL in *; clear - SEPrr DrC CEIL LO'; lia].
    clear ST1 MI1 BNr.
    step. step.
    do 8 step. release_frame FR1 STc (bv_unsigned sp). step. step.
    apply evt_done.
    assert (HWLc : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64 - 16, bv_unsigned sp + -64); (ar, ar + 24)]).
    { constructor; [left; cbn; clear - LO'; lia|]. constructor; [right; left; exists (qr, Ar, nr); cbn [blk_addr blk_size fst snd]; split; [exact Hinr | clear - Rr1 Rr2; lia]| constructor]. }
    assert (WOKc : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) [rr]) [(bv_unsigned sp + -64 - 16, bv_unsigned sp + -64); (ar, ar + 24)]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; clear - LO' CEIL; lia|].
      constructor; [eapply (w_struct OW LB ls PL EA (bv_unsigned sp) false [rr] _ rr ar); [left; reflexivity| exact HAr| exact NRO| cbn; clear; lia| cbn; clear; lia]| constructor]. }
    pose proof PARTS as (WFS0 & PWF0 & IDS0 & _).
    unfold bn_postA. do 17 eexists. exists m2, OW, PL. split; [reflexivity|]. cbn [fst snd].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP1 PARTS FROK MUc WMc HWLc CEIL ltac:(unfold USTACK_TOP; clear - SPT; lia))|].
    split.
    { unfold lib_state. eapply (lib_state_close [] ls m2 OW PL EA rr ar); [| exact ND| exact HAr| exact NRO| | |].
      - exact (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [rr] ls m1 m2 OW PL EA _ HEAP1 LSH MUc WMc FROK WOKc).
      - exists Dr. split; [exact BNr2|]. unfold bn_zero_pure. eapply bn_arr_of_u64arr; [exact ARRr|]. cbn [bn_buf]. exact Ur.
      - pose proof OKR' as (OKq1 & OKq2 & OKq3 & OKq4). unfold bg_ok, bn_zero_pure, bn_dmax in *. cbn [bn_buf bn_top bn_flags]. split; [exact OKq1|]. split; [clear; lia|]. split; [exact OKq3| exact OKq4].
      - apply ids_ok_setbn_same; [exact IDS0| exact HVr| reflexivity]. }
    split; [exact STc|]. split; [exact MIc|].
    split; [eapply ax_pres_trans; [exact AXP1|]; exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP1 PARTS FROK MUc HWLc CEIL ltac:(clear - LO'; lia))|].
    split; [unfold MC; clear - CRED; lia|].
    split. { unfold cnt_eq. rewrite (cnt_bal_setbn rr _ ls OW OW HVr). fold br. unfold bn_blocks, bn_zero_pure. cbn [bn_d]. destruct (bn_d br); cbn [length]; clear; lia. }
    split. { apply refs_stable_setbn. }
    unfold shift_res. split; [reflexivity|]. split; [reflexivity| intros q0 A0 n0 Hq0 _; exact Hq0].
  -
    assert (NTOP : (nw < topx)%nat) by (clear - KT; lia).
    set (top' := (topx - nw)%nat).
    assert (Etop' : Z.of_nat top' = Z.of_nat topx - Z.of_nat nw) by (subst top'; clear - NTOP; lia).

    assert (COMMON : forall (Σ1 : rts RT) (ls1 : bstate bptr) (m2 : mem) (OW2 : list block) (used : Z) (FT : bvmap 5 word) (fcT : bv 32)
                       (q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word),
        cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MC Σ ls OW m
              [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] used Σ1 ls1 m2 OW2 ->
        lib_state ls1 m2 OW2 PL EA -> used <= MC ->
        (forall q A n, In (q, A, n) OW -> bn_d (getbn rr ls) <> Some q -> In (q, A, n) OW2) ->
        ref_at ls1 OW2 PL rr ar -> ref_at ls1 OW2 PL rx ax ->
        bn_top (getbn rx ls1) = topx -> (top' <= bn_dmax (getbn rr ls1))%nat ->
        implA (rshift_rest rr rx nw top' rb ls1) Σ1
          (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC (shift_res rr ls OW PL))
          (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 TP_A) q5 q6 q7 sp (Z_to_bv 64 ar) q10 q11 q12 q13 q14 q15 q16 q17
                   (Z_to_bv 64 (Z.of_nat top')) (Z_to_bv 64 ax) (Z_to_bv 64 n) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.of_nat nw)) s7 s8 s9 s10 s11 q28 q29 q30 q31)
              FT (Z_to_bv 64 0x234804) fcT None m2 (seg_rom bgasegs))).
    { intros Σ1 ls1 m2 OW2 used FT fcT q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 EV1 LS2 USED BST HAr2 HAx2 ETX HDM.
      clear BNx MU WM ST MI FR HWL WOK LS1 HEAP1 EV OK KT ACX OFF SHB1 SHB2 HEAP LS PARTS PRE UW ND HVr HVx C1 C2 C3.
      pose proof EV1 as (OK1 & HEAP2 & ST2 & MI2 & AXP2 & CR2 & CNT2 & RS2 & FR2 & FSZ2 & UW2).
      cbn [app] in FR2.
      pose proof (AH_nodup_l _ _ _ _ HEAP2) as ND2.
      pose proof (AH_ceil _ _ _ _ HEAP2) as (C1' & C2' & C3'). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
      pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS1; pose proof PARTS1 as (WFS1 & PWF1 & IDS1 & PLB1 & ERRB1).
      pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAr2) as HVr2. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAx2) as HVx2.

      destruct (lib_state_open [] ls1 m2 OW2 PL EA rr ar LS2 ND2 HAr2 ltac:(intros []) NRO) as ((Dr & BNr & ARRr) & OKR' & LSH).
      pose proof OKR' as (OKq1 & OKq2 & OKq3 & OKq4). unfold BG_DMAX in OKq3.
      destruct (bn_arr_facts_w ls1 OW2 PL EA (bv_unsigned sp) USTACK_TOP Σ1 LB m2 rr Dr HEAP2 PARTS1 FROK HVr2 (hpl_wref PL rr HP) ARRr) as (Ur & LENr & Dr0 & DrC & DrI & DSEPr).
      destruct (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 HAr2 HP) as (SA0 & SAC & SAI & (qr2 & Ar2 & nr2 & Hinr2 & Rr21 & Rr22)).
      destruct (operand_cellsA Σ1 OW2 LB m2 ls1 PL EA (bv_unsigned sp) USTACK_TOP rr ar Dr rx ax topx HEAP2 LS2 FROK NOFR HAr2 HP BNr ARRr HAx2 NROx ltac:(rewrite ETX; apply Nat.le_refl) ltac:(solve_nbuf))
        as (Dx2 & ARRxo & BNx2 & OKX & LAx & X0' & XC' & DX0 & DXC & SXR & SRX & ALXD & SXD & DX8).
      set (br := getbn rr ls1) in *. set (bx := getbn rx ls1) in *.
      pose proof OKX as (OKy1 & OKy2 & OKy3 & OKy4). unfold BG_DMAX in OKy3.

      set (f := slice (bn_buf bx) nw top') in *.
      assert (Lf : length f = top').
      { subst f. unfold slice. apply firstn_length_le. rewrite length_skipn. clear - OKy2 ETX NTOP. unfold bn_dmax in OKy2. subst top'. lia. }
      assert (EFX : firstn topx (bn_buf bx) = firstn nw (bn_buf bx) ++ f).
      { subst f. unfold slice. rewrite <- (firstn_skipn nw (firstn topx (bn_buf bx))). f_equal.
        - rewrite firstn_firstn. f_equal. clear - NTOP. lia.
        - rewrite skipn_firstn_comm. reflexivity. }
      assert (HLF : limbs_at bgasegs m2 (Dx2 + 8 * Z.of_nat nw) f).
      { rewrite EFX in LAx. apply limbs_at_app in LAx. destruct LAx as [_ H2].
        rewrite firstn_length_le in H2 by (clear - OKy2 ETX NTOP; unfold bn_dmax in OKy2; lia). exact H2. }
      pose proof (DSEPr rr ar HAr2) as SEPrr. fold br in SEPrr.
      destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP2 LS2 NOFR HAr2 NRO) as (ACR & ALR & OFR).
      destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP2 LS2 NOFR HAx2 NROx) as (ACX2 & ALX2 & _).
      pose proof ARRr as ARRo. apply (fun ARRnb__ => bn_arr_nofr PL rr m2 OW2 Dr _ PWF1 NOFR NRO ARRnb__ ltac:(solve_nbuf)) in ARRo.
      destruct (arr_shA _ _ _ _ _ _ HEAP2 ARRo) as (ACDR & ALDR & OFDR). fold br in ACDR, OFDR.
      destruct (arr_shA _ _ _ _ _ _ HEAP2 ARRxo) as (ACDX & ALDX & _). fold bx in ACDX.
      pose proof (arr_ceilA _ _ _ _ _ _ HEAP2 ARRxo) as (_ & DXC47). fold bx in DXC47.
      unfold bn_cells, BnRepDefs.bn_cells in BNx2, BNr. unfold MallocRep.wz in *. unfold SHLO, SHHI in *.
      rewrite ETX in BNx2.

      assert (HDr : exists pr, bn_d br = Some pr /\ In (pr, Dr, 8 * Z.of_nat (bn_dmax br)) OW2).
      { unfold BnRepDefs.bn_arr in ARRo. fold br in ARRo. destruct (bn_d br) as [pr|]; [exists pr; split; [reflexivity| exact (proj1 ARRo)]|].
        exfalso. destruct ARRo as [_ E]. unfold bn_dmax in HDM. fold br in HDM. rewrite E in HDM. cbn in HDM. clear - HDM NTOP. subst top'. lia. }
      destruct HDr as (pr & Edr & Hinpr).
      assert (LBr : length (bn_buf br) = bn_dmax br) by reflexivity.
      fold br in HDM.
      rewrite (OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_rshift.rshift_rest_eq rr rx nw top' rb ls1). fold br bx f.
      apply implA_ret_evt.
      destruct (proj1 (limbarr_split bgasegs m2 Dr (bn_buf br) top' ltac:(rewrite LBr; exact HDM)) Ur) as (Ulo & Uhi).
      destruct (proj1 (limbarr_limbs_at bgasegs m2 _ _) Ulo) as (_ & WRlo).
      rewrite firstn_length_le in WRlo by (rewrite LBr; exact HDM). rewrite <- Lf in WRlo.
      clear Ulo Ur.
      pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m2) as MU3.
      pose proof (wmono_refl bgasegs m2) as WM3.
      assert (OFF3 : offshW [(bv_unsigned sp + -64, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
      { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. clear - OFR OFDR SPR LO' CEIL C1' C2' C3'. lia. }
      assert (LfZ : Z.of_nat (length f) = Z.of_nat top') by (rewrite Lf; reflexivity).
      assert (HDMZ : Z.of_nat top' <= Z.of_nat (bn_dmax br)) by (clear - HDM; lia).
      assert (LUhi : Z.of_nat (length (wlimbs (skipn top' (bn_buf br)))) = Z.of_nat (bn_dmax br) - Z.of_nat top') by (rewrite wlimbs_len, length_skipn, LBr; clear - HDM; lia).
      assert (NWX : Z.of_nat nw < Z.of_nat topx /\ Z.of_nat topx <= Z.of_nat (bn_dmax bx)) by (clear - NTOP OKy2 ETX; unfold bn_dmax in *; lia).
      assert (BDX : 0 <= Dx2 /\ Dx2 + 8 * Z.of_nat (bn_dmax bx) <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - DX0 DXC47 C1' C2' C3'; lia).
      do 2 step. shl_with ACR ALR. chk0.
      do 2 step. shl_with ACX2 ALX2. chk0.
      step. zstep.
      replace (Z.of_nat nw ≪ 3) with (8 * Z.of_nat nw) by (rewrite Z.shiftl_mul_pow2 by (clear; lia); clear; lia).
      zstep.
      do 2 step. shl_limb ACDX ALDX BDX (Z.of_nat nw). chk0. step.
      replace (Z.of_nat top') with (Z.of_nat (length f)) by exact LfZ.
      assert (HN31 : 0 <= n < 2147483648) by (clear - Hn; lia).
      assert (ERB : Z.land n 63 = rb) by (subst rb; change 63 with (Z.ones 6); apply Z.land_ones; clear; lia).
      assert (LMf : limbs f) by (subst f; unfold slice; apply limbs_firstn; apply limbs_skipn; exact OKy1).
      assert (HTOP : 1 <= Z.of_nat (length f) < 2147483647) by (clear - LfZ Etop' NTOP OKy2 OKy3 ETX; unfold bn_dmax in *; lia).
      assert (DISJ : Dr <= Dx2 + 8 * Z.of_nat nw \/ Dx2 + 8 * Z.of_nat nw + 8 * Z.of_nat (length f) <= Dr) by (clear - ALXD HDMZ LfZ Etop'; lia).
      eapply (rshg_blockA _ _ _ _ _ _ (Z_to_bv 64 ax) _ _ _ _ _ _ _ _ _ _ _ m2 f (Dx2 + 8 * Z.of_nat nw) Dr n rb).
      { exact HN31. }
      { exact Hrb. }
      { exact ERB. }
      { exact LMf. }
      { exact HTOP. }
      { exact DISJ. }
      { eapply acc_sub; [exact ACDX | clear; lia | clear - LfZ Etop' NWX; lia]. }
      { eapply acc_sub; [exact ACDR | clear; lia | clear - LfZ HDMZ; lia]. }
      { clear - ALDX. Z.div_mod_to_equations. lia. }
      { exact ALDR. }
      { cbn [offshW]. unfold SHLO, SHHI. clear - OFDR HDMZ Dr0 LfZ. lia. }
      { exact HLF. }
      { exact WRlo. }
      { exact MI2. }
      intros m3 z5 z6 z7 z11 z12 z14 z15 z16 z17 z28 z29 HRES MI3 MUb WMb.
      rewrite LfZ in MUb. rewrite ?LfZ. rewrite (unsigned_lit ax) by (unfold BnHeapA.ACEIL in *; clear - X0 XC C1' C2' C3'; lia).

      assert (DJW : forall A k, (A + k <= Dr \/ Dr + 8 * Z.of_nat (bn_dmax br) <= A) ->
                disjoint_from [(Dr, Dr + 8 * Z.of_nat top')] A k).
      { intros A k H. cbn [disjoint_from]. split; [|exact I]. clear - H HDMZ. lia. }
      eapply (rw_cells_transport bgasegs _ m2 m3) in BNx2; [| exact MUb | exact WMb | apply DJW; cbn; clear - SXD; lia].
      eapply (rw_cells_transport bgasegs _ m2 m3) in BNr; [| exact MUb | exact WMb | apply DJW; cbn; clear - SEPrr; lia].
      eapply (rw_cells_transport bgasegs _ m2 m3) in FR2; [| exact MUb | exact WMb | apply DJW; cbn; unfold BnHeapA.ACEIL in *; clear - DrC CEIL LO'; lia].
      eapply (stk_transport_disjoint bgasegs _ m2 m3) in ST2; [| exact MUb | exact WMb | apply DJW; unfold BnHeapA.ACEIL in *; clear - DrC CEIL LO'; lia].
      eapply (u64arr_transport bgasegs _ m2 m3) in Uhi; [| exact MUb | exact WMb | cbn [disjoint_from]; split; [|exact I]; clear; lia].
      assert (MU4 : munch [(bv_unsigned sp + -64, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m2 m3).
      { eapply munch_weaken; [|exact MUb]. unfold sub_fp. intros x Hx. cbn [outside] in *. split; [|exact I]. clear - Hx HDMZ. lia. }
      clear MU3 WM3.
      destruct (rshift_limbs_spec f rb LMf Hrb) as (RSL & RSN & _).
      assert (Ures : u64arr bgasegs m3 Dr (wlimbs (rshift_limbs f rb))).
      { apply limbarr_limbs_at. split; [rewrite rshift_limbs_seq; exact HRES| rewrite RSN; eapply wr_at_transport; [exact WRlo| exact WMb]]. }
      set (nb := splice (bn_buf br) 0 (rshift_limbs f rb)).
      assert (Lnb : length nb = bn_dmax br) by (subst nb; rewrite splice_length; [exact LBr| rewrite RSN, Lf, LBr; cbn [Nat.add]; exact HDM]).
      assert (LMnb : limbs nb) by (subst nb; apply splice_limbs; [exact OKq1| exact RSL]).
      assert (UF : u64arr bgasegs m3 Dr (wlimbs nb)).
      { subst nb. unfold splice. change (firstn 0 (bn_buf br)) with (@nil Z). cbn [app Nat.add]. rewrite RSN, Lf.
        apply limbarr_app. split; [exact Ures|]. rewrite RSN, Lf. exact Uhi. }
      assert (LENnb : Z.of_nat (length (wlimbs nb)) = Z.of_nat (bn_dmax br)) by (rewrite wlimbs_len, Lnb; reflexivity).
      clearbody nb.
      clear HRES WRlo Ures Uhi HLF MUb MI2 LAx DISJ DJW ACDX ACDR.

      clear XC' DXC SXR SRX ALXD SXD DX8 DSEPr DrI SAI OKy4 X0' DX0 OFR OFDR DXC47 BDX NWX.

      do 2 step. shl_with ACX2 ALX2. chk0.
      do 3 step. shl_with ACR ALR. step. rewrite (sx32_small (Z.b2z (bn_neg bx))) by (destruct (bn_neg bx); cbn; clear; lia). chk0.
      clear BNx2.
      step.
      do 3 step. shl_with ACR ALR. chk0.
      step. step.
      do 8 step. release_frame FR2 ST2 (bv_unsigned sp). step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mG end.
      apply evt_done.
      assert (HWL3 : Forall (w_lib ls1 OW2 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
      { constructor; [left; cbn; clear - LO'; lia|]. constructor; [right; left; exists (qr2, Ar2, nr2); cbn [blk_addr blk_size fst snd]; split; [exact Hinr2 | clear - Rr21 Rr22; lia]|].
        constructor; [right; left; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn [blk_addr blk_size fst snd]; split; [exact Hinpr| clear; lia]| constructor]. }
      assert (WOK3 : Forall (w_ok OW2 LB ls1 PL EA (bv_unsigned sp) [rr]) [(bv_unsigned sp + -64, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
      { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; clear - LO' CEIL; lia|].
        constructor; [eapply (w_struct OW2 LB ls1 PL EA (bv_unsigned sp) false [rr] _ rr ar); [left; reflexivity| exact HAr2| exact NRO| cbn; clear; lia| cbn; clear; lia]|].
        constructor; [eapply (w_limbs OW2 LB ls1 PL EA (bv_unsigned sp) false [rr] _ rr pr Dr); [left; reflexivity| exact HVr2| exact Edr| exact Hinpr| cbn [fst snd]; clear; lia| cbn [fst snd]; fold br; clear; lia]| constructor]. }
      assert (OKF : bg_ok (mkBN (bn_d br) nb top' (bn_neg bx) (bn_flags br))).
      { unfold bg_ok, bn_dmax, BG_DMAX. cbn [bn_buf bn_top bn_flags]. rewrite Lnb.
        split; [exact LMnb|]. split; [exact HDM|]. split; [clear - OKq3; unfold bn_dmax in *; lia| exact OKq4]. }
      unfold bn_postA. do 17 eexists. exists mG, OW2, PL. split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 FROK MU4 WMb HWL3 CEIL ltac:(unfold USTACK_TOP; clear - SPT; lia))|].
      split.
      { unfold lib_state. eapply (lib_state_close [] ls1 mG OW2 PL EA rr ar); [| exact ND2| exact HAr2| exact NRO| | exact OKF|].
        - eapply (lib_state_frame Σ1 LB (bv_unsigned sp) USTACK_TOP); [exact HEAP2| exact LSH| exact MU4| exact WMb| exact FROK| exact WOK3].
        - exists Dr. split.
          + unfold bn_cells, bn_dmax, MallocRep.wz. cbn [bn_top bn_buf bn_neg bn_flags]. rewrite Lnb. exact BNr.
          + apply (fun ARRnb__ => bn_arr_of_nofr PL rr mG OW2 Dr _ PWF1 NOFR NRO ARRnb__ ltac:(solve_nbuf)). unfold BnRepDefs.bn_arr, bn_dmax. cbn [bn_d bn_buf]. rewrite Edr, Lnb. split; [exact Hinpr| exact UF].
        - apply ids_ok_setbn_same; [exact IDS1| exact HVr2|]. fold br. unfold bn_blocks, bn_dmax. cbn [bn_d bn_buf]. rewrite Edr, Lnb. reflexivity. }
      split; [exact ST2|]. split; [exact MI3|].
      split; [eapply ax_pres_trans; [exact AXP2|]; exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 FROK MU4 HWL3 CEIL ltac:(clear - LO'; lia))|].
      split; [clear - CR2 USED; lia|].
      split. { unfold cnt_eq in *. rewrite (cnt_bal_setbn rr _ ls1 OW2 OW2 HVr2). fold br. rewrite CNT2.
               unfold bn_blocks, bn_dmax. cbn [bn_d bn_buf]. rewrite Edr, Lnb. cbn [length]. clear. lia. }
      split. { eapply refs_stable_trans; [exact RS2| apply refs_stable_setbn]. }
      unfold shift_res. split; [reflexivity|]. split; [reflexivity| exact BST]. }
    zstep.
    setreg 18%Z (Z_to_bv 64 (Z.of_nat top')) ltac:(f_equal; rewrite bk_swrap32_small by (clear - NTOP OKx2 OKx3 Hnw Enw; unfold bn_dmax in *; lia); clear - Etop'; lia).
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP PARTS HAr HP) as (SA0e & SACe & _).
    zstep. if_cases KE; zify_cond KE.
    +
      assert (ERX : rr = rx).
      { destruct (Nat.eq_dec rr rx) as [E|NE]; [exact E|]. exfalso.
        pose proof (struct_disj Σ OW LB m HEAP ls PL EA _ _ PARTS FROK rr rx ar ax NE HAr HAx) as SD.
        clear - KE SD. lia. }
      clear KE. subst rx.
      apply evt_done.
      rewrite (OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_rshift.rshift_eq_shift rr rr n ls) by (fold topx nw; clear - NTOP Hn; lia).
      rewrite Nat.eqb_refl. unfold bret. cbn [ret tree_ops tbind fst snd]. fold topx nw rb top'.
      eapply (COMMON Σ ls m1 OW 0 F fc);
        [ exact EV | exact LS1 | unfold MC; clear; lia | intros q0 A0 n0 Hq0 _; exact Hq0 | exact HAr | exact HAx | reflexivity
        | subst top'; clear - OKx2; unfold bn_dmax in *; lia ].
    +
      assert (NRX : rr <> rx).
      { intros E. subst rx. pose proof (ref_at_fun _ _ _ _ _ _ ND HAr HAx) as E. apply KE. rewrite E. reflexivity. }
      clear KE.
      do 3 step.
      clear HEAP LS ST MI MU WM HWL WOK FR BNx ACX OFF SHB1 SHB2 PRE PARTS.
      apply evt_done.
      rewrite (OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_rshift.rshift_eq_shift rr rx n ls) by (fold topx nw; clear - NTOP Hn; lia).
      replace (rr =? rx)%nat with false by (symmetry; apply Nat.eqb_neq; exact NRX). fold topx nw rb top'.
      eapply implA_bind.
      { eapply (bn_wexpand_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (r := rr) (a := ar) (words := top') (OW := OW) (LB := LB) (PL := PL) (EA := EA);
          [| | | reflexivity | exact HAr | exact (hpl_wref PL rr HP) | reflexivity | reflexivity | subst top'; clear - OKx2 OKx3; unfold bn_dmax in *; lia].
        - eapply cenv_preA; [exact EV | exact LS1 | unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO'; lia | clear; lia].
        - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV).
        - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_rs_wexpand CTX). }
      cbv beta. intros [u ls1] Σ1 ms1 PO.
      apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) MC Σ ls OW) in PO; [| exact OK | exact HEAP1].
      cbn [fst snd] in *.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & PL2 & -> & CP & (EPL & -> & HDM & WRES & BST)).
      subst PL2. specialize (CP eq_refl).
      assert (E1 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MC Σ ls OW m
                     [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] (0 + MC) Σ1 ls1 m2 OW2 /\ lib_state ls1 m2 OW2 PL EA)
        by (eapply cenv_postA; [exact EV | exact CP]).
      destruct E1 as (EV1 & LS2).
      pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP) as RST2.
      rewrite (ret_pc_even 2312192) by (clear; lia).
      pose proof (ref_at_stable _ _ _ _ _ _ _ RST2 HAr) as HAr2. pose proof (ref_at_stable _ _ _ _ _ _ _ RST2 HAx) as HAx2.
      assert (ETX : bn_top (getbn rx ls1) = topx) by (apply (wexpand_keeps_topA rr top' ls ls1 rx WRES HVr)).
      apply implA_from_evt.
      zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by (clear - SA0e SACe C1 C2 C3; unfold BnHeapA.ACEIL in *; lia). clear - KZ SA0e. lia. }
      clear KZ.
      apply evt_done.
      eapply (COMMON Σ1 ls1 m2 OW2 (0 + MC) F2 fc2);
        [ exact EV1 | exact LS2 | clear; lia | exact BST | exact HAr2 | exact HAx2 | exact ETX | exact HDM ].
Qed.

End WithRT.
