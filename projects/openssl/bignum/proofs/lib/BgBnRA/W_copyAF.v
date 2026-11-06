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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR Require Import BgLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA UnwindA EdgesA AsStruct RtCallA W_cryptoA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import BnAKitAF W_expandAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BN_COPY : Z := 0x2246fc.
Definition BN_COPY_STACK : Z := 64 + BN_EXPAND2_STACK.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_cp_expand := (E_BN_copy_2245cc : uk_call BN_COPY 0x2247b4 BN_EXPAND2).

Lemma BN_copy_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (rx ry : bnref) (ax ay : Z),
  bn_preA Σ ls m OW LB PL EA sp lo BN_COPY_STACK MC ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_COPY (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> ref_at ls OW PL rx ax -> ref_at ls OW PL ry ay -> wref PL rx -> ry <> ROne -> a0 = wz ax -> a1 = wz ay ->
  implA (BN_copy (tree_ops bptr) rx ry ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC
              (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = wz ax /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx ls) <> Some q -> In (q, A, n) OW')))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_COPY) fc None m (seg_rom bgasegs)).
Proof.
  intros until ay. intros (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR) UW CTX -> HAx HAy WRx NROy -> ->. pose proof (proj1 WRx : not_one rx) as NROx. change (not_one ry) in NROy.
  unfold BN_COPY_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK, BN_COPY, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).

  destruct (lib_state_open [] ls m OW PL EA ry ay LS ND HAy ltac:(intros []) NROy) as ((Dy & BNy & ARRy) & (OKy1 & OKy2 & OKy3 & OKy4) & _).
  destruct (lib_state_open [] ls m OW PL EA rx ax LS ND HAx ltac:(intros []) NROx) as ((Dx & BNx & ARRx) & (OKx1 & OKx2 & OKx3 & OKx4) & _).
  set (by_ := getbn ry ls) in *. set (bx := getbn rx ls) in *.
  destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP PARTS NOFR HAx NROx) as (qx & Ax & nx & Hinx & Rx1 & Rx2).
  pose proof (AH_range_in _ _ _ _ _ _ _ HEAP Hinx) as (XA0 & XA16 & _ & XAC & XAI).
  destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP PARTS NOFR HAy NROy) as (qy & Ay & ny & Hiny & Ry1 & Ry2).
  pose proof (AH_range_in _ _ _ _ _ _ _ HEAP Hiny) as (YA0 & YA16 & _ & YAC & YAI).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAx) as HVx.
  pose proof (ref_at_al8A _ _ _ _ _ _ _ _ _ HEAP PARTS NOFR HAx NROx) as ALx.
  pose proof (ref_at_al8A _ _ _ _ _ _ _ _ _ HEAP PARTS NOFR HAy NROy) as ALy.
  assert (FLRy : 0 <= bn_flags by_ <= 1) by (destruct OKy4 as [E|E]; rewrite E; lia).
  assert (EL4 : Z.land (bn_flags by_) 4 = 0) by (destruct OKy4 as [E|E]; rewrite E; reflexivity).
  unfold bn_cells in BNx, BNy. unfold BG_DMAX in OKx3, OKy3.
  apply (flag_cell_split bgasegs m ay _ _ _ _ (bn_flags by_) FLRy) in BNy.
  assert (INX : In (qx, Ax, nx) (OW ++ LB)) by (exact Hinx).
  assert (INY : In (qy, Ay, ny) (OW ++ LB)) by (exact Hiny).
  pose proof (AH_acc_in _ _ _ _ (qx, Ax, nx) ax 24 HEAP INX Rx1 Rx2) as ACCx.
  pose proof (AH_acc_in _ _ _ _ (qy, Ay, ny) ay 24 HEAP INY Ry1 Ry2) as ACCy.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 64, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  unfold BN_copy, bbind, bget. cbn [bind ret tree_ops tbind fst snd]. fold by_.
  unfold has_flag, BN_FLG_CONSTTIME. rewrite EL4. cbn [Z.eqb negb].
  apply implA_from_evt.
  carve_frame 64%nat ST.
  apply (rw_cells_split_CB bgasegs _ _ [] 64 _ [] [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 10 step. do 3 step. do 4 step. shl. step. chk0.
  step. rewrite (zxb_small (bn_flags by_)) by lia.
  step. rewrite (unsigned_lit (bn_flags by_)), EL4 by lia.
  step. step. if_true. do 2 step.
  do 2 step. shl. chk0.
  assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -64, bv_unsigned sp)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  lazymatch goal with |- evt _ (fun ms' => implA _ _ ?Q0 _) _ => set (QQ := Q0) end.
  destruct (Nat.eqb rx ry) eqn:EXY.
  {
    apply Nat.eqb_eq in EXY. subst ry. pose proof (ref_at_fun _ _ _ _ _ _ ND HAx HAy) as EA0. subst ay.
    step. if_true.
    do 9 step. release_frame FR ST (bv_unsigned sp). step. step.
    apply evt_done. unfold bret. cbn [ret tree_ops]. apply implA_ret.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into mF end.
    unfold QQ, bn_postA. do 17 eexists. exists mF, OW, PL. split; [reflexivity|]. cbn [fst snd].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|].
    split; [exact (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m mF OW PL EA _ HEAP LS MU WM FROK WOK)|].
    split; [exact ST|]. split; [exact MI|].
    split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL CEIL ltac:(lia))|].
    split; [unfold MC; lia|]. split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|].
    split; [reflexivity|]. split; [reflexivity|]. intros q0 A0 n0 Hq0 _. exact Hq0. }
  apply Nat.eqb_neq in EXY.
  pose proof (struct_disj Σ OW LB m HEAP ls PL EA _ _ PARTS FROK rx ry ax ay EXY HAx HAy) as SDJ.
  step. if_cases KE; zify_cond KE; rewrite ?unsigned_lit in KE by (unfold BnHeapA.ACEIL in *; lia); [exfalso; lia|]. clear KE.
  do 4 step. shl.
  step. rewrite (sx32_small (Z.of_nat (bn_top by_))) by lia. chk0.
  step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_dmax bx))) by lia.
  step.

  assert (FIN : forall (Σ1 : rts RT) (ls1 : bstate bptr) (m2 : mem) (OW2 : list block)
                       (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F2 : bvmap 5 word) (fc2 : bv 32),
    AHEAP Σ1 OW2 LB m2 -> lib_state ls1 m2 OW2 PL EA -> stk bgasegs m2 lo (bv_unsigned sp + -64) -> mem_inv bgasegs m2 ->
    ax_pres LB (bv_unsigned sp) (XW PL) m m2 -> rt_credit RT Σ - MC <= rt_credit RT Σ1 -> cnt_eq ls OW ls1 OW2 ->
    refs_stable ls OW ls1 OW2 -> getbn ry ls1 = by_ -> (bn_top by_ <= bn_dmax (getbn rx ls1))%nat ->
    (forall q A n, In (q, A, n) OW -> bn_d (getbn rx ls) <> Some q -> In (q, A, n) OW2) ->
    rw_cells bgasegs m2 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    implA (TRet (tt, setbn rx (mkBN (bn_d (getbn rx ls1))
                                    (if (0 <? bn_top by_)%nat then splice (bn_buf (getbn rx ls1)) 0 (firstn (bn_top by_) (bn_buf by_))
                                     else bn_buf (getbn rx ls1))
                                    (bn_top by_) (bn_neg by_) (bn_flags (getbn rx ls1))) ls1)) Σ1 QQ
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 TP_A) x5 x6 x7 sp (Z_to_bv 64 ax) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (ay + 8)) (Z_to_bv 64 ay) (Z_to_bv 64 (Z.of_nat (bn_top by_))) (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F2 (Z_to_bv 64 0x2247b8) fc2 None m2 (seg_rom bgasegs))).
  { intros Σ1 ls1 m2 OW2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F2 fc2
           HEAP2 LS2 ST2 MI2 AXP2 CR2 CNT2 RST2 Eby HDM BST FR2.
    clear BNx BNy ARRx ARRy MU WM ST MI FR HWL WOK ACCx ACCy SHB1 SHB2 OFF.
    pose proof (ref_at_stable _ _ _ _ _ _ _ RST2 HAx) as HAx2. pose proof (ref_at_stable _ _ _ _ _ _ _ RST2 HAy) as HAy2.
    pose proof (AH_nodup_l _ _ _ _ HEAP2) as ND2.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS2. pose proof PARTS2 as (WFS2 & PWF2 & IDS2 & PLB2 & ERRB2).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAx2) as HVx2. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAy2) as HVy2.
    destruct (lib_state_open [] ls1 m2 OW2 PL EA ry ay LS2 ND2 HAy2 ltac:(intros []) NROy) as ((Dy2 & BNy2 & ARRy2) & _ & _).
    destruct (lib_state_open [] ls1 m2 OW2 PL EA rx ax LS2 ND2 HAx2 ltac:(intros []) NROx) as ((Dr & BNr & ARRr) & (OKq1 & OKq2 & OKq3 & OKq4) & LSH).
    destruct (bn_arr_factsA Σ1 OW2 LB m2 ls1 PL EA _ ry Dy2 HEAP2 PARTS2 FROK NOFR HVy2 NROy ARRy2) as (Uy & LENy & Dy0 & DyC & DyI & DSEPy).
    destruct (bn_arr_factsA Σ1 OW2 LB m2 ls1 PL EA _ rx Dr HEAP2 PARTS2 FROK NOFR HVx2 NROx ARRr) as (Ur & LENr & Dr0 & DrC & DrI & DSEPr).
    rewrite Eby in BNy2, ARRy2, Uy, LENy, DyC, DyI, DSEPy.
    set (br := getbn rx ls1) in *.
    pose proof (DSEPr rx ax HAx2) as SEPrr. pose proof (DSEPr ry ay HAy2) as SEPry.
    pose proof (DSEPy rx ax HAx2) as SEPyr.
    pose proof (struct_disj Σ1 OW2 LB m2 HEAP2 ls1 PL EA _ _ PARTS2 FROK rx ry ax ay EXY HAx2 HAy2) as SDJ2.
    destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 NOFR HAx2 NROx) as (qx2 & Ax2 & nx2 & Hinx2 & Rx21 & Rx22).
    pose proof (AH_range_in _ _ _ _ _ _ _ HEAP2 Hinx2) as (XB0 & XB16 & _ & XBC & XBI).
    destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 NOFR HAy2 NROy) as (qy2 & Ay2 & ny2 & Hiny2 & Ry21 & Ry22).
    pose proof (AH_range_in _ _ _ _ _ _ _ HEAP2 Hiny2) as (YB0 & YB16 & _ & YBC & YBI).
    unfold bn_cells in BNy2, BNr. unfold BG_DMAX in OKq3.
    unfold MallocRep.wz in *.
    assert (INX2 : In (qx2, Ax2, nx2) (OW2 ++ LB)) by (exact Hinx2).
    assert (INY2 : In (qy2, Ay2, ny2) (OW2 ++ LB)) by (exact Hiny2).
    pose proof (AH_acc_in _ _ _ _ (qx2, Ax2, nx2) ax 24 HEAP2 INX2 Rx21 Rx22) as ACCx2.
    pose proof (AH_acc_in _ _ _ _ (qy2, Ay2, ny2) ay 24 HEAP2 INY2 Ry21 Ry22) as ACCy2.
    pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)]%Z m2) as MU3. pose proof (wmono_refl bgasegs m2) as WM3.
    assert (OFF3 : offshW [(bv_unsigned sp + -64, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).

    assert (FIN2 : forall mF (nb : list Z) z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 (F3 : bvmap 5 word) (fc3 : bv 32),
              AHEAP Σ1 OW2 LB mF -> lib_state_h [rx] ls1 mF OW2 PL EA ->
              length nb = bn_dmax br -> limbs nb -> u64arr bgasegs mF Dr (wlimbs nb) ->
              rw_cells bgasegs mF ay [C8 (Z_to_bv 64 Dy2); C4 (Z_to_bv 64 (Z.of_nat (bn_top by_))); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax by_)));
                                    C4 (Z_to_bv 64 (Z.b2z (bn_neg by_))); C4 (Z_to_bv 64 (bn_flags by_))] ->
              rw_cells bgasegs mF ax [C8 (Z_to_bv 64 Dr); C4 (Z_to_bv 64 (Z.of_nat (bn_top br))); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax br)));
                                    C4 (Z_to_bv 64 (Z.b2z (bn_neg br))); C4 (Z_to_bv 64 (bn_flags br))] ->
              rw_cells bgasegs mF (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
              stk bgasegs mF lo (bv_unsigned sp + -64) -> mem_inv bgasegs mF -> ax_pres LB (bv_unsigned sp) (XW PL) m mF ->
              implA (TRet (tt, setbn rx (mkBN (bn_d br) nb (bn_top by_) (bn_neg by_) (bn_flags br)) ls1)) Σ1 QQ
                (MS (mkR z1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 TP_A) z5 z6 z7 sp (Z_to_bv 64 ax)
                         z10 z11 z12 z13 z14 z15 z16 z17 (Z_to_bv 64 (ay + 8)) (Z_to_bv 64 ay) (Z_to_bv 64 (Z.of_nat (bn_top by_)))
                         (Z_to_bv 64 SHB) (Z_to_bv 64 ((ay + 8) ≫ 3 + SHB)) s7 s8 s9 s10 s11 z28 z29 z30 z31)
                    F3 (Z_to_bv 64 0x224800) fc3 None mF (seg_rom bgasegs))).
    { intros mF nb z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 F3 fc3 HEAPF LSHF Lnb LMnb UF BNyF BNrF FRF STF MIF AXPF.
      clear BNy2 BNr FR2 ST2 MI2 Ur Uy ACCx2 ACCy2 MU3 WM3 OFF3.
      clear SDJ SEPry SEPyr XAI YAI YBI DyI.
      pose proof (AH_acc_in _ _ _ _ (qx2, Ax2, nx2) ax 24 HEAPF INX2 Rx21 Rx22) as ACCxF.
      pose proof (AH_acc_in _ _ _ _ (qy2, Ay2, ny2) ay 24 HEAPF INY2 Ry21 Ry22) as ACCyF.
      pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp); (ax, ax + 24)]%Z mF) as MUF. pose proof (wmono_refl bgasegs mF) as WMF.
      assert (OFFF : offshW [(bv_unsigned sp + -64, bv_unsigned sp); (ax, ax + 24)]).
      { pose proof (AH_offsh _ _ _ _ (qx2, Ax2, nx2) HEAPF INX2) as O. cbn [blk_addr blk_size fst snd] in O.
        cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. lia. }
      assert (LENnb : Z.of_nat (length (wlimbs nb)) = Z.of_nat (bn_dmax br)) by (rewrite wlimbs_len, Lnb; reflexivity).
      apply implA_from_evt.
      do 3 step. shl. chk0. do 3 step. shl.
      step. rewrite (sx32_small (Z.b2z (bn_neg by_))) by (destruct (bn_neg by_); cbn; lia). chk0.
      step. shl. chk0. do 3 step. shl.
      step. rewrite (sx32_small (Z.of_nat (bn_top by_))) by lia. chk0.
      step.
      do 9 step. release_frame FRF STF (bv_unsigned sp). step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mG end.
      apply evt_done. apply implA_ret.
      assert (HWL3 : Forall (w_lib ls1 OW2 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp); (ax, ax + 24)]).
      { constructor; [left; cbn; lia|]. constructor; [w_lib_ref HAx2 NROx| constructor]. }
      assert (WOK3 : Forall (w_ok OW2 LB ls1 PL EA (bv_unsigned sp) [rx]) [(bv_unsigned sp + -64, bv_unsigned sp); (ax, ax + 24)]).
      { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|].
        constructor; [eapply (w_struct OW2 LB ls1 PL EA (bv_unsigned sp) false [rx] _ rx ax); [left; reflexivity| exact HAx2| exact NROx| cbn; lia| cbn; lia]| constructor]. }
      unfold QQ, bn_postA. do 17 eexists. exists mG, OW2, PL. split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAPF PARTS2 FROK MUF WMF HWL3 CEIL ltac:(unfold USTACK_TOP; lia))|].
      split.
      { unfold lib_state. eapply (lib_state_close [] ls1 mG OW2 PL EA rx ax); [| exact ND2| exact HAx2| exact NROx| | |].
        - exact (lib_state_frame Σ1 LB (bv_unsigned sp) USTACK_TOP [rx] ls1 mF mG OW2 PL EA _ HEAPF LSHF MUF WMF FROK WOK3).
        - exists Dr. split.
          + unfold bn_cells, bn_dmax. cbn [bn_top bn_buf bn_neg bn_flags]. rewrite Lnb. exact BNrF.
          + apply (fun ARRnb__ => bn_arr_nofr PL rx m2 OW2 Dr br PWF2 NOFR NROx ARRnb__ ltac:(solve_nbuf)) in ARRr. apply (fun ARRnb__ => bn_arr_of_nofr PL rx mG OW2 Dr _ PWF2 NOFR NROx ARRnb__ ltac:(solve_nbuf)).
            unfold BnRepDefs.bn_arr, bn_dmax in *. cbn [bn_d bn_buf]. rewrite Lnb. destruct (bn_d br) as [pr|]; [split; [exact (proj1 ARRr)| exact UF]|].
            destruct ARRr as [ED Eb]. split; [exact ED|]. rewrite Eb in Lnb. cbn in Lnb. destruct nb; [reflexivity| discriminate].
        - unfold bg_ok, bn_dmax. cbn [bn_buf bn_top bn_flags]. rewrite Lnb. unfold BG_DMAX in *.
          split; [exact LMnb|]. split; [exact HDM|]. split; [clear - OKq3 Lnb; unfold bn_dmax in *; lia| exact OKq4].
        - apply ids_ok_setbn_same; [exact IDS2| exact HVx2|]. unfold bn_blocks, bn_dmax. cbn [bn_d bn_buf]. rewrite Lnb. reflexivity. }
      split; [exact STF|]. split; [exact MIF|].
      split; [eapply ax_pres_trans; [exact AXPF|]; exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAPF PARTS2 FROK MUF HWL3 CEIL ltac:(lia))|].
      split; [exact CR2|].
      split. { unfold cnt_eq in *. rewrite (cnt_bal_setbn rx _ ls1 OW2 OW2 HVx2). fold br. rewrite CNT2.
               unfold bn_blocks. cbn [bn_d]. destruct (bn_d br); cbn [length]; lia. }
      split. { eapply refs_stable_trans; [exact RST2| apply refs_stable_setbn]. }
      split; [reflexivity|]. split; [reflexivity| exact BST]. }
    clear SDJ XAI YAI XBI YBI DyI OKx4 OKy4.
    assert (LSH2 : lib_state_h [rx] ls1 m2 OW2 PL EA) by exact LSH.
    apply implA_from_evt.
    do 2 step. shl. chk0.
    step. rewrite (sx32_small (Z.of_nat (bn_top by_))) by lia.
    step. if_cases KT; zify_cond KT.
    -
      assert (ET0 : bn_top by_ = 0%nat) by (apply andb_false_iff in KT; destruct KT as [KT|KT]; apply Z.ltb_ge in KT; lia).
      replace (0 <? bn_top by_)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
      apply evt_done.
      eapply (FIN2 m2 (bn_buf br)); [exact HEAP2 | exact LSH2 | reflexivity | exact OKq1 | exact Ur | exact BNy2 | exact BNr | exact FR2 | exact ST2 | exact MI2 | exact AXP2].
    -
      assert (TOPP : (0 < bn_top by_)%nat) by lia.
      replace (0 <? bn_top by_)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
      assert (HDr : exists pr, bn_d br = Some pr /\ In (pr, Dr, 8 * Z.of_nat (bn_dmax br)) OW2).
      { pose proof (bn_arr_nofr PL rx m2 OW2 Dr br PWF2 NOFR NROx ARRr ltac:(solve_nbuf)) as ARRr0. unfold BnRepDefs.bn_arr in ARRr0.
        destruct (bn_d br) as [pr|]; [exists pr; split; [reflexivity| exact (proj1 ARRr0)]|].
        exfalso. destruct ARRr0 as [_ E]. unfold bn_dmax in HDM. rewrite E in HDM. cbn in HDM. lia. }
      destruct HDr as (pr & Edr & Hinpr).
      destruct (bn_arr_blk Σ1 OW2 LB m2 PL (bv_unsigned sp) USTACK_TOP ry Dy2 by_ HEAP2 PWF2 FROK NROy ARRy2 ltac:(unfold bn_dmax in *; lia)) as (bsrc & INYD2 & BS1 & BS2 & PY0 & PYC).
      assert (LDJ : Dr + 8 * Z.of_nat (bn_dmax br) <= Dy2 \/ Dy2 + 8 * Z.of_nat (bn_dmax by_) <= Dr).
      { rewrite <- Eby in ARRy2 |- *.
        exact (arr_arr_disj ls1 OW2 PL EA (bv_unsigned sp) USTACK_TOP Σ1 LB m2 rx ry pr Dr Dy2 HEAP2 PARTS2 FROK EXY HVx2 HVy2 NROy Edr Hinpr ARRy2). }
      assert (LBR : length (bn_buf br) = bn_dmax br) by reflexivity.
      assert (LBY : length (bn_buf by_) = bn_dmax by_) by reflexivity.
      pose proof (AH_range _ _ _ _ _ _ _ HEAP2 Hinpr) as (PR0 & _ & _ & PRC & _).
      apply (proj1 (limbarr_split bgasegs m2 Dr (bn_buf br) (bn_top by_) ltac:(lia))) in Ur. destruct Ur as [U1 U2].
      set (cp := u64s (wlimbs (firstn (bn_top by_) (bn_buf by_)))).
      assert (LCP : Z.of_nat (length cp) = Z.of_nat (bn_top by_) * 8).
      { subst cp. rewrite u64s_length, wlimbs_len, firstn_length_le by lia. lia. }
      assert (SRC : bytes_at bgasegs m2 Dy2 cp).
      { apply limbarr_bytes. apply (proj1 (limbarr_split bgasegs m2 Dy2 (bn_buf by_) (bn_top by_) ltac:(lia))) in Uy. exact (proj1 Uy). }
      do 2 step. shl. chk0. do 2 step. shl. chk0.
      do 3 step.
      rewrite ?(unsigned_lit (Z.of_nat (bn_top by_))) by lia.
      replace (Z.shiftl (Z.of_nat (bn_top by_)) 3) with (Z.of_nat (bn_top by_) * 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
      rewrite <- LCP.
      step.
      assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
      assert (INR2 : In (pr, Dr, 8 * Z.of_nat (bn_dmax br)) (OW2 ++ LB)) by (apply in_or_app; left; exact Hinpr).
      apply evt_done.
      eapply implA_step_same.
      + eapply (asan_memcpy_cpsA) with (d := Dr) (s := Dy2) (bs := cp) (bd := (pr, Dr, 8 * Z.of_nat (bn_dmax br)))
                                       (bsrc := bsrc) (lo := lo) (OW := OW2) (LB := LB); try reflexivity.
        * exact HEAP2.
        * rewrite ESP. exact ST2.
        * exact CEIL.
        * rewrite ESP. unfold RT_STACK. lia.
        * rewrite ESP. unfold USTACK_TOP. lia.
        * rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
        * exact MI2.
        * exact INR2.
        * cbn [blk_addr blk_size fst snd]. lia.
        * exact INYD2.
        * exact BS1.
        * lia.
        * exact SRC.
        * lia.
        * lia.
      + intros ms5 PO. unfold icall_post in PO. rewrite ?ESP in PO.
        destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F5 & fc5 & m4 & -> & MI4 & ST4 & HEAP4 & WM4 & AG4 & BZ & WR4).
        rewrite (ret_pc_even 2246656) by lia. unfold MallocRep.wz.
        assert (LSEG : length (firstn (bn_top by_) (bn_buf by_)) = bn_top by_) by (apply firstn_length_le; lia).
        eapply (FIN2 m4 (splice (bn_buf br) 0 (firstn (bn_top by_) (bn_buf by_)))); [exact HEAP4 | | | | | | | | exact ST4 | exact MI4 | ].
        * eapply (lib_state_h_icall Σ1 LB [rx] ls1 m2 m4 OW2 PL EA (bv_unsigned sp + -64) (bv_unsigned sp) Dr (Z.of_nat (length cp)) HEAP2 LSH2 FROK ltac:(lia) AG4).
          eapply (w_limbs OW2 LB ls1 PL EA (bv_unsigned sp) false [rx] _ rx pr Dr); [left; reflexivity| exact HVx2| exact Edr| exact Hinpr| cbn [fst snd]; lia| cbn [fst snd]; fold br; lia].
        * rewrite splice_length; [exact LBR| rewrite LSEG; lia].
        * apply splice_limbs; [exact OKq1| apply limbs_firstn; exact OKy1].
        * unfold splice. rewrite firstn_O. cbn [app Nat.add]. rewrite LSEG. apply limbarr_app. rewrite LSEG. split.
          -- apply u64arr_u8arr. fold cp. split; [exact BZ | exact WR4].
          -- eapply (u64arr_agree _ _ _ _ _ AG4); [exact U2|]. intros x Hx. rewrite wlimbs_len, length_skipn in Hx.
             split; [right; right; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); split; [exact INR2 | cbn [blk_addr blk_size fst snd]; lia] | lia].
        * eapply (rw_cells_agree _ _ _ _ _ AG4); [exact BNy2|]. intros x Hx. cbn in Hx.
          split; [right; right; exists (qy2, Ay2, ny2); split; [exact INY2 | cbn; lia] | lia].
        * eapply (rw_cells_agree _ _ _ _ _ AG4); [exact BNr|]. intros x Hx. cbn in Hx.
          split; [right; right; exists (qx2, Ax2, nx2); split; [exact INX2 | cbn; lia] | lia].
        * eapply (rw_cells_agree _ _ _ _ _ AG4); [exact FR2|]. intros x Hx. cbn in Hx. split; [left; unfold USTACK_TOP; lia | unfold BnHeapA.ACEIL in *; lia].
        * eapply ax_pres_trans; [exact AXP2|]. eapply agree_on_mono; [exact AG4|]. intros x [_ Hc]. split.
          -- destruct Hc as [Hc|[Hc|(b0 & Hb0 & Hr)]]; [left; lia | right; left; exact Hc | right; right; exists b0; split; [apply in_or_app; right; exact Hb0 | exact Hr]].
          -- intros HAr. destruct Hc as [Hc|[Hc|(b0 & Hb0 & Hr)]].
             ++ unfold BnHeapA.ACEIL in *. lia.
             ++ eapply (blk_not_static Σ1 OW2 LB m2 (pr, Dr, 8 * Z.of_nat (bn_dmax br)) x HEAP2 Hinpr); [cbn; lia | exact Hc].
             ++ assert (NE : blk_id b0 <> pr).
                { intros E. pose proof (AH_nodup _ _ _ _ HEAP2) as NDA. rewrite map_app in NDA.
                  eapply (nodup_app_disj _ _ pr NDA); [apply (in_map blk_id) in Hinpr; exact Hinpr | rewrite <- E; apply in_map; exact Hb0]. }
                pose proof (AH_disjoint_gen _ _ _ _ b0 (pr, Dr, 8 * Z.of_nat (bn_dmax br)) HEAP2 (in_or_app _ _ _ (or_intror Hb0)) INR2 NE) as DJ. cbn in DJ. lia. }
  if_cases KD; zify_cond KD; rewrite !signed_small in KD by lia.
  -
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    apply evt_done. unfold bn_wexpand, bbind, bget, bret, bset. cbn [bind ret tree_ops tbind fst snd]. fold bx.
    replace (bn_top by_ <=? bn_dmax bx)%nat with true by (symmetry; apply Nat.leb_le; lia).
    cbn [tbind fst snd].
    eapply (FIN Σ ls m1 OW);
      [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))
      | exact (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m m1 OW PL EA _ HEAP LS MU WM FROK WOK)
      | exact ST | exact MI
      | exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL CEIL ltac:(lia))
      | unfold MC; lia | apply cnt_eq_refl | apply refs_stable_refl | reflexivity | fold bx; lia
      | intros q0 A0 n0 Hq0 _; exact Hq0 | exact FR].
  -
    do 3 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
    pose proof (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia)) as HEAP1.
    pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
    assert (AXP1 : ax_pres LB (bv_unsigned sp) (XW PL) m m1) by (exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL CEIL ltac:(lia))).
    assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp + -64) (bv_unsigned sp) (bv_unsigned ra :: ras)).
    { apply (uw_push_frame m1 _ (bv_unsigned sp) 64 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] (bv_unsigned ra) (bv_unsigned s0) ras);
        [reflexivity | lia | clear - SP16; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | apply bv_unsigned_in_range | |].
      - rewrite !Z_to_bv_bv_unsigned. exact FR.
      - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
    apply evt_done.
    eapply implA_bind.
    { eapply implA_leaves; [apply (bn_wexpand_leaves rx (bn_top by_) ls HVx OKx2)|].
      eapply (bn_expand2_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (r := rx) (a := ax) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HAx | exact WRx | reflexivity | reflexivity | lia].
      - unfold bn_preA. rewrite ESP.
        split; [exact HEAP1|]. split; [exact LS1|]. split; [eapply frames_ok_call; [exact FROK| exact CEIL| lia| lia]|]. split; [exact ST|]. split; [exact CEIL|].
        split; [unfold BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; lia|].
        split; [unfold USTACK_TOP; lia|]. split; [clear - SP16; Z.div_mod_to_equations; lia|]. split; [exact MI|]. split; [exact CNT|]. split; [exact CRED|]. split; [exact FAL| exact NOFR].
      - rewrite ESP. exact UW1.
      - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_cp_expand CTX). }
    cbv beta. intros [u ls1] Σ1 ms1 [PO LEAF]. unfold bn_postA in PO. cbn [fst snd] in *.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & PL2 & -> & HEAP2 & LS2 & ST2
                    & MI2 & AXP2 & CR2 & CNT2 & RST2 & -> & -> & HDM & WRES & BST).
    rewrite ESP in *.
    rewrite (ret_pc_even 2246580) by lia.
    destruct LEAF as (LF1 & LF2 & LF3 & LF4 & LF5 & LF6). cbn [snd] in *.
    assert (FR2 : rw_cells bgasegs m2 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rw_cells_agree; [exact AXP2 | exact FR |].
      intros x Hx. cbn in Hx. xw_client_stack FROK. }
    apply implA_from_evt.
    step. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (unfold BnHeapA.ACEIL in *; lia); lia|]. clear KZ.
    apply evt_done. unfold bset. cbn [ret tree_ops].
    eapply (FIN Σ1 ls1 m2 OW2);
      [exact HEAP2 | exact LS2 | exact ST2 | exact MI2
      | eapply ax_pres_trans; [exact AXP1|]; eapply ax_pres_weaken; [exact AXP2| lia]
      | exact CR2 | exact CNT2 | exact RST2 | apply LF1; exact EXY | exact HDM | exact BST | exact FR2].
Qed.

End WithRT.
