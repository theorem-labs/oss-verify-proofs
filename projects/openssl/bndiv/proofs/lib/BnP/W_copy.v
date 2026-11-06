(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.openssl.bndiv.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnModel BnTree BnInv BnSpecs BnMInv BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Layout Lib_iface Lib_kit F_memset F_memcpy.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnMem BnTac.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnHeap BnArr BnRep BnIface W_crypto W_expand BnLeaves.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Lemma bnref_eqb_false_ne : forall x y, bnref_eqb x y = false -> x <> y.
Proof. intros x y H E. subst y. destruct x; cbn in H; try discriminate. rewrite Nat.eqb_refl in H. discriminate. Qed.
Lemma bnref_eqb_true_eq : forall x y, bnref_eqb x y = true -> x = y.
Proof. intros x y H. destruct x, y; cbn in H; try discriminate; try reflexivity. apply Nat.eqb_eq in H. subst. reflexivity. Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_COPY : Z := 0xddc10.
Definition BN_COPY_STACK : Z := 48 + BN_EXPAND2_STACK.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma BN_copy_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
      (lo B : Z) (errv : word) (rx ry : bnref) (ax ay : Z),
    bn_pre s ls m OW LB AD EA sp lo B errv BN_COPY_STACK -> tp = wz RATP ->
    ref_at ls OW AD rx ax -> ref_at ls OW AD ry ay -> a0 = wz ax -> a1 = wz ay ->
    implM psegs (interp (embed (BN_copy (tree_ops bptr) rx ry ls))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA
               (fun _ _ OW' a0' => a0' = wz ax /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx ls) <> Some q -> In (q, A, n) OW')))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_COPY) fc None m (seg_rom psegs)).
  Proof.
    intros until ay. intros (HEAP & LS & AUX & SPB & ST & CEIL & GLO & LO & ERR & MI) -> HAx HAy -> ->.
    unfold BN_COPY_STACK, BN_EXPAND2_STACK, BN_COPY, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
    (* [comment removed for export] *)
    destruct (lib_state_open [] ls m OW AD EA ry ay LS ND HAy ltac:(intros [])) as ((Dy & BNy & ARRy) & (OKy1 & OKy2 & OKy3 & OKy4) & _).
    destruct (lib_state_open [] ls m OW AD EA rx ax LS ND HAx ltac:(intros [])) as ((Dx & BNx & ARRx) & (OKx1 & OKx2 & OKx3 & OKx4) & _).
    set (by_ := getbn ry ls) in *. set (bx := getbn rx ls) in *.
    destruct (ref_at_inb _ _ _ _ _ ADB HAx) as (qx & Ax & nx & Eqx & Hinx & Rx1 & Rx2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP Hinx) as (XA0 & XA16 & _ & XAC & XAI).
    destruct (ref_at_inb _ _ _ _ _ ADB HAy) as (qy & Ay & ny & Eqy & Hiny & Ry1 & Ry2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP Hiny) as (YA0 & YA16 & _ & YAC & YAI).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAx) as HVx.
    assert (FLRy : 0 <= bn_flags by_ <= 1) by (destruct OKy4 as [E|E]; rewrite E; lia).
    assert (EL4 : Z.land (bn_flags by_) 4 = 0) by (destruct OKy4 as [E|E]; rewrite E; reflexivity).
    unfold bn_cells in BNx, BNy. unfold BN_WORDS_MAX in OKx3, OKy3.
    apply (flag_cell_split psegs m ay _ _ _ _ (bn_flags by_) FLRy) in BNy.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3063480 - 164) with 3063316 in ERR.
    unfold BN_copy, bbind, bget. cbn [bind ret tree_ops tbind fst snd]. fold by_.
    unfold BN_FLG_CONSTTIME. rewrite EL4. cbn [Z.eqb negb].
    unfold implM. iprefix.
    carve_frame 48%nat ST. do 7 step. step. step.
    rewrite (zxb_small (bn_flags by_)) by lia.
    step. rewrite (unsigned_lit (bn_flags by_)), EL4 by lia.
    step. step. if_true. step.
    assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB ls AD EA []) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    destruct (bnref_eqb rx ry) eqn:EXY.
    { (* [comment removed for export] *)
      apply bnref_eqb_true_eq in EXY. subst ry. pose proof (ref_at_fun _ _ _ _ _ _ ND HAx HAy) as EA0. subst ay.
      step. replace (bv_eqb (Z_to_bv 64 ax) (Z_to_bv 64 ax)) with true by (symmetry; unfold bv_eqb; apply Z.eqb_refl).
      step. do 5 step. step. release_frame FR ST (bv_unsigned sp). step.
      ihere. to_implM. unfold bret. cbn [ret tree_ops embed interp]. apply implM_ret. apply evt_done.
      lazymatch goal with |- bn_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
      unfold bn_post. do 15 eexists. exists mF, OW, errv. split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL)|].
      split; [exact (lib_state_frame s LB [] ls m mF OW AD EA _ HEAP LS MU WM WOK)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ HEAP AUX MU WM HWL SPB); unfold GLOBALS_TOP; lia|]. split; [exact ST|].
      split; [unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL); unfold GLOBALS_TOP; lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|].
      split; [reflexivity|]. intros q0 A0 n0 Hq0 _. exact Hq0. }
    apply bnref_eqb_false_ne in EXY.
    pose proof (struct_disj s OW LB m HEAP ls AD EA IDS ADB rx ry ax ay EXY HAx HAy) as SDJ.
    step. if_cases KE; zify_cond KE; rewrite ?unsigned_lit in KE by lia; [exfalso; lia|]. clear KE.
    step. step. rewrite (sx32_small (Z.of_nat (bn_top by_))) by lia.
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_dmax bx))) by lia.
    (* [comment removed for export] *)
    assert (FIN : forall (st1 : PState) (ls1 : lstate bptr) (m2 : mem) (OW2 : list block) (errv2 : word) (jk : list byte)
                         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      RHEAP st1 (OW2 ++ LB) m2 -> lib_state ls1 m2 OW2 AD EA -> rauxv_ok m2 B -> stk psegs m2 lo (bv_unsigned sp + -48) ->
      rw_cells psegs m2 3063316 [C4 errv2] -> mem_inv psegs m2 -> lx_pres LB (bv_unsigned sp) LIBW_bn m m2 ->
      ps_fa st1 = ps_fa s -> ps_so st1 = ps_so s -> refs_stable ls OW ls1 OW2 AD ->
      getbn ry ls1 = by_ -> (bn_top by_ <= bn_dmax (getbn rx ls1))%nat ->
      (forall q A n, In (q, A, n) OW -> bn_d (getbn rx ls) <> Some q -> In (q, A, n) OW2) ->
      rw_cells psegs m2 (bv_unsigned sp + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      implM psegs (interp (embed (TRet (tt, setbn rx (mkBN (bn_d (getbn rx ls1))
                                                          (if (0 <? bn_top by_)%nat then splice (bn_buf (getbn rx ls1)) 0 (firstn (bn_top by_) (bn_buf by_))
                                                           else bn_buf (getbn rx ls1))
                                                          (bn_top by_) (bn_neg by_) (bn_flags (getbn rx ls1))) ls1)))) st1
        (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA
                 (fun _ _ OW' a0' => a0' = Z_to_bv 64 ax /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx ls) <> Some q -> In (q, A, n) OW')))
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 RATP) x5 x6 x7 sp (Z_to_bv 64 ax) x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 ay) (Z_to_bv 64 (Z.of_nat (bn_top by_))) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0xddc70) fc None m2 (seg_rom psegs))).
    { intros st1 ls1 m2 OW2 errv2 jk x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
             HEAP2 LS2 AUX2 ST2 ERR2 MI2 LXP2 FA2 SO2 RST2 Eby HDM BST FR2.
      clear BNx BNy ARRx ARRy MU WM ST ERR MI FR HWL WOK.
      pose proof (RST2 _ _ HAx) as HAx2. pose proof (RST2 _ _ HAy) as HAy2.
      pose proof (RH_nodup_l _ _ _ _ HEAP2) as ND2.
      destruct (lib_state_h_parts _ _ _ _ _ _ LS2) as (IDS2 & ADB2 & ERRB2 & SOK2).
      pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAx2) as HVx2. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAy2) as HVy2.
      destruct (lib_state_open [] ls1 m2 OW2 AD EA ry ay LS2 ND2 HAy2 ltac:(intros [])) as ((Dy2 & BNy2 & ARRy2) & _ & _).
      destruct (lib_state_open [] ls1 m2 OW2 AD EA rx ax LS2 ND2 HAx2 ltac:(intros [])) as ((Dr & BNr & ARRr) & (OKq1 & OKq2 & OKq3 & OKq4) & LSH).
      destruct (bn_arr_facts st1 OW2 LB m2 HEAP2 ls1 AD EA IDS2 ADB2 ry Dy2 HVy2 ARRy2) as (Uy & LENy & Dy0 & DyC & DyI & DSEPy).
      destruct (bn_arr_facts st1 OW2 LB m2 HEAP2 ls1 AD EA IDS2 ADB2 rx Dr HVx2 ARRr) as (Ur & LENr & Dr0 & DrC & DrI & DSEPr).
      rewrite Eby in BNy2, ARRy2, Uy, LENy, DyC, DyI, DSEPy.
      set (br := getbn rx ls1) in *.
      pose proof (DSEPr rx ax HAx2) as SEPrr. pose proof (DSEPr ry ay HAy2) as SEPry.
      pose proof (DSEPy rx ax HAx2) as SEPyr.
      pose proof (struct_disj st1 OW2 LB m2 HEAP2 ls1 AD EA IDS2 ADB2 rx ry ax ay EXY HAx2 HAy2) as SDJ2.
      destruct (ref_at_inb _ _ _ _ _ ADB2 HAx2) as (qx2 & Ax2 & nx2 & Eqx2 & Hinx2 & Rx21 & Rx22).
      pose proof (RH_range _ _ _ _ _ _ _ HEAP2 Hinx2) as (XB0 & XB16 & _ & XBC & XBI).
      destruct (ref_at_inb _ _ _ _ _ ADB2 HAy2) as (qy2 & Ay2 & ny2 & Eqy2 & Hiny2 & Ry21 & Ry22).
      pose proof (RH_range _ _ _ _ _ _ _ HEAP2 Hiny2) as (YB0 & YB16 & _ & YBC & YBI).
      unfold bn_cells in BNy2, BNr. unfold BN_WORDS_MAX in OKq3.
      cbn [embed interp]. apply implM_ret.
      unfold MallocRep.wz in *.
      (* [comment removed for export] *)
      assert (FIN2 : forall mF (nb : list Z) (l3 h3 : Z) z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31,
                w_lib OW2 lo (bv_unsigned sp) (l3, h3) -> w_okc OW2 LB ls1 AD EA false [rx] (l3, h3) ->
                length nb = bn_dmax br -> limbs nb ->
                u64arr psegs mF Dr (wlimbs nb) ->
                rw_cells psegs mF ay [C8 (Z_to_bv 64 Dy2); C4 (Z_to_bv 64 (Z.of_nat (bn_top by_))); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax by_)));
                                      C4 (Z_to_bv 64 (Z.b2z (bn_neg by_))); C4 (Z_to_bv 64 (bn_flags by_))] ->
                rw_cells psegs mF ax [C8 (Z_to_bv 64 Dr); C4 (Z_to_bv 64 (Z.of_nat (bn_top br))); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax br)));
                                      C4 (Z_to_bv 64 (Z.b2z (bn_neg br))); C4 (Z_to_bv 64 (bn_flags br))] ->
                rw_cells psegs mF (bv_unsigned sp + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
                rw_cells psegs mF 3063316 [C4 errv2] -> stk psegs mF lo (bv_unsigned sp + -48) -> mem_inv psegs mF ->
                munch [(bv_unsigned sp + -48, bv_unsigned sp); (ax, ax + 24); (l3, h3)]%Z m2 mF -> wmono psegs m2 mF ->
                evt psegs
                  (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA
                     (fun _ _ OW' a0' => a0' = Z_to_bv 64 ax /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx ls) <> Some q -> In (q, A, n) OW'))
                     (tt, setbn rx (mkBN (bn_d br) nb (bn_top by_) (bn_neg by_) (bn_flags br)) ls1) st1)
                  (MS (mkR z1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 RATP) z5 z6 z7 sp (Z_to_bv 64 ax)
                           (Z_to_bv 64 (Z.of_nat (bn_top by_))) z11 z12 z13 z14 z15 z16 z17 (Z_to_bv 64 ay) (Z_to_bv 64 (Z.of_nat (bn_top by_)))
                           s4 s5 s6 s7 s8 s9 s10 s11 z28 z29 z30 z31)
                      F (Z_to_bv 64 0xddc90) fc None mF (seg_rom psegs))).
      { intros mF nb l3 h3 z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 HW3L HW3K Lnb LMnb UF BNyF BNrF FRF ERRF STF MIF MUF WMF.
        clear BNy2 BNr FR2 ERR2 ST2 MI2 Ur Uy.
        clear SDJ SEPry SEPyr XAI YAI YBI DyI.
        assert (LENnb : Z.of_nat (length (wlimbs nb)) = Z.of_nat (bn_dmax br)) by (rewrite wlimbs_len, Lnb; reflexivity).
        step. rewrite (sx32_small (Z.b2z (bn_neg by_))) by (destruct (bn_neg by_); cbn; lia).
        step. step. step.
        do 5 step. step. release_frame FRF STF (bv_unsigned sp). step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mG end.
        apply evt_done.
        assert (HWL3 : Forall (w_lib OW2 lo (bv_unsigned sp)) [(bv_unsigned sp + -48, bv_unsigned sp); (ax, ax + 24); (l3, h3)]).
        { constructor; [left; cbn; lia|]. constructor; [right; exists (qx2, Ax2, nx2); cbn; auto|]. constructor; [exact HW3L| constructor]. }
        assert (WOK3 : Forall (w_ok OW2 LB ls1 AD EA [rx]) [(bv_unsigned sp + -48, bv_unsigned sp); (ax, ax + 24); (l3, h3)]).
        { constructor; [apply w_stack; cbn; lia|]. constructor; [eapply (w_struct OW2 LB ls1 AD EA false [rx] _ rx ax); [left; reflexivity| exact HAx2| cbn; lia| cbn; lia]|].
          constructor; [exact HW3K| constructor]. }
        unfold bn_post. do 15 eexists. exists mG, OW2, errv2. split; [reflexivity|]. cbn [fst snd].
        split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP2 MUF WMF HWL3 CEIL)|].
        split.
        { unfold lib_state. eapply (lib_state_close [] ls1 mG OW2 AD EA rx ax); [| exact ND2| exact HAx2| | |].
          - exact (lib_state_frame st1 LB [rx] ls1 m2 mG OW2 AD EA _ HEAP2 LSH MUF WMF WOK3).
          - exists Dr. split.
            + unfold bn_cells, bn_dmax. cbn [bn_top bn_buf bn_neg bn_flags]. rewrite Lnb. exact BNrF.
            + unfold bn_arr, bn_dmax in *. cbn [bn_d bn_buf]. rewrite Lnb. destruct (bn_d br) as [pr|]; [split; [exact (proj1 ARRr)| exact UF]|].
              destruct ARRr as [ED Eb]. split; [exact ED|]. rewrite Eb in Lnb. cbn in Lnb. destruct nb; [reflexivity| discriminate].
          - unfold bn_okm, bn_dmax. cbn [bn_buf bn_top bn_flags]. rewrite Lnb. unfold BN_WORDS_MAX.
            split; [exact LMnb|]. split; [exact HDM|]. split; [lia| exact OKq4].
          - apply ids_ok_setbn_same; [exact IDS2| exact HVx2|]. unfold bn_blocks, bn_dmax. cbn [bn_d bn_buf]. rewrite Lnb. reflexivity. }
        split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ HEAP2 AUX2 MUF WMF HWL3 SPB); unfold GLOBALS_TOP; lia|]. split; [exact STF|].
        split; [unfold LX_ERRNO, RATP; exact ERRF|]. split; [exact MIF|].
        split. { eapply lx_pres_trans; [exact LXP2|]. apply (seg_lx_pres _ _ _ _ _ _ _ _ _ HEAP2 MUF WMF HWL3 CEIL); unfold GLOBALS_TOP; lia. }
        split; [exact FA2|]. split; [exact SO2|].
        split. { intros r' a' HA'. apply ref_at_setbn. apply RST2. exact HA'. }
        split; [reflexivity| exact BST]. }
      clear SDJ SDJ2 SEPyr XAI YAI XBI YBI DyI OKx4 OKy4 OKq4.
      pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (ax, ax + 24); (ax, ax + 24)]%Z m2) as MU3.
      pose proof (wmono_refl psegs m2) as WM3.
      step. rewrite (sx32_small (Z.of_nat (bn_top by_))) by lia.
      step. if_cases KT; zify_cond KT.
      - (* [comment removed for export] *)
        assert (ET0 : bn_top by_ = 0%nat) by (apply andb_false_iff in KT; destruct KT as [KT|KT]; apply Z.ltb_ge in KT; lia).
        replace (0 <? bn_top by_)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
        eapply (FIN2 m2 (bn_buf br) ax (ax + 24));
          [ right; exists (qx2, Ax2, nx2); cbn; auto
          | eapply (w_struct OW2 LB ls1 AD EA false [rx] _ rx ax); [left; reflexivity| exact HAx2| cbn; lia| cbn; lia]
          | reflexivity | exact OKq1 | exact Ur | exact BNy2 | exact BNr | exact FR2 | exact ERR2 | exact ST2 | exact MI2 | exact MU3 | exact WM3].
      - (* [comment removed for export] *)
        assert (TOPP : (0 < bn_top by_)%nat) by lia.
        replace (0 <? bn_top by_)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
        clear MU3 WM3.
        assert (HDr : exists pr, bn_d br = Some pr /\ In (pr, Dr, 8 * Z.of_nat (bn_dmax br)) OW2).
        { unfold bn_arr in ARRr. destruct (bn_d br) as [pr|]; [exists pr; split; [reflexivity| exact (proj1 ARRr)]|].
          exfalso. destruct ARRr as [_ E]. unfold bn_dmax in HDM. rewrite E in HDM. cbn in HDM. lia. }
        destruct HDr as (pr & Edr & Hinpr).
        assert (HDy : exists py, bn_d by_ = Some py /\ In (py, Dy2, 8 * Z.of_nat (bn_dmax by_)) OW2).
        { unfold bn_arr in ARRy2. destruct (bn_d by_) as [py|]; [exists py; split; [reflexivity| exact (proj1 ARRy2)]|].
          exfalso. destruct ARRy2 as [_ E]. unfold bn_dmax in OKy2. rewrite E in OKy2. cbn in OKy2. lia. }
        destruct HDy as (py & Edy & Hinpy).
        assert (Edy1 : bn_d (getbn ry ls1) = Some py) by (rewrite Eby; exact Edy).
        pose proof (limbs_limbs_disj st1 OW2 LB m2 HEAP2 ls1 AD EA IDS2 rx ry pr Dr _ py Dy2 _ EXY HVx2 HVy2 Edr Edy1 Hinpr Hinpy) as LDJ.
        pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m2) as MU3.
        pose proof (wmono_refl psegs m2) as WM3.
        assert (LBR : length (bn_buf br) = bn_dmax br) by reflexivity.
        assert (LBY : length (bn_buf by_) = bn_dmax by_) by reflexivity.
        apply (proj1 (limbarr_split psegs m2 Dr (bn_buf br) (bn_top by_) ltac:(lia))) in Ur. destruct Ur as [U1 U2].
        assert (SRC : bytes_at psegs m2 Dy2 (u64s (wlimbs (firstn (bn_top by_) (bn_buf by_))))).
        { apply limbarr_bytes. apply (proj1 (limbarr_split psegs m2 Dy2 (bn_buf by_) (bn_top by_) ltac:(lia))) in Uy. exact (proj1 Uy). }
        apply limbarr_CB in U1. rewrite firstn_length_le in U1 by lia.
        do 3 step.
        rewrite ?(unsigned_lit (Z.of_nat (bn_top by_))) by lia.
        replace (Z.shiftl (Z.of_nat (bn_top by_)) 3) with (Z.of_nat (bn_top by_) * 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
        step. step.
        eapply evt_cut.
        { eapply (memcpy_callZ (Z_to_bv 64 908428) (Z_to_bv 64 (bv_unsigned sp + -48))) with (Dst := Dr) (Src := Dy2) (N := Z.of_nat (bn_top by_) * 8)
            (src := u64s (wlimbs (firstn (bn_top by_) (bn_buf by_)))) (junk := u64s (wlimbs (firstn (bn_top by_) (bn_buf br))));
            [exact SRC| rewrite u64s_length, wlimbs_len, firstn_length_le by (clear - OKy2 LBY; lia); clear; lia
            | replace (Z.to_nat (Z.of_nat (bn_top by_) * 8)) with (8 * bn_top by_)%nat by (clear; lia); exact U1
            | clear - LDJ HDM OKy2; lia | clear - OKy3 OKy2; lia | clear - Dy0 DyC CEIL LO SPR; lia | clear - Dr0 DrC CEIL LO SPR; lia | exact MI2]. }
        post_call psegs m2.
        step. rewrite (sx32_small (Z.of_nat (bn_top by_))) by (clear - OKy2 OKy3; lia).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
        assert (LSEG : length (firstn (bn_top by_) (bn_buf by_)) = bn_top by_) by (apply firstn_length_le; clear - OKy2 LBY; lia).
        eapply (FIN2 m4 (splice (bn_buf br) 0 (firstn (bn_top by_) (bn_buf by_))) Dr (Dr + 8 * Z.of_nat (bn_dmax br)));
          [ right; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn; split; [exact Hinpr| clear; lia]
          | eapply (w_limbs OW2 LB ls1 AD EA false [rx] _ rx pr Dr); [left; reflexivity| exact HVx2| exact Edr| exact Hinpr| cbn [fst snd]; fold br; clear; lia| cbn [fst snd]; fold br; clear; lia]
          | rewrite splice_length; [exact LBR| rewrite LSEG; clear - HDM LBR; lia]
          | apply splice_limbs; [exact OKq1| apply limbs_firstn; exact OKy1]
          | | exact BNy2 | exact BNr | exact FR2 | exact ERR2 | exact ST2 | exact MI | exact MU3 | exact WM3].
        unfold splice. rewrite firstn_O. cbn [app Nat.add]. rewrite LSEG. apply limbarr_app. rewrite LSEG. split; [|exact U2].
        eapply CB_u64arr. exact PC.
      }
    step. if_cases KD; zify_cond KD; rewrite !signed_small in KD by lia.
    - (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      ihere. to_implM. unfold bn_wexpand, bbind, bget, bret, bset. cbn [bind ret tree_ops tbind fst snd]. fold bx.
      replace (bn_top by_ <=? bn_dmax bx)%nat with true by (symmetry; apply Nat.leb_le; lia).
      cbn [tbind fst snd].
      eapply (FIN s ls m1 OW errv);
        [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL)
        | exact (lib_state_frame s LB [] ls m m1 OW AD EA _ HEAP LS MU WM WOK)
        | apply (seg_auxv _ _ _ _ _ _ _ _ _ HEAP AUX MU WM HWL SPB); unfold GLOBALS_TOP; lia
        | exact ST | exact ERR | exact MI
        | apply (seg_lx_pres _ _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL); unfold GLOBALS_TOP; lia
        | reflexivity | reflexivity | apply refs_stable_refl | reflexivity | fold bx; lia
        | intros q0 A0 n0 Hq0 _; exact Hq0 | exact FR].
    - (* [comment removed for export] *)
      step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
      pose proof (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL) as HEAP1.
      pose proof (lib_state_frame s LB [] ls m m1 OW AD EA _ HEAP LS MU WM WOK) as LS1.
      assert (AUX1 : rauxv_ok m1 B) by (apply (seg_auxv _ _ _ _ _ _ _ _ _ HEAP AUX MU WM HWL SPB); unfold GLOBALS_TOP; lia).
      assert (LXP1 : lx_pres LB (bv_unsigned sp) LIBW_bn m m1) by (apply (seg_lx_pres _ _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL); unfold GLOBALS_TOP; lia).
      ihere. to_implM.
      eapply implM_embed_bind.
      { eapply implM_embed_leaves; [apply (bn_wexpand_leaves rx (bn_top by_) ls HVx OKx2)|].
        eapply (bn_expand2_walk HM HF) with (lo := lo) (B := B) (errv := errv) (r := rx) (a := ax) (OW := OW) (LB := LB) (AD := AD) (EA := EA);
          [| reflexivity | exact HAx | reflexivity | reflexivity | lia].
        unfold bn_pre. rewrite ESP.
        split; [exact HEAP1|]. split; [exact LS1|]. split; [exact AUX1|]. split; [lia|].
        split; [exact ST|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|]. split; [unfold BN_EXPAND2_STACK; lia|].
        split; [unfold LX_ERRNO, RATP; exact ERR| exact MI]. }
      cbv beta. intros [u ls1] st1 ms1 [PO LEAF]. unfold bn_post in PO. cbn [fst snd] in *.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & OW2 & errv2 & -> & HEAP2 & LS2 & AUX2 & ST2 & ERR2
                      & MI2 & LXP2 & FA2 & SO2 & RST2 & -> & HDM & WRES & BST).
      rewrite ESP in *.
      replace (ret_pc (Z_to_bv 64 908396)) with (Z_to_bv 64 908396) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct LEAF as (LF1 & LF2 & LF3 & LF4 & LF5). cbn [snd] in *.
      assert (FR2 : rw_cells psegs m2 (bv_unsigned sp + -48) [CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 junk))))); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply rw_cells_agree; [apply agree_of_lx_pres; exact LXP2 | exact FR |].
        intros a Ha. cbn in Ha. split; [|left; lia]. unfold LIBW_bn. cbn [rin_ivs fst snd]. lia. }
      unfold implM. iprefix.
      step. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by lia; lia|]. clear KZ.
      ihere. to_implM. unfold bset. cbn [ret tree_ops].
      eapply (FIN st1 ls1 m2 OW2 errv2);
        [exact HEAP2 | exact LS2 | exact AUX2 | exact ST2 | unfold LX_ERRNO, RATP in ERR2; exact ERR2 | exact MI2
        | eapply lx_pres_trans; [exact LXP1|]; eapply lx_pres_weaken; [exact LXP2| lia | intros b0 Hb0; exact Hb0 | intros a0 Ha0; exact Ha0]
        | congruence | congruence | exact RST2 | apply LF1; exact EXY | exact HDM | exact BST | exact FR2].
  Qed.
End Proofs.
End WithCeiling0.
