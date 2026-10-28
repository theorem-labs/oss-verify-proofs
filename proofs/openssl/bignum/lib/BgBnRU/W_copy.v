(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BnInv BnBridge BgState BgInv BgLib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit F_memset F_memcpy.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem BnTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_crypto BnUKit BnUKit2.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep BnLeaves.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import BgLeaves W_expand.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_COPY : Z := 0xfe304.
Definition BN_COPY_STACK : Z := 48 + BN_EXPAND2_STACK.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma BN_copy_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rx ry : bnref) (ax ay : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_COPY_STACK -> tp = wz RATP ->
    ref_at bs OW PL rx ax -> ref_at bs OW PL ry ay -> wref PL rx -> ry <> ROne -> a0 = wz ax -> a1 = wz ay ->
    implM bgusegs (interp (embed (BN_copy (tree_ops bptr) rx ry bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = wz ax /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW')))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_COPY) fc None m (seg_rom bgusegs)).
  Proof.
    intros until ay. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> HAx HAy WRx NROy -> ->. pose proof (proj1 WRx) as NROx.
    unfold BN_COPY_STACK, BN_EXPAND2_STACK, BN_COPY, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).

    destruct (lib_state_open [] bs m OW PL EA ry ay LS ND HAy ltac:(intros []) NROy) as ((Dy & BNy & ARRy) & (OKy1 & OKy2 & OKy3 & OKy4) & _).
    destruct (lib_state_open [] bs m OW PL EA rx ax LS ND HAx ltac:(intros []) NROx) as ((Dx & BNx & ARRx) & (OKx1 & OKx2 & OKx3 & OKx4) & _).
    set (by_ := getbn ry bs) in *. set (bx := getbn rx bs) in *.
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAx NROx) as (XA0 & XAC & XAI).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAy NROy) as (YA0 & YAC & YAI).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAx) as HVx.
    assert (FLRy : 0 <= bn_flags by_ <= 1) by (destruct OKy4 as [E|E]; rewrite E; lia).
    assert (EL4 : Z.land (bn_flags by_) 4 = 0) by (destruct OKy4 as [E|E]; rewrite E; reflexivity).
    unfold bn_cells in BNx, BNy. unfold BG_DMAX in OKx3, OKy3.
    apply (flag_cell_split bgusegs m ay _ _ _ _ (bn_flags by_) FLRy) in BNy.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    unfold BN_copy, bbind, bget. cbn [bind ret tree_ops tbind fst snd]. fold by_.
    unfold has_flag, BN_FLG_CONSTTIME. rewrite EL4. cbn [Z.eqb negb].
    unfold implM. iprefix.
    destruct (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HAx NROx) as (PX0 & PX8).
    destruct (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HAy NROy) as (PY0 & PY8).
    carve_frame 48%nat ST. do 7 step.
    chk ltac:(fun C => clear - C PY0 YAC; lia).
    step. step.
    step. rewrite (land7_wrap _ PY8).
    chk ltac:(fun C => clear - C; lia).
    step.
    rewrite (zxb_small (bn_flags by_)) by lia.
    step. rewrite (unsigned_lit (bn_flags by_)), EL4 by lia.
    step. if_true. step.
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    destruct (Nat.eqb rx ry) eqn:EXY.
    {
      apply Nat.eqb_eq in EXY. subst ry. pose proof (ref_at_fun _ _ _ _ _ _ ND HAx HAy) as EA0. subst ay.
      step. replace (bv_eqb (Z_to_bv 64 ax) (Z_to_bv 64 ax)) with true by (symmetry; unfold bv_eqb; apply Z.eqb_refl).
      step. do 5 step. step. release_frame FR ST (bv_unsigned sp). step.
      ihere. to_implM. unfold bret. cbn [ret tree_ops embed interp]. apply implM_ret. apply evt_done.
      lazymatch goal with |- bn_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
      unfold bn_post. do 15 eexists. exists mF, OW, PL, errv. split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)|].
      split; [exact (lib_state_frame s LB _ _ [] bs m mF OW PL EA _ HEAP LS MU WM FROK WOK)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia|]. split; [exact ST|].
      split; [unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); unfold GLOBALS_TOP; lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|].
      split; [reflexivity|]. split; [reflexivity|]. intros q0 A0 n0 Hq0 _. exact Hq0. }
    apply Nat.eqb_neq in EXY.
    pose proof (struct_disj s OW LB m HEAP bs PL EA _ _ PARTS FROK rx ry ax ay EXY HAx HAy) as SDJ.
    step. if_cases KE; zify_cond KE; rewrite ?unsigned_lit in KE by lia; [exfalso; lia|]. clear KE.
    chk ltac:(fun C => clear - C PX0 XAC; lia).
    step. rewrite (land7_wrap _ PX8).
    chk ltac:(fun C => clear - C; lia).
    step. step. rewrite (sx32_small (Z.of_nat (bn_top by_))) by lia.
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_dmax bx))) by lia.

    assert (FIN : forall (st1 : PState) (bs1 : bstate bptr) (m2 : mem) (OW2 : list block) (errv2 : word) (jk : list byte)
                         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      RHEAP st1 (OW2 ++ LB) m2 -> lib_state bs1 m2 OW2 PL EA -> rauxv_ok m2 B -> stk bgusegs m2 lo (bv_unsigned sp + -48) ->
      rw_cells bgusegs m2 3346164 [C4 errv2] -> mem_inv bgusegs m2 -> lx_pres LB (bv_unsigned sp) (XW PL) m m2 ->
      ps_fa st1 = ps_fa s -> ps_so st1 = ps_so s -> refs_stable bs OW bs1 OW2 -> st_ctx bs1 = st_ctx bs ->
      getbn ry bs1 = by_ -> (bn_top by_ <= bn_dmax (getbn rx bs1))%nat ->
      (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW2) ->
      rw_cells bgusegs m2 (bv_unsigned sp + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      implM bgusegs (interp (embed (TRet (tt, setbn rx (mkBN (bn_d (getbn rx bs1))
                                                          (if (0 <? bn_top by_)%nat then splice (bn_buf (getbn rx bs1)) 0 (firstn (bn_top by_) (bn_buf by_))
                                                           else bn_buf (getbn rx bs1))
                                                          (bn_top by_) (bn_neg by_) (bn_flags (getbn rx bs1))) bs1)))) st1
        (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
                 (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 ax /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW')))
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 RATP) x5 x6 x7 sp (Z_to_bv 64 ax) x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 ay) (Z_to_bv 64 (Z.of_nat (bn_top by_))) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0xfe37c) fc None m2 (seg_rom bgusegs))).
    { intros st1 bs1 m2 OW2 errv2 jk x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
             HEAP2 LS2 AUX2 ST2 ERR2 MI2 LXP2 FA2 SO2 RST2 ECTX Eby HDM BST FR2.
      clear BNx BNy ARRx ARRy MU WM ST ERR MI FR HWL WOK.
      assert (FROK2 : frames_ok PL (bv_unsigned sp) B) by exact FROK.
      pose proof (ref_at_stable _ _ _ _ _ _ _ RST2 HAx) as HAx2. pose proof (ref_at_stable _ _ _ _ _ _ _ RST2 HAy) as HAy2.
      pose proof (RH_nodup_l _ _ _ _ HEAP2) as ND2.
      pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS2; pose proof PARTS2 as (WFS2 & PWF2 & IDS2 & PLB2 & ERRB2).
      pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAx2) as HVx2. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAy2) as HVy2.
      destruct (lib_state_open [] bs1 m2 OW2 PL EA ry ay LS2 ND2 HAy2 ltac:(intros []) NROy) as ((Dy2 & BNy2 & ARRy2) & _ & _).
      destruct (lib_state_open [] bs1 m2 OW2 PL EA rx ax LS2 ND2 HAx2 ltac:(intros []) NROx) as ((Dr & BNr & ARRr) & (OKq1 & OKq2 & OKq3 & OKq4) & LSH).
      destruct (bn_arr_facts st1 OW2 LB m2 HEAP2 bs1 PL EA _ _ PARTS2 FROK2 ry Dy2 HVy2 ltac:(assumption) ARRy2) as (Uy & LENy & Dy0 & DyC & DyI & DSEPy).
      destruct (bn_arr_facts st1 OW2 LB m2 HEAP2 bs1 PL EA _ _ PARTS2 FROK2 rx Dr HVx2 ltac:(assumption) ARRr) as (Ur & LENr & Dr0 & DrC & DrI & DSEPr).
      rewrite Eby in BNy2, ARRy2, Uy, LENy, DyC, DyI, DSEPy.
      set (br := getbn rx bs1) in *.
      pose proof (DSEPr rx ax HAx2) as SEPrr. pose proof (DSEPr ry ay HAy2) as SEPry.
      pose proof (DSEPy rx ax HAx2) as SEPyr.
      pose proof (struct_disj st1 OW2 LB m2 HEAP2 bs1 PL EA _ _ PARTS2 FROK2 rx ry ax ay EXY HAx2 HAy2) as SDJ2.
      pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROK2 HAx2 NROx) as (XB0 & XBC & XBI).
      pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROK2 HAy2 NROy) as (YB0 & YBC & YBI).
      unfold bn_cells in BNy2, BNr. unfold BG_DMAX in OKq3.
      cbn [embed interp]. apply implM_ret.
      unfold MallocRep.wz in *.

      assert (FIN2 : forall mF (nb : list Z) (l3 h3 : Z) z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31,
                w_lib bs1 OW2 PL lo (bv_unsigned sp) (l3, h3) -> w_okc OW2 LB bs1 PL EA (bv_unsigned sp) false [rx] (l3, h3) ->
                length nb = bn_dmax br -> limbs nb ->
                u64arr bgusegs mF Dr (wlimbs nb) ->
                rw_cells bgusegs mF ay [C8 (Z_to_bv 64 Dy2); C4 (Z_to_bv 64 (Z.of_nat (bn_top by_))); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax by_)));
                                      C4 (Z_to_bv 64 (Z.b2z (bn_neg by_))); C4 (Z_to_bv 64 (bn_flags by_))] ->
                rw_cells bgusegs mF ax [C8 (Z_to_bv 64 Dr); C4 (Z_to_bv 64 (Z.of_nat (bn_top br))); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax br)));
                                      C4 (Z_to_bv 64 (Z.b2z (bn_neg br))); C4 (Z_to_bv 64 (bn_flags br))] ->
                rw_cells bgusegs mF (bv_unsigned sp + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
                rw_cells bgusegs mF 3346164 [C4 errv2] -> stk bgusegs mF lo (bv_unsigned sp + -48) -> mem_inv bgusegs mF ->
                munch [(bv_unsigned sp + -48, bv_unsigned sp); (ax, ax + 24); (l3, h3)]%Z m2 mF -> wmono bgusegs m2 mF ->
                evt bgusegs
                  (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
                     (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 ax /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW'))
                     (tt, setbn rx (mkBN (bn_d br) nb (bn_top by_) (bn_neg by_) (bn_flags br)) bs1) st1)
                  (MS (mkR z1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 RATP) z5 z6 z7 sp (Z_to_bv 64 ax)
                           z10 z11 z12 z13 z14 z15 z16 z17 (Z_to_bv 64 ay) (Z_to_bv 64 (Z.of_nat (bn_top by_)))
                           s4 s5 s6 s7 s8 s9 s10 s11 z28 z29 z30 z31)
                      F (Z_to_bv 64 0xfe3a4) fc None mF (seg_rom bgusegs))).
      { intros mF nb l3 h3 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 HW3L HW3K Lnb LMnb UF BNyF BNrF FRF ERRF STF MIF MUF WMF.
        clear BNy2 BNr FR2 ERR2 ST2 MI2 Ur Uy.
        clear SDJ SEPry SEPyr XAI YAI YBI DyI.
        assert (LENnb : Z.of_nat (length (wlimbs nb)) = Z.of_nat (bn_dmax br)) by (rewrite wlimbs_len, Lnb; reflexivity).
        step. rewrite (sx32_small (Z.of_nat (bn_top by_))) by lia.
        step. rewrite (sx32_small (Z.b2z (bn_neg by_))) by (destruct (bn_neg by_); cbn; lia).
        step. step. step.
        do 5 step. step. release_frame FRF STF (bv_unsigned sp). step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mG end.
        apply evt_done.
        assert (HWL3 : Forall (w_lib bs1 OW2 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -48, bv_unsigned sp); (ax, ax + 24); (l3, h3)]).
        { constructor; [left; cbn; lia|]. constructor; [right; right; exists rx, ax; split; [exact HAx2|]; split; [exact NROx|]; cbn; lia|]. constructor; [exact HW3L| constructor]. }
        assert (WOK3 : Forall (w_ok OW2 LB bs1 PL EA (bv_unsigned sp) [rx]) [(bv_unsigned sp + -48, bv_unsigned sp); (ax, ax + 24); (l3, h3)]).
        { constructor; [apply w_stack; cbn; lia|]. constructor; [eapply (w_struct OW2 LB bs1 PL EA (bv_unsigned sp) false [rx] _ rx ax); [left; reflexivity| exact HAx2| assumption| cbn; lia| cbn; lia]|].
          constructor; [exact HW3K| constructor]. }
        unfold bn_post. do 15 eexists. exists mG, OW2, PL, errv2. split; [reflexivity|]. cbn [fst snd].
        split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROK2 MUF WMF HWL3 CEIL)|].
        split.
        { unfold lib_state. eapply (lib_state_close [] bs1 mG OW2 PL EA rx ax); [| exact ND2| exact HAx2| exact NROx| | |].
          - exact (lib_state_frame st1 LB _ _ [rx] bs1 m2 mG OW2 PL EA _ HEAP2 LSH MUF WMF FROK WOK3).
          - exists Dr. split.
            + unfold bn_cells, bn_dmax. cbn [bn_top bn_buf bn_neg bn_flags]. rewrite Lnb. exact BNrF.
            + pose proof ARRr as ARRr'. unfold bn_arr in ARRr'. unfold bn_dmax in *. destruct (bn_d br) as [pr|] eqn:Edr0.
              * unfold bn_arr, bn_dmax. cbn [bn_d bn_buf]. rewrite Lnb. split; [exact (proj1 ARRr')| exact UF].
              * destruct (bn_arr_null PL rx m2 OW2 Dr br PWF2 WRx Edr0 ARRr) as [ED Eb].
                apply (bn_arr_nil_intro PL rx mG OW2 Dr _ PWF2 WRx ED); [|reflexivity]. cbn [bn_buf]. rewrite Eb in Lnb. cbn in Lnb. destruct nb; [reflexivity| discriminate].
          - unfold bg_ok, bn_dmax. cbn [bn_buf bn_top bn_flags]. rewrite Lnb. unfold BG_DMAX in *.
            split; [exact LMnb|]. split; [exact HDM|]. split; [clear - OKq3 Lnb; unfold bn_dmax in *; lia| exact OKq4].
          - apply ids_ok_setbn_same; [exact IDS2| exact HVx2|]. unfold bn_blocks, bn_dmax. cbn [bn_d bn_buf]. rewrite Lnb. reflexivity. }
        split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROK2 AUX2 MUF WMF HWL3 SPB ltac:(lia)); unfold GLOBALS_TOP; lia|]. split; [exact STF|].
        split; [unfold LX_ERRNO, RATP; exact ERRF|]. split; [exact MIF|].
        split. { eapply lx_pres_trans; [exact LXP2|]. apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROK2 MUF WMF HWL3 CEIL); unfold GLOBALS_TOP; lia. }
        split; [exact FA2|]. split; [exact SO2|].
        split. { eapply refs_stable_trans; [exact RST2| apply refs_stable_setbn]. }
        split; [reflexivity|]. split; [reflexivity| exact BST]. }
      clear SDJ SDJ2 SEPyr XAI YAI XBI YBI DyI OKx4 OKy4 OKq4.
      pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (ax, ax + 24); (ax, ax + 24)]%Z m2) as MU3.
      pose proof (wmono_refl bgusegs m2) as WM3.
      step. rewrite (sx32_small (Z.of_nat (bn_top by_))) by lia.
      step. if_cases KT; zify_cond KT.
      -
        assert (ET0 : bn_top by_ = 0%nat) by (apply andb_false_iff in KT; destruct KT as [KT|KT]; apply Z.ltb_ge in KT; lia).
        replace (0 <? bn_top by_)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
        eapply (FIN2 m2 (bn_buf br) ax (ax + 24));
          [ right; right; exists rx, ax; split; [exact HAx2|]; split; [exact NROx|]; cbn; lia
          | eapply (w_struct OW2 LB bs1 PL EA (bv_unsigned sp) false [rx] _ rx ax); [left; reflexivity| exact HAx2| assumption| cbn; lia| cbn; lia]
          | reflexivity | exact OKq1 | exact Ur | exact BNy2 | exact BNr | exact FR2 | exact ERR2 | exact ST2 | exact MI2 | exact MU3 | exact WM3].
      -
        assert (TOPP : (0 < bn_top by_)%nat) by lia.
        replace (0 <? bn_top by_)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
        clear MU3 WM3.
        assert (HDr : exists pr, bn_d br = Some pr /\ In (pr, Dr, 8 * Z.of_nat (bn_dmax br)) OW2).
        { pose proof ARRr as ARRr'. unfold bn_arr in ARRr'. destruct (bn_d br) as [pr|] eqn:Edr0; [exists pr; split; [reflexivity| exact (proj1 ARRr')]|].
          exfalso. destruct (bn_arr_null PL rx m2 OW2 Dr br PWF2 WRx Edr0 ARRr) as [_ E]. unfold bn_dmax in HDM. rewrite E in HDM. cbn in HDM. lia. }
        destruct HDr as (pr & Edr & Hinpr).

        assert (LDJ : Dr + 8 * Z.of_nat (bn_dmax br) <= Dy2 \/ Dy2 + 8 * Z.of_nat (bn_dmax by_) <= Dr).
        { subst br by_. rewrite <- Eby. eapply (arr_arr_disj bs1 OW2 PL EA (bv_unsigned sp) B); [exact HEAP2| exact PARTS2| exact FROK2| exact EXY| exact HVx2| exact HVy2| exact NROy| exact Edr| exact Hinpr|].
          rewrite Eby. exact ARRy2. }
        pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m2) as MU3.
        pose proof (wmono_refl bgusegs m2) as WM3.
        assert (LBR : length (bn_buf br) = bn_dmax br) by reflexivity.
        assert (LBY : length (bn_buf by_) = bn_dmax by_) by reflexivity.
        apply (proj1 (limbarr_split bgusegs m2 Dr (bn_buf br) (bn_top by_) ltac:(lia))) in Ur. destruct Ur as [U1 U2].
        assert (SRC : bytes_at bgusegs m2 Dy2 (u64s (wlimbs (firstn (bn_top by_) (bn_buf by_))))).
        { apply limbarr_bytes. apply (proj1 (limbarr_split bgusegs m2 Dy2 (bn_buf by_) (bn_top by_) ltac:(lia))) in Uy. exact (proj1 Uy). }
        apply limbarr_CB in U1. rewrite firstn_length_le in U1 by lia.
        pose proof (RH_range _ _ _ _ _ _ _ HEAP2 Hinpr) as (_ & DR16 & _).
        pose proof (bn_arr_ualign _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 ARRy2 ltac:(clear - TOPP OKy2; unfold bn_dmax in *; lia)) as (_ & DY16).
        do 2 step. step. step.
        rewrite (lor_land7 Dr Dy2) by (clear - DR16 DY16; Z.div_mod_to_equations; lia).
        chk ltac:(fun C => clear - C; lia).
        step.
        rewrite ?(unsigned_lit (Z.of_nat (bn_top by_))) by lia.
        replace (Z.shiftl (Z.of_nat (bn_top by_)) 3) with (Z.of_nat (bn_top by_) * 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
        step. step.
        eapply evt_cut.
        { eapply (memcpy_callZ (Z_to_bv 64 1041316) (Z_to_bv 64 (bv_unsigned sp + -48))) with (Dst := Dr) (Src := Dy2) (N := Z.of_nat (bn_top by_) * 8)
            (src := u64s (wlimbs (firstn (bn_top by_) (bn_buf by_)))) (junk := u64s (wlimbs (firstn (bn_top by_) (bn_buf br))));
            [exact SRC| rewrite u64s_length, wlimbs_len, firstn_length_le by (clear - OKy2 LBY; lia); clear; lia
            | replace (Z.to_nat (Z.of_nat (bn_top by_) * 8)) with (8 * bn_top by_)%nat by (clear; lia); exact U1
            | clear - LDJ HDM OKy2; lia | clear - OKy3 OKy2; lia | clear - Dy0 DyC CEIL LO SPR; lia | clear - Dr0 DrC CEIL LO SPR; lia | exact MI2]. }
        post_call bgusegs m2.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
        assert (LSEG : length (firstn (bn_top by_) (bn_buf by_)) = bn_top by_) by (apply firstn_length_le; clear - OKy2 LBY; lia).
        eapply (FIN2 m4 (splice (bn_buf br) 0 (firstn (bn_top by_) (bn_buf by_))) Dr (Dr + 8 * Z.of_nat (bn_dmax br)));
          [ right; left; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn; split; [exact Hinpr| clear; lia]
          | eapply (w_limbs OW2 LB bs1 PL EA (bv_unsigned sp) false [rx] _ rx pr Dr); [left; reflexivity| exact HVx2| exact Edr| exact Hinpr| cbn [fst snd]; fold br; clear; lia| cbn [fst snd]; fold br; clear; lia]
          | rewrite splice_length; [exact LBR| rewrite LSEG; clear - HDM LBR; lia]
          | apply splice_limbs; [exact OKq1| apply limbs_firstn; exact OKy1]
          | | exact BNy2 | exact BNr | exact FR2 | exact ERR2 | exact ST2 | exact MI | exact MU3 | exact WM3].
        unfold splice. rewrite firstn_O. cbn [app Nat.add]. rewrite LSEG. apply limbarr_app. rewrite LSEG. split; [|exact U2].
        eapply CB_u64arr. exact PC.
      }
    step. if_cases KD; zify_cond KD; rewrite !signed_small in KD by lia.
    -
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      ihere. to_implM. unfold bn_wexpand, bbind, bget, bret, bset. cbn [bind ret tree_ops tbind fst snd]. fold bx.
      replace (bn_top by_ <=? bn_dmax bx)%nat with true by (symmetry; apply Nat.leb_le; lia).
      cbn [tbind fst snd].
      eapply (FIN s bs m1 OW errv);
        [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)
        | exact (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK)
        | apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia
        | exact ST | exact ERR | exact MI
        | apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); unfold GLOBALS_TOP; lia
        | reflexivity | reflexivity | apply refs_stable_refl | reflexivity | reflexivity | fold bx; lia
        | intros q0 A0 n0 Hq0 _; exact Hq0 | exact FR].
    -
      step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
      pose proof (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL) as HEAP1.
      pose proof (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
      assert (AUX1 : rauxv_ok m1 B) by (apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia).
      assert (LXP1 : lx_pres LB (bv_unsigned sp) (XW PL) m m1) by (apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); unfold GLOBALS_TOP; lia).
      ihere. to_implM.
      eapply implM_embed_bind.
      { eapply BnLeaves.implM_embed_leaves; [apply (bn_wexpand_leaves rx (bn_top by_) bs HVx OKx2)|].
        eapply (bn_expand2_walk HM HF) with (lo := lo) (B := B) (errv := errv) (r := rx) (a := ax) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
          [| reflexivity | exact HAx | exact WRx | reflexivity | reflexivity | lia].
        unfold bn_pre. rewrite ESP.
        split; [exact HEAP1|]. split; [exact LS1|]. split; [eapply frames_ok_call; [exact FROK| exact CEIL| lia| lia]|]. split; [exact AUX1|]. split; [lia|]. split; [exact B63|].
        split; [exact ST|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|]. split; [unfold BN_EXPAND2_STACK; lia|].
        split; [unfold LX_ERRNO, RATP; exact ERR| exact MI]. }
      cbv beta. intros [u bs1] st1 ms1 [PO LEAF]. unfold bn_post in PO. cbn [fst snd] in *.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & OW2 & PL2 & errv2 & -> & HEAP2 & LS2 & AUX2 & ST2 & ERR2
                      & MI2 & LXP2 & FA2 & SO2 & RST2 & -> & -> & HDM & WRES & BST).
      rewrite ESP in *.
      replace (ret_pc (Z_to_bv 64 1041272)) with (Z_to_bv 64 1041272) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct LEAF as (LF1 & LF2 & LF3 & LF4 & LF5 & LF6). cbn [snd] in *.
      assert (FR2 : rw_cells bgusegs m2 (bv_unsigned sp + -48) [CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 junk))))); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply rw_cells_agree; [apply agree_of_lx_pres; exact LXP2 | exact FR |].
        intros a Ha. cbn in Ha. eapply (xw_client PL LB _ (bv_unsigned sp) B); [exact (proj1 FROK)| lia|].
        unfold LIBW_bgr, BnRep.LIBW_bn, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. lia. }
      unfold implM. iprefix.
      step. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by lia; lia|]. clear KZ.
      ihere. to_implM. unfold bset. cbn [ret tree_ops].
      eapply (FIN st1 bs1 m2 OW2 errv2);
        [exact HEAP2 | exact LS2 | exact AUX2 | exact ST2 | unfold LX_ERRNO, RATP in ERR2; exact ERR2 | exact MI2
        | eapply lx_pres_trans; [exact LXP1|]; eapply lx_pres_weaken; [exact LXP2| lia | intros b0 Hb0; exact Hb0 | intros a0 Ha0; exact Ha0]
        | congruence | congruence | exact RST2 | exact LF6 | apply LF1; exact EXY | exact HDM | exact BST | exact FR2].
  Qed.
End Proofs.
End WithCeiling0.
