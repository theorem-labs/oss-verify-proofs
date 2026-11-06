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
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Layout Lib_iface Lib_kit.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnHeap BnArr BnRep BnIface W_small W_expand BnLeaves ShiftPure RshiftArr W_lshift.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].


(* [comment removed for export] *)
Lemma BN_zero_ex_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A D : Z) (b : bignum bptr),
  rw_cells psegs m A (bn_cells D b) ->
  stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z -> mem_inv psegs m ->
  (A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A)%Z ->
  a0 = Z_to_bv 64 A ->
  evt psegs (bn_small_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)]%Z lo m
               (fun _ m' => rw_cells psegs m' A (bn_cells D (bn_zero_pure b))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xded14) fc None m (seg_rom psegs)).
Proof.
  intros until b. intros BN ST LO MI SEP ->.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 24)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  unfold bn_cells in BN.
  carve_frame 16%nat ST.
  do 4 step. step. step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
  finish.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_RSHIFT : Z := 0xf65c8.
Definition BN_RSHIFT_STACK : Z := 64 + BN_WEXPAND_STACK.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma bn_rshift_fixed_top_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
      (lo B : Z) (errv : word) (rr rx : bnref) (ar ax : Z) (n : Z),
    bn_pre s ls m OW LB AD EA sp lo B errv BN_RSHIFT_STACK -> tp = wz RATP ->
    ref_at ls OW AD rr ar -> ref_at ls OW AD rx ax -> a0 = wz ar -> a1 = wz ax -> a2 = wz n -> 0 <= n < 64 ->
    implM psegs (interp (embed (bn_rshift_fixed_top (tree_ops bptr) rr rx n ls))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA
               (fun _ _ _ a0' => a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_RSHIFT) fc None m (seg_rom psegs)).
  Proof.
    intros until n. intros (HEAP & LS & AUX & SPB & ST & CEIL & GLO & LO & ERR & MI) -> HAr HAx -> -> -> Hn.
    unfold BN_RSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, BN_RSHIFT, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    unfold bn_rshift_fixed_top.
    destruct (bnref_eqb rr rx) eqn:ERX; cbn [orb]. { unfold bunr. cbn [unreachable tree_ops embed interp]. apply implM_interp_unr. }
    apply bnref_eqb_false in ERX.
    replace (n <? 64) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
    unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
    destruct (lib_state_open [] ls m OW AD EA rx ax LS ND HAx ltac:(intros [])) as ((Dx & BNx & ARRx) & (OKx1 & OKx2 & OKx3 & OKx4) & _).
    set (bx := getbn rx ls) in *.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
    destruct (ref_at_inb _ _ _ _ _ ADB HAx) as (qx & Ax & nx & Eqx & Hinx & Rx1 & Rx2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP Hinx) as (XA0 & XA16 & _ & XAC & XAI).
    destruct (ref_at_inb _ _ _ _ _ ADB HAr) as (qr & Ar & nr & Eqr & Hinr & Rr1 & Rr2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP Hinr) as (RA0 & RA16 & _ & RAC & RAI).
    pose proof (struct_disj s OW LB m HEAP ls AD EA IDS ADB rr rx ar ax ERX HAr HAx) as SDJ0.
    unfold bn_cells in BNx. unfold BN_WORDS_MAX in OKx3.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3063480 - 164) with 3063316 in ERR.
    unfold implM. iprefix.
    carve_frame 64%nat ST. do 11 step. zstep.
    step. rewrite (sx32_small (Z.of_nat (bn_top bx))) by lia.
    do 3 zstep.
    setreg 21%Z (Z_to_bv 64 0) ltac:(f_equal; symmetry; apply (nw_m_0 n Hn)).
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
    assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB ls AD EA []) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL) as HEAP1.
    pose proof (lib_state_frame s LB [] ls m m1 OW AD EA _ HEAP LS MU WM WOK) as LS1.
    assert (AUX1 : rauxv_ok m1 B) by (apply (seg_auxv _ _ _ _ _ _ _ _ _ HEAP AUX MU WM HWL SPB); unfold GLOBALS_TOP; lia).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAr) as HVr.
    pose proof (st_okm_getbn rr ls SOK HVr) as (OKr1 & OKr2 & OKr3 & OKr4).
    zstep. if_cases KT; zify_cond KT.
    - (* [comment removed for export] *)
      assert (ETOP : bn_top bx = 0%nat).
      { clear - KT OKx2 OKx3. destruct (Z.ltb_spec 0 (Z.of_nat (bn_top bx))); [|lia]. destruct (Z.ltb_spec (Z.of_nat (bn_top bx)) 9223372036854775808); [discriminate | lia]. }
      clear KT.
      replace (bn_top bx =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; exact ETOP).
      cbn [tbind].
      (* [comment removed for export] *)
      destruct (lib_state_open [] ls m1 OW AD EA rr ar LS1 ND HAr ltac:(intros [])) as ((Dr & BNr & ARRr) & _ & LSH).
      set (br := getbn rr ls) in *.
      pose proof (munch_refl [(bv_unsigned sp + -64 - 16, bv_unsigned sp + -64); (ar, ar + 24)]%Z m1) as MUz. pose proof (wmono_refl psegs m1) as WMz.
      clear BNx SDJ0 XAI XA0 XA16 XAC Rx1 Rx2.
      do 2 zstep.
      eapply evt_cut.
      { eapply BN_zero_ex_spec with (lo := lo) (A := ar) (D := Dr) (b := br); [exact BNr | rewrite ESP; exact ST | rewrite ESP; lia | exact MI | rewrite ESP; lia | reflexivity]. }
      intros ms' PO. unfold bn_small_post in PO.
      destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & STc & BNr2).
      subst ms'. rewrite ESP in *.
      replace (ret_pc (Z_to_bv 64 1009320)) with (Z_to_bv 64 1009320) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply (rw_cells_transport psegs _ m1 m2) in FR; [| exact MUc | exact WMc | cbn; lia].
      eapply (rw_cells_transport psegs _ m1 m2) in ERR; [| exact MUc | exact WMc | cbn; lia].
      clear ST MI BNr.
      zstep. zstep.
      do 7 step. release_frame FR STc (bv_unsigned sp). step. step.
      ihere. to_implM. cbn [embed interp]. apply implM_ret. apply evt_done.
      assert (MUT : munch [(bv_unsigned sp - 80, bv_unsigned sp); (ar, ar + 24)]%Z m m2).
      { eapply munch_trans; [eapply munch_weaken; [|exact MU]| eapply munch_weaken; [|exact MUc]];
          unfold sub_fp; intros x Hx; cbn [outside] in *; lia. }
      assert (WMT : wmono psegs m m2) by (eapply wmono_trans; eauto).
      assert (HWLT : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp - 80, bv_unsigned sp); (ar, ar + 24)]).
      { constructor; [left; cbn; lia|]. constructor; [right; exists (qr, Ar, nr); cbn; auto| constructor]. }
      assert (WOKc : Forall (w_ok OW LB ls AD EA [rr]) [(bv_unsigned sp + -64 - 16, bv_unsigned sp + -64); (ar, ar + 24)]).
      { constructor; [apply w_stack; cbn; lia|]. constructor; [eapply (w_struct OW LB ls AD EA false [rr] _ rr ar); [left; reflexivity| exact HAr| cbn; lia| cbn; lia]| constructor]. }
      unfold bn_post. do 15 eexists. exists m2, OW, errv. split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MUT WMT HWLT CEIL)|].
      split.
      { unfold lib_state. eapply (lib_state_close [] ls m2 OW AD EA rr ar); [| exact ND| exact HAr| | |].
        - exact (lib_state_frame s LB [rr] ls m1 m2 OW AD EA _ HEAP1 LSH MUc WMc WOKc).
        - exists Dr. split; [exact BNr2|]. unfold bn_arr, bn_zero_pure in *. cbn [bn_d bn_buf bn_dmax].
          destruct (bn_d br) as [pr|] eqn:Edr; [|exact ARRr]. destruct ARRr as [Hin Uarr]. split; [exact Hin|].
          eapply u64arr_transport; [exact Uarr | exact MUc | exact WMc |].
          pose proof (RH_range _ _ _ _ _ _ _ HEAP Hin) as (_ & _ & _ & PC & _).
          pose proof (struct_limbs_disj s OW LB m HEAP ls AD EA IDS ADB rr rr ar pr Dr _ HAr HVr Edr Hin) as SLD.
          cbn [disjoint_from]. rewrite wlimbs_len. fold (bn_dmax br). lia.
        - unfold bn_okm, bn_zero_pure, bn_dmax in *. cbn [bn_buf bn_top bn_flags]. split; [exact OKr1|]. split; [lia|]. split; [exact OKr3| exact OKr4].
        - apply ids_ok_setbn_same; [exact IDS| exact HVr| reflexivity]. }
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ HEAP AUX MUT WMT HWLT SPB); unfold GLOBALS_TOP; lia|]. split; [exact STc|].
      split; [unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MIc|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ HEAP MUT WMT HWLT CEIL); unfold GLOBALS_TOP; lia|].
      split; [reflexivity|]. split; [reflexivity|].
      split. { intros r0 a0 H0. apply ref_at_setbn. exact H0. }
      reflexivity.
    - (* [comment removed for export] *)
      assert (NTOP : bn_top bx <> 0%nat) by (clear - KT0; lia). clear KT1.
      replace (bn_top bx =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; exact NTOP).
      zstep.
      setreg 19%Z (Z_to_bv 64 (Z.of_nat (bn_top bx))) ltac:(f_equal; rewrite bk_swrap32_small by (clear - OKx2 OKx3; lia); clear; lia).
      zstep. if_cases KE; zify_cond KE. { exfalso. rewrite ?unsigned_lit in KE by lia. clear - KE SDJ0. lia. }
      clear KE.
      do 3 zstep.
      ihere. to_implM.
      eapply implM_embed_bind.
      { eapply implM_embed_leaves; [apply (bn_wexpand_leaves rr (bn_top bx) ls HVr OKr2)|].
        eapply (bn_wexpand_walk HM HF) with (lo := lo) (B := B) (errv := errv) (r := rr) (a := ar) (OW := OW) (LB := LB) (AD := AD) (EA := EA);
          [| reflexivity | exact HAr | reflexivity | reflexivity | lia].
        unfold bn_pre. rewrite ESP.
        split; [exact HEAP1|]. split; [exact LS1|]. split; [exact AUX1|]. split; [lia|].
        split; [exact ST|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|]. split; [unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia|].
        split; [unfold LX_ERRNO, RATP; exact ERR| exact MI]. }
      cbv beta. intros [u ls1] st1 ms1 [PO LEAF]. unfold bn_post in PO. cbn [fst snd] in *.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & OW2 & errv2 & -> & HEAP2 & LS2 & AUX2 & ST2 & ERR2
                      & MI2 & LXP2 & FA2 & SO2 & RST2 & -> & HDM & WRES).
      rewrite ESP in *.
      replace (ret_pc (Z_to_bv 64 1009188)) with (Z_to_bv 64 1009188) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct LEAF as (LF1 & LF2 & LF3 & LF4 & LF5). cbn [snd] in *.
      assert (Ebx : getbn rx ls1 = bx) by (apply LF1; exact ERX).
      pose proof (RST2 _ _ HAr) as HAr2. pose proof (RST2 _ _ HAx) as HAx2.
      pose proof (RH_nodup_l _ _ _ _ HEAP2) as ND2.
      destruct (lib_state_h_parts _ _ _ _ _ _ LS2) as (IDS2 & ADB2 & ERRB2 & SOK2).
      pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAr2) as HVr2. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAx2) as HVx2.
      destruct (lib_state_open [] ls1 m2 OW2 AD EA rx ax LS2 ND2 HAx2 ltac:(intros [])) as ((Dx2 & BNx2 & ARRx2) & _ & _).
      rewrite Ebx in BNx2, ARRx2.
      destruct (lib_state_open [] ls1 m2 OW2 AD EA rr ar LS2 ND2 HAr2 ltac:(intros [])) as ((Dr & BNr & ARRr) & (OKq1 & OKq2 & OKq3 & OKq4) & LSH).
      set (br := getbn rr ls1) in *.
      destruct (bn_arr_facts st1 OW2 LB m2 HEAP2 ls1 AD EA IDS2 ADB2 rr Dr HVr2 ARRr) as (Ur & LENr & Dr0 & DrC & DrI & DSEPr).
      fold br in Ur, LENr, DrC, DrI, DSEPr.
      pose proof (DSEPr rr ar HAr2) as SEPrr. pose proof (DSEPr rx ax HAx2) as SEPrx.
      pose proof (struct_disj st1 OW2 LB m2 HEAP2 ls1 AD EA IDS2 ADB2 rr rx ar ax ERX HAr2 HAx2) as SDJ.
      destruct (ref_at_inb _ _ _ _ _ ADB2 HAr2) as (qr2 & Ar2 & nr2 & Eqr2 & Hinr2 & Rr21 & Rr22).
      pose proof (RH_range _ _ _ _ _ _ _ HEAP2 Hinr2) as (RB0 & RB16 & _ & RBC & RBI).
      unfold bn_cells in BNx2, BNr. unfold BN_WORDS_MAX in OKq3.
      assert (FR2 : rw_cells psegs m2 (bv_unsigned sp + -64) [CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 (take 48 (take 56 junk)))))));
                                                             C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply rw_cells_agree; [apply agree_of_lx_pres; exact LXP2 | exact FR |].
        intros a Ha. cbn in Ha. split; [|left; lia]. unfold LIBW_bn. cbn [rin_ivs fst snd]. lia. }
      clear FR BNx SDJ0 XAI XA0 XA16 XAC Rx1 Rx2 RAI RA0 RA16 RAC Rr1 Rr2.
      cbn [embed interp]. apply implM_ret.
      pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m2) as MU3.
      pose proof (wmono_refl psegs m2) as WM3.
      unfold LX_ERRNO, RATP in ERR2. change (3063480 - 164) with 3063316 in ERR2.
      unfold MallocRep.wz in *.
      zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by lia. lia. }
      assert (HDr : exists pr, bn_d br = Some pr /\ In (pr, Dr, 8 * Z.of_nat (bn_dmax br)) OW2).
      { unfold bn_arr in ARRr. destruct (bn_d br) as [pr|]; [exists pr; split; [reflexivity| exact (proj1 ARRr)]|].
        exfalso. destruct ARRr as [_ E]. unfold bn_dmax in HDM. rewrite E in HDM. cbn in HDM. lia. }
      destruct HDr as (pr & Edr & Hinpr).
      step. step.
      destruct (proj1 (limbarr_limbs_at psegs m2 Dr (bn_buf br)) Ur) as (LAr & WRr).
      assert (LBr : length (bn_buf br) = bn_dmax br) by reflexivity.
      destruct (bn_arr_facts st1 OW2 LB m2 HEAP2 ls1 AD EA IDS2 ADB2 rx Dx2 HVx2 ltac:(rewrite Ebx; exact ARRx2)) as (Ux & LENx & Dx0 & DxC & DxI & _).
      rewrite Ebx in Ux, LENx, DxC, DxI.
      assert (HDx : exists px, bn_d bx = Some px /\ In (px, Dx2, 8 * Z.of_nat (bn_dmax bx)) OW2).
      { unfold bn_arr in ARRx2. destruct (bn_d bx) as [px|]; [exists px; split; [reflexivity| exact (proj1 ARRx2)]|].
        exfalso. destruct ARRx2 as [_ E]. unfold bn_dmax in OKx2. rewrite E in OKx2. cbn in OKx2. lia. }
      destruct HDx as (px & Edx & Hinpx).
      pose proof (limbs_limbs_disj st1 OW2 LB m2 HEAP2 ls1 AD EA IDS2 rx rr px Dx2 _ pr Dr _ ltac:(congruence) HVx2 HVr2
                    ltac:(rewrite Ebx; exact Edx) Edr Hinpx Hinpr) as LDJ.
      destruct (proj1 (limbarr_limbs_at psegs m2 Dx2 (bn_buf bx)) Ux) as (LAx & _).
      set (f := firstn (bn_top bx) (bn_buf bx)).
      assert (Lf : length f = bn_top bx) by (subst f; apply firstn_length_le; exact OKx2).
      assert (LAf : limbs_at psegs m2 Dx2 f).
      { rewrite <- (firstn_skipn (bn_top bx) (bn_buf bx)) in LAx. apply limbs_at_app in LAx. exact (proj1 LAx). }
      assert (LArest : limbs_at psegs m2 (Dr + 8 * Z.of_nat (bn_top bx)) (skipn (bn_top bx) (bn_buf br))).
      { rewrite <- (firstn_skipn (bn_top bx) (bn_buf br)) in LAr. apply limbs_at_app in LAr. destruct LAr as [_ LA2].
        rewrite length_firstn, LBr in LA2. replace (Nat.min (bn_top bx) (bn_dmax br)) with (bn_top bx) in LA2 by (clear - HDM; lia). exact LA2. }
      assert (DISJf : Dx2 + 8 * Z.of_nat (length f) <= Dr \/ Dr + 8 * Z.of_nat (length f) <= Dx2) by (rewrite Lf; clear - LDJ OKx2 HDM; lia).
      assert (DJW : forall A k, (A + k <= Dr \/ Dr + 8 * Z.of_nat (bn_dmax br) <= A) ->
                disjoint_from [(Dr, Dr + 8 * Z.of_nat (length f))] A k).
      { intros A k H. cbn [disjoint_from]. split; [|exact I]. rewrite Lf. clear - H HDM. lia. }
      replace (Z.of_nat (bn_top bx)) with (Z.of_nat (length f)) by (rewrite Lf; reflexivity).
      assert (Hf : limbs f) by (unfold f; apply limbs_firstn; exact OKx1).
      assert (Htopf : 1 <= Z.of_nat (length f) < 2147483647) by (rewrite Lf; clear - NTOP OKx2 OKx3; lia).
      eapply (rsh_block _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 f Dx2 Dr n); try eassumption.
      { rewrite Lf. apply (wr_at_sub psegs m2 Dr (8 * Z.of_nat (length (bn_buf br))) 0 (8 * Z.of_nat (bn_top bx))) in WRr; [rewrite Z.add_0_r in WRr; exact WRr | clear; lia | clear; lia | rewrite LBr; clear - HDM; lia]. }
      intros m3 z5 z6 z7 z12 z14 z15 z16 z17 z21 RI.
      pose proof RI as (_ & _ & _ & MI3 & MUb & WMb).
      eapply (rw_cells_transport psegs _ m2 m3) in BNx2; [| exact MUb | exact WMb | apply DJW; cbn; clear - SEPrx; lia].
      step. rewrite (sx32_small (Z.b2z (bn_neg bx))) by (destruct (bn_neg bx); cbn; lia).
      eapply (rsh_last _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 f Dx2 Dr n); try eassumption.
      intros m4 z10 HR HFx MI4 MUc WMc.
      eapply (rw_cells_transport psegs _ m2 m4) in BNr; [| exact MUc | exact WMc | apply DJW; cbn; clear - SEPrr; lia].
      eapply (rw_cells_transport psegs _ m2 m4) in FR2; [| exact MUc | exact WMc | apply DJW; cbn; clear - DrC CEIL LO; lia].
      eapply (rw_cells_transport psegs _ m2 m4) in ERR2; [| exact MUc | exact WMc | apply DJW; cbn; clear - DrI HDM NTOP; lia].
      eapply (stk_transport_disjoint psegs _ m2 m4) in ST2; [| exact MUc | exact WMc | apply DJW; clear - DrC CEIL LO; lia].
      assert (MU4 : munch [(bv_unsigned sp + -64, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m2 m4).
      { eapply munch_weaken; [|exact MUc]. unfold sub_fp. intros x Hx. cbn [outside] in *. split; [|exact I]. rewrite Lf. clear - Hx HDM. lia. }
      assert (LArest4 : limbs_at psegs m4 (Dr + 8 * Z.of_nat (bn_top bx)) (skipn (bn_top bx) (bn_buf br))).
      { eapply limbs_at_transport; [exact LArest | exact MUc |]. cbn [disjoint_from]. split; [|exact I]. rewrite length_skipn, LBr, Lf. clear - HDM. lia. }
      set (nb := splice (bn_buf br) 0 (rshift_limbs f n)).
      destruct (rshift_limbs_spec f n Hf Hn) as (RS1 & RS2 & _).
      assert (Lnb : length nb = bn_dmax br) by (unfold nb; rewrite splice_length by (rewrite RS2, Lf, LBr; clear - HDM; lia); exact LBr).
      assert (UF : u64arr psegs m4 Dr (wlimbs nb)).
      { apply limbarr_limbs_at. split.
        - unfold nb, splice. change (firstn 0 (bn_buf br)) with (@nil Z). change (0 + length (rshift_limbs f n))%nat with (length (rshift_limbs f n)).
          change ([] ++ rshift_limbs f n ++ skipn (length (rshift_limbs f n)) (bn_buf br)) with (rshift_limbs f n ++ skipn (length (rshift_limbs f n)) (bn_buf br)).
          apply limbs_at_app. split; [rewrite rshift_limbs_seq; exact HR|]. rewrite RS2, Lf. exact LArest4.
        - rewrite Lnb, <- LBr. eapply wr_at_transport; [exact WRr | exact WMc]. }
      assert (LENnb : Z.of_nat (length (wlimbs nb)) = Z.of_nat (bn_dmax br)) by (rewrite wlimbs_len, Lnb; reflexivity).
      assert (WM4 : wmono psegs m2 m4) by exact WMc.
      clear MU3 WM3 SEPrx DrI BNx2 MUb WMb MUc WMc RI MI3 Ur LAr WRr LAx Ux LArest LArest4 HR HFx LAf DJW DISJf LDJ.
      rewrite Lf.
      step. step. zstep.
      do 7 step. release_frame FR2 ST2 (bv_unsigned sp). step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mG end.
      apply evt_done.
      assert (HWL3 : Forall (w_lib OW2 lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
      { constructor; [left; cbn; lia|]. constructor; [right; exists (qr2, Ar2, nr2); cbn; auto|].
        constructor; [right; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn; split; [exact Hinpr| lia]| constructor]. }
      assert (WOK3 : Forall (w_ok OW2 LB ls1 AD EA [rr]) [(bv_unsigned sp + -64, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
      { constructor; [apply w_stack; cbn; lia|]. constructor; [eapply (w_struct OW2 LB ls1 AD EA false [rr] _ rr ar); [left; reflexivity| exact HAr2| cbn; lia| cbn; lia]|].
        constructor; [eapply (w_limbs OW2 LB ls1 AD EA false [rr] _ rr pr Dr); [left; reflexivity| exact HVr2| exact Edr| exact Hinpr| cbn [fst snd]; fold br; lia| cbn [fst snd]; fold br; lia]| constructor]. }
      unfold bn_post. do 15 eexists. exists mG, OW2, errv2. split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP2 MU4 WM4 HWL3 CEIL)|].
      split.
      { unfold lib_state. eapply (lib_state_close [] ls1 mG OW2 AD EA rr ar); [| exact ND2| exact HAr2| | |].
        - exact (lib_state_frame st1 LB [rr] ls1 m2 mG OW2 AD EA _ HEAP2 LSH MU4 WM4 WOK3).
        - exists Dr. split.
          + unfold bn_cells, bn_dmax. cbn [bn_top bn_buf bn_neg bn_flags]. fold nb. rewrite Lnb. exact BNr.
          + unfold bn_arr, bn_dmax. cbn [bn_d bn_buf]. fold nb. rewrite Edr, Lnb. split; [exact Hinpr| exact UF].
        - unfold bn_okm, bn_dmax. cbn [bn_buf bn_top bn_flags]. fold nb. rewrite Lnb. unfold BN_WORDS_MAX.
          split; [unfold nb; apply splice_limbs; [exact OKq1| exact RS1]|]. split; [exact HDM|]. split; [lia| exact OKq4].
        - apply ids_ok_setbn_same; [exact IDS2| exact HVr2|]. unfold bn_blocks, bn_dmax. cbn [bn_d bn_buf]. fold nb. rewrite Lnb. reflexivity. }
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ HEAP2 AUX2 MU4 WM4 HWL3 SPB); unfold GLOBALS_TOP; lia|]. split; [exact ST2|].
      split; [unfold LX_ERRNO, RATP; exact ERR2|]. split; [exact MI4|].
      split.
      { eapply lx_pres_trans; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL); unfold GLOBALS_TOP; lia|].
        eapply lx_pres_trans; [eapply lx_pres_weaken; [exact LXP2| lia| auto| auto]|].
        apply (seg_lx_pres _ _ _ _ _ _ _ _ _ HEAP2 MU4 WM4 HWL3 CEIL); unfold GLOBALS_TOP; lia. }
      split; [exact FA2|]. split; [exact SO2|].
      split. { intros r0 a0 H0. apply ref_at_setbn. apply RST2. exact H0. }
      reflexivity.
  Qed.
End Proofs.
End WithCeiling0.
