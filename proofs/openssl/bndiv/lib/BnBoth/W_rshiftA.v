(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA ZBridge RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem BnTacX.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr BnLeaves ShiftPure.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA BnRepX ImplA ImplAX BnIfaceA UnwindA EdgesA AsStruct RtCallA W_cryptoA W_expandA W_smallA BnAKitA BnCallA AW_lshift_arr AW_rshift_arr AsStruct2 W_lshiftA UbKit UbStruct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2248904 => 2
  | 2248916 => 1
  | 2248920 => 2
  | 2248988 => 1
  | 2248992 => 2
  | 2249016 => 2
  | 2249020 => 1
  | 2249024 => 2
  | 2249072 => 1
  | 2249076 => 1
  | 2249080 => 2
  | 2249084 => 1
  | 2249088 => 1
  | 2249092 => 1
  | 2249096 => 1
  | 2249100 => 2
  | 2249104 => 2
  | 2249108 => 1
  | 2249112 => 2
  | 2249120 => 2
  | 2249176 => 1
  | 2249180 => 1
  | 2249184 => 1
  | 2249192 => 1
  | 2249200 => 1
  | 2249224 => 2
  | 2249252 => 2
  | 2249256 => 1
  | 2249260 => 1
  | 2249264 => 2
  | 2249268 => 2
  | 2249356 => 2
  | 2249360 => 1
  | 2249364 => 1
  | 2249368 => 1
  | 2249372 => 2
  | 2249376 => 2
  | 2249380 => 1
  | 2249384 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
Ltac unhide := repeat match goal with H : hide _ |- _ => apply hide_elim in H end.
Open Scope Z_scope.

Definition BN_RSHIFT : Z := 0x2250a0.
Definition BN_RSHIFT_STACK : Z := 64 + BN_WEXPAND_STACK.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_rs_wexpand := (E_bn_rshift_fixed_top_2268e4 : uk_call BN_RSHIFT 0x225134 BN_WEXPAND).

Lemma bn_rshift_fixed_top_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
    (lo : Z) (ras : list Z) (rr rx : bnref) (ar ax : Z) (n : Z),
  bn_preA Σ ls m OW LB AD EA sp lo BN_RSHIFT_STACK MC ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_RSHIFT (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> ref_at ls OW AD rr ar -> ref_at ls OW AD rx ax -> a0 = wz ar -> a1 = wz ax -> a2 = wz n -> 0 <= n < 64 ->
  implA (bn_rshift_fixed_top (tree_ops bptr) rr rx n ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA MC (fun _ _ _ a0' => a0' = wz 1))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_RSHIFT) fc None m (seg_rom bsegs)).
Proof.
  intros until n. intros PRE UW CTX -> HAr HAx -> -> -> Hn.
  pose proof PRE as (HEAP & LS & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED).
  pose proof LO as LO'. unfold BN_RSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO'.
  unfold BN_RSHIFT, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  unfold bn_rshift_fixed_top.
  destruct (bnref_eqb rr rx) eqn:ERX; cbn [orb]. { unfold bunr. cbn [unreachable tree_ops]. apply implA_unr. }
  apply bnref_eqb_false in ERX.
  replace (n <? 64) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
  unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
  (* [comment removed for export] *)
  destruct (open_ro_sh Σ OW LB m ls AD EA rx ax HEAP LS HAx) as (Dx & BNx & (OKx1 & OKx2 & OKx3 & OKx4) & _ & X0 & XC & _ & _ & ACX & ALX & _ & _).
  set (bx := getbn rx ls) in *.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  pose proof (struct_disj Σ OW LB m HEAP ls AD EA IDS ADB rr rx ar ax ERX HAr HAx) as SDJ0.
  destruct (ref_at_inb _ _ _ _ _ ADB HAr) as (qr & Ar & nr & Eqr & Hinr & Rr1 & Rr2).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP Hinr) as (RA0 & RA16 & _ & RAC & RAI).
  unfold bn_cells, MallocRep.wz in BNx. unfold BN_WORDS_MAX in OKx3.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 64, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  apply implA_from_evt.
  carve_frame 64%nat ST.
  do 10 step.
  ub. do 2 step. ub. step.
  do 4 step. do 2 step. shl_with ACX ALX. chk0.
  zstep.
  step. rewrite (sx32_small (Z.of_nat (bn_top bx))) by lia.
  do 3 zstep.
  setreg 22%Z (Z_to_bv 64 0) ltac:(f_equal; symmetry; apply (nw_mA_0 n Hn)).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK : Forall (w_ok OW LB ls AD EA []) [(bv_unsigned sp + -64, bv_unsigned sp)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  pose proof (lib_state_frame Σ LB [] ls m m1 OW AD EA _ HEAP LS MU WM WOK) as LS1.
  assert (EV : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MC Σ ls OW m
                 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] 0 Σ ls m1 OW).
  { unfold cenvA, cenv_ok. split; [repeat split; try assumption; try (unfold USTACK_TOP; lia); clear - SP16; Z.div_mod_to_equations; lia|].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|].
    split; [exact ST|]. split; [exact MI|].
    split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP MU HWL CEIL ltac:(lia))|].
    split; [lia|]. split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|].
    split; [cbn [app]; exact FR|]. split; [cbn; lia|]. unfold uw_opt.
    eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  pose proof EV as (OK & HEAP1 & _).
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
    pose proof EV as (_ & _ & ST1 & MI1 & AXP1 & _ & _ & _ & FR1 & _ & _). cbn [app] in FR1.
    destruct (lib_state_open [] ls m1 OW AD EA rr ar LS1 ND HAr ltac:(intros [])) as ((Dr & BNr & ARRr) & _ & LSH).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP1 LS1 HAr) as (ACR & ALR & OFR).
    set (br := getbn rr ls) in *.
    clear BNx SDJ0 ST MI FR.
    do 2 step.
    eapply evt_cut.
    { eapply (BN_zero_ex_specA (Z_to_bv 64 2249340) (Z_to_bv 64 (bv_unsigned sp + -64))) with (lo := lo) (A := ar) (D := Dr) (b := br);
        [exact BNr | rewrite ESP; exact ST1 | rewrite ESP; lia | exact MI1 | rewrite ESP; unfold BnHeapA.ACEIL in *; lia
        | exact (AH_shb _ _ _ _ HEAP1) | exact ACR | exact ALR | unfold SHHI, BnHeapA.ACEIL in *; lia | exact OFR | reflexivity | clear - RA0 Rr1; lia]. }
    intros ms' PO. unfold bn_small_postA in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & STc & BNr2).
    subst ms'. rewrite ESP in *.
    rewrite (ret_pc_even 2249340) by lia.
    eapply (rw_cells_transport bsegs _ m1 m2) in FR1; [| exact MUc | exact WMc | cbn; unfold BnHeapA.ACEIL in *; lia].
    clear ST1 MI1 BNr.
    step. step.
    do 8 step. release_frame FR1 STc (bv_unsigned sp). step. step.
    apply evt_done. apply implA_ret.
    assert (HWLc : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -64 - 16, bv_unsigned sp + -64); (ar, ar + 24)]).
    { constructor; [left; cbn; lia|]. constructor; [right; exists (qr, Ar, nr); cbn; auto| constructor]. }
    assert (WOKc : Forall (w_ok OW LB ls AD EA [rr]) [(bv_unsigned sp + -64 - 16, bv_unsigned sp + -64); (ar, ar + 24)]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [eapply (w_struct OW LB ls AD EA false [rr] _ rr ar); [left; reflexivity| exact HAr| cbn; lia| cbn; lia]| constructor]. }
    unfold bn_postA. do 17 eexists. exists m2, OW. split; [reflexivity|]. cbn [fst snd].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP1 MUc WMc HWLc CEIL ltac:(unfold USTACK_TOP; lia))|].
    split.
    { unfold lib_state. eapply (lib_state_close [] ls m2 OW AD EA rr ar); [| exact ND| exact HAr| | |].
      - exact (lib_state_frame Σ LB [rr] ls m1 m2 OW AD EA _ HEAP1 LSH MUc WMc WOKc).
      - exists Dr. split; [exact BNr2|]. unfold bn_arr, bn_zero_pure in *. cbn [bn_d bn_buf bn_dmax].
        destruct (bn_d br) as [pr|] eqn:Edr; [|exact ARRr]. destruct ARRr as [Hin Uarr]. split; [exact Hin|].
        eapply u64arr_transport; [exact Uarr | exact MUc | exact WMc |].
        pose proof (AH_range _ _ _ _ _ _ _ HEAP1 Hin) as (_ & _ & _ & PC & _).
        pose proof (struct_limbs_disj Σ OW LB m1 HEAP1 ls AD EA IDS ADB rr rr ar pr Dr _ HAr HVr Edr Hin) as SLD.
        cbn [disjoint_from]. rewrite wlimbs_len. fold (bn_dmax br). unfold BnHeapA.ACEIL in *. lia.
      - unfold bn_okm, bn_zero_pure, bn_dmax in *. cbn [bn_buf bn_top bn_flags]. split; [exact OKr1|]. split; [lia|]. split; [exact OKr3| exact OKr4].
      - apply ids_ok_setbn_same; [exact IDS| exact HVr| reflexivity]. }
    split; [exact STc|]. split; [exact MIc|].
    split; [eapply ax_pres_trans; [exact AXP1|]; exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP1 MUc HWLc CEIL ltac:(lia))|].
    split; [unfold MC; lia|].
    split. { unfold cnt_eq. rewrite (cnt_bal_setbn rr _ ls OW OW HVr). fold br. unfold bn_blocks, bn_zero_pure. cbn [bn_d]. destruct (bn_d br); cbn [length]; lia. }
    split. { intros r0 a0 H0. apply ref_at_setbn. exact H0. }
    reflexivity.
  - (* [comment removed for export] *)
    assert (NTOP : bn_top bx <> 0%nat) by (clear - KT0; lia).
    replace (bn_top bx =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; exact NTOP).
    zstep. rewrite Z.sub_0_r, (bk_swrap32_small (Z.of_nat (bn_top bx))) by lia.
    assert (SA0e : 0 < ar) by (clear - RA0 Rr1; lia).
    ub.
    zstep. if_cases KE; zify_cond KE. { exfalso. clear - KE SDJ0. lia. }
    do 3 step.
    clear HEAP LS ST MI MU WM HWL WOK FR BNx ACX OFF SHB1 SHB2 PRE SDJ0 KE.
    apply evt_done.
    eapply implA_bind.
    { eapply implA_leaves; [apply (bn_wexpand_leaves rr (bn_top bx) ls HVr OKr2)|].
      eapply (bn_wexpand_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (r := rr) (a := ar) (OW := OW) (LB := LB) (AD := AD) (EA := EA);
        [| | | reflexivity | exact HAr | reflexivity | reflexivity | lia].
      - eapply cenv_preA; [exact EV | exact LS1 | unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; lia | lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV).
      - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_rs_wexpand CTX). }
    cbv beta. intros [u ls1] Σ1 ms1 [PO LEAF].
    apply (bn_postA_cpost LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -64) MC Σ ls OW) in PO; [| exact OK | exact HEAP1].
    cbn [fst snd] in *.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & -> & CP & (-> & HDM & WRES & BST)).
    assert (E1 : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MC Σ ls OW m
                   [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] (0 + MC) Σ1 ls1 m2 OW2 /\ lib_state ls1 m2 OW2 AD EA)
      by (eapply cenv_postA; [exact EV | exact CP]).
    destruct E1 as (EV1 & LS2).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP) as RST2.
    rewrite (ret_pc_even 2249012) by lia.
    destruct LEAF as (LF1 & LF2 & LF3 & LF4 & LF5). cbn [snd] in *.
    assert (Ebx : getbn rx ls1 = bx) by (apply LF1; exact ERX).
    pose proof (RST2 _ _ HAr) as HAr2. pose proof (RST2 _ _ HAx) as HAx2.
    pose proof EV1 as (_ & HEAP2 & ST2 & MI2 & AXP2 & CR2 & CNT2 & RS2 & FR2 & FSZ2 & UW2).
    cbn [app] in FR2.
    pose proof (AH_nodup_l _ _ _ _ HEAP2) as ND2.
    pose proof (AH_ceil _ _ _ _ HEAP2) as (C1' & C2' & C3').
    destruct (lib_state_h_parts _ _ _ _ _ _ LS2) as (IDS2 & ADB2 & ERRB2 & SOK2).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAr2) as HVr2. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAx2) as HVx2.
    (* [comment removed for export] *)
    destruct (lib_state_open [] ls1 m2 OW2 AD EA rx ax LS2 ND2 HAx2 ltac:(intros [])) as ((Dx2 & BNx2 & ARRx2) & _ & _).
    rewrite Ebx in BNx2, ARRx2.
    destruct (lib_state_open [] ls1 m2 OW2 AD EA rr ar LS2 ND2 HAr2 ltac:(intros [])) as ((Dr & BNr & ARRr) & (OKq1 & OKq2 & OKq3 & OKq4) & LSH).
    set (br := getbn rr ls1) in *.
    destruct (bn_arr_facts Σ1 OW2 LB m2 HEAP2 ls1 AD EA IDS2 ADB2 rr Dr HVr2 ARRr) as (Ur & LENr & Dr0 & DrC & DrI & DSEPr).
    fold br in Ur, LENr, DrC, DrI, DSEPr.
    pose proof (DSEPr rr ar HAr2) as SEPrr. pose proof (DSEPr rx ax HAx2) as SEPrx.
    pose proof (struct_disj Σ1 OW2 LB m2 HEAP2 ls1 AD EA IDS2 ADB2 rr rx ar ax ERX HAr2 HAx2) as SDJ.
    destruct (ref_at_inb _ _ _ _ _ ADB2 HAx2) as (qx2 & Ax2 & nx2 & Eqx2 & Hinx2 & Rx21 & Rx22).
    pose proof (AH_range _ _ _ _ _ _ _ HEAP2 Hinx2) as (XB0 & XB16 & _ & XBC & XBI).
    destruct (ref_at_inb _ _ _ _ _ ADB2 HAr2) as (qr2 & Ar2 & nr2 & Eqr2 & Hinr2 & Rr21 & Rr22).
    pose proof (AH_range _ _ _ _ _ _ _ HEAP2 Hinr2) as (RB0 & RB16 & _ & RBC & RBI).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP2 LS2 HAr2) as (ACR & ALR & OFR).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP2 LS2 HAx2) as (ACX2 & ALX2 & _).
    destruct (arr_shA _ _ _ _ _ _ HEAP2 ARRr) as (ACDR & ALDR & OFDR). fold br in ACDR, OFDR.
    unfold bn_cells in BNx2, BNr. unfold BN_WORDS_MAX in OKq3. unfold MallocRep.wz in *. unfold SHLO, SHHI in *.
    (* [comment removed for export] *)
    assert (HDr : exists pr, bn_d br = Some pr /\ In (pr, Dr, 8 * Z.of_nat (bn_dmax br)) OW2).
    { unfold bn_arr in ARRr. destruct (bn_d br) as [pr|]; [exists pr; split; [reflexivity| exact (proj1 ARRr)]|].
      exfalso. destruct ARRr as [_ E]. unfold bn_dmax in HDM. rewrite E in HDM. cbn in HDM. lia. }
    destruct HDr as (pr & Edr & Hinpr).
    pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m2) as MU3.
    pose proof (wmono_refl bsegs m2) as WM3.
    assert (OFF3 : offshW [(bv_unsigned sp + -64, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
    { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. lia. }
    apply implA_ret_evt.
    (* [comment removed for export] *)
    assert (FIN : forall mF (nb : list Z) x5 x6 x7 x10 x11 x14 x15 x16 x17 x20 x28 x29 x30 x31,
              length nb = bn_dmax br -> limbs nb ->
              u64arr bsegs mF Dr (wlimbs nb) ->
              rw_cells bsegs mF ax [C8 (Z_to_bv 64 Dx2); C4 (Z_to_bv 64 (Z.of_nat (bn_top bx))); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax bx)));
                                    C4 (Z_to_bv 64 (Z.b2z (bn_neg bx))); C4 (Z_to_bv 64 (bn_flags bx))] ->
              rw_cells bsegs mF ar [C8 (Z_to_bv 64 Dr); C4 (Z_to_bv 64 (Z.of_nat (bn_top br))); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax br)));
                                    C4 (Z_to_bv 64 (Z.b2z (bn_neg br))); C4 (Z_to_bv 64 (bn_flags br))] ->
              rw_cells bsegs mF (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
              stk bsegs mF lo (bv_unsigned sp + -64) -> mem_inv bsegs mF ->
              munch [(bv_unsigned sp + -64, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m2 mF -> wmono bsegs m2 mF ->
              evt bsegs
                (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA MC
                   (fun _ _ _ a0' => a0' = Z_to_bv 64 1)
                   (tt, setbn rr (mkBN (bn_d br) nb (bn_top bx) (bn_neg bx) (bn_flags br)) ls1) Σ1)
                (MS (mkR (Z_to_bv 64 2249012) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 TP_A) x5 x6 x7 sp (Z_to_bv 64 ar)
                         x10 x11 (Z_to_bv 64 n) (Z_to_bv 64 Dr) x14 x15 x16 x17 (Z_to_bv 64 (Z.of_nat (bn_top bx))) (Z_to_bv 64 (ax + 16))
                         x20 (Z_to_bv 64 SHB) (Z_to_bv 64 0) s7 s8 s9 s10 s11 x28 x29 x30 x31)
                    F2 (Z_to_bv 64 0x2252c8) fc2 None mF (seg_rom bsegs))).
    { intros mF nb x5 x6 x7 x10 x11 x14 x15 x16 x17 x20 x28 x29 x30 x31 Lnb LMnb UF BNxF BNrF FRF STF MIF MUF WMF.
      clear SEPrx XBI DrI BNx2 BNr FR2 ST2 MI2 MU3 WM3 Ur.
      assert (LENnb : Z.of_nat (length (wlimbs nb)) = Z.of_nat (bn_dmax br)) by (rewrite wlimbs_len, Lnb; reflexivity).
      do 2 step. shl_with ACX2 ALX2. chk0.
      do 3 step. shl_with ACR ALR. step. rewrite (sx32_small (Z.b2z (bn_neg bx))) by (destruct (bn_neg bx); cbn; lia). chk0.
      step.
      do 3 step. shl_with ACR ALR. chk0.
      step. step.
      do 8 step. release_frame FRF STF (bv_unsigned sp). step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mG end.
      apply evt_done.
      assert (HWL3 : Forall (w_lib OW2 lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
      { constructor; [left; cbn; lia|]. constructor; [right; exists (qr2, Ar2, nr2); cbn; auto|].
        constructor; [right; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn; split; [exact Hinpr| lia]| constructor]. }
      assert (WOK3 : Forall (w_ok OW2 LB ls1 AD EA [rr]) [(bv_unsigned sp + -64, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
      { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [eapply (w_struct OW2 LB ls1 AD EA false [rr] _ rr ar); [left; reflexivity| exact HAr2| cbn; lia| cbn; lia]|].
        constructor; [eapply (w_limbs OW2 LB ls1 AD EA false [rr] _ rr pr Dr); [left; reflexivity| exact HVr2| exact Edr| exact Hinpr| cbn [fst snd]; fold br; lia| cbn [fst snd]; fold br; lia]| constructor]. }
      pose proof OK as (CEIL' & _).
      unfold bn_postA. do 17 eexists. exists mG, OW2. split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP2 MUF WMF HWL3 CEIL ltac:(unfold USTACK_TOP; lia))|].
      split.
      { unfold lib_state. eapply (lib_state_close [] ls1 mG OW2 AD EA rr ar); [| exact ND2| exact HAr2| | |].
        - exact (lib_state_frame Σ1 LB [rr] ls1 m2 mG OW2 AD EA _ HEAP2 LSH MUF WMF WOK3).
        - exists Dr. split.
          + unfold bn_cells, bn_dmax. cbn [bn_top bn_buf bn_neg bn_flags]. rewrite Lnb. exact BNrF.
          + unfold bn_arr, bn_dmax. cbn [bn_d bn_buf]. rewrite Edr, Lnb. split; [exact Hinpr| exact UF].
        - unfold bn_okm, bn_dmax. cbn [bn_buf bn_top bn_flags]. rewrite Lnb. unfold BN_WORDS_MAX.
          split; [exact LMnb|]. split; [exact HDM|]. split; [lia| exact OKq4].
        - apply ids_ok_setbn_same; [exact IDS2| exact HVr2|]. unfold bn_blocks, bn_dmax. cbn [bn_d bn_buf]. rewrite Lnb. reflexivity. }
      split; [exact STF|]. split; [exact MIF|].
      split; [eapply ax_pres_trans; [exact AXP2|]; exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP2 MUF HWL3 CEIL ltac:(lia))|].
      split; [lia|].
      split. { unfold cnt_eq in *. rewrite (cnt_bal_setbn rr _ ls1 OW2 OW2 HVr2). fold br. rewrite CNT2.
               unfold bn_blocks, bn_dmax. cbn [bn_d bn_buf]. rewrite Edr, Lnb. cbn [length]. lia. }
      split. { intros r0 a0 H0. apply ref_at_setbn. apply RS2. exact H0. }
      reflexivity. }
    destruct (proj1 (limbarr_limbs_at bsegs m2 Dr (bn_buf br)) Ur) as (LAr & WRr).
    assert (LBr : length (bn_buf br) = bn_dmax br) by reflexivity.
    zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by lia. lia. }
    pose proof (arr_ubA _ _ _ _ _ _ HEAP2 ARRx2 ltac:(unfold bn_dmax in *; clear - NTOP OKx2; lia)) as (UDX & UDX16).
    pose proof (arr_ubA _ _ _ _ _ _ HEAP2 ARRr ltac:(clear - NTOP HDM; lia)) as (PR0 & PR16).
    assert (UAR : 0 < ar /\ ar mod 8 = 0) by (split; [clear - RB0 Rr21; lia | exact ALR]).
    hide_ors. ub. unhide.
    do 2 step. shl_with ACR ALR. chk0.
    do 2 step. shl_with ACX2 ALX2. chk0.
    (* [comment removed for export] *)
    destruct (bn_arr_facts Σ1 OW2 LB m2 HEAP2 ls1 AD EA IDS2 ADB2 rx Dx2 HVx2 ltac:(rewrite Ebx; exact ARRx2)) as (Ux & LENx & Dx0 & DxC & DxI & _).
    rewrite Ebx in Ux, LENx, DxC, DxI.
    assert (HDx : exists px, bn_d bx = Some px /\ In (px, Dx2, 8 * Z.of_nat (bn_dmax bx)) OW2).
    { unfold bn_arr in ARRx2. destruct (bn_d bx) as [px|]; [exists px; split; [reflexivity| exact (proj1 ARRx2)]|].
      exfalso. destruct ARRx2 as [_ E]. unfold bn_dmax in OKx2. rewrite E in OKx2. cbn in OKx2. lia. }
    destruct HDx as (px & Edx & Hinpx).
    pose proof (AH_range _ _ _ _ _ _ _ HEAP2 Hinpx) as (PX0 & PX16 & _ & _ & _).
    pose proof (limbs_limbs_disj Σ1 OW2 LB m2 HEAP2 ls1 AD EA IDS2 rx rr px Dx2 _ pr Dr _ ltac:(congruence) HVx2 HVr2
                  ltac:(rewrite Ebx; exact Edx) Edr Hinpx Hinpr) as LDJ.
    destruct (arr_shA _ _ _ _ _ _ HEAP2 ARRx2) as (ACDX & ALDX & _).
    destruct (proj1 (limbarr_limbs_at bsegs m2 Dx2 (bn_buf bx)) Ux) as (LAx & _).
    set (f := firstn (bn_top bx) (bn_buf bx)).
    assert (Lf : length f = bn_top bx) by (subst f; apply firstn_length_le; exact OKx2).
    assert (LAf : limbs_at bsegs m2 Dx2 f).
    { rewrite <- (firstn_skipn (bn_top bx) (bn_buf bx)) in LAx. apply limbs_at_app in LAx. exact (proj1 LAx). }
    assert (LArest : limbs_at bsegs m2 (Dr + 8 * Z.of_nat (bn_top bx)) (skipn (bn_top bx) (bn_buf br))).
    { rewrite <- (firstn_skipn (bn_top bx) (bn_buf br)) in LAr. apply limbs_at_app in LAr. destruct LAr as [_ LA2].
      rewrite length_firstn, LBr in LA2. replace (Nat.min (bn_top bx) (bn_dmax br)) with (bn_top bx) in LA2 by (clear - HDM; lia). exact LA2. }
    step. do 2 zstep.
    assert (BDX : 0 <= Dx2 /\ Dx2 + 8 * Z.of_nat (bn_dmax bx) <= 140737488355328) by (unfold BnHeapA.ACEIL in *; lia).
    hide_ors. ub.
    zstep. rewrite (bk_swrap32_small (Z.of_nat (bn_top bx) + -1)) by (clear - NTOP OKx2 OKx3; unfold bn_dmax in *; lia).
    ub. unhide.
    do 2 step. shl_limb ACDX ALDX BDX 0. chk0.
    zstep.
    setreg 12%Z (Z_to_bv 64 n) ltac:(f_equal; rewrite ?(Z.mod_small n 18446744073709551616) by lia; change 63 with (Z.ones 6); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; change (2 ^ 6) with 64; lia).
    step.
    replace (Z.of_nat (bn_top bx) + -1) with (Z.of_nat (bn_top bx) - 1) by lia.
    replace (Z.of_nat (bn_top bx)) with (Z.of_nat (length f)) by (rewrite Lf; reflexivity).
    eapply (rsh_blockA _ _ _ _ _ _ (Z_to_bv 64 ax) _ _ _ _ _ _ _ _ _ m2 f Dx2 Dr n).
    { exact Hn. }
    { subst f. apply limbs_firstn. exact OKx1. }
    { rewrite Lf. clear - NTOP OKx2 OKx3. lia. }
    { rewrite Lf. clear - LDJ OKx2 HDM. lia. }
    { rewrite Lf. eapply acc_sub; [exact ACDX | lia | clear - OKx2; lia]. }
    { rewrite Lf. eapply acc_sub; [exact ACDR | lia | clear - HDM; lia]. }
    { exact ALDX. }
    { exact ALDR. }
    { rewrite Lf. cbn [offshW]. unfold SHLO, SHHI. clear - OFDR HDM Dr0. lia. }
    { exact UDX. }
    { exact PR0. }
    { exact LAf. }
    { rewrite Lf. apply (wr_at_sub bsegs m2 Dr (8 * Z.of_nat (length (bn_buf br))) 0 (8 * Z.of_nat (bn_top bx))) in WRr; [rewrite Z.add_0_r in WRr; exact WRr | clear; lia | clear; lia | rewrite LBr; clear - HDM; lia]. }
    { exact MI2. }
    intros m3 z5 z6 z7 z10 z11 z14 z15 z16 z17 z20 z28 z29 z30 z31 HR HFx MI3 MUb WMb.
    rewrite Lf in HR, MUb. rewrite Lf. rewrite (unsigned_lit ax) by lia.
    (* [comment removed for export] *)
    assert (DJW : forall A k, (A + k <= Dr \/ Dr + 8 * Z.of_nat (bn_dmax br) <= A) ->
              disjoint_from [(Dr, Dr + 8 * Z.of_nat (bn_top bx))] A k).
    { intros A k H. cbn [disjoint_from]. split; [|exact I]. clear - H HDM. lia. }
    eapply (rw_cells_transport bsegs _ m2 m3) in BNx2; [| exact MUb | exact WMb | apply DJW; cbn; clear - SEPrx; lia].
    eapply (rw_cells_transport bsegs _ m2 m3) in BNr; [| exact MUb | exact WMb | apply DJW; cbn; clear - SEPrr; lia].
    eapply (rw_cells_transport bsegs _ m2 m3) in FR2; [| exact MUb | exact WMb | apply DJW; cbn; unfold BnHeapA.ACEIL in *; lia].
    eapply (stk_transport_disjoint bsegs _ m2 m3) in ST2; [| exact MUb | exact WMb | apply DJW; unfold BnHeapA.ACEIL in *; lia].
    assert (MU4 : munch [(bv_unsigned sp + -64, bv_unsigned sp); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m2 m3).
    { eapply munch_weaken; [|exact MUb]. unfold sub_fp. intros x Hx. cbn [outside] in *. split; [|exact I]. clear - Hx HDM. lia. }
    assert (LArest3 : limbs_at bsegs m3 (Dr + 8 * Z.of_nat (bn_top bx)) (skipn (bn_top bx) (bn_buf br))).
    { eapply limbs_at_transport; [exact LArest | exact MUb |]. cbn [disjoint_from]. split; [|exact I]. rewrite length_skipn, LBr. clear - HDM. lia. }
    clear MU3 WM3.
    pose proof (rshift_limbs_seq f n) as ESEQ.
    assert (Lnew : length (rshift_limbs f n) = bn_top bx) by (rewrite ESEQ, length_map, length_seq, Lf; reflexivity).
    assert (LIMBnew : limbs (rshift_limbs f n)).
    { apply (rshift_limbs_spec f n); [subst f; apply limbs_firstn; exact OKx1 | exact Hn]. }
    eapply (FIN m3 (splice (bn_buf br) 0 (rshift_limbs f n))); try eassumption.
    + rewrite splice_length by (rewrite Lnew, LBr; clear - HDM; lia). exact LBr.
    + apply splice_limbs; [exact OKq1 | exact LIMBnew].
    + apply limbarr_limbs_at. split.
      * unfold splice. change (firstn 0 (bn_buf br)) with (@nil Z). change (0 + length (rshift_limbs f n))%nat with (length (rshift_limbs f n)).
        change ([] ++ rshift_limbs f n ++ skipn (length (rshift_limbs f n)) (bn_buf br)) with (rshift_limbs f n ++ skipn (length (rshift_limbs f n)) (bn_buf br)).
        apply limbs_at_app. split; [rewrite ESEQ at 1; rewrite Lf; exact HR|]. rewrite Lnew. exact LArest3.
      * rewrite splice_length by (rewrite Lnew, LBr; clear - HDM; lia). eapply wr_at_transport; [exact WRr | exact WMb].
Qed.

End WithRT.
