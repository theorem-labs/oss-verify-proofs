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
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnA Require Import BnAPure.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA BnRepX ImplA BnIfaceA UnwindA EdgesA AsStruct RtCallA W_cryptoA W_expandA W_smallA BnAKitA BnCallA W_ucmpA W_cmpA W_uaddA W_usubA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit UbStruct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2437524 => 2
  | 2437536 => 1
  | 2437540 => 2
  | 2437580 => 2
  | 2437584 => 1
  | 2437588 => 2
  | 2437692 => 2
  | 2437720 => 2
  | 2437724 => 1
  | 2437728 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Open Scope Z_scope.

Definition BN_ADD : Z := 0x253160.
Definition BN_ADD_STACK : Z := 96 + BN_UADD_STACK.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_add_uadd := (E_BN_add_24fb00 : uk_call BN_ADD 0x253208 BN_UADD).
Local Notation E_add_usub := (E_BN_add_24fb30 : uk_call BN_ADD 0x25323c BN_USUB).

Section Proofs.
  (* [comment removed for export] *)
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (jb : list byte)
            (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo : Z) (ras : list Z)
            (rr : bnref) (R : Z).
  Notation SP := (bv_unsigned sp).
  Notation PRE := [CB 8 jb; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1].
  Notation ENV := (cenvA LB AD lo SP (SP + -96) s0 ra (Some ras) MC Σ ls OW m PRE).
  Notation POSTA := (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA MC (fun _ _ _ a0' => a0' = wz 1)).

  (* [comment removed for export] *)
  Lemma add_finA : forall (Σx : rts RT) (lsx : lstate bptr) (mx : mem) (OWx : list block) (used : Z) (rneg : bool)
      (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x24 x25 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    ENV used Σx lsx mx OWx -> used <= MC -> lib_state lsx mx OWx AD EA -> ref_at lsx OWx AD rr R ->
    evt bsegs (POSTA (tt, setbn rr (bn_with_neg (getbn rr lsx) rneg) lsx) Σx)
      (MS (mkR x1 (Z_to_bv 64 (SP + -96)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 R) (wz 1) a1 a2 a3 a4 a5 a6 a7
               x18 x19 x20 x21 (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.b2z rneg)) x24 x25 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x25325c) fc None mx (seg_rom bsegs)).
  Proof.
    intros until fc. intros EV HU LS HR.
    pose proof EV as ((CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0) & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_open [] lsx mx OWx AD EA rr R LS ND HR ltac:(intros [])) as ((Dr & SR & ARR) & OKR & LSH).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
    destruct (bn_arr_facts Σx OWx LB mx HEAP lsx AD EA IDS ADB rr Dr HVR ARR) as (U & LENW & D0 & DC & DI & DSEP).
    specialize (DSEP rr R HR).
    destruct (ref_at_inb _ _ _ _ _ ADB HR) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
    pose proof (AH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & SAI).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS HR) as (ACC & AL & OFR). unfold SHLO, SHHI in OFR.
    set (b := getbn rr lsx) in *.
    unfold bn_cells, MallocRep.wz in SR. unfold MallocRep.wz.
    pose proof (munch_refl [(R, R + 24)]%Z mx) as MU. pose proof (wmono_refl bsegs mx) as WM.
    assert (OFF : offshW [(R, R + 24)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; lia).
    cbn [app] in FR.
    do 3 (ub; step). ub; shl. ub; chk0. ub; step.
    do 11 (ub; step). release_frame FR ST (bv_unsigned sp). ub; step. ub; step.
    apply evt_done.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => rename mf into mF end.
    assert (HWL : Forall (w_lib OWx lo (bv_unsigned sp)) [(R, R + 24)]).
    { constructor; [right; exists (qs, As, ns); cbn [blk_addr blk_size fst snd]; split; [exact Hins | lia] | constructor]. }
    assert (WOK : Forall (w_ok OWx LB lsx AD EA [rr]) [(R, R + 24)]).
    { constructor; [eapply (w_struct OWx LB lsx AD EA false [rr] _ rr R); [left; reflexivity | exact HR | cbn; lia | cbn; lia] | constructor]. }
    unfold bn_postA. do 17 eexists. exists mF, OWx. split; [reflexivity|]. cbn [fst snd].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|].
    split.
    { unfold lib_state. eapply (lib_state_close [] lsx mF OWx AD EA rr R); [| exact ND | exact HR | | |].
      - eapply lib_state_frame; [exact HEAP | exact LSH | exact MU | exact WM | exact WOK].
      - exists Dr. split; [unfold bn_cells, bn_with_neg, bn_dmax; cbn [bn_top bn_buf bn_neg bn_flags]; exact SR|].
        eapply bn_arr_of_u64arr; [exact ARR | exact U].
      - destruct OKR as (O1 & O2 & O3 & O4). unfold bn_okm, bn_with_neg, bn_dmax in *. cbn [bn_top bn_buf bn_flags]. auto.
      - apply ids_ok_setbn_same; [exact IDS | exact HVR | reflexivity]. }
    split; [exact ST|]. split; [exact MI|].
    split. { eapply ax_pres_trans; [exact AXP|]. exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP MU HWL CEIL ltac:(lia)). }
    split; [lia|].
    split. { unfold cnt_eq in *. rewrite (cnt_bal_setbn rr _ lsx OWx OWx HVR), CNT. fold b. unfold bn_blocks, bn_with_neg. cbn [bn_d]. destruct (bn_d b); cbn [length]; lia. }
    split. { intros r0 a0' H0. apply ref_at_setbn. apply RS. exact H0. }
    reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition add_joinA (v : bool * lstate bptr) (Σ' : rts RT) : machine_state -> Prop :=
    fun ms' => exists x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x24 x25 t3 t4 t5 t6 F' fc' m' OW' used,
      ms' = MS (mkR x1 (Z_to_bv 64 (SP + -96)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 R) (wz 1) a1 a2 a3 a4 a5 a6 a7
                    x18 x19 x20 x21 (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.b2z (fst v))) x24 x25 s10 s11 t3 t4 t5 t6)
               F' (Z_to_bv 64 0x25325c) fc' None m' (seg_rom bsegs)
      /\ ENV used Σ' (snd v) m' OW' /\ used <= MC /\ lib_state (snd v) m' OW' AD EA /\ ref_at (snd v) OW' AD rr R.

  Hypothesis CTX : uk_ctx BN_ADD (bv_unsigned ra :: ras).
  Hypothesis LOS : lo <= SP - BN_ADD_STACK.

  (* [comment removed for export] *)
  Lemma add_usub_pathA : forall (Σx : rts RT) (lsx : lstate bptr) (mx : mem) (OWx : list block) (used : Z) (n : bool) (p q : bnref) (P Q : Z)
      (x1 t0 t1 t2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x24 x25 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    ENV used Σx lsx mx OWx -> used <= 0 -> lib_state lsx mx OWx AD EA ->
    ref_at lsx OWx AD rr R -> ref_at lsx OWx AD p P -> ref_at lsx OWx AD q Q ->
    implA (tbind (BN_usub (tree_ops bptr) rr p q lsx) (fun p0 : unit * lstate bptr => TRet (n, snd p0))) Σx add_joinA
      (MS (mkR x1 (Z_to_bv 64 (SP + -96)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 R) (Z_to_bv 64 R) (Z_to_bv 64 P) (Z_to_bv 64 Q)
               a3 a4 a5 a6 a7 x18 x19 x20 x21 (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.b2z n)) x24 x25 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x253238) fc None mx (seg_rom bsegs)).
  Proof.
    intros until fc. intros EV HU LS HR HP HQ.
    pose proof EV as (OK & HEAP & _). pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    assert (ESP : bv_unsigned (Z_to_bv 64 (SP + -96)) = SP + -96) by (apply unsigned_lit; lia).
    unfold MallocRep.wz in *.
    apply implA_from_evt. ub; step. apply evt_done.
    eapply implA_bind.
    { eapply (BN_usub_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (rr := rr) (x := p) (y := q) (R := R) (X := P) (Y := Q)
                                  (OW := OWx) (LB := LB) (AD := AD) (EA := EA);
        [| | | reflexivity | exact HR | exact HP | exact HQ | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EV | exact LS | | lia].
        unfold BN_ADD_STACK, BN_UADD_STACK, BN_USUB_STACK in *. lia.
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV).
      - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_add_usub CTX). }
    cbv beta. intros [[] lsu] Σu msu PO.
    apply (bn_postA_cpost LB AD EA lo SP (SP + -96) MC Σ ls OW) in PO; [| exact OK | exact HEAP].
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & -> & CP & (-> & _)).
    destruct (cenv_postA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EV CP) as (EV1 & LS1).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP) as RS.
    cbn [fst snd] in *.
    rewrite (ret_pc_even 2437692) by lia.
    destruct (ref_ubA _ _ _ _ _ _ _ _ _ HEAP LS HR) as (R0 & R8 & RC).
    apply implA_ret_evt. ub; step. apply evt_done.
    unfold add_joinA. do 23 eexists. exists m2, OW2, (used + MC). split; [reflexivity|]. cbn [fst snd].
    split; [exact EV1|]. split; [lia|]. split; [exact LS1 | apply RS; exact HR].
  Qed.

  (* [comment removed for export] *)
  Lemma add_uadd_pathA : forall (Σx : rts RT) (lsx : lstate bptr) (mx : mem) (OWx : list block) (used : Z) (n : bool) (p q : bnref) (P Q : Z)
      (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x24 x25 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    ENV used Σx lsx mx OWx -> used <= 0 -> lib_state lsx mx OWx AD EA ->
    ref_at lsx OWx AD rr R -> ref_at lsx OWx AD p P -> ref_at lsx OWx AD q Q ->
    implA (tbind (BN_uadd (tree_ops bptr) rr p q lsx) (fun p0 : unit * lstate bptr => TRet (n, snd p0))) Σx add_joinA
      (MS (mkR x1 (Z_to_bv 64 (SP + -96)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 R) a0 a1 a2
               a3 a4 a5 a6 a7 (Z_to_bv 64 Q) (Z_to_bv 64 P) x20 x21 (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.b2z n)) x24 x25 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2531f8) fc None mx (seg_rom bsegs)).
  Proof.
    intros until fc. intros EV HU LS HR HP HQ.
    pose proof EV as (OK & HEAP & _). pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    assert (ESP : bv_unsigned (Z_to_bv 64 (SP + -96)) = SP + -96) by (apply unsigned_lit; lia).
    unfold MallocRep.wz in *.
    apply implA_from_evt. do 4 (ub; step). apply evt_done.
    eapply implA_bind.
    { eapply (BN_uadd_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (rr := rr) (ra_ := p) (rb_ := q) (R := R) (A := P) (Bb := Q)
                                  (OW := OWx) (LB := LB) (AD := AD) (EA := EA);
        [| | | reflexivity | exact HR | exact HP | exact HQ | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EV | exact LS | | lia].
        unfold BN_ADD_STACK, BN_UADD_STACK in *. lia.
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV).
      - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_add_uadd CTX). }
    cbv beta. intros [[] lsu] Σu msu PO.
    apply (bn_postA_cpost LB AD EA lo SP (SP + -96) MC Σ ls OW) in PO; [| exact OK | exact HEAP].
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & -> & CP & (-> & _)).
    destruct (cenv_postA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EV CP) as (EV1 & LS1).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP) as RS.
    cbn [fst snd] in *.
    rewrite (ret_pc_even 2437640) by lia.
    destruct (ref_ubA _ _ _ _ _ _ _ _ _ HEAP LS HR) as (R0 & R8 & RC).
    apply implA_ret_evt. step. if_cases K; zify_cond K; [clear K | exfalso; ub_norm K; first [ub_solve K | ub_ltb_cases K]]. apply evt_done.
    unfold add_joinA. do 23 eexists. exists m2, OW2, (used + MC). split; [reflexivity|]. cbn [fst snd].
    split; [exact EV1|]. split; [lia|]. split; [exact LS1 | apply RS; exact HR].
  Qed.
End Proofs.

Lemma BN_add_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
    (lo : Z) (ras : list Z) (rr x y : bnref) (R X Y : Z),
  bn_preA Σ ls m OW LB AD EA sp lo BN_ADD_STACK MC ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_ADD (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> ref_at ls OW AD rr R -> ref_at ls OW AD x X -> ref_at ls OW AD y Y ->
  a0 = wz R -> a1 = wz X -> a2 = wz Y ->
  implA (BN_add (tree_ops bptr) rr x y ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA MC (fun _ _ _ a0' => a0' = wz 1))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_ADD) fc None m (seg_rom bsegs)).
Proof.
  intros until Y. intros PRE UW CTX -> HR HX HY -> -> ->.
  pose proof PRE as (HEAP & LS & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED).
  pose proof LO as LO'. unfold BN_ADD_STACK, BN_UADD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO'.
  unfold BN_ADD, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  destruct (open_ro_sh Σ OW LB m ls AD EA x X HEAP LS HX) as (Dx0 & SX & OKX & _ & X0 & XC & _ & _ & ACX & ALX & _ & _).
  destruct (open_ro_sh Σ OW LB m ls AD EA y Y HEAP LS HY) as (Dy0 & SY & OKY & _ & Y0 & YC & _ & _ & ACY & ALY & _ & _).
  unfold bn_cells, MallocRep.wz in SX, SY.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 96, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  unfold BN_add, bbind, bget, bset, bret. cbn [bind ret tree_ops tbind fst snd].
  set (na := bn_neg (getbn x ls)) in *. set (nb := bn_neg (getbn y ls)) in *.
  assert (NA : 0 <= Z.b2z na <= 1) by (destruct na; cbn; lia).
  assert (NB : 0 <= Z.b2z nb <= 1) by (destruct nb; cbn; lia).
  apply implA_from_evt.
  carve_frame 96%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 96 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 13 (ub; step). do 3 (ub; step). do 4 (ub; step).
  do 2 (ub; step). ub; shl. ub; chk0.
  ub; step. do 2 (ub; step). ub; shl. ub; step. rewrite (sx32_small (Z.b2z na)) by (clear - NA; lia). ub; chk0.
  ub; step. rewrite (sx32_small (Z.b2z nb)) by (clear - NB; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (HWL0 : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -96, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK0 : Forall (w_ok OW LB ls AD EA []) [(bv_unsigned sp + -96, bv_unsigned sp)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  pose proof (lib_state_frame Σ LB [] ls m m1 OW AD EA _ HEAP LS MU WM WOK0) as LS0.
  assert (EV : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -96) s0 ra (Some ras) MC Σ ls OW m
                 [CB 8 (take 8 junk); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] 0 Σ ls m1 OW).
  { unfold cenvA, cenv_ok. split; [repeat split; try assumption; try (unfold USTACK_TOP; lia); clear - SP16; Z.div_mod_to_equations; lia|].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL0 CEIL ltac:(unfold USTACK_TOP; lia))|].
    split; [exact ST|]. split; [exact MI|].
    split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP MU HWL0 CEIL ltac:(lia))|].
    split; [lia|]. split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|].
    split; [cbn [app]; exact FR|]. split; [cbn; lia|]. unfold uw_opt.
    eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  pose proof EV as (OK & HEAP1 & _).
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
  clear HEAP LS ST MI MU WM HWL0 WOK0 FR PRE SX SY ACX ACY OFF SHB1 SHB2.
  ub; step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  2:{ (* [comment removed for export] *)
    replace (eqb na nb) with true by (symmetry; clear - K; destruct na, nb; cbn in *; congruence).
    apply evt_done.
    eapply implA_bind with (Q1 := add_joinA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (take 8 junk) m Σ ls OW LB AD EA lo ras rr R).
    2:{ cbv beta. intros [rn lsu] Σu msu (x1 & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & x18 & x19 & x20 & x21 & x24 & x25 & u3 & u4 & u5 & u6
                                          & F' & fc' & m' & OW' & used & -> & ENV' & HU' & LS' & HR').
        cbn [fst snd] in *. apply implA_ret_evt.
        eapply add_finA; [exact ENV' | exact HU' | exact LS' | exact HR']. }
    eapply (add_uadd_pathA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (take 8 junk) m Σ ls OW LB AD EA lo ras rr R CTX LO);
      [exact EV | lia | exact LS0 | exact HR | exact HX | exact HY]. }
  (* [comment removed for export] *)
  replace (eqb na nb) with false by (symmetry; clear - K; destruct na, nb; cbn in *; congruence).
  do 3 (ub; step).
  apply evt_done.
  eapply implA_bind with (Q1 := add_joinA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (take 8 junk) m Σ ls OW LB AD EA lo ras rr R).
  2:{ cbv beta. intros [rn lsu] Σu msu (x1 & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & x18 & x19 & x20 & x21 & x24 & x25 & u3 & u4 & u5 & u6
                                        & F' & fc' & m' & OW' & used & -> & ENV' & HU' & LS' & HR').
      cbn [fst snd] in *. apply implA_ret_evt.
      eapply add_finA; [exact ENV' | exact HU' | exact LS' | exact HR']. }
  eapply implA_bind.
  { eapply BN_ucmp_walkA with (lo := lo) (OW := OW) (LB := LB) (AD := AD) (EA := EA) (r1 := x) (r2 := y) (a := X) (b := Y);
      [| reflexivity | exact HX | exact HY | reflexivity | reflexivity].
    eapply cenv_preA; [exact EV | exact LS0 | unfold BN_UCMP_STACK; lia | unfold MC; lia]. }
  cbv beta. intros [c lsc] Σc msc PO.
  apply (bn_postA_cpost LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -96) MC Σ ls OW) in PO; [| exact OK | exact HEAP1].
  cbn [fst snd] in PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & -> & CP & ((-> & CR & -> & ->) & EC)).
  destruct (cenv_postA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EV CP) as (EV1 & LS1).
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP) as RS.
  cbn [fst snd] in *.
  rewrite (ret_pc_even 2437660) by lia.
  clear CP EV LS0 EC HEAP1.
  pose proof EV1 as (_ & HEAP2 & ST2 & MI2 & _).
  pose proof (RS _ _ HR) as HR1. pose proof (RS _ _ HX) as HX1. pose proof (RS _ _ HY) as HY1.
  destruct (open_ro_sh Σc OW LB m2 ls AD EA x X HEAP2 LS1 HX1) as (Dx1 & SX & _ & _ & _ & _ & _ & _ & ACX & _ & _ & _).
  destruct (open_ro_sh Σc OW LB m2 ls AD EA y Y HEAP2 LS1 HY1) as (Dy1 & SY & _ & _ & _ & _ & _ & _ & ACY & _ & _ & _).
  unfold bn_cells, MallocRep.wz in SX, SY. fold na in SX. fold nb in SY.
  pose proof (munch_refl (@nil (Z * Z)) m2) as MU2.
  apply implA_from_evt.
  ub; step. if_cases K1; zify_cond K1.
  2:{ (* [comment removed for export] *)
    assert (K1' : (0 <? c) = true) by (rewrite <- (land64_pos_iff c) by (clear - CR; lia); apply andb_true_iff; split; apply Z.ltb_lt; assumption).
    ub; shl. ub; chk0.
    ub; step. rewrite (sx32_small (Z.b2z na)) by (clear - NA; lia).
    do 3 (ub; step).
    apply evt_done. rewrite K1'.
    eapply (add_usub_pathA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (take 8 junk) m Σ ls OW LB AD EA lo ras rr R CTX LO);
      [exact EV1 | unfold MC; lia | exact LS1 | exact HR1 | exact HX1 | exact HY1]. }
  rewrite land64_pos_iff in K1 by (clear - CR; lia).
  ub; step. if_cases K2; zify_cond K2.
  { (* [comment removed for export] *)
    rewrite land64_neg_iff in K2 by (clear - CR; lia).
    assert (K2' : (c <? 0) = true) by (apply Z.ltb_lt; exact K2).
    ub; shl. ub; chk0.
    ub; step. rewrite (sx32_small (Z.b2z nb)) by (clear - NB; lia).
    do 4 (ub; step).
    apply evt_done. rewrite K1, K2'.
    eapply (add_usub_pathA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (take 8 junk) m Σ ls OW LB AD EA lo ras rr R CTX LO);
      [exact EV1 | unfold MC; lia | exact LS1 | exact HR1 | exact HY1 | exact HX1]. }
  (* [comment removed for export] *)
  assert (K2' : (c <? 0) = false).
  { apply Z.ltb_ge. destruct (Z_lt_ge_dec c 0) as [Hc|Hc]; [|lia]. exfalso.
    apply (land64_neg_iff c ltac:(clear - CR; lia)) in Hc. clear - Hc K2. lia. }
  pose proof EV1 as (_ & _ & _ & _ & _ & _ & _ & _ & FR2 & FSZ2 & _).
  pose proof (AH_nodup_l _ _ _ _ HEAP2) as ND2.
  destruct (lib_state_open [] ls m2 OW AD EA rr R LS1 ND2 HR1 ltac:(intros [])) as ((Dr & SR & ARR) & OKR & LSH).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS1 HR1) as HVR.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS1) as (IDS & ADB & ERRB & SOK).
  destruct (bn_arr_facts Σc OW LB m2 HEAP2 ls AD EA IDS ADB rr Dr HVR ARR) as (U & LENW & D0 & DC & DI & DSEP).
  specialize (DSEP rr R HR1).
  destruct (ref_at_inb _ _ _ _ _ ADB HR1) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP2 Hins) as (SA0 & _ & _ & SAC & SAI).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP2 LS1 HR1) as (ACR & ALR & OFR).
  set (b := getbn rr ls) in *.
  ub; step. ub; step.
  apply evt_done. rewrite K1, K2'. apply implA_ret_evt.
  eapply evt_cut.
  { eapply (BN_zero_ex_specA (Z_to_bv 64 2437712) (Z_to_bv 64 (bv_unsigned sp + -96))) with (A := R) (D := Dr) (b := b) (lo := lo);
      [exact SR | rewrite ESP; exact ST2 | rewrite ESP; lia | exact MI2 | rewrite ESP; unfold BnHeapA.ACEIL in *; lia
      | exact (AH_shb _ _ _ _ HEAP2) | exact ACR | exact ALR | unfold SHHI, BnHeapA.ACEIL in *; lia | exact OFR | reflexivity | clear - SA0 Ra1; lia]. }
  intros ms' (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m3 & -> & MUz & WMz & MIz & STz & SRz).
  rewrite ESP in MUz, STz.
  rewrite (ret_pc_even 2437712) by lia.
  assert (FR3 : rw_cells bsegs m3 (bv_unsigned sp + -96)
                  ([CB 8 (take 8 junk); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra])).
  { eapply rw_cells_transport; [exact FR2 | exact MUz | exact WMz |]. cbn. unfold BnHeapA.ACEIL in *. lia. }
  ub; step. ub; step. ub1 ub_kind. apply evt_done.
  assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -96 - 16, bv_unsigned sp + -96); (R, R + 24)]).
  { constructor; [left; cbn [fst snd]; lia|]. constructor; [|constructor].
    right. exists (qs, As, ns). cbn [blk_addr blk_size fst snd]. split; [exact Hins | lia]. }
  assert (WOK : Forall (w_ok OW LB ls AD EA [rr]) [(bv_unsigned sp + -96 - 16, bv_unsigned sp + -96); (R, R + 24)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [|constructor].
    eapply (w_struct OW LB ls AD EA false [rr] _ rr R); [left; reflexivity | exact HR1 | cbn; lia | cbn; lia]. }
  unfold add_joinA. do 23 eexists. exists m3, OW, (0 + 0). split; [reflexivity|]. cbn [fst snd].
  split.
  { apply cenv_setbnA; [| exact HVR | reflexivity].
    eapply cenv_silentA; [exact EV1 | exact MUz | exact WMz | exact HWL | exact STz | exact MIz | exact FR3 | exact FSZ2]. }
  split; [unfold MC; lia|]. split; [|apply ref_at_setbn; exact HR1].
  unfold lib_state. eapply (lib_state_close [] ls m3 OW AD EA rr R); [| exact ND2 | exact HR1 | | |].
  - eapply lib_state_frame; [exact HEAP2 | exact LSH | exact MUz | exact WMz | exact WOK].
  - exists Dr. split; [exact SRz|]. eapply bn_arr_of_u64arr; [exact ARR|].
    eapply u64arr_transport; [exact U | exact MUz | exact WMz |]. cbn [disjoint_from]. rewrite LENW. unfold BnHeapA.ACEIL in *. lia.
  - destruct OKR as (O1 & O2 & O3 & O4). unfold bn_okm, bn_zero_pure, bn_dmax in *. cbn [bn_top bn_buf bn_flags]. repeat split; [exact O1 | lia | exact O3 | exact O4].
  - apply ids_ok_setbn_same; [exact IDS | exact HVR | reflexivity].
Qed.
End WithRT.
