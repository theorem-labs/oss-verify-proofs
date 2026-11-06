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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnAddSpec BnMInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnA Require Import BnAPure.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA W_ucmpA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitAF W_expandAF BnCallAF W_cmpAF W_uaddAF W_usubAF.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import UbStructF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2322048 => 2
  | 2322060 => 1
  | 2322064 => 2
  | 2322104 => 2
  | 2322108 => 1
  | 2322112 => 2
  | 2322192 => 2
  | 2322216 => 2
  | 2322220 => 1
  | 2322224 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Open Scope Z_scope.

Definition BN_SUB : Z := 0x236e4c.
Definition BN_SUB_STACK : Z := 96 + BN_UADD_STACK.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_sub_uadd := (E_BN_sub_236d40 : uk_call BN_SUB 0x236f28 BN_UADD).
Local Notation E_sub_usub := (E_BN_sub_236d28 : uk_call BN_SUB 0x236f10 BN_USUB).

Section Proofs.

  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (jb : list byte)
            (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (lo : Z) (ras : list Z)
            (rr : bnref) (R : Z).
  Notation SP := (bv_unsigned sp).
  Notation PRE := [CB 8 jb; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1].
  Notation ENV := (cenvA LB PL lo SP (SP + -96) s0 ra (Some ras) MC Σ ls OW m PRE).
  Notation POSTA := (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1)).

  Lemma sub_finA : forall (Σx : rts RT) (lsx : bstate bptr) (mx : mem) (OWx : list block) (used : Z) (rneg : bool)
      (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x24 x25 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    ENV used Σx lsx mx OWx -> used <= MC -> lib_state lsx mx OWx PL EA -> ref_at lsx OWx PL rr R -> hpl PL rr ->
    evt bgbsegs (POSTA (tt, setbn rr (bn_with_neg (getbn rr lsx) rneg) lsx) Σx)
      (MS (mkR x1 (Z_to_bv 64 (SP + -96)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 R) (wz 1) a1 a2 a3 a4 a5 a6 a7
               x18 x19 x20 x21 (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.b2z rneg)) x24 x25 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x236f2c) fc None mx (seg_rom bgbsegs)).
  Proof.
    intros until fc. intros EV HU LS HR HPL. pose proof (proj1 (hpl_wref PL rr HPL) : not_one rr) as NRO.
    pose proof EV as ((CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & FROK & FAL & NOFR) & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_open [] lsx mx OWx PL EA rr R LS ND HR ltac:(intros []) NRO) as ((Dr & SR & ARR) & OKR & LSH).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    destruct (bn_arr_factsA Σx OWx LB mx lsx PL EA _ rr Dr HEAP PARTS FROK NOFR HVR NRO ARR) as (U & LENW & D0 & DC & DI & DSEP).
    specialize (DSEP rr R HR).
    destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP PARTS NOFR HR NRO) as (qs & As & ns & Hins & Ra1 & Ra2).
    pose proof (AH_range_in _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & SAI).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HR NRO) as (ACC & AL & OFR). unfold SHLO, SHHI in OFR.
    set (b := getbn rr lsx) in *.
    unfold bn_cells, MallocRep.wz in SR. unfold MallocRep.wz.
    pose proof (munch_refl [(R, R + 24)]%Z mx) as MU. pose proof (wmono_refl bgbsegs mx) as WM.
    assert (OFF : offshW [(R, R + 24)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; lia).
    cbn [app] in FR.
    do 3 (ub; step). ub; shl. ub; chk0. ub; step.
    do 11 (ub; step). release_frame FR ST (bv_unsigned sp). ub; step. ub; step.
    apply evt_done.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => rename mf into mF end.
    assert (HWL : Forall (w_lib lsx OWx PL lo (bv_unsigned sp)) [(R, R + 24)]).
    { constructor; [w_lib_ref HR NRO | constructor]. }
    assert (WOK : Forall (w_ok OWx LB lsx PL EA (bv_unsigned sp) [rr]) [(R, R + 24)]).
    { constructor; [eapply (w_struct OWx LB lsx PL EA (bv_unsigned sp) false [rr] _ rr R); [left; reflexivity | exact HR | exact NRO | cbn; lia | cbn; lia] | constructor]. }
    unfold bn_postA. do 17 eexists. exists mF, OWx, PL. split; [reflexivity|]. cbn [fst snd].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|].
    split.
    { unfold lib_state. eapply (lib_state_close [] lsx mF OWx PL EA rr R); [| exact ND | exact HR | exact NRO | | |].
      - eapply (lib_state_frame Σx LB (bv_unsigned sp) USTACK_TOP); [exact HEAP | exact LSH | exact MU | exact WM | exact FROK | exact WOK].
      - exists Dr. split; [unfold bn_cells, bn_with_neg, bn_dmax; cbn [bn_top bn_buf bn_neg bn_flags]; exact SR|].
        eapply bn_arr_of_u64arr; [exact ARR | exact U].
      - destruct OKR as (O1 & O2 & O3 & O4). unfold bg_ok, bn_with_neg, bn_dmax in *. cbn [bn_top bn_buf bn_flags]. auto.
      - apply ids_ok_setbn_same; [exact IDS | exact HVR | reflexivity]. }
    split; [exact ST|]. split; [exact MI|].
    split. { eapply ax_pres_trans; [exact AXP|]. exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL CEIL ltac:(lia)). }
    split; [lia|].
    split. { unfold cnt_eq in *. rewrite (cnt_bal_setbn rr _ lsx OWx OWx HVR), CNT. fold b. unfold bn_blocks, bn_with_neg. cbn [bn_d]. destruct (bn_d b); cbn [length]; lia. }
    split. { eapply refs_stable_trans; [exact RS| apply refs_stable_setbn]. }
    split; reflexivity.
  Qed.

  Definition sub_joinA (v : bool * bstate bptr) (Σ' : rts RT) : machine_state -> Prop :=
    fun ms' => exists x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x24 x25 t3 t4 t5 t6 F' fc' m' OW' used,
      ms' = MS (mkR x1 (Z_to_bv 64 (SP + -96)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 R) (wz 1) a1 a2 a3 a4 a5 a6 a7
                    x18 x19 x20 x21 (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.b2z (fst v))) x24 x25 s10 s11 t3 t4 t5 t6)
               F' (Z_to_bv 64 0x236f2c) fc' None m' (seg_rom bgbsegs)
      /\ ENV used Σ' (snd v) m' OW' /\ used <= MC /\ lib_state (snd v) m' OW' PL EA /\ ref_at (snd v) OW' PL rr R.

  Hypothesis CTX : uk_ctx BN_SUB (bv_unsigned ra :: ras).
  Hypothesis LOS : lo <= SP - BN_SUB_STACK.

  Lemma sub_usub_pathA : forall (Σx : rts RT) (lsx : bstate bptr) (mx : mem) (OWx : list block) (used : Z) (n : bool) (p q : bnref) (P Q : Z)
      (x1 t0 t1 t2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x24 x25 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    ENV used Σx lsx mx OWx -> used <= 0 -> lib_state lsx mx OWx PL EA ->
    ref_at lsx OWx PL rr R -> hpl PL rr -> ref_at lsx OWx PL p P -> p <> ROne -> ref_at lsx OWx PL q Q -> q <> ROne ->
    implA (tbind (BN_usub (tree_ops bptr) rr p q lsx) (fun p0 : unit * bstate bptr => TRet (n, snd p0))) Σx sub_joinA
      (MS (mkR x1 (Z_to_bv 64 (SP + -96)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 R) (Z_to_bv 64 R) (Z_to_bv 64 P) (Z_to_bv 64 Q)
               a3 a4 a5 a6 a7 x18 x19 x20 x21 (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.b2z n)) x24 x25 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x236f0c) fc None mx (seg_rom bgbsegs)).
  Proof.
    intros until fc. intros EV HU LS HR HPL HP NP HQ NQ. pose proof (proj1 (hpl_wref PL rr HPL) : not_one rr) as NRO.
    pose proof EV as (OK & HEAP & _). pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & _ & _ & NOFR).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    assert (ESP : bv_unsigned (Z_to_bv 64 (SP + -96)) = SP + -96) by (apply unsigned_lit; lia).
    unfold MallocRep.wz in *.
    apply implA_from_evt. ub; step. apply evt_done.
    eapply implA_bind.
    { eapply (BN_usub_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (rr := rr) (x := p) (y := q) (R := R) (X := P) (Y := Q)
                                  (OW := OWx) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HR | exact HPL | exact HP | exact NP | exact HQ | exact NQ | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EV | exact LS | | lia].
        unfold BN_SUB_STACK, BN_UADD_STACK, BN_USUB_STACK in *. lia.
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV).
      - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_sub_usub CTX). }
    cbv beta. intros [[] lsu] Σu msu PO.
    apply (bn_postA_cpost LB PL EA lo SP (SP + -96) MC Σ ls OW) in PO; [| exact OK | exact HEAP].
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & PL2 & -> & CP & (EPL & -> & _)).
    subst PL2. specialize (CP eq_refl).
    destruct (cenv_postA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EV CP) as (EV1 & LS1).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP) as RS.
    cbn [fst snd] in *.
    rewrite (ret_pc_even 2322192) by lia.
    destruct (ref_ubA _ _ _ _ _ _ _ _ _ HEAP LS NOFR HR NRO) as (R0 & R8 & RC).
    apply implA_ret_evt. ub; step. apply evt_done.
    unfold sub_joinA. do 23 eexists. exists m2, OW2, (used + MC). split; [reflexivity|]. cbn [fst snd].
    split; [exact EV1|]. split; [lia|]. split; [exact LS1 | exact (ref_at_stable _ _ _ _ _ _ _ RS HR)].
  Qed.

  Lemma sub_uadd_pathA : forall (Σx : rts RT) (lsx : bstate bptr) (mx : mem) (OWx : list block) (used : Z) (n : bool) (p q : bnref) (P Q : Z)
      (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x24 x25 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    ENV used Σx lsx mx OWx -> used <= 0 -> lib_state lsx mx OWx PL EA ->
    ref_at lsx OWx PL rr R -> hpl PL rr -> ref_at lsx OWx PL p P -> p <> ROne -> ref_at lsx OWx PL q Q -> q <> ROne ->
    implA (tbind (BN_uadd (tree_ops bptr) rr p q lsx) (fun p0 : unit * bstate bptr => TRet (n, snd p0))) Σx sub_joinA
      (MS (mkR x1 (Z_to_bv 64 (SP + -96)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 R) a0 a1 a2
               a3 a4 a5 a6 a7 (Z_to_bv 64 Q) (Z_to_bv 64 P) x20 x21 (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.b2z n)) x24 x25 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x236f18) fc None mx (seg_rom bgbsegs)).
  Proof.
    intros until fc. intros EV HU LS HR HPL HP NP HQ NQ. pose proof (proj1 (hpl_wref PL rr HPL) : not_one rr) as NRO.
    pose proof EV as (OK & HEAP & _). pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & _ & _ & NOFR).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    assert (ESP : bv_unsigned (Z_to_bv 64 (SP + -96)) = SP + -96) by (apply unsigned_lit; lia).
    unfold MallocRep.wz in *.
    apply implA_from_evt. do 4 (ub; step). apply evt_done.
    eapply implA_bind.
    { eapply (BN_uadd_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (rr := rr) (ra_ := p) (rb_ := q) (R := R) (A := P) (Bb := Q)
                                  (OW := OWx) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HR | exact HPL | exact HP | exact NP | exact HQ | exact NQ | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EV | exact LS | | lia].
        unfold BN_SUB_STACK, BN_UADD_STACK in *. lia.
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV).
      - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_sub_uadd CTX). }
    cbv beta. intros [[] lsu] Σu msu PO.
    apply (bn_postA_cpost LB PL EA lo SP (SP + -96) MC Σ ls OW) in PO; [| exact OK | exact HEAP].
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & PL2 & -> & CP & (EPL & -> & _)).
    subst PL2. specialize (CP eq_refl).
    destruct (cenv_postA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EV CP) as (EV1 & LS1).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP) as RS.
    cbn [fst snd] in *.
    rewrite (ret_pc_even 2322216) by lia.
    destruct (ref_ubA _ _ _ _ _ _ _ _ _ HEAP LS NOFR HR NRO) as (R0 & R8 & RC).
    apply implA_ret_evt. ub1 ub_kind. apply evt_done.
    unfold sub_joinA. do 23 eexists. exists m2, OW2, (used + MC). split; [reflexivity|]. cbn [fst snd].
    split; [exact EV1|]. split; [lia|]. split; [exact LS1 | exact (ref_at_stable _ _ _ _ _ _ _ RS HR)].
  Qed.
End Proofs.

Lemma BN_sub_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (rr x y : bnref) (R X Y : Z),
  bn_preA Σ ls m OW LB PL EA sp lo BN_SUB_STACK MC ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_SUB (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> ref_at ls OW PL rr R -> hpl PL rr -> ref_at ls OW PL x X -> x <> ROne -> ref_at ls OW PL y Y -> y <> ROne ->
  a0 = wz R -> a1 = wz X -> a2 = wz Y ->
  implA (BN_sub (tree_ops bptr) rr x y ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_SUB) fc None m (seg_rom bgbsegs)).
Proof.
  intros until Y. intros PRE UW CTX -> HR HPL HX NROx HY NROy -> -> ->.
  pose proof (proj1 (hpl_wref PL rr HPL) : not_one rr) as NRO. change (not_one x) in NROx. change (not_one y) in NROy.
  pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  pose proof LO as LO'. unfold BN_SUB_STACK, BN_UADD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO'.
  unfold BN_SUB, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  destruct (open_ro_sh Σ OW LB m ls PL EA _ x X HEAP LS FROK NOFR HX NROx) as (Dx0 & SX & OKX & _ & X0 & XC & _ & _ & ACX & ALX & _ & _).
  destruct (open_ro_sh Σ OW LB m ls PL EA _ y Y HEAP LS FROK NOFR HY NROy) as (Dy0 & SY & OKY & _ & Y0 & YC & _ & _ & ACY & ALY & _ & _).
  unfold bn_cells, MallocRep.wz in SX, SY.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 96, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  unfold BN_sub, bbind, bget, bset, bret. cbn [bind ret tree_ops tbind fst snd].
  set (na := bn_neg (getbn x ls)) in *. set (nb := bn_neg (getbn y ls)) in *.
  assert (NA : 0 <= Z.b2z na <= 1) by (destruct na; cbn; lia).
  assert (NB : 0 <= Z.b2z nb <= 1) by (destruct nb; cbn; lia).
  apply implA_from_evt.
  carve_frame 96%nat ST.
  apply (rw_cells_split_CB bgbsegs _ _ [] 96 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 13 (ub; step). do 3 (ub; step). do 4 (ub; step).
  do 2 (ub; step). ub; shl. ub; chk0.
  ub; step. do 2 (ub; step). ub; shl. ub; step. rewrite (sx32_small (Z.b2z na)) by (clear - NA; lia). ub; chk0.
  ub; step. rewrite (sx32_small (Z.b2z nb)) by (clear - NB; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (HWL0 : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -96, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK0 : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -96, bv_unsigned sp)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m m1 OW PL EA _ HEAP LS MU WM FROK WOK0) as LS0.
  assert (EV : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -96) s0 ra (Some ras) MC Σ ls OW m
                 [CB 8 (take 8 junk); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] 0 Σ ls m1 OW).
  { unfold cenvA, cenv_ok.
    split; [split; [exact CEIL|]; split; [lia|]; split; [lia|]; split; [unfold USTACK_TOP; lia|]; split; [exact SP16|];
            split; [clear - SP16; Z.div_mod_to_equations; lia|]; split; [exact CNT|]; split; [exact CRED|]; split; [exact FROK|]; split; [exact FAL| exact NOFR]|].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL0 CEIL ltac:(unfold USTACK_TOP; lia))|].
    split; [exact ST|]. split; [exact MI|].
    split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL0 CEIL ltac:(lia))|].
    split; [lia|]. split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|].
    split; [cbn [app]; exact FR|]. split; [cbn; lia|]. unfold uw_opt.
    eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  pose proof EV as (OK & HEAP1 & _).
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
  clear HEAP LS ST MI MU WM HWL0 WOK0 FR PRE SX SY ACX ACY OFF SHB1 SHB2 PARTS.
  ub; step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  1:{
    replace (eqb na nb) with false by (symmetry; clear - K; destruct na, nb; cbn in *; congruence). cbn [negb].
    apply evt_done.
    eapply implA_bind with (Q1 := sub_joinA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (take 8 junk) m Σ ls OW LB PL EA lo ras rr R).
    2:{ cbv beta. intros [rn lsu] Σu msu (x1 & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & x18 & x19 & x20 & x21 & x24 & x25 & u3 & u4 & u5 & u6
                                          & F' & fc' & m' & OW' & used & -> & ENV' & HU' & LS' & HR').
        cbn [fst snd] in *. apply implA_ret_evt.
        eapply sub_finA; [exact ENV' | exact HU' | exact LS' | exact HR' | exact HPL]. }
    eapply (sub_uadd_pathA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (take 8 junk) m Σ ls OW LB PL EA lo ras rr R CTX LO);
      [exact EV | lia | exact LS0 | exact HR | exact HPL | exact HX | exact NROx | exact HY | exact NROy]. }

  replace (eqb na nb) with true by (symmetry; clear - K; destruct na, nb; cbn in *; congruence). cbn [negb].
  do 3 (ub; step).
  apply evt_done.
  eapply implA_bind with (Q1 := sub_joinA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (take 8 junk) m Σ ls OW LB PL EA lo ras rr R).
  2:{ cbv beta. intros [rn lsu] Σu msu (x1 & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & x18 & x19 & x20 & x21 & x24 & x25 & u3 & u4 & u5 & u6
                                        & F' & fc' & m' & OW' & used & -> & ENV' & HU' & LS' & HR').
      cbn [fst snd] in *. apply implA_ret_evt.
      eapply sub_finA; [exact ENV' | exact HU' | exact LS' | exact HR' | exact HPL]. }
  eapply implA_bind.
  { eapply BN_ucmp_walkA with (lo := lo) (OW := OW) (LB := LB) (PL := PL) (EA := EA) (r1 := x) (r2 := y) (a := X) (b := Y);
      [| reflexivity | exact HX | exact HY | exact NROx | exact NROy | reflexivity | reflexivity].
    eapply cenv_preA; [exact EV | exact LS0 | unfold BN_UCMP_STACK; lia | unfold MC; lia]. }
  cbv beta. intros [c lsc] Σc msc PO.
  apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -96) MC Σ ls OW) in PO; [| exact OK | exact HEAP1].
  cbn [fst snd] in PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & PL2 & -> & CP & ((EPL & -> & CR & -> & ->) & EC)).
  subst PL2. specialize (CP eq_refl).
  destruct (cenv_postA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EV CP) as (EV1 & LS1).
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP) as RS.
  cbn [fst snd] in *.
  rewrite (ret_pc_even 2322160) by lia.
  clear CP EV LS0 EC HEAP1.
  pose proof EV1 as (_ & HEAP2 & ST2 & MI2 & _).
  pose proof (ref_at_stable _ _ _ _ _ _ _ RS HR) as HR1. pose proof (ref_at_stable _ _ _ _ _ _ _ RS HX) as HX1. pose proof (ref_at_stable _ _ _ _ _ _ _ RS HY) as HY1.
  pose proof EV1 as ((_ & _ & _ & _ & _ & _ & _ & _ & FROK1 & _) & _).
  destruct (open_ro_sh Σc OW LB m2 ls PL EA _ x X HEAP2 LS1 FROK1 NOFR HX1 NROx) as (Dx1 & SX & _ & _ & _ & _ & _ & _ & ACX & _ & _ & _).
  destruct (open_ro_sh Σc OW LB m2 ls PL EA _ y Y HEAP2 LS1 FROK1 NOFR HY1 NROy) as (Dy1 & SY & _ & _ & _ & _ & _ & _ & ACY & _ & _ & _).
  unfold bn_cells, MallocRep.wz in SX, SY. fold na in SX. fold nb in SY.
  pose proof (munch_refl (@nil (Z * Z)) m2) as MU2.
  apply implA_from_evt.
  ub; step. if_cases K1; zify_cond K1.
  2:{
    assert (K1' : (0 <? c) = true) by (rewrite <- (land64_pos_iff c) by (clear - CR; lia); apply andb_true_iff; split; apply Z.ltb_lt; assumption).
    ub; shl. ub; chk0.
    ub; step. rewrite (sx32_small (Z.b2z na)) by (clear - NA; lia).
    do 3 (ub; step).
    apply evt_done. rewrite K1'.
    eapply (sub_usub_pathA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (take 8 junk) m Σ ls OW LB PL EA lo ras rr R CTX LO);
      [exact EV1 | unfold MC; lia | exact LS1 | exact HR1 | exact HPL | exact HX1 | exact NROx | exact HY1 | exact NROy]. }
  rewrite land64_pos_iff in K1 by (clear - CR; lia).
  ub; step. if_cases K2; zify_cond K2.
  {
    rewrite land64_neg_iff in K2 by (clear - CR; lia).
    assert (K2' : (c <? 0) = true) by (apply Z.ltb_lt; exact K2).
    ub; shl. ub; chk0.
    ub; step. rewrite (sx32_small (Z.b2z nb)) by (clear - NB; lia).
    ub; step. setreg 23%Z (Z_to_bv 64 (Z.b2z (negb nb))) ltac:(clear; destruct nb; reflexivity).
    do 4 (ub; step).
    apply evt_done. rewrite K1, K2'.
    eapply (sub_usub_pathA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (take 8 junk) m Σ ls OW LB PL EA lo ras rr R CTX LO);
      [exact EV1 | unfold MC; lia | exact LS1 | exact HR1 | exact HPL | exact HY1 | exact NROy | exact HX1 | exact NROx]. }

  assert (K2' : (c <? 0) = false).
  { apply Z.ltb_ge. destruct (Z_lt_ge_dec c 0) as [Hc|Hc]; [|lia]. exfalso.
    apply (land64_neg_iff c ltac:(clear - CR; lia)) in Hc. clear - Hc K2. lia. }
  pose proof EV1 as (_ & _ & _ & _ & _ & _ & _ & _ & FR2 & FSZ2 & _).
  pose proof (AH_nodup_l _ _ _ _ HEAP2) as ND2.
  destruct (lib_state_open [] ls m2 OW PL EA rr R LS1 ND2 HR1 ltac:(intros []) NRO) as ((Dr & SR & ARR) & OKR & LSH).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS1 HR1) as HVR.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS1) as PARTS1. pose proof PARTS1 as (WFS & PWF & IDS & PLB & ERRB).
  destruct (bn_arr_factsA Σc OW LB m2 ls PL EA _ rr Dr HEAP2 PARTS1 FROK1 NOFR HVR NRO ARR) as (U & LENW & D0 & DC & DI & DSEP).
  specialize (DSEP rr R HR1).
  destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 NOFR HR1 NRO) as (qs & As & ns & Hins & Ra1 & Ra2).
  pose proof (AH_range_in _ _ _ _ _ _ _ HEAP2 Hins) as (SA0 & _ & _ & SAC & SAI).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP2 LS1 NOFR HR1 NRO) as (ACR & ALR & OFR).
  set (b := getbn rr ls) in *.
  ub; step. ub; step.
  apply evt_done. rewrite K1, K2'. apply implA_ret_evt.
  eapply evt_cut.
  { eapply (BN_zero_ex_specA (Z_to_bv 64 2322316) (Z_to_bv 64 (bv_unsigned sp + -96))) with (A := R) (D := Dr) (b := b) (lo := lo);
      [exact SR | rewrite ESP; exact ST2 | rewrite ESP; lia | exact MI2 | rewrite ESP; unfold BnHeapA.ACEIL in *; lia
      | exact (AH_shb _ _ _ _ HEAP2) | exact ACR | exact ALR | unfold SHHI, BnHeapA.ACEIL in *; lia | exact OFR | reflexivity | clear - SA0 Ra1; lia]. }
  intros ms' (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m3 & -> & MUz & WMz & MIz & STz & SRz).
  rewrite ESP in MUz, STz.
  rewrite (ret_pc_even 2322316) by lia.
  assert (FR3 : rw_cells bgbsegs m3 (bv_unsigned sp + -96)
                  ([CB 8 (take 8 junk); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra])).
  { eapply rw_cells_transport; [exact FR2 | exact MUz | exact WMz |]. cbn. unfold BnHeapA.ACEIL in *. lia. }
  assert (R0 : 0 < R) by (clear - SA0 Ra1; lia).
  ub; step. ub; step. step. if_cases KJ; zify_cond KJ; [clear KJ | exfalso; ub_norm KJ; first [ub_solve KJ | ub_ltb_cases KJ]]. apply evt_done.
  assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -96 - 16, bv_unsigned sp + -96); (R, R + 24)]).
  { constructor; [left; cbn [fst snd]; lia|]. constructor; [|constructor].
    w_lib_ref HR1 NRO. }
  assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) [rr]) [(bv_unsigned sp + -96 - 16, bv_unsigned sp + -96); (R, R + 24)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [|constructor].
    eapply (w_struct OW LB ls PL EA (bv_unsigned sp) false [rr] _ rr R); [left; reflexivity | exact HR1 | exact NRO | cbn; lia | cbn; lia]. }
  unfold sub_joinA. do 23 eexists. exists m3, OW, (0 + 0). split; [reflexivity|]. cbn [fst snd].
  split.
  { apply cenv_setbnA; [| exact HVR | reflexivity].
    eapply cenv_silentA; [exact EV1 | exact LS1 | exact MUz | exact WMz | exact HWL | exact STz | exact MIz | exact FR3 | exact FSZ2]. }
  split; [unfold MC; lia|]. split; [|apply ref_at_setbn; exact HR1].
  unfold lib_state. eapply (lib_state_close [] ls m3 OW PL EA rr R); [| exact ND2 | exact HR1 | exact NRO | | |].
  - eapply (lib_state_frame Σc LB (bv_unsigned sp) USTACK_TOP); [exact HEAP2 | exact LSH | exact MUz | exact WMz | exact FROK1 | exact WOK].
  - exists Dr. split; [exact SRz|]. eapply bn_arr_of_u64arr; [exact ARR|].
    eapply u64arr_transport; [exact U | exact MUz | exact WMz |]. cbn [disjoint_from]. rewrite LENW. unfold BnHeapA.ACEIL in *. lia.
  - destruct OKR as (O1 & O2 & O3 & O4). unfold bg_ok, bn_zero_pure, bn_dmax in *. cbn [bn_top bn_buf bn_flags]. repeat split; [exact O1 | lia | exact O3 | exact O4].
  - apply ids_ok_setbn_same; [exact IDS | exact HVR | reflexivity].
Qed.
End WithRT.
