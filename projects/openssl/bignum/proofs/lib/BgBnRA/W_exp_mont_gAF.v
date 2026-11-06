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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnDivWords BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib BgWords BgArith BgMont BgExp.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout R_unwind_chain RT_iface RT_iface2 RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import MState Mem Cells Step Arr Bytes Frame.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import W_ctxA W_ctx_getA W_ctx_endA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnE Require W_gueron_arr.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import AFrameKit AFrameCall AFrameTac AFrameEnv BnAKitAF BnCallAF W_expandAF W_callsAF W_ctxAF W_ctx_getAF W_ctx_endAF W_lshiftAF W_div_tailAF W_divAF W_bndivAF W_uaddAF W_addAF W_subAF W_set_wordAF W_cmpAF AFrameComp ExpKitAF W_small3A W_calls3AF W_nnmodAF ExpStmtF ExpBodyKitF PlaceMont PlaceKitA W_mont_ctxAF W_mont_freeAF MontKitAF Fr_exp_mont W_exp_montAF InvKitAF HoleKitAF AW_gueron_arr.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation ops := (tree_ops bptr).

Definition GFILL_allA {AR1 : ARun} {UK : UnwindKit} (CS : Z) : Prop := forall (sp gp s0 ra : word) (Σ1 : rts (@ar_RT AR1)) (ls : bstate bptr) (OW LB : list block)
    (PL0 : placement) (EA : BnRepDefs.err_addrs) (lo spa f TOTAL : Z) (q : bptr) (ras : list Z) (g : nat) (junk : list byte) (rm : bnref) (arr arp arm ac : Z),
  lo <= spa - CS ->
  uk_ctx BN_MOD_EXP_MONT (bv_unsigned ra :: ras) ->
  rm <> ROne ->
  forall (am : Z) (qm : bptr), @GFILL_stmt AR1 sp gp s0 ra Σ1 ls OW LB PL0 EA lo spa f TOTAL q ras g junk rm arr arp arm ac am qm.

Section Body.
Context {AR1 : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR1).
Local Notation AF := (@ar_AF AR1).
Local Notation PMc := (@ar_PMc AR1).
Local Notation ACEIL := (@BnHeapA.ACEIL AR1).
Local Notation AHEAP := (@BnHeapA.AHEAP AR1).

Section Proofs.
  Variable CS : Z.
  Hypothesis CSwexp : BN_WEXPAND_STACK <= CS.

  Lemma gueron_fill_allA : GFILL_allA CS.
  Proof.
    unfold GFILL_allA. intros sp gp s0 ra Σ1 ls OW LB PL0 EA lo spa f TOTAL q ras g junk rm arr arp arm ac LOK CTX NROm am qm.
    unfold GFILL_stmt. intros until fc. intros EVT LST HAqT Er HAmT NEQ TOP1 COST.
    set (PL := pl_set_mont PL0 (Some (am, qm))) in *.
    pose proof EVT as (OK & _).
    pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _ & _ & FROKK & _ & _).
    pose proof (ESPvA _ _ _ _ _ _ _ _ _ _ _ _ OK (proj1 (proj2 EVT))) as ESP.
    pose proof (AH_ceil _ _ _ _ (proj1 (proj2 EVT))) as (CE1 & CE2 & CE3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CE1, CE2, CE3.
    assert (CS16 : 16 <= CS) by (pose proof CSwexp as H; unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in H; clear - H; lia).
    assert (LOFB16 : lo <= spa - 16) by (clear - LOK CS16; lia).
    assert (LOFW : lo <= spa - BN_WEXPAND_STACK) by (clear - LOK CSwexp; lia).
    pose proof MC0 as MCP.
    unfold bst, MallocRep.wz in *.
    assert (NROq : rq <> ROne) by (rewrite Er; unfold RPool, ROne, NFIX; clear; lia).
    assert (WRq : wref PL rq) by (rewrite Er; exact (hpl_wref _ _ (hpl_pool PL ri))).

    destruct (open_for_read ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mb _ _ _ _ _ _ _ _ 16 EVT LST HAmT NROm ltac:(clear; lia) LOFB16)
      as (Dm0 & _ & (_ & OKm2 & OKm3 & _) & _).
    set (bmT := getbn rm lsT) in *. set (j := bn_top bmT) in *.
    assert (J512 : Z.of_nat j <= 512) by (unfold BG_DMAX in OKm3; clear - OKm2 OKm3; lia).
    clear Dm0.
    pose proof EVT as (_ & _ & STT & MIT & _ & _ & _ & _ & FRT & FSZT & _). cbn [app locs] in FRT.
    apply implA_from_evt.
    do 3 step.

    apply evt_done.
    eapply implA_bind.
    { eapply (bn_wexpand_walkA) with (lo := lo) (OW := OWT) (LB := ((q, f + 32, 256) :: LB)) (PL := PL) (EA := EA) (r := rq) (a := ar) (words := j);
        [| | | reflexivity | exact HAqT | exact WRq | reflexivity | reflexivity | clear - J512; lia].
      - eapply cenv_preA; [exact EVT | exact LST | exact LOFW | exact COST].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVT).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_2af3e0 CTX).
    }
    cbv beta. intros [u1 ls1] Σ2 ms1 PO.
    apply (bn_postA_cpost ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EVT))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F1 & fc1 & m2 & OW2 & PL2 & -> & CP1 & (EPL & -> & HDM1 & WXR1 & _)).
    subst PL2. specialize (CP1 eq_refl).
    destruct (cenv_postA ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mb _ _ _ _ _ _ _ _ _ _ _ EVT CP1) as (EV2 & LS2).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP1) as RS2. clear CP1.
    rewrite (ret_pc_even 2815432) by (clear; lia).

    pose proof (ref_at_stable _ _ _ _ PL _ _ RS2 HAqT) as HAq2. pose proof (ref_at_stable _ _ _ _ PL _ _ RS2 HAmT) as HAm2.
    assert (EM1 : getbn rm ls1 = bmT).
    { destruct WXR1 as [[_ ->]|[_ (pn & ->)]]; [reflexivity| apply getbn_setbn_other; exact NEQ]. }
    set (rb := getbn rq ls1) in *.
    assert (HDr : (0 < bn_dmax rb)%nat) by (clear - HDM1 TOP1; lia).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAq2) as HVq2.
    destruct (cenv_hole1A ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra ras TOTAL Σ1 ls ((qm, am, 96) :: OW) mb LOFB16 _ _ _ _ _ _ rq ar EV2 LS2 HAq2 WRq HDr)
      as (Dr & pr & Edr & Hinr & BNr & Ur & (OKr1 & OKr2 & OKr3 & OKr4) & (ACCr & ALr & Ar0 & SEPr & OFRr) & (ACDr & ALDr & Dr0 & DrS & OFDr) & SEPd & _ & ST2 & MI2 & CLOSE).
    fold rb in Edr, Hinr, BNr, Ur, OKr1, OKr2, OKr3, OKr4, ACDr, DrS, OFDr, SEPd, CLOSE.
    destruct (cenv_read_roA ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra ras TOTAL Σ1 ls ((qm, am, 96) :: OW) mb LOFB16 _ _ _ _ _ _ rm arm EV2 LS2 HAm2 NROm)
      as (Dm & BNm & Um & (OKm1 & _ & _ & _) & (ACCm & ALm & Am0 & SEPm) & (ACDm & ALDm & Dm0 & DmS) & SEPdm & LLm).
    rewrite EM1 in BNm, Um, OKm1, ACDm, DmS, SEPdm, LLm.
    pose proof (LLm rq pr Dr NEQ HVq2 Edr Hinr) as DJ. fold rb in DJ.
    pose proof (SEPd rq ar HAq2) as SQR. pose proof (SEPd rm arm HAm2) as SMR. pose proof (SEPdm rq ar HAq2) as SQM.
    clear SEPd SEPdm LLm.
    unfold BnRepDefs.bn_cells, MallocRep.wz in BNr, BNm. unfold BG_DMAX in OKr3.
    pose proof (munch_refl (fpw1A ar Dr (bn_dmax rb)) m2) as MU. pose proof (wmono_refl bgasegs m2) as WM. unfold fpw1A in MU.
    pose proof EV2 as (_ & _ & _ & _ & _ & _ & _ & _ & FR2 & FSZ2 & _). cbn [app locs] in FR2.
    assert (LBm : length (bn_buf bmT) = bn_dmax bmT) by reflexivity.
    assert (LBr : length (bn_buf rb) = bn_dmax rb) by reflexivity.
    assert (J1 : (1 <= j)%nat) by exact TOP1.
    assert (ArR : 0 < ar < 2 ^ 64) by (clear - Ar0 SEPr SPT FBSP CE1 CEIL LOFB; unfold USTACK_TOP in *; lia).
    unfold USTACK_TOP in SPT. unfold SHLO, SHHI in OFRr, OFDr.

    unfold bset. cbn [tree_ops]. rewrite EM1. fold rb. fold j.
    apply implA_from_evt.
    unfold MallocRep.wz.
    step.
    if_cases KZ; zify_cond KZ; rewrite ?unsigned_lit in KZ by (clear - ArR; lia); [exfalso; clear - KZ ArR; lia| clear KZ].

    shl_with ACCm ALm. chk0.
    step.

    do 2 step.
    assert (BDm : 0 <= Dm /\ Dm + 8 * Z.of_nat (bn_dmax bmT) <= 140737488355328) by (clear - Dm0 DmS SPT FBSP; lia).
    assert (BDr : 0 <= Dr /\ Dr + 8 * Z.of_nat (bn_dmax rb) <= 140737488355328) by (clear - Dr0 DrS SPT FBSP; lia).
    shl_limb ACDm ALDm BDm 0.
    do 2 step.
    chk0.

    do 2 step. shl_with ACCr ALr. chk0.
    step.
    do 2 step. shl_limb ACDr ALDr BDr 0. chk0.

    assert (ACM : acc bgasegs m2 Dm (8 * Z.of_nat j)) by (eapply acc_sub; [exact ACDm | clear; lia | clear - OKm2; unfold bn_dmax in *; lia]).
    assert (ACR : acc bgasegs m2 Dr (8 * Z.of_nat j)) by (eapply acc_sub; [exact ACDr | clear; lia | clear - HDM1; lia]).
    rewrite <- ESP in ST2.
    eapply (gueron_fill_walkA) with (lo := lo) (RD := Dr) (MD := Dm) (R := bn_buf rb) (M := bn_buf bmT) (j := j);
      [ exact OKm1 | exact J1 | rewrite LBr; exact HDM1 | rewrite LBm; exact OKm2 | clear - J512; lia | rewrite LBm, LBr; clear - DJ; lia
      | exact ACM | exact ACR | exact ALDm | exact ALDr | clear - BDm OKm2; unfold bn_dmax in *; lia | clear - BDr HDM1; lia
      | cbn [offshW]; unfold SHLO, SHHI; split; [clear - OFDr HDM1; lia | exact I]
      | | exact Ur | exact Um | exact MI2 | exact ST2 ].
    unfold GKONT. intros m3 y10 y11 y12 y13 y14 y15 y16 MUc WMc MIc UR3 UM3 STc.
    rewrite ESP in STc.

    eapply (rw_cells_transport bgasegs _ m2 m3) in BNr; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - SQR HDM1; lia | exact I]].
    assert (MU3 : munch [(ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax rb))] m2 m3).
    { eapply (munch_weaken [(Dr, Dr + 8 * Z.of_nat j)]); [| exact MUc]. unfold sub_fp. cbn [outside]. intros xx Hx. clear - Hx HDM1. lia. }
    clear MU WM Ur Um BNm FR2 ST2 MI2 UM3 ACM ACR ACDm ACDr ACCm MUc.
    assert (LG : length (gfin (bn_buf rb) (bn_buf bmT) j) = length (bn_buf rb)) by (apply W_gueron_arr.gfin_length; [rewrite LBr; exact HDM1| rewrite LBm; exact OKm2]).
    assert (LUr : Z.of_nat (length (wlimbs (gfin (bn_buf rb) (bn_buf bmT) j))) = Z.of_nat (bn_dmax rb)) by (rewrite wlimbs_len, LG, LBr; reflexivity).

    do 3 step. shl_with ACCr ALr. chk0.
    apply hide_intro in DJ. apply hide_intro in SQM. apply hide_intro in SMR. apply hide_intro in OKr4.
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    apply hide_elim in OKr4.

    set (b2 := mkBN (bn_d rb) (gfin (bn_buf rb) (bn_buf bmT) j) j (bn_neg rb) (bn_flags rb)) in *.
    assert (OK2 : bg_ok b2).
    { unfold bg_ok, BG_DMAX. change (bn_dmax b2) with (length (gfin (bn_buf rb) (bn_buf bmT) j)). cbn [b2 bn_buf bn_top bn_flags]. rewrite LG, LBr.
      split; [apply W_gueron_arr.gfin_limbs; [exact OKr1| exact OKm1]|]. split; [exact HDM1|]. split; [exact OKr3| exact OKr4]. }
    destruct (CLOSE m4 b2 MU3 WMc) as (ENV3 & LS3).
    { change (BnRepDefs.bn_cells Dr b2) with [C8 (wz Dr); C4 (wz (Z.of_nat j)); C4 (wz (Z.of_nat (length (gfin (bn_buf rb) (bn_buf bmT) j))));
                                              C4 (wz (Z.b2z (bn_neg rb))); C4 (wz (bn_flags rb))].
      rewrite LG, LBr. exact BNr. }
    { exact UR3. } { reflexivity. } { exact LG. } { exact OK2. } { exact STc. } { exact MIc. }
    apply evt_done. apply implA_ret.
    unfold GFQ, bst. exists m4, OW2, (used + MC). do 22 eexists. split; [reflexivity|]. cbn [fst snd].
    split; [exact ENV3|]. split; [exact LS3|].
    split; [eapply refs_stable_trans; [exact RS2| apply refs_stable_setbn] | clear; lia].
  Qed.

End Proofs.
End Body.
