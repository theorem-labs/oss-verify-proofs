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
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_iface2 RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import MState Mem Cells Step Arr Bytes Frame.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import W_ctxA W_ctx_getA W_ctx_endA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnE Require W_gueron_arr.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import AFrameKit AFrameCall AFrameTac AFrameEnv BnAKitAF BnCallAF W_expandAF W_callsAF W_ctxAF W_ctx_getAF W_ctx_endAF W_lshiftAF W_div_tailAF W_divAF W_bndivAF W_uaddAF W_addAF W_subAF W_set_wordAF W_cmpAF AFrameComp ExpKitAF W_small3A W_calls3AF W_nnmodAF ExpStmtF ExpBodyKitF PlaceMont PlaceKitA W_mont_ctxAF W_mont_freeAF MontKitAF Fr_exp_mont W_exp_montAF InvKitAF HoleKitAF AW_gueron_arr.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import UbStructF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2857820 => 2 | 2857824 => 1 | 2857828 => 2
  | 2857852 => 1 | 2857856 => 2 | 2857860 => 1 | 2857864 => 1 | 2857868 => 2
  | 2857900 => 2 | 2857904 => 1 | 2857908 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
Ltac unhide := repeat match goal with H : hide _ |- _ => apply hide_elim in H end.
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
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_2b9964 CTX).
    }
    cbv beta. intros [u1 ls1] Σ2 ms1 PO.
    apply (bn_postA_cpost ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EVT))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F1 & fc1 & m2 & OW2 & PL2 & -> & CP1 & (EPL & -> & HDM1 & WXR1 & _)).
    subst PL2. specialize (CP1 eq_refl).
    destruct (cenv_postA ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mb _ _ _ _ _ _ _ _ _ _ _ EVT CP1) as (EV2 & LS2).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP1) as RS2. clear CP1.
    rewrite (ret_pc_even 2857804) by (clear; lia).

    pose proof (ref_at_stable _ _ _ _ PL _ _ RS2 HAqT) as HAq2. pose proof (ref_at_stable _ _ _ _ PL _ _ RS2 HAmT) as HAm2.
    assert (EM1 : getbn rm ls1 = bmT).
    { destruct WXR1 as [[_ ->]|[_ (pn & ->)]]; [reflexivity| apply getbn_setbn_other; exact NEQ]. }
    set (rb := getbn rq ls1) in *.
    assert (HDr : (0 < bn_dmax rb)%nat) by (clear - HDM1 TOP1; lia).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAq2) as HVq2.
    destruct (cenv_hole1A ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra ras TOTAL Σ1 ls ((qm, am, 96) :: OW) mb LOFB16 _ _ _ _ _ _ rq ar EV2 LS2 HAq2 WRq HDr)
      as (Dr & pr & Edr & Hinr & BNr & Ur & (OKr1 & OKr2 & OKr3 & OKr4) & (ACCr & ALr & Ar0 & SEPr & OFRr) & (ACDr & ALDr & Dr0 & DrS & OFDr) & SEPd & _ & ST2 & MI2 & CLOSE).
    fold rb in Edr, Hinr, BNr, Ur, OKr1, OKr2, OKr3, OKr4, ACDr, DrS, OFDr, SEPd, CLOSE.
    destruct (cenv_read_roU ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra ras TOTAL Σ1 ls ((qm, am, 96) :: OW) mb LOFB16 _ _ _ _ _ _ rm arm EV2 LS2 HAm2 NROm)
      as (Dm & BNm & Um & (OKm1 & _ & _ & _) & (ACCm & ALm & Am0 & SEPm) & (ACDm & ALDm & Dm0 & DmS) & UBPm & SEPdm & LLm).
    rewrite EM1 in BNm, Um, OKm1, ACDm, DmS, UBPm, SEPdm, LLm.
    pose proof (LLm rq pr Dr NEQ HVq2 Edr Hinr) as DJ. fold rb in DJ.
    pose proof (SEPd rq ar HAq2) as SQR. pose proof (SEPd rm arm HAm2) as SMR. pose proof (SEPdm rq ar HAq2) as SQM.
    clear SEPd SEPdm LLm.
    unfold BnRepDefs.bn_cells, MallocRep.wz in BNr, BNm. unfold BG_DMAX in OKr3.
    pose proof (munch_refl (fpw1A ar Dr (bn_dmax rb)) m2) as MU. pose proof (wmono_refl bgbsegs m2) as WM. unfold fpw1A in MU.
    pose proof EV2 as (_ & _ & _ & _ & _ & _ & _ & _ & FR2 & FSZ2 & _). cbn [app locs] in FR2.
    assert (LBm : length (bn_buf bmT) = bn_dmax bmT) by reflexivity.
    assert (LBr : length (bn_buf rb) = bn_dmax rb) by reflexivity.
    assert (J1 : (1 <= j)%nat) by exact TOP1.
    assert (ArR : 0 < ar < 2 ^ 64) by (clear - Ar0 SEPr SPT FBSP CE1 CEIL LOFB; unfold USTACK_TOP in *; lia).
    unfold USTACK_TOP in SPT. unfold SHLO, SHHI in OFRr, OFDr.

    unfold bset. cbn [tree_ops]. rewrite EM1. fold rb. fold j.
    assert (AmR : 0 < arm < 2 ^ 64) by (clear - Am0 SEPm FBSP SPT; lia).
    assert (DmP : 0 < Dm) by (destruct (UBPm ltac:(clear - OKm2 TOP1; unfold j in *; lia)) as (P0 & _); exact P0).
    assert (DrP : 0 < Dr /\ Dr mod 16 = 0) by (pose proof (AH_range _ _ _ _ _ _ _ (proj1 (proj2 EV2)) Hinr) as (R0 & R16 & _); split; assumption).
    apply implA_from_evt.
    unfold MallocRep.wz.
    step.
    if_cases KZ; zify_cond KZ; rewrite ?unsigned_lit in KZ by (clear - ArR; lia); [exfalso; clear - KZ ArR; lia| clear KZ].

    shl_with ACCm ALm. chk0.
    step.

    hide_ors. ub. unhide.

    do 3 step. rewrite ?(unsigned_lit SHB) by (unfold SHB; clear; lia).
    assert (BDm : 0 <= Dm /\ Dm + 8 * Z.of_nat (bn_dmax bmT) <= 140737488355328) by (clear - Dm0 DmS SPT FBSP; lia).
    assert (BDr : 0 <= Dr /\ Dr + 8 * Z.of_nat (bn_dmax rb) <= 140737488355328) by (clear - Dr0 DrS SPT FBSP; lia).
    shl_limb ACDm ALDm BDm 0. chk0.

    hide_ors. ub. unhide.
    step.
    do 3 step. rewrite ?(unsigned_lit SHB) by (unfold SHB; clear; lia).
    shl_with ACCr ALr. chk0.
    step.
    destruct DrP as (DrP & Dr16).
    hide_ors. ub. unhide.
    do 3 step. rewrite ?(unsigned_lit SHB) by (unfold SHB; clear; lia).
    shl_limb ACDr ALDr BDr 0. chk0.

    assert (LG : length (gfin (bn_buf rb) (bn_buf bmT) j) = length (bn_buf rb)) by (apply W_gueron_arr.gfin_length; [rewrite LBr; exact HDM1| rewrite LBm; exact OKm2]).
    assert (LUr : Z.of_nat (length (wlimbs (gfin (bn_buf rb) (bn_buf bmT) j))) = Z.of_nat (bn_dmax rb)) by (rewrite wlimbs_len, LG, LBr; reflexivity).
    lazymatch goal with |- evt _ ?P _ => set (POSTF := P) end.
    assert (TAILF : forall m3 (x1' x5 x10 x11' x12' x13' x14' x15 x16 x17 y28 y29 y30 y31 : word),
              munch [(Dr, Dr + 8 * Z.of_nat j)] m2 m3 -> wmono bgbsegs m2 m3 -> mem_inv bgbsegs m3 ->
              u64arr bgbsegs m3 Dr (wlimbs (gfin (bn_buf rb) (bn_buf bmT) j)) -> stk bgbsegs m3 lo spa ->
              evt bgbsegs POSTF
                (MS (mkR x1' (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) x5 (Z_to_bv 64 SHB) (Z_to_bv 64 ar) sp (Z_to_bv 64 spa) x10 x11' x12' x13' x14' x15 x16 x17
                         (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 (shad arm)) x21 (Z_to_bv 64 f) (Z_to_bv 64 ac) (Z_to_bv 64 (Z.of_nat j)) x25 (Z_to_bv 64 arm) (Z_to_bv 64 (bits - 1)) y28 y29 y30 y31)
                    F1 (Z_to_bv 64 2858048) fc1 None m3 (seg_rom bgbsegs))).
    { intros m3 z1 z5 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 MUc WMc MIc UR3 STc.
      eapply (rw_cells_transport bgbsegs _ m2 m3) in BNr; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - SQR HDM1; lia | exact I]].
      assert (MU3 : munch [(ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax rb))] m2 m3).
      { eapply (munch_weaken [(Dr, Dr + 8 * Z.of_nat j)]); [| exact MUc]. unfold sub_fp. cbn [outside]. intros xx Hx. clear - Hx HDM1. lia. }
      clear MU WM Ur Um BNm FR2 ST2 MI2 ACDm ACDr ACCm MUc.
      do 3 step. rewrite ?(unsigned_lit SHB) by (unfold SHB; clear; lia). shl_with ACCr ALr. chk0.
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
      apply evt_done. subst POSTF. cbv beta. apply implA_ret.
      unfold GFQ, bst. exists m4, OW2, (used + MC). do 23 eexists. split; [reflexivity|]. cbn [fst snd].
      split; [exact ENV3|]. split; [exact LS3|].
      split; [eapply refs_stable_trans; [exact RS2| apply refs_stable_setbn] | clear; lia]. }

    assert (NTH0 : nth_error (wlimbs (bn_buf bmT)) (Z.to_nat 0) = Some (Z_to_bv 64 (nth 0 (bn_buf bmT) 0))).
    { change (Z.to_nat 0) with 0%nat. apply W_exp_montAF.nth_error_wlimbs. rewrite LBm. clear - OKm2 J1. unfold j in *. lia. }
    assert (Rx0 : 0 <= nth 0 (bn_buf bmT) 0 < 2 ^ 64).
    { assert (Hl : limb (nth 0 (bn_buf bmT) 0)) by (apply (proj1 (List.Forall_nth limb (bn_buf bmT)) OKm1); rewrite LBm; clear - OKm2 J1; unfold j in *; lia). unfold limb, BW in Hl. exact Hl. }
    let a := cur_mem_addr in pose proof (u64arr_read bgbsegs m2 Dm _ 0 _ a Um NTH0 ltac:(clear; lia) ltac:(addr_tac)) as RD.
    step. clear RD.
    step. rewrite ?(unsigned_lit (nth 0 (bn_buf bmT) 0)) by exact Rx0.
    rewrite (W_gueron_arr.g_to_bv_mod64 (0 + - nth 0 (bn_buf bmT) 0)).
    replace ((0 + - nth 0 (bn_buf bmT) 0) mod 18446744073709551616) with (negw (nth 0 (bn_buf bmT) 0)) by (unfold negw, BW; f_equal; clear; lia).
    set (v := negw (nth 0 (bn_buf bmT) 0)).
    assert (Ev : v = nth 0 (gfin (bn_buf rb) (bn_buf bmT) j) 0) by (subst v; rewrite W_gueron_arr.gfin_nth0 by (first [rewrite LBr; exact HDM1 | rewrite LBm; exact OKm2 | exact J1]); reflexivity).
    step.
    assert (IDXR : 0 <= Z.of_nat 0 < Z.of_nat (length (wlimbs (bn_buf rb)))) by (rewrite wlimbs_len, LBr; clear - HDr; lia).
    pose proof (u64arr_store_ok bgbsegs m2 Dr _ (Z.of_nat 0) (wa Dr) Ur IDXR ltac:(unfold wa; f_equal; clear; lia)) as SOKW.
    pose proof (u64arr_write bgbsegs m2 Dr _ (Z.of_nat 0) (Z_to_bv 64 v) Ur IDXR) as UR2.
    pose proof (u64arr_frame bgbsegs m2 Dm _ Dr (le8 (Z_to_bv 64 v)) Um ltac:(clear - Dr0; lia) ltac:(rewrite length_le8; clear - BDr HDr; lia)
                  ltac:(rewrite length_le8, wlimbs_len, LBm; clear - DJ HDr; lia)) as UM2.
    replace (wa (Dr + 8 * Z.of_nat 0)) with (wa Dr) in UR2 by (unfold wa; f_equal; clear; lia).
    pose proof (munch_refl [(Dr, Dr + 8 * Z.of_nat j)]%Z m2) as MUs. pose proof (wmono_refl bgbsegs m2) as WMs.
    pose proof ACCm as ACCm0. pose proof ACCr as ACCr0. pose proof ACDm as ACDm0. pose proof ACDr as ACDr0.
    apply hide_intro in ACCm0. apply hide_intro in ACCr0. apply hide_intro in ACDm0. apply hide_intro in ACDr0.
    pose proof BNr as BNr0. apply hide_intro in BNr0. pose proof MI2 as MI20. apply hide_intro in MI20. pose proof ST2 as ST20. apply hide_intro in ST20.
    clear Ur Um MU WM.

    step. store_done.
    rewrite Nat2Z.id, Ev in UR2. replace (wlimbs (bn_buf rb)) with (wlimbs (mixl 0 (gfin (bn_buf rb) (bn_buf bmT) j) (bn_buf rb))) in UR2 by (rewrite W_from_mont_loops.mixl_0; reflexivity).
    rewrite mixl_step in UR2 by (first [rewrite LG; reflexivity | rewrite LBr; clear - HDr; lia]).
    clear IDXR Ev. subst v.
    step.
    step. rewrite lts_signed by (clear - J512; lia).
    destruct (Z.ltb_spec (Z.of_nat j) 2) as [J2|J2].
    -
      assert (EJ : j = 1%nat) by (clear - J2 J1; lia).
      replace 1%nat with j in UR2 by (clear - EJ; lia). rewrite gfin_mixl in UR2 by (first [rewrite LBr; exact HDM1 | rewrite LBm; exact OKm2]).
      eapply TAILF; [exact MUs | exact WMs | exact MI2 | exact UR2 | exact ST2].
    - do 6 step.
      rewrite ?(unsigned_lit Dm), ?(unsigned_lit Dr), ?(unsigned_lit (Z.of_nat j)) by (first [clear - BDm; lia | clear - BDr; lia | clear - J512; lia]).
      rewrite (W_gueron_arr.g_lxor_ones64 Dm) by (clear - BDm; lia). rewrite (W_gueron_arr.g_lxor_ones64 Dr) by (clear - BDr; lia).
      rewrite Z.shiftl_mul_pow2 by (clear; lia). replace (Z.of_nat j * 2 ^ 3) with (8 * Z.of_nat j) by (clear; lia).
      change (Z_to_bv 64 8) with (Z_to_bv 64 (8 * Z.of_nat 1)).
      assert (ACM : acc bgbsegs m2 Dm (8 * Z.of_nat j)) by (eapply acc_sub; [exact ACDm | clear; lia | clear - OKm2; unfold bn_dmax in *; lia]).
      assert (ACR : acc bgbsegs m2 Dr (8 * Z.of_nat j)) by (eapply acc_sub; [exact ACDr | clear; lia | clear - HDM1; lia]).
      rewrite <- ESP in ST2.
      eapply (gueron_loopB) with (lo := lo) (m := m2) (RD := Dr) (MD := Dm) (R := bn_buf rb) (M := bn_buf bmT) (j := j) (K := (j - 1)%nat) (i := 1%nat);
        [ exact OKm1 | exact J1 | rewrite LBr; exact HDM1 | rewrite LBm; exact OKm2 | rewrite LBm, LBr; clear - DJ; lia
        | exact ACM | exact ACR | exact ALDm | exact ALDr | clear - BDm OKm2; unfold bn_dmax in *; lia | clear - BDr HDM1; lia
        | cbn [offshW]; unfold SHLO, SHHI; split; [clear - OFDr HDM1; lia | exact I]
        | | reflexivity | clear - J2; lia
        | split; [exact UR2|]; split; [exact UM2|]; split; [exact MI2|]; split; [exact MUs|]; split; [exact WMs| exact ST2] ].
      unfold GKONT. intros m3 y5 y12 y13 y17 MUc WMc MIc UR3 UM3 STc.
      rewrite ESP in STc.
      eapply TAILF; [exact MUc | exact WMc | exact MIc | exact UR3 | exact STc].
  Qed.

End Proofs.
End Body.
