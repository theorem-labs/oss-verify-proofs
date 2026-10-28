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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWordsCorrect BnModel BnTree BnInv BnBridge BgState BgInv BgLib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small W_small2 W_top.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require Import ExpKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require ValArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU2 Require Import PlaceTmod.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma buf2_cells_arr : forall m A (l0 l1 : Z),
  rw_cells bgusegs m A [C8 (Z_to_bv 64 l0); C8 (Z_to_bv 64 l1)] <-> u64arr bgusegs m A (wlimbs [l0; l1]).
Proof.
  intros m A l0 l1. rewrite <- (ValArr.rw_cells_CB_u64arr bgusegs m A (wlimbs [l0; l1]) 16) by reflexivity.
  split; intros H; (eapply bk_rw_cells_recast; [exact H| cbn; auto | cbn [cells_bytes cbytes wlimbs map u64s]; rewrite ?app_nil_r; reflexivity | reflexivity]).
Qed.

Section EnvT.
  Variables (LB : list block) (PL0 : placement) (EA : BnRep.err_addrs) (lo B SPv FB : Z).
  Variables (s0 : PState) (bs0 : bstate bptr) (OW0 : list block) (m0 : mem).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis LOFB : lo <= FB.
  Hypothesis FB40 : FB + 40 <= SPv.
  Hypothesis SPB : SPv <= B.
  Hypothesis B63 : B < 2^63.
  Hypothesis SPR : SPv < 2^64.
  Hypothesis FROK0 : frames_ok PL0 SPv B.
  Hypothesis FRESH : pl_bn PL0 RTmod = None.

  Local Notation PL := (pl_place_tmod PL0 (FB + 16) FB).

  Lemma FBSPT : FB <= SPv. Proof using FB40. clear - FB40. lia. Qed.

  Lemma FROKT : frames_ok PL FB B.
  Proof using CEIL LOFB FB40 SPB FROK0.
    eapply (frames_ok_place_tmod PL0 (FB + 16) FB SPv B FB FROK0); clear - CEIL LOFB FB40 SPB; lia.
  Qed.

  Lemma lx_unplaceT : forall st L SP' m m' mh, RHEAP st (L ++ LB) mh -> SP' <= SPv -> lx_pres LB SP' (XW PL) m m' -> lx_pres LB SPv (XW PL0) m m'.
  Proof using CEIL GLO LOFB FB40.
    intros st L SP' m m' mh HEAP HS H a Ha [Hx Hc]. apply H; [exact Ha|]. split.
    - intros Hx'. apply xw_place_tmod in Hx'. destruct Hx' as [Hx'|Hr]; [exact (Hx Hx')|].
      destruct Hc as [Hc|[(b & Hb & Hr')|Hc]].
      + clear - Hc Hr FB40. lia.
      + pose proof (LH_block_range _ _ _ b HEAP ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & BC & _).
        clear - BC Hr Hr' CEIL LOFB. lia.
      + unfold GLOBALS_TOP in GLO. clear - Hc Hr GLO LOFB. lia.
    - destruct Hc as [Hc|[Hc|Hc]]; [left; clear - Hc HS; lia| right; left; exact Hc| right; right; exact Hc].
  Qed.

  Lemma frame_clientT : forall x, FB + 40 <= x < SPv -> lx_client LB FB (XW PL) x.
  Proof using CEIL GLO LOFB FROK0.
    intros x Hx. split; [|left; lia]. unfold XW. rewrite rin_ivs_app. intros [H|H].
    - revert H. unfold LIBW_bgr, BnRep.LIBW_bn, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. unfold GLOBALS_TOP in GLO. clear - Hx GLO LOFB. lia.
    - apply rin_ivs_In in H. destruct H as (iv & Hin & Hiv). apply pl_frames_place_tmod_In in Hin.
      destruct Hin as [->|[->|Hin]]; cbn [fst snd] in Hiv; try (clear - Hiv Hx; lia).
      destruct (proj1 FROK0 iv Hin) as [P1 P2]. clear - P1 Hiv Hx. lia.
  Qed.

  Lemma kenvT_place : forall fr2 st bs m OW (tm : BN) (l0 l1 : Z),
    kenv LB PL0 lo B SPv FB s0 bs0 OW0 m0 ([C8 (Z_to_bv 64 l0); C8 (Z_to_bv 64 l1)] ++ bn_cells FB tm ++ fr2) st bs m OW ->
    lib_state bs m OW PL0 EA -> 0 < FB -> FB mod 8 = 0 ->
    bn_d tm = None -> bn_buf tm = [l0; l1] -> bg_ok tm ->
    kenv LB PL lo B FB FB st (setbn RTmod tm bs) OW m [] st (setbn RTmod tm bs) m OW
    /\ lib_state (setbn RTmod tm bs) m OW PL EA
    /\ rw_cells bgusegs m (FB + 40) fr2 /\ Z.of_nat (cells_size fr2) = SPv - (FB + 40).
  Proof using CEIL GLO LOFB FB40 SPB FROK0 FRESH.
    intros fr2 st bs m OW tm l0 l1 (HEAP & AUX & ST & ERR & MI & LXP & FA & SO & RS & FR & FSZ) LS FB0 FB8 ED EB OK.
    apply bk_rw_cells_app in FR. destruct FR as [FBUF FR].
    change (Z.of_nat (cells_size [C8 (Z_to_bv 64 l0); C8 (Z_to_bv 64 l1)])) with 16 in FR.
    apply bk_rw_cells_app in FR. destruct FR as [FSTR F2].
    change (Z.of_nat (cells_size (bn_cells FB tm))) with 24 in F2. replace (FB + 16 + 24) with (FB + 40) in F2 by (clear; lia).
    assert (Z2 : Z.of_nat (cells_size fr2) = SPv - (FB + 40)).
    { rewrite !cells_size_app in FSZ. change (cells_size [C8 (Z_to_bv 64 l0); C8 (Z_to_bv 64 l1)]) with 16%nat in FSZ.
      change (cells_size (bn_cells FB tm)) with 24%nat in FSZ. clear - FSZ. lia. }
    assert (FNIL : rw_cells bgusegs m FB []).
    { change [C8 (Z_to_bv 64 l0); C8 (Z_to_bv 64 l1)] with ([] ++ [C8 (Z_to_bv 64 l0); C8 (Z_to_bv 64 l1)]) in FBUF.
      apply bk_rw_cells_app in FBUF. exact (proj1 FBUF). }
    split; [|split; [|split; [exact F2| exact Z2]]].
    - unfold kenv. do 5 (split; [assumption|]). split; [apply lx_pres_refl|]. split; [reflexivity|]. split; [reflexivity|].
      split; [apply refs_stable_refl|]. split; [exact FNIL| cbn; clear; lia].
    - unfold lib_state. eapply (lib_state_place_tmod false [] bs m OW PL0 EA (FB + 16) FB SPv B tm);
        [exact LS| exact FROK0| exact FRESH| clear - FB0; lia| exact FB0| clear - FB40; lia| clear - FB40; lia| right; clear; lia
        | clear - FB8; Z.div_mod_to_equations; lia| exact FB8| exact ED| rewrite EB; reflexivity| exact OK| exact FSTR|].
      rewrite EB. apply buf2_cells_arr. exact FBUF.
  Qed.

  Lemma kenvT_unplace : forall fr fr2 st1 bs1 bs1' m1 OW1 st2 bs2 m2 OW2,
    kenv LB PL0 lo B SPv FB s0 bs0 OW0 m0 fr st1 bs1 m1 OW1 -> refs_stable bs1 OW1 bs1' OW1 ->
    rw_cells bgusegs m1 (FB + 40) fr2 -> Z.of_nat (cells_size fr2) = SPv - (FB + 40) ->
    kenv LB PL lo B FB FB st1 bs1' OW1 m1 [] st2 bs2 m2 OW2 -> lib_state bs2 m2 OW2 PL EA ->
    pl_wf PL0 -> bn_d (getbn RTmod bs2) = None ->
    kenv LB PL0 lo B SPv FB s0 bs0 OW0 m0 ((CB 16 (u64s (wlimbs (bn_buf (getbn RTmod bs2)))) :: bn_cells FB (getbn RTmod bs2)) ++ fr2)
         st2 (setbn RTmod (bn_nil 0) bs2) m2 OW2
    /\ lib_state (setbn RTmod (bn_nil 0) bs2) m2 OW2 PL0 EA.
  Proof using CEIL GLO LOFB FB40 FROK0 FRESH.
    intros fr fr2 st1 bs1 bs1' m1 OW1 st2 bs2 m2 OW2 (HEAP1 & _ & _ & _ & _ & LXP1 & FA1 & SO1 & RS1 & _ & _) RSP F2 Z2
           (HEAP2 & AUX2 & ST2 & ERR2 & MI2 & LXP2 & FA2 & SO2 & RS2 & _ & _) LS2 PWF0 ND.

    pose proof LS2 as (_ & _ & _ & (_ & _ & _ & (M1 & _))).
    destruct (M1 RTmod (PFrameBuf (FB + 16) FB) ltac:(unfold RTmod, NFIX; lia) (pl_of_place_tmod_same PL0 (FB + 16) FB)) as [_ HR].
    destruct HR as [[]|(D & SC & ARR)]. cbn [place_addr] in SC. rewrite pl_of_place_tmod_same in SC, ARR.
    unfold struct_cells in SC. unfold bn_arr in ARR. rewrite ND in ARR. destruct ARR as (-> & U & EL).
    apply limbarr_CB in U. rewrite EL in U.
    set (b := getbn RTmod bs2) in *.
    change (8 * 2)%nat with 16%nat in U.
    split.
    - apply kenv_setbn. unfold kenv.
      split; [exact HEAP2|]. split; [exact AUX2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact MI2|].
      split. { eapply lx_pres_trans; [exact LXP1|]. eapply (lx_unplaceT st2 OW2 FB _ _ m2); [exact HEAP2| exact FBSPT| exact LXP2]. }
      split; [congruence|]. split; [congruence|].
      split. { eapply refs_stable_trans; [exact RS1|]. eapply refs_stable_trans; [exact RSP| exact RS2]. }
      split.
      + change ((CB 16 (u64s (wlimbs (bn_buf b))) :: bn_cells FB b) ++ fr2) with ([CB 16 (u64s (wlimbs (bn_buf b)))] ++ bn_cells FB b ++ fr2).
        apply bk_rw_cells_app. split; [exact U|].
        change (Z.of_nat (cells_size [CB 16 (u64s (wlimbs (bn_buf b)))])) with 16.
        apply bk_rw_cells_app. split; [exact SC|].
        change (Z.of_nat (cells_size (bn_cells FB b))) with 24. replace (FB + 16 + 24) with (FB + 40) by (clear; lia).
        eapply rw_cells_agree; [apply agree_of_lx_pres; exact LXP2 | exact F2 |]. intros a Ha. apply frame_clientT. clear - Ha Z2. lia.
      + rewrite cells_size_app. change (cells_size (CB 16 (u64s (wlimbs (bn_buf b))) :: bn_cells FB b)) with 40%nat. clear - Z2 FB40. lia.
    - unfold lib_state. eapply (lib_state_unplace_tmod false [] [] bs2 m2 OW2 PL0 EA (FB + 16) FB); [exact LS2| exact PWF0| exact FRESH| exact ND| intros r []].
  Qed.

End EnvT.
End WithCeiling0.
