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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small W_small2 W_top.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require Import ExpKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Section Env.

  Variables (LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B SPv FB : Z).
  Variables (s0 : PState) (bs0 : bstate bptr) (OW0 : list block) (m0 : mem).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis LOFB : lo <= FB.
  Hypothesis FBSP : FB <= SPv.
  Hypothesis SPB : SPv <= B.
  Hypothesis B63 : B < 2^63.
  Hypothesis SPR : SPv < 2^64.
  Hypothesis FROK : frames_ok PL SPv B.

  Local Notation kenv := (kenv LB PL lo B SPv FB s0 bs0 OW0 m0).
  Local Notation dm b := (Z.of_nat (bn_dmax b)).

  Lemma kenv_read : forall fr st bs m OW n an,
    kenv fr st bs m OW -> lib_state bs m OW PL EA -> ref_at bs OW PL n an -> wref PL n -> (0 < bn_dmax (getbn n bs))%nat ->
    exists Dn pn,
      bn_d (getbn n bs) = Some pn /\ In (pn, Dn, 8 * dm (getbn n bs)) OW
      /\ rw_cells bgusegs m an (bn_cells Dn (getbn n bs)) /\ u64arr bgusegs m Dn (wlimbs (bn_buf (getbn n bs))) /\ bg_ok (getbn n bs)
      /\ (0 < an /\ (an + 24 <= lo \/ SPv <= an) /\ an + 24 < 2^63 /\ (an + 24 <= 0x10000 \/ 0x353000 <= an))
      /\ (0 < Dn /\ Dn + 8 * dm (getbn n bs) <= lo /\ (Dn + 8 * dm (getbn n bs) <= 0x10000 \/ 0x353000 <= Dn))
      /\ (forall r a, ref_at bs OW PL r a -> a + 24 <= Dn \/ Dn + 8 * dm (getbn n bs) <= a)
      /\ (forall r p D, r <> n -> vref r bs -> bn_d (getbn r bs) = Some p -> In (p, D, 8 * dm (getbn r bs)) OW ->
            D + 8 * dm (getbn r bs) <= Dn \/ Dn + 8 * dm (getbn n bs) <= D).
  Proof using CEIL FROK.
    intros fr st bs m OW n an ENV LS HA WR HD. pose proof (proj1 WR) as NRO.
    pose proof ENV as (HEAP & _). pose proof (RH_nodup_l _ _ _ _ HEAP) as ND. pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    destruct (lib_state_open [] bs m OW PL EA n an LS ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & OK & _).
    destruct (bn_arr_facts st OW LB m HEAP bs PL EA _ _ PARTS FROK n D HV NRO ARR) as (U & LEN & D0 & DC & DI & SEP).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HA NRO) as (A0 & AC & AI).
    assert (HDp : exists pn, bn_d (getbn n bs) = Some pn /\ In (pn, D, 8 * dm (getbn n bs)) OW).
    { pose proof ARR as ARR'. unfold bn_arr in ARR'. destruct (bn_d (getbn n bs)) as [pn|] eqn:Ed; [exists pn; split; [reflexivity| exact (proj1 ARR')]|].
      exfalso. destruct (bn_arr_null PL n m OW D (getbn n bs) PWF WR Ed ARR) as [_ E]. unfold bn_dmax in HD. rewrite E in HD. cbn in HD. lia. }
    destruct HDp as (pn & Ed & Hin).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP Hin) as (B0 & _ & _ & BC & BI).
    exists D, pn. split; [exact Ed|]. split; [exact Hin|]. split; [exact BN|]. split; [exact U|]. split; [exact OK|].
    split. { split; [exact A0|]. split; [clear - AC CEIL; lia|]. split; [clear - AC; lia| exact AI]. }
    split. { split; [exact B0|]. split; [clear - BC CEIL; lia|]. clear - BI HD. lia. }
    split; [exact SEP|].
    intros r p Dr NE HVr Edr Hinr.
    exact (limbs_limbs_disj st OW LB m HEAP bs PL EA PARTS r n p Dr _ pn D _ NE HVr HV Edr Ed Hinr Hin).
  Qed.

  Definition fpw1 (K a D : Z) (d : nat) : list (Z * Z) := [(FB - K, FB); (a, a + 24); (D, D + 8 * Z.of_nat d)].
  Definition fpw2 (K a1 D1 : Z) (d1 : nat) (a2 D2 : Z) (d2 : nat) : list (Z * Z) :=
    [(FB - K, FB); (a1, a1 + 24); (D1, D1 + 8 * Z.of_nat d1); (a2, a2 + 24); (D2, D2 + 8 * Z.of_nat d2)].

  Lemma kenv_hole1 : forall fr st bs m OW r a D p K,
    kenv fr st bs m OW -> lib_state bs m OW PL EA -> ref_at bs OW PL r a -> r <> ROne ->
    bn_d (getbn r bs) = Some p -> In (p, D, 8 * dm (getbn r bs)) OW -> 0 <= K -> lo <= FB - K ->
    (forall m', munch (fpw1 K a D (bn_dmax (getbn r bs))) m m' -> wmono bgusegs m m' ->
        RHEAP st (OW ++ LB) m' /\ lib_state_hc false [r] bs m' OW PL EA)
    /\ (forall m' b' (errv' : word),
        munch (fpw1 K a D (bn_dmax (getbn r bs))) m m' -> wmono bgusegs m m' ->
        rw_cells bgusegs m' a (bn_cells D b') -> u64arr bgusegs m' D (wlimbs (bn_buf b')) ->
        bn_d b' = bn_d (getbn r bs) -> length (bn_buf b') = length (bn_buf (getbn r bs)) -> bg_ok b' ->
        stk bgusegs m' lo FB -> mem_inv bgusegs m' -> rw_cells bgusegs m' FB fr -> rw_cells bgusegs m' LX_ERRNO [C4 errv'] ->
        kenv fr st (setbn r b' bs) m' OW /\ lib_state (setbn r b' bs) m' OW PL EA).
  Proof using CEIL GLO LOFB FBSP SPB B63 SPR FROK.
    intros fr st bs m OW r a D p K ENV LS HA NRO Ed Hin K0 LOK.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & FSZ).
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    destruct (lib_state_open [] bs m OW PL EA r a LS ND HA ltac:(intros []) NRO) as (_ & _ & LSH).
    set (b := getbn r bs) in *.
    assert (WOK : Forall (w_okc OW LB bs PL EA SPv false [r]) (fpw1 K a D (bn_dmax b))).
    { unfold fpw1. constructor; [apply w_stack; cbn [fst snd]; lia|].
      constructor; [eapply (w_struct OW LB bs PL EA SPv false [r] _ r a); [left; reflexivity| exact HA| exact NRO| cbn; lia| cbn; lia]|].
      constructor; [| constructor].
      eapply (w_limbs OW LB bs PL EA SPv false [r] _ r p D); [left; reflexivity| exact HV| exact Ed| exact Hin| cbn [fst snd]; lia| cbn [fst snd]; fold b; lia]. }
    assert (HWL : Forall (w_lib bs OW PL lo SPv) (fpw1 K a D (bn_dmax b))).
    { unfold fpw1. constructor; [left; cbn [fst snd]; lia|].
      constructor; [right; right; exists r, a; cbn [fst snd]; split; [exact HA|]; split; [exact NRO| lia]|].
      constructor; [| constructor]. right; left. exists (p, D, 8 * dm b). cbn. split; [exact Hin| lia]. }
    split.
    - intros m' MU WM. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)|].
      exact (lib_state_frame st LB SPv B [r] bs m m' OW PL EA _ HEAP LSH MU WM FROK WOK).
    - intros m' b' errv' MU WM BN' U' Ed' EL' OK' ST' MI' FR' ERR'.
      assert (EDM : bn_dmax b' = bn_dmax b) by (unfold bn_dmax; exact EL').
      assert (LS' : lib_state (setbn r b' bs) m' OW PL EA).
      { unfold lib_state. eapply (lib_state_close [] bs m' OW PL EA r a); [| exact ND | exact HA | exact NRO | | exact OK' |].
        - exact (lib_state_frame st LB SPv B [r] bs m m' OW PL EA _ HEAP LSH MU WM FROK WOK).
        - exists D. split; [exact BN'|]. unfold bn_arr. rewrite Ed', Ed, EDM. split; [exact Hin| exact U'].
        - apply ids_ok_setbn_same; [exact (proj1 (proj2 (proj2 PARTS))) | exact HV |]. unfold bn_blocks. fold b. rewrite Ed', EDM. reflexivity. }
      split; [| exact LS'].
      apply kenv_setbn.
      eapply (kenv_silent LB PL EA lo B SPv FB s0 bs0 OW0 m0 CEIL GLO LOFB FBSP SPB FROK fr fr st bs m m' OW _ errv');
        [exact ENV | exact PARTS | exact MU | exact WM | exact HWL | exact ST' | exact ERR' | exact MI' | exact FR' | exact FSZ].
  Qed.

  Lemma kenv_hole2 : forall fr st bs m OW r1 a1 D1 p1 r2 a2 D2 p2 K,
    kenv fr st bs m OW -> lib_state bs m OW PL EA -> r1 <> r2 ->
    ref_at bs OW PL r1 a1 -> r1 <> ROne -> bn_d (getbn r1 bs) = Some p1 -> In (p1, D1, 8 * dm (getbn r1 bs)) OW ->
    ref_at bs OW PL r2 a2 -> r2 <> ROne -> bn_d (getbn r2 bs) = Some p2 -> In (p2, D2, 8 * dm (getbn r2 bs)) OW ->
    0 <= K -> lo <= FB - K ->
    (forall m', munch (fpw2 K a1 D1 (bn_dmax (getbn r1 bs)) a2 D2 (bn_dmax (getbn r2 bs))) m m' -> wmono bgusegs m m' ->
        RHEAP st (OW ++ LB) m' /\ lib_state_hc false [r1; r2] bs m' OW PL EA)
    /\ (forall m' b1' b2' (errv' : word),
        munch (fpw2 K a1 D1 (bn_dmax (getbn r1 bs)) a2 D2 (bn_dmax (getbn r2 bs))) m m' -> wmono bgusegs m m' ->
        rw_cells bgusegs m' a1 (bn_cells D1 b1') -> u64arr bgusegs m' D1 (wlimbs (bn_buf b1')) ->
        bn_d b1' = bn_d (getbn r1 bs) -> length (bn_buf b1') = length (bn_buf (getbn r1 bs)) -> bg_ok b1' ->
        rw_cells bgusegs m' a2 (bn_cells D2 b2') -> u64arr bgusegs m' D2 (wlimbs (bn_buf b2')) ->
        bn_d b2' = bn_d (getbn r2 bs) -> length (bn_buf b2') = length (bn_buf (getbn r2 bs)) -> bg_ok b2' ->
        stk bgusegs m' lo FB -> mem_inv bgusegs m' -> rw_cells bgusegs m' FB fr -> rw_cells bgusegs m' LX_ERRNO [C4 errv'] ->
        kenv fr st (setbn r2 b2' (setbn r1 b1' bs)) m' OW /\ lib_state (setbn r2 b2' (setbn r1 b1' bs)) m' OW PL EA).
  Proof using CEIL GLO LOFB FBSP SPB B63 SPR FROK.
    intros fr st bs m OW r1 a1 D1 p1 r2 a2 D2 p2 K ENV LS NE12 HA1 NRO1 Ed1 Hin1 HA2 NRO2 Ed2 Hin2 K0 LOK.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & FSZ).
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA1) as HV1. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA2) as HV2.
    destruct (lib_state_open [] bs m OW PL EA r2 a2 LS ND HA2 ltac:(intros []) NRO2) as (_ & _ & LSH2).
    destruct (lib_state_open [r2] bs m OW PL EA r1 a1 LSH2 ND HA1 ltac:(intros [E|[]]; apply NE12; symmetry; exact E) NRO1) as (_ & _ & LSH).
    set (b1 := getbn r1 bs) in *. set (b2 := getbn r2 bs) in *.
    assert (WOK : Forall (w_okc OW LB bs PL EA SPv false [r1; r2]) (fpw2 K a1 D1 (bn_dmax b1) a2 D2 (bn_dmax b2))).
    { unfold fpw2. constructor; [apply w_stack; cbn [fst snd]; lia|].
      constructor; [eapply (w_struct OW LB bs PL EA SPv false [r1; r2] _ r1 a1); [left; reflexivity| exact HA1| exact NRO1| cbn; lia| cbn; lia]|].
      constructor; [eapply (w_limbs OW LB bs PL EA SPv false [r1; r2] _ r1 p1 D1); [left; reflexivity| exact HV1| exact Ed1| exact Hin1| cbn [fst snd]; lia| cbn [fst snd]; fold b1; lia]|].
      constructor; [eapply (w_struct OW LB bs PL EA SPv false [r1; r2] _ r2 a2); [right; left; reflexivity| exact HA2| exact NRO2| cbn; lia| cbn; lia]|].
      constructor; [| constructor].
      eapply (w_limbs OW LB bs PL EA SPv false [r1; r2] _ r2 p2 D2); [right; left; reflexivity| exact HV2| exact Ed2| exact Hin2| cbn [fst snd]; lia| cbn [fst snd]; fold b2; lia]. }
    assert (HWL : Forall (w_lib bs OW PL lo SPv) (fpw2 K a1 D1 (bn_dmax b1) a2 D2 (bn_dmax b2))).
    { unfold fpw2. constructor; [left; cbn [fst snd]; lia|].
      constructor; [right; right; exists r1, a1; cbn [fst snd]; split; [exact HA1|]; split; [exact NRO1| lia]|].
      constructor; [right; left; exists (p1, D1, 8 * dm b1); cbn; split; [exact Hin1| lia]|].
      constructor; [right; right; exists r2, a2; cbn [fst snd]; split; [exact HA2|]; split; [exact NRO2| lia]|].
      constructor; [| constructor]. right; left. exists (p2, D2, 8 * dm b2). cbn. split; [exact Hin2| lia]. }
    split.
    - intros m' MU WM. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)|].
      exact (lib_state_frame st LB SPv B [r1; r2] bs m m' OW PL EA _ HEAP LSH MU WM FROK WOK).
    - intros m' b1' b2' errv' MU WM BN1 U1 Ed1' EL1 OK1 BN2 U2 Ed2' EL2 OK2 ST' MI' FR' ERR'.
      assert (EDM1 : bn_dmax b1' = bn_dmax b1) by (unfold bn_dmax; exact EL1).
      assert (EDM2 : bn_dmax b2' = bn_dmax b2) by (unfold bn_dmax; exact EL2).
      pose proof (lib_state_frame st LB SPv B [r1; r2] bs m m' OW PL EA _ HEAP LSH MU WM FROK WOK) as LSH'.
      assert (IDS1 : ids_ok (setbn r1 b1' bs) PL EA).
      { apply ids_ok_setbn_same; [exact (proj1 (proj2 (proj2 PARTS))) | exact HV1 |]. unfold bn_blocks. fold b1. rewrite Ed1', EDM1. reflexivity. }
      assert (LS1 : lib_state_hc false [r2] (setbn r1 b1' bs) m' OW PL EA).
      { eapply (lib_state_close [r2] bs m' OW PL EA r1 a1); [exact LSH'| exact ND | exact HA1 | exact NRO1 | | exact OK1 | exact IDS1].
        exists D1. split; [exact BN1|]. unfold bn_arr. rewrite Ed1', Ed1, EDM1. split; [exact Hin1| exact U1]. }
      assert (HA2' : ref_at (setbn r1 b1' bs) OW PL r2 a2) by (apply ref_at_setbn; exact HA2).
      assert (HV2' : vref r2 (setbn r1 b1' bs)) by (eapply ref_at_valid; [exact LS1| exact HA2']).
      assert (G2 : getbn r2 (setbn r1 b1' bs) = b2) by (apply getbn_setbn_other; exact NE12).
      assert (LS' : lib_state (setbn r2 b2' (setbn r1 b1' bs)) m' OW PL EA).
      { unfold lib_state. eapply (lib_state_close [] (setbn r1 b1' bs) m' OW PL EA r2 a2); [exact LS1| exact ND | exact HA2' | exact NRO2 | | exact OK2 |].
        - exists D2. split; [exact BN2|]. unfold bn_arr. rewrite Ed2', Ed2, EDM2. split; [exact Hin2| exact U2].
        - apply ids_ok_setbn_same; [exact IDS1 | exact HV2' |]. rewrite G2. unfold bn_blocks. rewrite Ed2', EDM2. reflexivity. }
      split; [| exact LS'].
      apply kenv_setbn. apply kenv_setbn.
      eapply (kenv_silent LB PL EA lo B SPv FB s0 bs0 OW0 m0 CEIL GLO LOFB FBSP SPB FROK fr fr st bs m m' OW _ errv');
        [exact ENV | exact PARTS | exact MU | exact WM | exact HWL | exact ST' | exact ERR' | exact MI' | exact FR' | exact FSZ].
  Qed.

End Env.
End WithCeiling0.
