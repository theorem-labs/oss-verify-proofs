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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnBridge.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnArith.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small W_small2 W_top.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep BnLeaves.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BgState BgInv BgLib BgArith.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import BgLeaves BnCall BnRKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Section Calls.
  Variables (LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B SPv FB : Z).
  Variables (s0 : PState) (bs0 : bstate bptr) (OW0 : list block) (m0 : mem).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis LOFB : lo <= FB - 16.
  Hypothesis FBSP : FB <= SPv.
  Hypothesis SPB : SPv <= B.
  Hypothesis SPR : SPv < 2^64.
  Hypothesis FROK : frames_ok PL SPv B.

  Lemma ESPc : bv_unsigned (Z_to_bv 64 FB) = FB.
  Proof using CEIL LOFB FBSP SPR. apply unsigned_lit. clear - CEIL LOFB FBSP SPR. lia. Qed.

  Lemma cenv_stack16 : forall fr st bs m m' OW,
    cenv LB PL lo B SPv FB s0 bs0 OW0 m0 fr st bs m OW -> lib_state bs m OW PL EA ->
    munch [(FB - 16, FB)]%Z m m' -> wmono bgusegs m m' -> mem_inv bgusegs m' -> stk bgusegs m' lo FB ->
    cenv LB PL lo B SPv FB s0 bs0 OW0 m0 fr st bs m' OW /\ lib_state bs m' OW PL EA.
  Proof using CEIL GLO LOFB FBSP SPB SPR FROK.
    intros fr st bs m m' OW ENV LS MU WM MI' ST'.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & FSZ).
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR. pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'.
    eapply (rw_cells_transport bgusegs _ m m') in FR; [| exact MU | exact WM | cbn [disjoint_from]; split; [right; clear; lia| exact I]].
    eapply (rw_cells_transport bgusegs _ m m') in ERR; [| exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; split; [left; clear - GLO' LOFB; lia| exact I]].
    assert (WOK : Forall (w_okc OW LB bs PL EA SPv false []) [(FB - 16, FB)]) by (constructor; [apply w_stack; cbn [fst snd]; clear - CEIL LOFB FBSP; lia| constructor]).
    assert (HWL : Forall (w_lib bs OW PL lo SPv) [(FB - 16, FB)]) by (constructor; [left; cbn [fst snd]; clear - LOFB FBSP; lia| constructor]).
    split.
    - eapply (cenv_silent LB PL EA lo B SPv FB s0 bs0 OW0 m0 CEIL GLO ltac:(clear - LOFB; lia) FBSP SPB FROK fr fr st bs m m' OW _ errv);
        [exact ENV | exact LS | exact MU | exact WM | exact HWL | exact ST' | unfold LX_ERRNO, RATP; exact ERR | exact MI' | exact FR | exact FSZ].
    - exact (lib_state_frame st LB SPv B [] bs m m' OW PL EA _ HEAP LS MU WM FROK WOK).
  Qed.

  Lemma is_zero_call : forall (POST : machine_state -> Prop) (fr : list cell) (st : PState) (bs : bstate bptr) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    cenv LB PL lo B SPv FB s0 bs0 OW0 m0 fr st bs m OW -> lib_state bs m OW PL EA -> ref_at bs OW PL r ar -> r <> ROne ->
    (forall m' y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        cenv LB PL lo B SPv FB s0 bs0 OW0 m0 fr st bs m' OW -> lib_state bs m' OW PL EA ->
        evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) y0 y1 y2 x8 x9 (Z_to_bv 64 (Z.b2z (bn_top (getbn r bs) =? 0)%nat))
                                y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bgusegs))) ->
    evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_IS_ZERO) fc None m (seg_rom bgusegs)).
  Proof using CEIL GLO LOFB FBSP SPB SPR FROK.
    intros until fc. intros ENV LS HA NRO K.
    pose proof ENV as (HEAP & AUX & ST & _ & MI & _).
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    destruct (lib_state_open [] bs m OW PL EA r ar LS ND HA ltac:(intros []) NRO) as ((D & BN & _) & (_ & OK2 & OK3 & _) & _).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HA NRO) as (A0 & AC & _).
    pose proof ESPc as ESP. unfold BG_DMAX in OK3.
    eapply evt_cut.
    { eapply BN_is_zero_spec with (lo := lo) (A := ar) (D := D) (b := getbn r bs);
        [exact BN | exact (ref_at_ualign st OW LB m bs PL EA r ar HEAP PARTS HA NRO) | clear - OK2 OK3; lia | rewrite ESP; exact ST | rewrite ESP; clear - LOFB; lia | exact MI | rewrite ESP; clear - AC CEIL LOFB FBSP; lia | reflexivity]. }
    intros ms' PO. unfold bn_small_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms' y3. rewrite ESP in *.
    destruct (cenv_stack16 fr st bs m m' OW ENV LS MUc WMc MIc STc) as (ENV' & LS').
    eapply K; [exact ENV' | exact LS'].
  Qed.

  Lemma set_neg_call : forall (POST : machine_state -> Prop) (fr : list cell) (st : PState) (bs : bstate bptr) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    cenv LB PL lo B SPv FB s0 bs0 OW0 m0 fr st bs m OW -> lib_state bs m OW PL EA -> ref_at bs OW PL r ar -> wref PL r ->
    (forall m' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        let bs' := setbn r (bn_with_neg (getbn r bs) (negb (bv_unsigned a1 =? 0) && negb (bn_top (getbn r bs) =? 0)%nat)) bs in
        cenv LB PL lo B SPv FB s0 bs0 OW0 m0 fr st bs' m' OW -> lib_state bs' m' OW PL EA ->
        evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) y0 y1 y2 x8 x9 y3 y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bgusegs))) ->
    evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 0xff4b8) fc None m (seg_rom bgusegs)).
  Proof using CEIL GLO LOFB FBSP SPB SPR FROK.
    intros until fc. intros ENV LS HA WR K.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & FSZ).
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (proj1 WR) as NRO.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    destruct (lib_state_open [] bs m OW PL EA r ar LS ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & (OK1 & OK2 & OK3 & OK4) & LSH).
    destruct (bn_arr_facts st OW LB m HEAP bs PL EA _ _ PARTS FROK r D HV NRO ARR) as (U & LEN & D0 & DC & DI & SEP).
    pose proof (SEP r ar HA) as SEPr. clear SEP.
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HA NRO) as (A0 & AC & AI).
    set (b := getbn r bs) in *.
    pose proof ESPc as ESP.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR. unfold BG_DMAX in OK3. pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'.
    eapply evt_cut.
    { eapply BN_set_negative_spec with (lo := lo) (A := ar) (D := D) (b := b);
        [exact BN | exact (ref_at_ualign st OW LB m bs PL EA r ar HEAP PARTS HA NRO) | clear - OK2 OK3; lia | rewrite ESP; exact ST | rewrite ESP; clear - LOFB; lia | exact MI | rewrite ESP; clear - AC CEIL LOFB FBSP; lia | reflexivity]. }
    intros ms' PO. unfold bn_small_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms'. rewrite ESP in *.
    set (b' := bn_with_neg b (negb (bv_unsigned a1 =? 0) && negb (bn_top b =? 0)%nat)) in *.
    assert (U' : u64arr bgusegs m' D (wlimbs (bn_buf b))).
    { eapply u64arr_transport; [exact U | exact MUc | exact WMc |]. cbn [disjoint_from]. rewrite wlimbs_len. fold (bn_dmax b).
      split; [clear - DC CEIL LOFB FBSP; lia|]. split; [clear - SEPr; lia| exact I]. }
    eapply (rw_cells_transport bgusegs _ m m') in FR; [| exact MUc | exact WMc | cbn [disjoint_from]; rewrite FSZ; split; [right; clear; lia|]; split; [clear - AC CEIL LOFB FBSP; lia| exact I]].
    eapply (rw_cells_transport bgusegs _ m m') in ERR; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; split; [left; clear - GLO' LOFB; lia|]; split; [clear - AI A0; lia| exact I]].
    assert (WOK : Forall (w_okc OW LB bs PL EA SPv false [r]) [(FB - 16, FB); (ar, ar + 24)]).
    { constructor; [apply w_stack; cbn [fst snd]; clear - CEIL LOFB FBSP; lia|].
      constructor; [eapply (w_struct OW LB bs PL EA SPv false [r] _ r ar); [left; reflexivity| exact HA| exact NRO| cbn; lia| cbn; lia]| constructor]. }
    assert (HWL : Forall (w_lib bs OW PL lo SPv) [(FB - 16, FB); (ar, ar + 24)]).
    { constructor; [left; cbn [fst snd]; clear - LOFB FBSP; lia|]. constructor; [right; right; exists r, ar; cbn [fst snd]; split; [exact HA|]; split; [exact NRO| clear; lia] | constructor]. }
    assert (LS' : lib_state (setbn r b' bs) m' OW PL EA).
    { unfold lib_state. eapply (lib_state_close [] bs m' OW PL EA r ar); [| exact ND | exact HA | exact NRO | | |].
      - exact (lib_state_frame st LB SPv B [r] bs m m' OW PL EA _ HEAP LSH MUc WMc FROK WOK).
      - exists D. split; [exact RES|].
        assert (ARR' : bn_arr m' OW (pl_of PL r) D b) by (eapply bn_arr_of_u64arr; [exact ARR| exact U']).
        unfold bn_arr in ARR' |- *. unfold b', bn_with_neg, bn_dmax in *. cbn [bn_d bn_buf]. exact ARR'.
      - unfold bg_ok, b', bn_with_neg, bn_dmax, BG_DMAX in *. cbn [bn_buf bn_top bn_flags].
        split; [exact OK1|]. split; [exact OK2|]. split; [exact OK3| exact OK4].
      - apply ids_ok_setbn_same; [exact (proj1 (proj2 (proj2 PARTS))) | exact HV | reflexivity]. }
    eapply K; [| exact LS'].
    apply cenv_setbn.
    eapply (cenv_silent LB PL EA lo B SPv FB s0 bs0 OW0 m0 CEIL GLO ltac:(clear - LOFB; lia) FBSP SPB FROK fr fr st bs m m' OW _ errv);
      [exact ENV | exact LS | exact MUc | exact WMc | exact HWL | exact STc | unfold LX_ERRNO, RATP; exact ERR | exact MIc | exact FR | exact FSZ].
  Qed.

End Calls.
End WithCeiling0.
