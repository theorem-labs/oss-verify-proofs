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
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnHeap BnArr BnRep BnIface BnCall W_small W_small2.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].






Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Section Calls.
  Variables (LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo B SPv FB : Z).
  Variables (s0 : PState) (ls0 : lstate bptr) (OW0 : list block) (m0 : mem).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis LOFB : lo <= FB - 16.
  Hypothesis FBSP : FB <= SPv.
  Hypothesis SPB : SPv <= B.
  Hypothesis SPR : SPv < 2^64.

  Lemma ESPc : bv_unsigned (Z_to_bv 64 FB) = FB.
  Proof using CEIL LOFB FBSP SPR. apply unsigned_lit. lia. Qed.

  (* [comment removed for export] *)
  Lemma cenv_stack16 : forall fr st ls m m' OW,
    cenv LB AD lo B SPv FB s0 ls0 OW0 m0 fr st ls m OW -> lib_state ls m OW AD EA ->
    munch [(FB - 16, FB)]%Z m m' -> wmono psegs m m' -> mem_inv psegs m' -> stk psegs m' lo FB ->
    cenv LB AD lo B SPv FB s0 ls0 OW0 m0 fr st ls m' OW /\ lib_state ls m' OW AD EA.
  Proof using CEIL GLO LOFB FBSP SPB SPR.
    intros fr st ls m m' OW ENV LS MU WM MI' ST'.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & FSZ).
    unfold LX_ERRNO, RATP in ERR. change (3063480 - 164) with 3063316 in ERR. unfold GLOBALS_TOP in GLO.
    eapply (rw_cells_transport psegs _ m m') in FR; [| exact MU | exact WM | cbn [disjoint_from]; split; [right; lia| exact I]].
    eapply (rw_cells_transport psegs _ m m') in ERR; [| exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; split; [left; lia| exact I]].
    assert (WOK : Forall (w_ok OW LB ls AD EA []) [(FB - 16, FB)]) by (constructor; [apply w_stack; cbn [fst]; lia| constructor]).
    assert (HWL : Forall (w_lib OW lo SPv) [(FB - 16, FB)]) by (constructor; [left; cbn [fst snd]; lia| constructor]).
    split.
    - eapply (cenv_silent LB AD lo B SPv FB s0 ls0 OW0 m0 CEIL ltac:(unfold GLOBALS_TOP; exact GLO) ltac:(lia) FBSP SPB fr fr);
        [exact ENV | exact MU | exact WM | exact HWL | exact ST' | unfold LX_ERRNO, RATP; exact ERR | exact MI' | exact FR | exact FSZ].
    - exact (lib_state_frame st LB [] ls m m' OW AD EA _ HEAP LS MU WM WOK).
  Qed.

  (* [comment removed for export] *)
  Lemma is_zero_call : forall (POST : machine_state -> Prop) (fr : list cell) (st : PState) (ls : lstate bptr) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    cenv LB AD lo B SPv FB s0 ls0 OW0 m0 fr st ls m OW -> lib_state ls m OW AD EA -> ref_at ls OW AD r ar ->
    (forall m' y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        cenv LB AD lo B SPv FB s0 ls0 OW0 m0 fr st ls m' OW -> lib_state ls m' OW AD EA ->
        evt psegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) y0 y1 y2 x8 x9 (Z_to_bv 64 (Z.b2z (bn_top (getbn r ls) =? 0)%nat))
                                y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom psegs))) ->
    evt psegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_IS_ZERO) fc None m (seg_rom psegs)).
  Proof using CEIL GLO LOFB FBSP SPB SPR.
    intros until fc. intros ENV LS HA K.
    pose proof ENV as (HEAP & AUX & ST & _ & MI & _).
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
    destruct (lib_state_open [] ls m OW AD EA r ar LS ND HA ltac:(intros [])) as ((D & BN & _) & (_ & OK2 & OK3 & _) & _).
    destruct (ref_at_inb _ _ _ _ _ ADB HA) as (q & A & n & _ & Hin & R1 & R2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP Hin) as (A0 & _ & _ & AC & _).
    pose proof ESPc as ESP. unfold BN_WORDS_MAX in OK3.
    eapply evt_cut.
    { eapply BN_is_zero_spec with (lo := lo) (A := ar) (D := D) (b := getbn r ls);
        [exact BN | lia | rewrite ESP; exact ST | rewrite ESP; lia | exact MI | rewrite ESP; left; lia | reflexivity]. }
    intros ms' PO. unfold bn_small_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms' y3. rewrite ESP in *.
    destruct (cenv_stack16 fr st ls m m' OW ENV LS MUc WMc MIc STc) as (ENV' & LS').
    eapply K; [exact ENV' | exact LS'].
  Qed.

  (* [comment removed for export] *)
  Lemma is_neg_call : forall (POST : machine_state -> Prop) (fr : list cell) (st : PState) (ls : lstate bptr) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    cenv LB AD lo B SPv FB s0 ls0 OW0 m0 fr st ls m OW -> lib_state ls m OW AD EA -> ref_at ls OW AD r ar ->
    (forall m' y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        cenv LB AD lo B SPv FB s0 ls0 OW0 m0 fr st ls m' OW -> lib_state ls m' OW AD EA ->
        evt psegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) y0 y1 y2 x8 x9 (Z_to_bv 64 (Z.b2z (bn_neg (getbn r ls))))
                                y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom psegs))) ->
    evt psegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_IS_NEGATIVE) fc None m (seg_rom psegs)).
  Proof using CEIL GLO LOFB FBSP SPB SPR.
    intros until fc. intros ENV LS HA K.
    pose proof ENV as (HEAP & AUX & ST & _ & MI & _).
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
    destruct (lib_state_open [] ls m OW AD EA r ar LS ND HA ltac:(intros [])) as ((D & BN & _) & _ & _).
    destruct (ref_at_inb _ _ _ _ _ ADB HA) as (q & A & n & _ & Hin & R1 & R2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP Hin) as (A0 & _ & _ & AC & _).
    pose proof ESPc as ESP.
    eapply evt_cut.
    { eapply BN_is_negative_spec with (lo := lo) (A := ar) (D := D) (b := getbn r ls);
        [exact BN | rewrite ESP; exact ST | rewrite ESP; lia | exact MI | rewrite ESP; left; lia | reflexivity]. }
    intros ms' PO. unfold bn_small_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms' y3. rewrite ESP in *.
    destruct (cenv_stack16 fr st ls m m' OW ENV LS MUc WMc MIc STc) as (ENV' & LS').
    eapply K; [exact ENV' | exact LS'].
  Qed.

  (* [comment removed for export] *)
  Lemma set_neg_call : forall (POST : machine_state -> Prop) (fr : list cell) (st : PState) (ls : lstate bptr) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    cenv LB AD lo B SPv FB s0 ls0 OW0 m0 fr st ls m OW -> lib_state ls m OW AD EA -> ref_at ls OW AD r ar ->
    (forall m' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        let ls' := setbn r (bn_with_neg (getbn r ls) (negb (bv_unsigned a1 =? 0) && negb (bn_top (getbn r ls) =? 0)%nat)) ls in
        cenv LB AD lo B SPv FB s0 ls0 OW0 m0 fr st ls' m' OW -> lib_state ls' m' OW AD EA ->
        evt psegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) y0 y1 y2 x8 x9 y3 y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom psegs))) ->
    evt psegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 0xdea20) fc None m (seg_rom psegs)).
  Proof using CEIL GLO LOFB FBSP SPB SPR.
    intros until fc. intros ENV LS HA K.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & FSZ).
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    destruct (lib_state_open [] ls m OW AD EA r ar LS ND HA ltac:(intros [])) as ((D & BN & ARR) & (OK1 & OK2 & OK3 & OK4) & LSH).
    set (b := getbn r ls) in *.
    destruct (bn_arr_facts st OW LB m HEAP ls AD EA IDS ADB r D HV ARR) as (U & _ & D0 & DC & DI & SEP). fold b in U, DC, DI, SEP.
    pose proof (SEP r ar HA) as SEPr. clear SEP.
    destruct (ref_at_inb _ _ _ _ _ ADB HA) as (q & A & n & _ & Hin & R1 & R2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP Hin) as (A0 & _ & _ & AC & AI).
    pose proof ESPc as ESP.
    unfold LX_ERRNO, RATP in ERR. change (3063480 - 164) with 3063316 in ERR. unfold BN_WORDS_MAX in OK3. unfold GLOBALS_TOP in GLO.
    eapply evt_cut.
    { eapply BN_set_negative_spec with (lo := lo) (A := ar) (D := D) (b := b);
        [exact BN | lia | rewrite ESP; exact ST | rewrite ESP; lia | exact MI | rewrite ESP; left; lia | reflexivity]. }
    intros ms' PO. unfold bn_small_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms'. rewrite ESP in *.
    set (b' := bn_with_neg b (negb (bv_unsigned a1 =? 0) && negb (bn_top b =? 0)%nat)) in *.
    assert (U' : u64arr psegs m' D (wlimbs (bn_buf b))).
    { eapply u64arr_transport; [exact U | exact MUc | exact WMc |]. cbn [disjoint_from]. rewrite wlimbs_len. fold (bn_dmax b).
      split; [left; lia|]. split; [lia| exact I]. }
    eapply (rw_cells_transport psegs _ m m') in FR; [| exact MUc | exact WMc | cbn [disjoint_from]; split; [right; lia|]; split; [right; lia| exact I]].
    eapply (rw_cells_transport psegs _ m m') in ERR; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; split; [left; lia|]; split; [lia| exact I]].
    assert (WOK : Forall (w_ok OW LB ls AD EA [r]) [(FB - 16, FB); (ar, ar + 24)]).
    { constructor; [apply w_stack; cbn [fst]; lia|].
      constructor; [eapply (w_struct OW LB ls AD EA false [r] _ r ar); [left; reflexivity| exact HA| cbn; lia| cbn; lia]| constructor]. }
    assert (HWL : Forall (w_lib OW lo SPv) [(FB - 16, FB); (ar, ar + 24)]).
    { constructor; [left; cbn [fst snd]; lia|]. constructor; [right; exists (q, A, n); cbn; auto| constructor]. }
    assert (LS' : lib_state (setbn r b' ls) m' OW AD EA).
    { unfold lib_state. eapply (lib_state_close [] ls m' OW AD EA r ar); [| exact ND | exact HA | | |].
      - exact (lib_state_frame st LB [r] ls m m' OW AD EA _ HEAP LSH MUc WMc WOK).
      - exists D. split; [exact RES|]. unfold bn_arr in *. unfold b', bn_with_neg, bn_dmax in *. cbn [bn_d bn_buf].
        destruct (bn_d b) as [p|]; [split; [exact (proj1 ARR)| exact U'] | exact ARR].
      - unfold bn_okm, b', bn_with_neg, bn_dmax, BN_WORDS_MAX in *. cbn [bn_buf bn_top bn_flags].
        split; [exact OK1|]. split; [exact OK2|]. split; [exact OK3| exact OK4].
      - apply ids_ok_setbn_same; [exact IDS | exact HV | reflexivity]. }
    eapply K; [| exact LS'].
    apply cenv_setbn.
    eapply (cenv_silent LB AD lo B SPv FB s0 ls0 OW0 m0 CEIL ltac:(unfold GLOBALS_TOP; exact GLO) ltac:(lia) FBSP SPB fr fr);
      [exact ENV | exact MUc | exact WMc | exact HWL | exact STc | unfold LX_ERRNO, RATP; exact ERR | exact MIc | exact FR | exact FSZ].
  Qed.

End Calls.
End WithCeiling0.
