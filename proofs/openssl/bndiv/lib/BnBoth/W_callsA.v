(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA ZBridge RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree BnInv BnSpecs BnMInv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA BnIfaceA UnwindA AsStruct W_smallA BnAKitA BnCallA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Section Calls.
  Variables (LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo SPv FB : Z) (s0w raw : word) (rasO : option (list Z)) (TOTAL : Z).
  Variables (Σ0 : rts RT) (ls0 : lstate bptr) (OW0 : list block) (m0 : mem).
  Notation CENV := (cenvA LB AD lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0).
  Hypothesis LOFB16 : lo <= FB - 16.

  (* [comment removed for export] *)
  Lemma cenv_stack16A : forall pre used Σ ls m m' OW,
    CENV pre used Σ ls m OW -> lib_state ls m OW AD EA ->
    munch [(FB - 16, FB)]%Z m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' lo FB ->
    CENV pre used Σ ls m' OW /\ lib_state ls m' OW AD EA.
  Proof using LOFB16.
    intros pre used Σ ls m m' OW ENV LS MU WM MI' ST'.
    pose proof ENV as (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW).
    pose proof OK as (CEIL & LOFB & FBSP & SPT & _).
    eapply (rw_cells_transport bsegs _ m m') in FR; [| exact MU | exact WM | cbn [disjoint_from]; split; [right; lia| exact I]].
    assert (WOK : Forall (w_ok OW LB ls AD EA []) [(FB - 16, FB)]) by (constructor; [apply w_stack; cbn [fst]; lia| constructor]).
    assert (HWL : Forall (w_lib OW lo SPv) [(FB - 16, FB)]) by (constructor; [left; cbn [fst snd]; lia| constructor]).
    split.
    - eapply cenv_silentA; [exact ENV | exact MU | exact WM | exact HWL | exact ST' | exact MI' | exact FR | exact FSZ].
    - exact (lib_state_frame Σ LB [] ls m m' OW AD EA _ HEAP LS MU WM WOK).
  Qed.

  (* [comment removed for export] *)
  Lemma open_for_call : forall pre used Σ ls m OW r ar,
    CENV pre used Σ ls m OW -> lib_state ls m OW AD EA -> ref_at ls OW AD r ar ->
    exists D, rw_cells bsegs m ar (bn_cells D (getbn r ls)) /\ bn_okm (getbn r ls)
      /\ bv_unsigned (Z_to_bv 64 FB) = FB /\ stk bsegs m lo FB /\ mem_inv bsegs m /\ ar + 24 <= FB - 16
      /\ shb_cells bsegs 6163672 6961656 m /\ acc bsegs m ar 24 /\ ar mod 8 = 0 /\ SHHI <= lo /\ (ar + 24 <= SHLO \/ SHHI <= ar) /\ 0 < ar.
  Proof using LOFB16.
    intros pre used Σ ls m OW r ar ENV LS HA.
    pose proof ENV as (OK & HEAP & ST & MI & _). pose proof OK as (CEIL & LOFB & FBSP & SPT & _).
    pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
    destruct (lib_state_open [] ls m OW AD EA r ar LS ND HA ltac:(intros [])) as ((D & BN & _) & OKB & _).
    destruct (ref_at_inb _ _ _ _ _ ADB HA) as (q & A & n & _ & Hin & R1 & R2).
    pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (A0 & _ & _ & AC & _).
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS HA) as (ACC & AL & OFR).
    exists D. split; [exact BN|]. split; [exact OKB|]. split; [exact (ESPvA _ _ _ _ _ _ _ _ _ _ _ OK HEAP)|]. split; [exact ST|]. split; [exact MI|].
    split; [lia|]. split; [exact (AH_shb _ _ _ _ HEAP)|]. split; [exact ACC|]. split; [exact AL|]. split; [lia|]. split; [exact OFR| clear - A0 R1; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma is_zero_callA : forall (POST : machine_state -> Prop) pre used Σ (ls : lstate bptr) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    CENV pre used Σ ls m OW -> lib_state ls m OW AD EA -> ref_at ls OW AD r ar ->
    (forall m' y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        CENV pre used Σ ls m' OW -> lib_state ls m' OW AD EA ->
        evt bsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) y0 y1 y2 x8 x9 (Z_to_bv 64 (Z.b2z (bn_top (getbn r ls) =? 0)%nat))
                                y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
    evt bsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_IS_ZERO) fc None m (seg_rom bsegs)).
  Proof using LOFB16.
    intros until fc. intros ENV LS HA K.
    destruct (open_for_call _ _ _ _ _ _ _ _ ENV LS HA) as (D & BN & (_ & OK2 & OK3 & _) & ESP & ST & MI & SEP & SHBC & ACC & AL & SLO & OFR & A0).
    unfold BN_WORDS_MAX in OK3.
    eapply evt_cut.
    { eapply BN_is_zero_specA with (lo := lo) (A := ar) (D := D) (b := getbn r ls);
        [exact BN | unfold bn_dmax in *; lia | rewrite ESP; exact ST | rewrite ESP; lia | exact MI | rewrite ESP; left; lia
        | exact SHBC | exact ACC | exact AL | exact SLO | exact OFR | reflexivity | exact A0]. }
    intros ms' PO. unfold bn_small_postA in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms' y3. rewrite ESP in *.
    destruct (cenv_stack16A _ _ _ _ _ _ _ ENV LS MUc WMc MIc STc) as (ENV' & LS').
    eapply K; [exact ENV' | exact LS'].
  Qed.

  (* [comment removed for export] *)
  Lemma is_neg_callA : forall (POST : machine_state -> Prop) pre used Σ (ls : lstate bptr) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    CENV pre used Σ ls m OW -> lib_state ls m OW AD EA -> ref_at ls OW AD r ar ->
    (forall m' y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        CENV pre used Σ ls m' OW -> lib_state ls m' OW AD EA ->
        evt bsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) y0 y1 y2 x8 x9 (Z_to_bv 64 (Z.b2z (bn_neg (getbn r ls))))
                                y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
    evt bsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_IS_NEGATIVE) fc None m (seg_rom bsegs)).
  Proof using LOFB16.
    intros until fc. intros ENV LS HA K.
    destruct (open_for_call _ _ _ _ _ _ _ _ ENV LS HA) as (D & BN & _ & ESP & ST & MI & SEP & SHBC & ACC & AL & SLO & OFR & A0).
    eapply evt_cut.
    { eapply BN_is_negative_specA with (lo := lo) (A := ar) (D := D) (b := getbn r ls);
        [exact BN | rewrite ESP; exact ST | rewrite ESP; lia | exact MI | rewrite ESP; left; lia
        | exact SHBC | exact ACC | exact AL | exact SLO | exact OFR | reflexivity | exact A0]. }
    intros ms' PO. unfold bn_small_postA in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms' y3. rewrite ESP in *.
    destruct (cenv_stack16A _ _ _ _ _ _ _ ENV LS MUc WMc MIc STc) as (ENV' & LS').
    eapply K; [exact ENV' | exact LS'].
  Qed.

  (* [comment removed for export] *)
  Lemma set_neg_callA : forall (POST : machine_state -> Prop) pre used Σ (ls : lstate bptr) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    CENV pre used Σ ls m OW -> lib_state ls m OW AD EA -> ref_at ls OW AD r ar ->
    (forall m' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        let ls' := setbn r (bn_with_neg (getbn r ls) (negb (bv_unsigned a1 =? 0) && negb (bn_top (getbn r ls) =? 0)%nat)) ls in
        CENV pre used Σ ls' m' OW -> lib_state ls' m' OW AD EA ->
        evt bsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) y0 y1 y2 x8 x9 y3 y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
    evt bsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_SET_NEGATIVE) fc None m (seg_rom bsegs)).
  Proof using LOFB16.
    intros until fc. intros ENV LS HA K.
    destruct (open_for_call _ _ _ _ _ _ _ _ ENV LS HA) as (D0 & _ & _ & ESP & ST & MI & SEP & SHBC & ACC & AL & SLO & OFR & A0).
    pose proof ENV as (OK & HEAP & _ & _ & AXP & CR & CNT & RS & FR & FSZ & UW). pose proof OK as (CEIL & LOFB & FBSP & SPT & _).
    pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    destruct (lib_state_open [] ls m OW AD EA r ar LS ND HA ltac:(intros [])) as ((D & BN & ARR) & (OK1 & OK2 & OK3 & OK4) & LSH).
    set (b := getbn r ls) in *.
    destruct (bn_arr_facts Σ OW LB m HEAP ls AD EA IDS ADB r D HV ARR) as (U & _ & DD0 & DC & DI & SEPd). fold b in U, DC, DI, SEPd.
    pose proof (SEPd r ar HA) as SEPr. clear SEPd.
    destruct (ref_at_inb _ _ _ _ _ ADB HA) as (q & A & n & _ & Hin & R1 & R2).
    pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (A0' & _ & _ & AC & AI).
    unfold BN_WORDS_MAX in OK3.
    eapply evt_cut.
    { eapply BN_set_negative_specA with (lo := lo) (A := ar) (D := D) (b := b);
        [exact BN | unfold bn_dmax in *; lia | rewrite ESP; exact ST | rewrite ESP; lia | exact MI | rewrite ESP; left; lia
        | exact SHBC | exact ACC | exact AL | exact SLO | exact OFR | reflexivity | exact A0]. }
    intros ms' PO. unfold bn_small_postA in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms'. rewrite ESP in *.
    set (b' := bn_with_neg b (negb (bv_unsigned a1 =? 0) && negb (bn_top b =? 0)%nat)) in *.
    assert (U' : u64arr bsegs m' D (wlimbs (bn_buf b))).
    { eapply u64arr_transport; [exact U | exact MUc | exact WMc |]. cbn [disjoint_from]. rewrite wlimbs_len. fold (bn_dmax b).
      split; [left; lia|]. split; [lia| exact I]. }
    eapply (rw_cells_transport bsegs _ m m') in FR; [| exact MUc | exact WMc | cbn [disjoint_from]; split; [right; lia|]; split; [right; lia| exact I]].
    assert (WOK : Forall (w_ok OW LB ls AD EA [r]) [(FB - 16, FB); (ar, ar + 24)]).
    { constructor; [apply w_stack; cbn [fst]; lia|].
      constructor; [eapply (w_struct OW LB ls AD EA false [r] _ r ar); [left; reflexivity| exact HA| cbn; lia| cbn; lia]| constructor]. }
    assert (HWL : Forall (w_lib OW lo SPv) [(FB - 16, FB); (ar, ar + 24)]).
    { constructor; [left; cbn [fst snd]; lia|]. constructor; [right; exists (q, A, n); cbn; auto| constructor]. }
    assert (LS' : lib_state (setbn r b' ls) m' OW AD EA).
    { unfold lib_state. eapply (lib_state_close [] ls m' OW AD EA r ar); [| exact ND | exact HA | | |].
      - exact (lib_state_frame Σ LB [r] ls m m' OW AD EA _ HEAP LSH MUc WMc WOK).
      - exists D. split; [exact RES|]. unfold bn_arr in *. unfold b', bn_with_neg, bn_dmax in *. cbn [bn_d bn_buf].
        destruct (bn_d b) as [p|]; [split; [exact (proj1 ARR)| exact U'] | exact ARR].
      - unfold bn_okm, b', bn_with_neg, bn_dmax, BN_WORDS_MAX in *. cbn [bn_buf bn_top bn_flags].
        split; [exact OK1|]. split; [exact OK2|]. split; [exact OK3| exact OK4].
      - apply ids_ok_setbn_same; [exact IDS | exact HV | reflexivity]. }
    eapply K; [| exact LS'].
    apply cenv_setbnA; [| exact HV | reflexivity].
    eapply cenv_silentA; [exact ENV | exact MUc | exact WMc | exact HWL | exact STc | exact MIc | exact FR | exact FSZ].
  Qed.

End Calls.
End WithRT.
