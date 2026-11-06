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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA UnwindA AsStruct W_smallA W_topA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitA BnCallA UbStruct.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import UbStruct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Section Calls.
  Variables (LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (lo SPv FB : Z) (s0w raw : word) (rasO : option (list Z)) (TOTAL : Z).
  Variables (Σ0 : rts RT) (ls0 : bstate bptr) (OW0 : list block) (m0 : mem).
  Notation CENV := (cenvA LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0).
  Hypothesis LOFB16 : lo <= FB - 16.

  Lemma cenv_stack16A : forall pre used Σ ls m m' OW,
    CENV pre used Σ ls m OW -> lib_state ls m OW PL EA ->
    munch [(FB - 16, FB)]%Z m m' -> wmono bgbsegs m m' -> mem_inv bgbsegs m' -> stk bgbsegs m' lo FB ->
    CENV pre used Σ ls m' OW /\ lib_state ls m' OW PL EA.
  Proof using LOFB16.
    intros pre used Σ ls m m' OW ENV LS MU WM MI' ST'.
    pose proof ENV as (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW).
    pose proof OK as (CEIL & LOFB & FBSP & SPT & _ & _ & _ & _ & FROK & _).
    eapply (rw_cells_transport bgbsegs _ m m') in FR; [| exact MU | exact WM | cbn [disjoint_from]; split; [right; clear; lia| exact I]].
    assert (WOK : Forall (w_ok OW LB ls PL EA SPv []) [(FB - 16, FB)]) by (constructor; [apply w_stack; cbn [fst snd]; clear - CEIL LOFB FBSP LOFB16; lia| constructor]).
    assert (HWL : Forall (w_lib ls OW PL lo SPv) [(FB - 16, FB)]) by (constructor; [left; cbn [fst snd]; clear - LOFB FBSP LOFB16; lia| constructor]).
    split.
    - eapply cenv_silentA; [exact ENV | exact LS | exact MU | exact WM | exact HWL | exact ST' | exact MI' | exact FR | exact FSZ].
    - exact (lib_state_frame Σ LB SPv USTACK_TOP [] ls m m' OW PL EA _ HEAP LS MU WM FROK WOK).
  Qed.

  Lemma open_for_call : forall pre used Σ ls m OW r ar,
    CENV pre used Σ ls m OW -> lib_state ls m OW PL EA -> ref_at ls OW PL r ar -> r <> ROne ->
    exists D, rw_cells bgbsegs m ar (BnRepDefs.bn_cells D (getbn r ls)) /\ bg_ok (getbn r ls)
      /\ bv_unsigned (Z_to_bv 64 FB) = FB /\ stk bgbsegs m lo FB /\ mem_inv bgbsegs m /\ ar + 24 <= FB - 16
      /\ shb_cells bgbsegs 6147864 6945336 m /\ acc bgbsegs m ar 24 /\ ar mod 8 = 0 /\ SHHI <= lo /\ (ar + 24 <= SHLO \/ SHHI <= ar) /\ 0 < ar.
  Proof using LOFB16.
    intros pre used Σ ls m OW r ar ENV LS HA NRO.
    pose proof ENV as (OK & HEAP & ST & MI & _). pose proof OK as (CEIL & LOFB & FBSP & SPT & _ & _ & _ & _ & FROK & _ & NOFR).
    pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    destruct (lib_state_open [] ls m OW PL EA r ar LS ND HA ltac:(intros []) NRO) as ((D & BN & _) & OKB & _).
    destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP PARTS NOFR HA NRO) as (q & A & n & Hin & R1 & R2).
    pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (A0 & _ & _ & AC & _).
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HA NRO) as (ACC & AL & OFR).
    exists D. split; [exact BN|]. split; [exact OKB|]. split; [exact (ESPvA _ _ _ _ _ _ _ _ _ _ _ _ OK HEAP)|]. split; [exact ST|]. split; [exact MI|].
    split; [clear - AC R2 CEIL LOFB16; lia|]. split; [exact (AH_shb _ _ _ _ HEAP)|]. split; [exact ACC|]. split; [exact AL|].
    split; [unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *; clear - C1 C2 C3 CEIL; lia|]. split; [exact OFR| clear - A0 R1; lia].
  Qed.

  Lemma is_zero_callA : forall (POST : machine_state -> Prop) pre used Σ (ls : bstate bptr) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    CENV pre used Σ ls m OW -> lib_state ls m OW PL EA -> ref_at ls OW PL r ar -> r <> ROne ->
    (forall m' y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        CENV pre used Σ ls m' OW -> lib_state ls m' OW PL EA ->
        evt bgbsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) y0 y1 y2 x8 x9 (Z_to_bv 64 (Z.b2z (bn_top (getbn r ls) =? 0)%nat))
                                y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bgbsegs))) ->
    evt bgbsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_IS_ZERO) fc None m (seg_rom bgbsegs)).
  Proof using LOFB16.
    intros until fc. intros ENV LS HA NRO K.
    destruct (open_for_call _ _ _ _ _ _ _ _ ENV LS HA NRO) as (D & BN & (_ & OK2 & OK3 & _) & ESP & ST & MI & SEP & SHBC & ACC & AL & SLO & OFR & A0).
    unfold BG_DMAX in OK3.
    eapply evt_cut.
    { eapply BN_is_zero_specA with (lo := lo) (A := ar) (D := D) (b := getbn r ls);
        [exact BN | unfold bn_dmax in *; clear - OK2 OK3; lia | rewrite ESP; exact ST | rewrite ESP; exact LOFB16 | exact MI | rewrite ESP; left; exact SEP
        | exact SHBC | exact ACC | exact AL | exact SLO | exact OFR | reflexivity | exact A0]. }
    intros ms' PO. unfold bn_small_postA in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms' y3. rewrite ESP in *.
    destruct (cenv_stack16A _ _ _ _ _ _ _ ENV LS MUc WMc MIc STc) as (ENV' & LS').
    eapply K; [exact ENV' | exact LS'].
  Qed.

  Lemma set_neg_callA : forall (POST : machine_state -> Prop) pre used Σ (ls : bstate bptr) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    CENV pre used Σ ls m OW -> lib_state ls m OW PL EA -> ref_at ls OW PL r ar -> wref PL r ->
    (forall m' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        let ls' := setbn r (bn_with_neg (getbn r ls) (negb (bv_unsigned a1 =? 0) && negb (bn_top (getbn r ls) =? 0)%nat)) ls in
        CENV pre used Σ ls' m' OW -> lib_state ls' m' OW PL EA ->
        evt bgbsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) y0 y1 y2 x8 x9 y3 y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bgbsegs))) ->
    evt bgbsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_SET_NEGATIVE) fc None m (seg_rom bgbsegs)).
  Proof using LOFB16.
    intros until fc. intros ENV LS HA WR K.
    pose proof (proj1 WR : not_one r) as NRO.
    destruct (open_for_call _ _ _ _ _ _ _ _ ENV LS HA NRO) as (D0 & _ & _ & ESP & ST & MI & SEP & SHBC & ACC & AL & SLO & OFR & A0).
    pose proof ENV as (OK & HEAP & _ & _ & AXP & CR & CNT & RS & FR & FSZ & UW). pose proof OK as (CEIL & LOFB & FBSP & SPT & _ & _ & _ & _ & FROK & _ & NOFR).
    pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    destruct (lib_state_open [] ls m OW PL EA r ar LS ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & (OK1 & OK2 & OK3 & OK4) & LSH).
    set (b := getbn r ls) in *.
    destruct (bn_arr_facts_w ls OW PL EA SPv USTACK_TOP Σ LB m r D HEAP PARTS FROK HV WR ARR) as (U & _ & DD0 & DC & DI & SEPd). fold b in U, DC, DI, SEPd.
    pose proof (SEPd r ar HA) as SEPr. clear SEPd.
    destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP PARTS NOFR HA NRO) as (q & A & n & Hin & R1 & R2).
    pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (A0' & _ & _ & AC & AI).
    unfold BG_DMAX in OK3.
    eapply evt_cut.
    { eapply BN_set_negative_specA with (lo := lo) (A := ar) (D := D) (b := b);
        [exact BN | unfold bn_dmax in *; clear - OK2 OK3; lia | rewrite ESP; exact ST | rewrite ESP; exact LOFB16 | exact MI | rewrite ESP; left; exact SEP
        | exact SHBC | exact ACC | exact AL | exact SLO | exact OFR | reflexivity | exact A0]. }
    intros ms' PO. unfold bn_small_postA in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms'. rewrite ESP in *.
    set (b' := bn_with_neg b (negb (bv_unsigned a1 =? 0) && negb (bn_top b =? 0)%nat)) in *.
    assert (U' : u64arr bgbsegs m' D (wlimbs (bn_buf b))).
    { eapply u64arr_transport; [exact U | exact MUc | exact WMc |]. cbn [disjoint_from]. rewrite wlimbs_len. fold (bn_dmax b).
      split; [left; unfold BnHeapA.ACEIL in *; clear - DC CEIL LOFB16; lia|]. split; [clear - SEPr; lia| exact I]. }
    eapply (rw_cells_transport bgbsegs _ m m') in FR; [| exact MUc | exact WMc | cbn [disjoint_from]; split; [right; clear; lia|]; split; [right; clear - SEP; lia| exact I]].
    assert (WOK : Forall (w_ok OW LB ls PL EA SPv [r]) [(FB - 16, FB); (ar, ar + 24)]).
    { constructor; [apply w_stack; cbn [fst snd]; clear - CEIL LOFB FBSP LOFB16; lia|].
      constructor; [eapply (w_struct OW LB ls PL EA SPv false [r] _ r ar); [left; reflexivity| exact HA| exact NRO| cbn; clear; lia| cbn; clear; lia]| constructor]. }
    assert (HWL : Forall (w_lib ls OW PL lo SPv) [(FB - 16, FB); (ar, ar + 24)]).
    { constructor; [left; cbn [fst snd]; clear - LOFB FBSP LOFB16; lia|].
      constructor; [right; left; exists (q, A, n); cbn [blk_addr blk_size fst snd]; split; [exact Hin| clear - R1 R2; lia]| constructor]. }
    assert (LS' : lib_state (setbn r b' ls) m' OW PL EA).
    { unfold lib_state. eapply (lib_state_close [] ls m' OW PL EA r ar); [| exact ND | exact HA | exact NRO | | |].
      - exact (lib_state_frame Σ LB SPv USTACK_TOP [r] ls m m' OW PL EA _ HEAP LSH MUc WMc FROK WOK).
      - exists D. split; [exact RES|].
        assert (ARR' : bn_arr m' OW (pl_of PL r) D b) by (eapply bn_arr_of_u64arr; [exact ARR| exact U']).
        unfold bn_arr in ARR' |- *. unfold b', bn_with_neg, bn_dmax in *. cbn [bn_d bn_buf]. exact ARR'.
      - unfold bg_ok, b', bn_with_neg, bn_dmax, BG_DMAX in *. cbn [bn_buf bn_top bn_flags].
        split; [exact OK1|]. split; [exact OK2|]. split; [exact OK3| exact OK4].
      - apply ids_ok_setbn_same; [exact (proj1 (proj2 (proj2 PARTS))) | exact HV | reflexivity]. }
    eapply K; [| exact LS'].
    apply cenv_setbnA; [| exact HV | reflexivity].
    eapply cenv_silentA; [exact ENV | exact LS | exact MUc | exact WMc | exact HWL | exact STc | exact MIc | exact FR | exact FSZ].
  Qed.

End Calls.

End WithRT.
