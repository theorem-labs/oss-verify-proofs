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
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitAF BnCallAF W_callsAF W_small3A.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import UbStructF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
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
  Variables (LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (lo SPv FB : Z) (s0w raw : word) (rasO : option (list Z)) (TOTAL : Z).
  Variables (Σ0 : rts RT) (ls0 : bstate bptr) (OW0 : list block) (m0 : mem).
  Notation CENV := (cenvA LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0).

  Lemma cenv_belowA : forall pre used Σ ls m m' OW K,
    CENV pre used Σ ls m OW -> lib_state ls m OW PL EA -> 0 <= K -> lo <= FB - K ->
    munch [(FB - K, FB)]%Z m m' -> wmono bgbsegs m m' -> mem_inv bgbsegs m' -> stk bgbsegs m' lo FB ->
    CENV pre used Σ ls m' OW /\ lib_state ls m' OW PL EA.
  Proof.
    intros pre used Σ ls m m' OW K ENV LS K0 LOK MU WM MI' ST'.
    pose proof ENV as (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW).
    pose proof OK as (CEIL & LOFB & FBSP & SPT & _ & _ & _ & _ & FROK & _).
    eapply (rw_cells_transport bgbsegs _ m m') in FR; [| exact MU | exact WM | cbn [disjoint_from]; split; [right; clear; lia| exact I]].
    assert (WOK : Forall (w_ok OW LB ls PL EA SPv []) [(FB - K, FB)]) by (constructor; [apply w_stack; cbn [fst snd]; clear - CEIL LOFB FBSP LOK K0; lia| constructor]).
    assert (HWL : Forall (w_lib ls OW PL lo SPv) [(FB - K, FB)]) by (constructor; [left; cbn [fst snd]; clear - LOFB FBSP LOK K0; lia| constructor]).
    split.
    - eapply cenv_silentA; [exact ENV | exact LS | exact MU | exact WM | exact HWL | exact ST' | exact MI' | exact FR | exact FSZ].
    - exact (lib_state_frame Σ LB SPv USTACK_TOP [] ls m m' OW PL EA _ HEAP LS MU WM FROK WOK).
  Qed.

  Lemma open_for_read : forall pre used Σ ls m OW r ar K,
    CENV pre used Σ ls m OW -> lib_state ls m OW PL EA -> ref_at ls OW PL r ar -> r <> ROne -> 0 <= K -> lo <= FB - K ->
    exists D, rw_cells bgbsegs m ar (BnRepDefs.bn_cells D (getbn r ls)) /\ bg_ok (getbn r ls)
      /\ u64arr bgbsegs m D (wlimbs (bn_buf (getbn r ls)))
      /\ bv_unsigned (Z_to_bv 64 FB) = FB /\ stk bgbsegs m lo FB /\ mem_inv bgbsegs m
      /\ ar + 24 <= FB - K /\ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= FB - K
      /\ shb_cells bgbsegs 6147864 6945336 m /\ acc bgbsegs m ar 24 /\ ar mod 8 = 0
      /\ acc bgbsegs m D (8 * Z.of_nat (bn_top (getbn r ls))) /\ D mod 8 = 0
      /\ (0 <= D /\ D + 8 * Z.of_nat (bn_top (getbn r ls)) <= 140737488355328)
      /\ SHHI <= lo /\ 0 < ar /\ ub_ptr_ok (Z.of_nat (bn_top (getbn r ls))) D.
  Proof.
    intros pre used Σ ls m OW r ar K ENV LS HA NRO K0 LOK.
    pose proof ENV as (OK & HEAP & ST & MI & _). pose proof OK as (CEIL & LOFB & FBSP & SPT & _ & _ & _ & _ & FROK & _ & NOFR).
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3).
    destruct (open_ro_shu Σ OW LB m ls PL EA SPv r ar HEAP LS FROK NOFR HA NRO) as (D & BN & OKB & U & A0 & AC & D0 & DC & ACC & AL & ACCD & ALD & UBT & _).
    pose proof OKB as (_ & TD & _).
    exists D. split; [exact BN|]. split; [exact OKB|]. split; [exact U|].
    split; [exact (ESPvA _ _ _ _ _ _ _ _ _ _ _ _ OK HEAP)|]. split; [exact ST|]. split; [exact MI|].
    split; [unfold BnHeapA.ACEIL in *; clear - AC CEIL LOK; lia|]. split; [unfold BnHeapA.ACEIL in *; clear - DC CEIL LOK; lia|].
    split; [exact (AH_shb _ _ _ _ HEAP)|]. split; [exact ACC|]. split; [exact AL|]. split; [exact ACCD|]. split; [exact ALD|].
    split; [unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP, BnHeapA.ACEIL, bn_dmax in *; clear - D0 DC TD C1 C2 C3 CEIL LOFB FBSP SPT; lia|].
    split; [unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *; clear - C1 C2 C3 CEIL; lia|]. split; [exact A0| exact UBT].
  Qed.

  Hypothesis LOFB16 : lo <= FB - 16.

  Lemma get_flags_callA : forall (POST : machine_state -> Prop) pre used Σ (ls : bstate bptr) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    CENV pre used Σ ls m OW -> lib_state ls m OW PL EA -> ref_at ls OW PL r ar -> r <> ROne ->
    (forall m' y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        CENV pre used Σ ls m' OW -> lib_state ls m' OW PL EA ->
        evt bgbsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) y0 y1 y2 x8 x9 (Z_to_bv 64 (Z.land (bn_flags (getbn r ls)) (bv_unsigned a1)))
                                y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bgbsegs))) ->
    evt bgbsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_GET_FLAGS) fc None m (seg_rom bgbsegs)).
  Proof using LOFB16.
    intros until fc. intros ENV LS HA NRO K.
    destruct (open_for_read _ _ _ _ _ _ _ _ 16 ENV LS HA NRO ltac:(clear; lia) LOFB16)
      as (D & BN & (_ & _ & _ & OKF) & _ & ESP & ST & MI & SEP & _ & SHBC & ACC & AL & _ & _ & _ & SLO & A0 & UBP).
    eapply evt_cut.
    { eapply BN_get_flags_specA with (lo := lo) (A := ar) (D := D) (b := getbn r ls);
        [exact BN | clear - OKF; lia | rewrite ESP; exact ST | rewrite ESP; exact LOFB16 | exact MI | rewrite ESP; left; exact SEP
        | exact SHBC | exact ACC | exact AL | exact SLO | reflexivity | exact A0]. }
    intros ms' PO. unfold bn_small_postA in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms' y3. rewrite ESP in *.
    destruct (cenv_belowA _ _ _ _ _ _ _ 16 ENV LS ltac:(clear; lia) LOFB16 MUc WMc MIc STc) as (ENV' & LS').
    eapply K; [exact ENV' | exact LS'].
  Qed.

  Lemma value_one_callA : forall (POST : machine_state -> Prop) pre used Σ (ls : bstate bptr) (m : mem) (OW : list block)
      (ra gp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    CENV pre used Σ ls m OW -> lib_state ls m OW PL EA ->
    (forall m' y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        CENV pre used Σ ls m' OW -> lib_state ls m' OW PL EA ->
        evt bgbsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) y0 y1 y2 x8 x9 (Z_to_bv 64 CONST_ONE)
                                y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bgbsegs))) ->
    evt bgbsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_VALUE_ONE) fc None m (seg_rom bgbsegs)).
  Proof using LOFB16.
    intros until fc. intros ENV LS K.
    pose proof ENV as (OK & HEAP & ST & MI & _).
    pose proof (ESPvA _ _ _ _ _ _ _ _ _ _ _ _ OK HEAP) as ESP.
    eapply evt_cut.
    { eapply BN_value_one_specA with (lo := lo); [rewrite ESP; exact ST | rewrite ESP; exact LOFB16 | exact MI]. }
    intros ms' PO. unfold bn_small_postA in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms' y3. rewrite ESP in *.
    destruct (cenv_belowA _ _ _ _ _ _ _ 16 ENV LS ltac:(clear; lia) LOFB16 MUc WMc MIc STc) as (ENV' & LS').
    eapply K; [exact ENV' | exact LS'].
  Qed.

  Lemma is_odd_callA : forall (POST : machine_state -> Prop) pre used Σ (ls : bstate bptr) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    CENV pre used Σ ls m OW -> lib_state ls m OW PL EA -> ref_at ls OW PL r ar -> r <> ROne ->
    (forall m' y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        CENV pre used Σ ls m' OW -> lib_state ls m' OW PL EA ->
        evt bgbsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) y0 y1 y2 x8 x9 (Z_to_bv 64 (Z.b2z (is_odd_pure (getbn r ls))))
                                y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bgbsegs))) ->
    evt bgbsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_IS_ODD) fc None m (seg_rom bgbsegs)).
  Proof using LOFB16.
    intros until fc. intros ENV LS HA NRO K.
    destruct (open_for_read _ _ _ _ _ _ _ _ 16 ENV LS HA NRO ltac:(clear; lia) LOFB16)
      as (D & BN & (OK1 & OK2 & OK3 & _) & U & ESP & ST & MI & SEP & SEPD & SHBC & ACC & AL & ACCD & ALD & BD & SLO & A0 & UBP).
    unfold BG_DMAX in OK3.
    eapply evt_cut.
    { eapply BN_is_odd_specA with (lo := lo) (A := ar) (D := D) (b := getbn r ls);
        [exact BN | exact U | exact OK1 | exact OK2 | clear - OK3; lia | rewrite ESP; exact ST | rewrite ESP; exact LOFB16 | exact MI
        | rewrite ESP; left; exact SEP | rewrite ESP; left; exact SEPD
        | exact SHBC | exact ACC | exact AL | exact ACCD | exact ALD | exact BD | exact SLO | reflexivity | exact A0 | exact UBP]. }
    intros ms' PO. unfold bn_small_postA in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms' y3. rewrite ESP in *.
    destruct (cenv_belowA _ _ _ _ _ _ _ 16 ENV LS ltac:(clear; lia) LOFB16 MUc WMc MIc STc) as (ENV' & LS').
    eapply K; [exact ENV' | exact LS'].
  Qed.

  Lemma abs_is_word_callA : forall (POST : machine_state -> Prop) pre used Σ (ls : bstate bptr) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    CENV pre used Σ ls m OW -> lib_state ls m OW PL EA -> ref_at ls OW PL r ar -> r <> ROne ->
    (forall m' y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        CENV pre used Σ ls m' OW -> lib_state ls m' OW PL EA ->
        evt bgbsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) y0 y1 y2 x8 x9 (Z_to_bv 64 (Z.b2z (abs_is_word_pure (getbn r ls) (bv_unsigned a1))))
                                y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bgbsegs))) ->
    evt bgbsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_ABS_IS_WORD) fc None m (seg_rom bgbsegs)).
  Proof using LOFB16.
    intros until fc. intros ENV LS HA NRO K.
    destruct (open_for_read _ _ _ _ _ _ _ _ 16 ENV LS HA NRO ltac:(clear; lia) LOFB16)
      as (D & BN & (OK1 & OK2 & OK3 & _) & U & ESP & ST & MI & SEP & SEPD & SHBC & ACC & AL & ACCD & ALD & BD & SLO & A0 & UBP).
    unfold BG_DMAX in OK3.
    eapply evt_cut.
    { eapply BN_abs_is_word_specA with (lo := lo) (A := ar) (D := D) (b := getbn r ls);
        [exact BN | exact U | exact OK1 | exact OK2 | clear - OK3; lia | rewrite ESP; exact ST | rewrite ESP; exact LOFB16 | exact MI
        | rewrite ESP; left; exact SEP | rewrite ESP; left; exact SEPD
        | exact SHBC | exact ACC | exact AL | exact ACCD | exact ALD | exact BD | exact SLO | reflexivity | exact A0 | exact UBP]. }
    intros ms' PO. unfold bn_small_postA in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms' y3. rewrite ESP in *.
    destruct (cenv_belowA _ _ _ _ _ _ _ 16 ENV LS ltac:(clear; lia) LOFB16 MUc WMc MIc STc) as (ENV' & LS').
    eapply K; [exact ENV' | exact LS'].
  Qed.

  Lemma is_bit_set_callA : forall (POST : machine_state -> Prop) pre used Σ (ls : bstate bptr) (m : mem) (OW : list block) (r : bnref) (ar n : Z)
      (ra gp t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    CENV pre used Σ ls m OW -> lib_state ls m OW PL EA -> ref_at ls OW PL r ar -> r <> ROne -> -2147483648 <= n < 2147483648 ->
    (forall m' y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        CENV pre used Σ ls m' OW -> lib_state ls m' OW PL EA ->
        evt bgbsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) y0 y1 y2 x8 x9 (Z_to_bv 64 (Z.b2z (is_bit_set_pure (getbn r ls) n)))
                                y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bgbsegs))) ->
    evt bgbsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_IS_BIT_SET) fc None m (seg_rom bgbsegs)).
  Proof using LOFB16.
    intros until fc. intros ENV LS HA NRO HN K.
    destruct (open_for_read _ _ _ _ _ _ _ _ 16 ENV LS HA NRO ltac:(clear; lia) LOFB16)
      as (D & BN & (OK1 & OK2 & OK3 & _) & U & ESP & ST & MI & SEP & SEPD & SHBC & ACC & AL & ACCD & ALD & BD & SLO & A0 & UBP).
    unfold BG_DMAX in OK3.
    eapply evt_cut.
    { eapply BN_is_bit_set_specA with (lo := lo) (A := ar) (D := D) (n := n) (b := getbn r ls);
        [exact BN | exact U | exact OK1 | exact OK2 | clear - OK3; lia | rewrite ESP; exact ST | rewrite ESP; exact LOFB16 | exact MI
        | rewrite ESP; left; exact SEP | rewrite ESP; left; exact SEPD
        | exact SHBC | exact ACC | exact AL | exact ACCD | exact ALD | exact BD | exact SLO | reflexivity | reflexivity | exact HN | exact A0 | exact UBP]. }
    intros ms' PO. unfold bn_small_postA in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms' y3. rewrite ESP in *.
    destruct (cenv_belowA _ _ _ _ _ _ _ 16 ENV LS ltac:(clear; lia) LOFB16 MUc WMc MIc STc) as (ENV' & LS').
    eapply K; [exact ENV' | exact LS'].
  Qed.

  Lemma num_bits_callA : forall (POST : machine_state -> Prop) pre used Σ (ls : bstate bptr) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    CENV pre used Σ ls m OW -> lib_state ls m OW PL EA -> ref_at ls OW PL r ar -> r <> ROne -> lo <= FB - BN_NUM_BITS_STACK ->
    (forall m' y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        CENV pre used Σ ls m' OW -> lib_state ls m' OW PL EA ->
        evt bgbsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) y0 y1 y2 x8 x9 (Z_to_bv 64 (num_bits_pure (getbn r ls)))
                                y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bgbsegs))) ->
    evt bgbsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_NUM_BITS) fc None m (seg_rom bgbsegs)).
  Proof.
    intros until fc. intros ENV LS HA NRO LOK K. unfold BN_NUM_BITS_STACK in LOK.
    destruct (open_for_read _ _ _ _ _ _ _ _ 128 ENV LS HA NRO ltac:(clear; lia) LOK)
      as (D & BN & (OK1 & OK2 & OK3 & OK4) & U & ESP & ST & MI & SEP & SEPD & SHBC & ACC & AL & ACCD & ALD & BD & SLO & A0 & UBP).
    unfold BG_DMAX in OK3.
    eapply evt_cut.
    { eapply BN_num_bits_specA with (lo := lo) (A := ar) (D := D) (b := getbn r ls);
        [exact BN | exact U | exact OK1 | exact OK2 | clear - OK3; lia | clear - OK4; lia | clear - OK4; destruct OK4 as [-> | ->]; reflexivity
        | rewrite ESP; exact ST | rewrite ESP; exact LOK | exact MI
        | rewrite ESP; left; exact SEP | rewrite ESP; left; exact SEPD
        | exact SHBC | exact ACC | exact AL | exact ACCD | exact ALD | exact BD | exact SLO | reflexivity | exact A0 | exact UBP]. }
    intros ms' PO. unfold bn_small_postA in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms' y3. rewrite ESP in *.
    destruct (cenv_belowA _ _ _ _ _ _ _ 128 ENV LS ltac:(clear; lia) LOK MUc WMc MIc STc) as (ENV' & LS').
    eapply K; [exact ENV' | exact LS'].
  Qed.

End Calls.

End WithRT.
