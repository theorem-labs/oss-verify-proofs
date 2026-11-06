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
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA UnwindA AsStruct W_smallA W_topA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import BnAKitAF BnCallAF W_callsAF W_calls3AF AFrameKit AFrameEnv ExpKitAF InvKitAF HoleKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation ops := (tree_ops bptr).
Local Notation ST := (bstate bptr).

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Section Kit.
  Variables (LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (lo SPv FB : Z) (s0w raw : word) (ras : list Z) (TOTAL : Z).
  Variables (Σ0 : rts RT) (ls0 : bstate bptr) (OW0 : list block) (m0 : mem).
  Notation CENV := (cenvA LB PL lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0).
  Hypothesis LOFB16 : lo <= FB - 16.

  Definition fpF1 (K a D : Z) (d : nat) : list (Z * Z) := [(FB - K, SPv); (a, a + 24); (D, D + 8 * Z.of_nat d)].
  Definition fpF2 (K a1 D1 : Z) (d1 : nat) (a2 D2 : Z) (d2 : nat) : list (Z * Z) :=
    [(FB - K, SPv); (a1, a1 + 24); (D1, D1 + 8 * Z.of_nat d1); (a2, a2 + 24); (D2, D2 + 8 * Z.of_nat d2)].

  Lemma cenv_hole1F : forall pre used Σ ls m OW r a K,
    CENV pre used Σ ls m OW -> lib_state ls m OW PL EA -> ref_at ls OW PL r a -> wref PL r -> (0 < bn_dmax (getbn r ls))%nat -> 0 <= K -> lo <= FB - K ->
    exists D p, bn_d (getbn r ls) = Some p /\ In (p, D, 8 * Z.of_nat (bn_dmax (getbn r ls))) OW
      /\ rw_cells bgasegs m a (BnRepDefs.bn_cells D (getbn r ls)) /\ u64arr bgasegs m D (wlimbs (bn_buf (getbn r ls))) /\ bg_ok (getbn r ls)
      /\ (acc bgasegs m a 24 /\ a mod 8 = 0 /\ 0 < a /\ a + 24 <= FB - 16 /\ (a + 24 <= SHLO \/ SHHI <= a))
      /\ (acc bgasegs m D (8 * Z.of_nat (bn_dmax (getbn r ls))) /\ D mod 8 = 0 /\ 0 <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= FB - 16
          /\ (D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= SHLO \/ SHHI <= D))
      /\ (forall r' a', ref_at ls OW PL r' a' -> a' + 24 <= D \/ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= a')
      /\ (forall m', munch (fpF1 K a D (bn_dmax (getbn r ls))) m m' -> wmono bgasegs m m' ->
            AHEAP Σ OW LB m' /\ lib_state_hc false [r] ls m' OW PL EA)
      /\ forall m' b' pre',
           munch (fpF1 K a D (bn_dmax (getbn r ls))) m m' -> wmono bgasegs m m' ->
           rw_cells bgasegs m' a (BnRepDefs.bn_cells D b') -> u64arr bgasegs m' D (wlimbs (bn_buf b')) ->
           bn_d b' = bn_d (getbn r ls) -> length (bn_buf b') = length (bn_buf (getbn r ls)) -> bg_ok b' ->
           stk bgasegs m' lo FB -> mem_inv bgasegs m' ->
           rw_cells bgasegs m' FB (pre' ++ [C8 s0w; C8 raw]) -> Z.of_nat (cells_size pre') = SPv - FB - 16 ->
           CENV pre' used Σ (setbn r b' ls) m' OW /\ lib_state (setbn r b' ls) m' OW PL EA.
  Proof using LOFB16.
    intros pre used Σ ls m OW r a K ENV LS HA WR HD K0 LOK.
    pose proof (proj1 WR : not_one r) as NRO.
    destruct (cenv_hole1A LB PL EA lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0 LOFB16 _ _ _ _ _ _ _ _ ENV LS HA WR HD)
      as (D & p & Ed & Hin & BN & U & OKB & AS & AD & SEPd & _ & _ & _ & _).
    pose proof ENV as (OK & HEAP & _ & _ & AXP & CR & CNT & RS & FR & FSZ & UW). pose proof OK as (CEIL & LOFB & FBSP & SPT & _ & _ & _ & _ & FROK & FAL & NOFR).
    pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    destruct (lib_state_open [] ls m OW PL EA r a LS ND HA ltac:(intros []) NRO) as (_ & _ & LSH).
    set (b := getbn r ls) in *.
    assert (WOK : Forall (w_ok OW LB ls PL EA SPv [r]) (fpF1 K a D (bn_dmax b))).
    { unfold fpF1. constructor; [apply w_stack; cbn [fst snd]; clear - CEIL LOK; lia|].
      constructor; [eapply (w_struct OW LB ls PL EA SPv false [r] _ r a); [left; reflexivity| exact HA| exact NRO| cbn; clear; lia| cbn; clear; lia]|].
      constructor; [| constructor].
      eapply (w_limbs OW LB ls PL EA SPv false [r] _ r p D); [left; reflexivity| exact HV| exact Ed| exact Hin| cbn [fst snd]; clear; lia| cbn [fst snd]; fold b; clear; lia]. }
    assert (HWL : Forall (w_lib ls OW PL lo SPv) (fpF1 K a D (bn_dmax b))).
    { unfold fpF1. constructor; [left; cbn [fst snd]; clear - LOK; lia|]. constructor; [w_lib_ref HA NRO|]. constructor; [| constructor].
      right; left. exists (p, D, 8 * Z.of_nat (bn_dmax b)). cbn [blk_addr blk_size fst snd]. split; [exact Hin| clear; lia]. }
    exists D, p. split; [exact Ed|]. split; [exact Hin|]. split; [exact BN|]. split; [exact U|]. split; [exact OKB|].
    split; [exact AS|]. split; [exact AD|]. split; [exact SEPd|].
    split.
    { intros m' MUc WMc. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MUc WMc HWL CEIL ltac:(clear - FBSP SPT; lia))|].
      exact (lib_state_frame Σ LB SPv USTACK_TOP [r] ls m m' OW PL EA _ HEAP LSH MUc WMc FROK WOK). }
    intros m' b' pre' MUc WMc RES U' ED EB OKB' STc MIc FR' FSZ'.
    assert (EDM : bn_dmax b' = bn_dmax b) by (unfold bn_dmax; exact EB).
    assert (LS' : lib_state (setbn r b' ls) m' OW PL EA).
    { unfold lib_state. eapply (lib_state_close [] ls m' OW PL EA r a); [| exact ND | exact HA | exact NRO | | |].
      - exact (lib_state_frame Σ LB SPv USTACK_TOP [r] ls m m' OW PL EA _ HEAP LSH MUc WMc FROK WOK).
      - exists D. split; [exact RES|]. unfold bn_arr. rewrite ED, Ed, EDM. split; [exact Hin| exact U'].
      - exact OKB'.
      - apply ids_ok_setbn_same; [exact (proj1 (proj2 (proj2 PARTS))) | exact HV | unfold bn_blocks; fold b; rewrite ED, EDM; reflexivity]. }
    split; [| exact LS'].
    apply cenv_setbnA; [| exact HV | unfold bn_blocks; fold b; rewrite ED, EDM; reflexivity].
    eapply cenv_silentA; [exact ENV | exact LS | exact MUc | exact WMc | exact HWL | exact STc | exact MIc | exact FR' | exact FSZ'].
  Qed.

  Lemma cenv_hole2F : forall pre used Σ ls m OW r1 a1 D1 p1 r2 a2 D2 p2 K,
    CENV pre used Σ ls m OW -> lib_state ls m OW PL EA -> r1 <> r2 ->
    ref_at ls OW PL r1 a1 -> r1 <> ROne -> bn_d (getbn r1 ls) = Some p1 -> In (p1, D1, 8 * Z.of_nat (bn_dmax (getbn r1 ls))) OW ->
    ref_at ls OW PL r2 a2 -> r2 <> ROne -> bn_d (getbn r2 ls) = Some p2 -> In (p2, D2, 8 * Z.of_nat (bn_dmax (getbn r2 ls))) OW ->
    0 <= K -> lo <= FB - K ->
    (forall m', munch (fpF2 K a1 D1 (bn_dmax (getbn r1 ls)) a2 D2 (bn_dmax (getbn r2 ls))) m m' -> wmono bgasegs m m' ->
        AHEAP Σ OW LB m' /\ lib_state_hc false [r1; r2] ls m' OW PL EA)
    /\ (forall m' b1' b2' pre',
        munch (fpF2 K a1 D1 (bn_dmax (getbn r1 ls)) a2 D2 (bn_dmax (getbn r2 ls))) m m' -> wmono bgasegs m m' ->
        rw_cells bgasegs m' a1 (BnRepDefs.bn_cells D1 b1') -> u64arr bgasegs m' D1 (wlimbs (bn_buf b1')) ->
        bn_d b1' = bn_d (getbn r1 ls) -> length (bn_buf b1') = length (bn_buf (getbn r1 ls)) -> bg_ok b1' ->
        rw_cells bgasegs m' a2 (BnRepDefs.bn_cells D2 b2') -> u64arr bgasegs m' D2 (wlimbs (bn_buf b2')) ->
        bn_d b2' = bn_d (getbn r2 ls) -> length (bn_buf b2') = length (bn_buf (getbn r2 ls)) -> bg_ok b2' ->
        stk bgasegs m' lo FB -> mem_inv bgasegs m' ->
        rw_cells bgasegs m' FB (pre' ++ [C8 s0w; C8 raw]) -> Z.of_nat (cells_size pre') = SPv - FB - 16 ->
        CENV pre' used Σ (setbn r2 b2' (setbn r1 b1' ls)) m' OW /\ lib_state (setbn r2 b2' (setbn r1 b1' ls)) m' OW PL EA).
  Proof using LOFB16.
    intros pre used Σ ls m OW r1 a1 D1 p1 r2 a2 D2 p2 K ENV LS NE12 HA1 NRO1 Ed1 Hin1 HA2 NRO2 Ed2 Hin2 K0 LOK.
    pose proof ENV as (OK & HEAP & _ & _ & AXP & CR & CNT & RS & FR & FSZ & UW). pose proof OK as (CEIL & LOFB & FBSP & SPT & _ & _ & _ & _ & FROK & FAL & NOFR).
    pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA1) as HV1. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA2) as HV2.
    destruct (lib_state_open [] ls m OW PL EA r2 a2 LS ND HA2 ltac:(intros []) NRO2) as (_ & _ & LSH2).
    destruct (lib_state_open [r2] ls m OW PL EA r1 a1 LSH2 ND HA1 ltac:(intros [E|[]]; apply NE12; symmetry; exact E) NRO1) as (_ & _ & LSH).
    set (b1 := getbn r1 ls) in *. set (b2 := getbn r2 ls) in *.
    assert (WOK : Forall (w_ok OW LB ls PL EA SPv [r1; r2]) (fpF2 K a1 D1 (bn_dmax b1) a2 D2 (bn_dmax b2))).
    { unfold fpF2. constructor; [apply w_stack; cbn [fst snd]; clear - CEIL LOK; lia|].
      constructor; [eapply (w_struct OW LB ls PL EA SPv false [r1; r2] _ r1 a1); [left; reflexivity| exact HA1| exact NRO1| cbn; clear; lia| cbn; clear; lia]|].
      constructor; [eapply (w_limbs OW LB ls PL EA SPv false [r1; r2] _ r1 p1 D1); [left; reflexivity| exact HV1| exact Ed1| exact Hin1| cbn [fst snd]; clear; lia| cbn [fst snd]; fold b1; clear; lia]|].
      constructor; [eapply (w_struct OW LB ls PL EA SPv false [r1; r2] _ r2 a2); [right; left; reflexivity| exact HA2| exact NRO2| cbn; clear; lia| cbn; clear; lia]|].
      constructor; [| constructor].
      eapply (w_limbs OW LB ls PL EA SPv false [r1; r2] _ r2 p2 D2); [right; left; reflexivity| exact HV2| exact Ed2| exact Hin2| cbn [fst snd]; clear; lia| cbn [fst snd]; fold b2; clear; lia]. }
    assert (HWL : Forall (w_lib ls OW PL lo SPv) (fpF2 K a1 D1 (bn_dmax b1) a2 D2 (bn_dmax b2))).
    { unfold fpF2. constructor; [left; cbn [fst snd]; clear - LOK; lia|].
      constructor; [w_lib_ref HA1 NRO1|].
      constructor; [right; left; exists (p1, D1, 8 * Z.of_nat (bn_dmax b1)); cbn [blk_addr blk_size fst snd]; split; [exact Hin1| clear; lia]|].
      constructor; [w_lib_ref HA2 NRO2|].
      constructor; [| constructor]. right; left. exists (p2, D2, 8 * Z.of_nat (bn_dmax b2)). cbn [blk_addr blk_size fst snd]. split; [exact Hin2| clear; lia]. }
    split.
    - intros m' MUc WMc. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MUc WMc HWL CEIL ltac:(clear - FBSP SPT; lia))|].
      exact (lib_state_frame Σ LB SPv USTACK_TOP [r1; r2] ls m m' OW PL EA _ HEAP LSH MUc WMc FROK WOK).
    - intros m' b1' b2' pre' MUc WMc BN1 U1 Ed1' EL1 OK1 BN2 U2 Ed2' EL2 OK2 STc MIc FR' FSZ'.
      assert (EDM1 : bn_dmax b1' = bn_dmax b1) by (unfold bn_dmax; exact EL1).
      assert (EDM2 : bn_dmax b2' = bn_dmax b2) by (unfold bn_dmax; exact EL2).
      pose proof (lib_state_frame Σ LB SPv USTACK_TOP [r1; r2] ls m m' OW PL EA _ HEAP LSH MUc WMc FROK WOK) as LSH'.
      assert (IDS1 : ids_ok (setbn r1 b1' ls) PL EA).
      { apply ids_ok_setbn_same; [exact (proj1 (proj2 (proj2 PARTS))) | exact HV1 |]. unfold bn_blocks. fold b1. rewrite Ed1', EDM1. reflexivity. }
      assert (LS1 : lib_state_hc false [r2] (setbn r1 b1' ls) m' OW PL EA).
      { eapply (lib_state_close [r2] ls m' OW PL EA r1 a1); [exact LSH'| exact ND | exact HA1 | exact NRO1 | | exact OK1 | exact IDS1].
        exists D1. split; [exact BN1|]. unfold bn_arr. fold b1. rewrite Ed1', Ed1, EDM1. split; [exact Hin1| exact U1]. }
      assert (HA2' : ref_at (setbn r1 b1' ls) OW PL r2 a2) by (apply ref_at_setbn; exact HA2).
      assert (HV2' : vref r2 (setbn r1 b1' ls)) by (eapply ref_at_valid; [exact LS1| exact HA2']).
      assert (G2 : getbn r2 (setbn r1 b1' ls) = b2) by (apply getbn_setbn_other; exact NE12).
      assert (LS' : lib_state (setbn r2 b2' (setbn r1 b1' ls)) m' OW PL EA).
      { unfold lib_state. eapply (lib_state_close [] (setbn r1 b1' ls) m' OW PL EA r2 a2); [exact LS1| exact ND | exact HA2' | exact NRO2 | | exact OK2 |].
        - exists D2. split; [exact BN2|]. unfold bn_arr. fold b2. rewrite Ed2', Ed2, EDM2. split; [exact Hin2| exact U2].
        - apply ids_ok_setbn_same; [exact IDS1 | exact HV2' |]. rewrite G2. unfold bn_blocks. fold b2. rewrite Ed2', EDM2. reflexivity. }
      split; [| exact LS'].
      apply cenv_setbnA; [| exact HV2' | rewrite G2; unfold bn_blocks; fold b2; rewrite Ed2', EDM2; reflexivity].
      apply cenv_setbnA; [| exact HV1 | unfold bn_blocks; fold b1; rewrite Ed1', EDM1; reflexivity].
      eapply cenv_silentA; [exact ENV | exact LS | exact MUc | exact WMc | exact HWL | exact STc | exact MIc | exact FR' | exact FSZ'].
  Qed.

End Kit.
End WithRT.
