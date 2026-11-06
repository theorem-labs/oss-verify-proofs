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
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import BnAKitAF BnCallAF W_callsAF W_calls3AF AFrameKit AFrameEnv ExpKitAF InvKitAF.
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

  Definition fpw1A (a D : Z) (d : nat) : list (Z * Z) := [(a, a + 24); (D, D + 8 * Z.of_nat d)].

  Lemma cenv_hole1A : forall pre used Σ ls m OW r a,
    CENV pre used Σ ls m OW -> lib_state ls m OW PL EA -> ref_at ls OW PL r a -> wref PL r -> (0 < bn_dmax (getbn r ls))%nat ->
    exists D p, bn_d (getbn r ls) = Some p /\ In (p, D, 8 * Z.of_nat (bn_dmax (getbn r ls))) OW
      /\ rw_cells bgasegs m a (BnRepDefs.bn_cells D (getbn r ls)) /\ u64arr bgasegs m D (wlimbs (bn_buf (getbn r ls))) /\ bg_ok (getbn r ls)
      /\ (acc bgasegs m a 24 /\ a mod 8 = 0 /\ 0 < a /\ a + 24 <= FB - 16 /\ (a + 24 <= SHLO \/ SHHI <= a))
      /\ (acc bgasegs m D (8 * Z.of_nat (bn_dmax (getbn r ls))) /\ D mod 8 = 0 /\ 0 <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= FB - 16
          /\ (D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= SHLO \/ SHHI <= D))
      /\ (forall r' a', ref_at ls OW PL r' a' -> a' + 24 <= D \/ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= a')
      /\ (forall r' a' D', r <> r' -> ref_at ls OW PL r' a' -> r' <> ROne -> bn_arr m OW (pl_of PL r') D' (getbn r' ls) ->
            D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= D' \/ D' + 8 * Z.of_nat (bn_dmax (getbn r' ls)) <= D)
      /\ stk bgasegs m lo FB /\ mem_inv bgasegs m
      /\ forall m' b',
           munch (fpw1A a D (bn_dmax (getbn r ls))) m m' -> wmono bgasegs m m' ->
           rw_cells bgasegs m' a (BnRepDefs.bn_cells D b') -> u64arr bgasegs m' D (wlimbs (bn_buf b')) ->
           bn_d b' = bn_d (getbn r ls) -> length (bn_buf b') = length (bn_buf (getbn r ls)) -> bg_ok b' ->
           stk bgasegs m' lo FB -> mem_inv bgasegs m' ->
           CENV pre used Σ (setbn r b' ls) m' OW /\ lib_state (setbn r b' ls) m' OW PL EA.
  Proof using LOFB16.
    intros pre used Σ ls m OW r a ENV LS HA WR HD.
    pose proof (proj1 WR : not_one r) as NRO.
    destruct (open_for_call LB PL EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 LOFB16 _ _ _ _ _ _ _ _ ENV LS HA NRO)
      as (D0 & _ & _ & ESP & ST & MI & SEP & SHBC & ACC & AL & SLO & OFR & A0).
    pose proof ENV as (OK & HEAP & _ & _ & AXP & CR & CNT & RS & FR & FSZ & UW). pose proof OK as (CEIL & LOFB & FBSP & SPT & _ & _ & _ & _ & FROK & FAL & NOFR).
    pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    destruct (lib_state_open [] ls m OW PL EA r a LS ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & OKB & LSH).
    set (b := getbn r ls) in *.
    destruct (bn_arr_facts_w ls OW PL EA SPv USTACK_TOP Σ LB m r D HEAP PARTS FROK HV WR ARR) as (U & _ & DD0 & DC & DI & SEPd). fold b in U, DC, DI, SEPd.
    destruct (bn_arr_sh Σ OW LB m ls PL EA SPv USTACK_TOP r D HEAP PARTS FROK FAL HV NRO ARR) as (ACD & ALD & OFD). fold b in ACD, OFD.
    assert (HDp : exists p, bn_d b = Some p /\ In (p, D, 8 * Z.of_nat (bn_dmax b)) OW).
    { pose proof ARR as ARR'. unfold bn_arr in ARR'. fold b in ARR'. destruct (bn_d b) as [p|] eqn:Ed; [exists p; split; [reflexivity| exact (proj1 ARR')]|].
      exfalso. destruct (bn_arr_null PL r m OW D b (proj1 (proj2 PARTS)) WR Ed ARR) as [_ Eb]. unfold bn_dmax in HD. rewrite Eb in HD. cbn [length] in HD. clear - HD. lia. }
    destruct HDp as (p & Ed & Hin).
    exists D, p. split; [exact Ed|]. split; [exact Hin|]. split; [exact BN|]. split; [exact U|]. split; [exact OKB|].
    split; [split; [exact ACC|]; split; [exact AL|]; split; [exact A0|]; split; [exact SEP| exact OFR]|].
    split; [split; [exact ACD|]; split; [exact ALD|]; split; [exact DD0|]; split; [unfold BnHeapA.ACEIL in *; clear - DC CEIL LOFB16; lia| exact OFD]|].
    split; [exact SEPd|].
    split. { intros r' a' D' NE HA' NRO' ARR'. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA') as HV'.
             exact (arr_arr_disj ls OW PL EA SPv USTACK_TOP Σ LB m r r' p D D' HEAP PARTS FROK NE HV HV' NRO' Ed Hin ARR'). }
    split; [exact ST|]. split; [exact MI|].
    intros m' b' MUc WMc RES U' ED EB OKB' STc MIc. unfold fpw1A in MUc.
    pose proof (SEPd r a HA) as SEPr.
    eapply (rw_cells_transport bgasegs _ m m') in FR; [| exact MUc | exact WMc
      | cbn [disjoint_from]; split; [right; clear - SEP LOFB16; lia|]; split; [right; unfold BnHeapA.ACEIL in *; clear - DC CEIL LOFB; lia| exact I]].
    assert (WOK : Forall (w_ok OW LB ls PL EA SPv [r]) [(a, a + 24); (D, D + 8 * Z.of_nat (bn_dmax b))]).
    { constructor; [eapply (w_struct OW LB ls PL EA SPv false [r] _ r a); [left; reflexivity| exact HA| exact NRO| cbn; clear; lia| cbn; clear; lia]|].
      constructor; [| constructor].
      eapply (w_limbs OW LB ls PL EA SPv false [r] _ r p D); [left; reflexivity| exact HV| exact Ed| exact Hin| cbn [fst snd]; clear; lia| cbn [fst snd]; fold b; clear; lia]. }
    assert (HWL : Forall (w_lib ls OW PL lo SPv) [(a, a + 24); (D, D + 8 * Z.of_nat (bn_dmax b))]).
    { constructor; [w_lib_ref HA NRO|]. constructor; [| constructor].
      right; left. exists (p, D, 8 * Z.of_nat (bn_dmax b)). cbn [blk_addr blk_size fst snd]. split; [exact Hin| clear; lia]. }
    assert (EDM : bn_dmax b' = bn_dmax b) by (unfold bn_dmax; exact EB).
    assert (LS' : lib_state (setbn r b' ls) m' OW PL EA).
    { unfold lib_state. eapply (lib_state_close [] ls m' OW PL EA r a); [| exact ND | exact HA | exact NRO | | |].
      - exact (lib_state_frame Σ LB SPv USTACK_TOP [r] ls m m' OW PL EA _ HEAP LSH MUc WMc FROK WOK).
      - exists D. split; [exact RES|]. unfold bn_arr. rewrite ED, Ed, EDM. split; [exact Hin| exact U'].
      - exact OKB'.
      - apply ids_ok_setbn_same; [exact (proj1 (proj2 (proj2 PARTS))) | exact HV | unfold bn_blocks; fold b; rewrite ED, EDM; reflexivity]. }
    split; [| exact LS'].
    apply cenv_setbnA; [| exact HV | unfold bn_blocks; fold b; rewrite ED, EDM; reflexivity].
    eapply cenv_silentA; [exact ENV | exact LS | exact MUc | exact WMc | exact HWL | exact STc | exact MIc | exact FR | exact FSZ].
  Qed.

  Lemma cenv_read_roA : forall pre used Σ ls m OW n an,
    CENV pre used Σ ls m OW -> lib_state ls m OW PL EA -> ref_at ls OW PL n an -> n <> ROne ->
    exists Dn, rw_cells bgasegs m an (BnRepDefs.bn_cells Dn (getbn n ls)) /\ u64arr bgasegs m Dn (wlimbs (bn_buf (getbn n ls))) /\ bg_ok (getbn n ls)
      /\ (acc bgasegs m an 24 /\ an mod 8 = 0 /\ 0 < an /\ an + 24 <= FB - 16)
      /\ (acc bgasegs m Dn (8 * Z.of_nat (bn_dmax (getbn n ls))) /\ Dn mod 8 = 0 /\ 0 <= Dn /\ Dn + 8 * Z.of_nat (bn_dmax (getbn n ls)) <= FB - 16)
      /\ (forall r a, ref_at ls OW PL r a -> a + 24 <= Dn \/ Dn + 8 * Z.of_nat (bn_dmax (getbn n ls)) <= a)
      /\ (forall r p D, r <> n -> vref r ls -> bn_d (getbn r ls) = Some p -> In (p, D, 8 * Z.of_nat (bn_dmax (getbn r ls))) OW ->
            D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= Dn \/ Dn + 8 * Z.of_nat (bn_dmax (getbn n ls)) <= D).
  Proof using LOFB16.
    intros pre used Σ ls m OW n an ENV LS HA NRO.
    pose proof ENV as (OK & HEAP & _). pose proof OK as (CEIL & LOFB & FBSP & SPT & _ & _ & _ & _ & FROK & FAL & NOFR).
    pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    destruct (lib_state_open [] ls m OW PL EA n an LS ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & OKB & _).
    destruct (ref_at_rangeF ls OW PL EA SPv USTACK_TOP Σ LB m n an HEAP PARTS FROK HA NRO) as (A0 & AC & _).
    destruct (bn_arr_facts_lin Σ OW LB m HEAP ls PL EA _ _ PARTS FROK n D HV NRO ARR) as (U & _ & D0 & DC & _ & DSEP).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HA NRO) as (ACS & ALS & _).
    destruct (bn_arr_sh Σ OW LB m ls PL EA SPv USTACK_TOP n D HEAP PARTS FROK FAL HV NRO ARR) as (ACD & ALD & _).
    exists D. split; [exact BN|]. split; [exact U|]. split; [exact OKB|].
    split; [split; [exact ACS|]; split; [exact ALS|]; split; [exact A0|]; unfold BnHeapA.ACEIL in *; clear - AC CEIL LOFB16; lia|].
    split; [split; [exact ACD|]; split; [exact ALD|]; split; [exact D0|]; unfold BnHeapA.ACEIL in *; clear - DC CEIL LOFB16; lia|].
    split; [exact DSEP|].
    intros r p Dr NE HVr Edr Hinr.
    exact (arr_arr_disj ls OW PL EA SPv USTACK_TOP Σ LB m r n p Dr D HEAP PARTS FROK NE HVr HV NRO Edr Hinr ARR).
  Qed.

End Kit.
End WithRT.
