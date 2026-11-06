(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge Arr. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout RT_iface D_defs.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnMem.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA AsStruct.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma arr_ubA : forall Σ OW LB m D (b : bignum bptr),
  AHEAP Σ OW LB m -> BnRepDefs.bn_arr m OW D b -> (0 < bn_dmax b)%nat -> 0 < D /\ D mod 16 = 0.
Proof.
  intros Σ OW LB m D b HEAP ARR HD. unfold BnRepDefs.bn_arr in ARR. destruct (bn_d b) as [p|] eqn:Ed.
  - destruct ARR as [Hin _]. pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (R0 & R16 & _). split; assumption.
  - destruct ARR as [_ Eb]. unfold bn_dmax in HD. rewrite Eb in HD. cbn in HD. lia.
Qed.

Lemma arr_ub_okA : forall Σ OW LB m D (b : bignum bptr) n,
  AHEAP Σ OW LB m -> BnRepDefs.bn_arr m OW D b -> n <= Z.of_nat (bn_dmax b) -> ub_ptr_ok n D.
Proof.
  intros Σ OW LB m D b n HEAP ARR Hn Hpos.
  destruct (arr_ubA Σ OW LB m D b HEAP ARR ltac:(lia)) as (H0 & H16). split; [exact H0|]. clear - H16. Z.div_mod_to_equations. lia.
Qed.

Lemma bn_arr_ub : forall Σ OW LB m ls PL EA SPX r D n,
  AHEAP Σ OW LB m -> lib_parts ls OW PL EA -> frames_ok LB PL SPX USTACK_TOP -> frames_al PL -> vref r ls -> not_one r ->
  bn_arr m OW (pl_of PL r) D (getbn r ls) -> n <= Z.of_nat (bn_dmax (getbn r ls)) -> ub_ptr_ok n D.
Proof.
  intros Σ OW LB m ls PL EA SPX r D n HEAP PARTS FROK FAL HV NRO ARR Hn Hpos.
  destruct (bn_arr_blk Σ OW LB m PL SPX USTACK_TOP r D (getbn r ls) HEAP (proj1 (proj2 PARTS)) FROK NRO ARR ltac:(lia)) as (_ & _ & _ & _ & P0 & _).
  destruct (bn_arr_sh Σ OW LB m ls PL EA SPX USTACK_TOP r D HEAP PARTS FROK FAL HV NRO ARR) as (_ & AL & _).
  split; [exact P0 | exact AL].
Qed.

Lemma open_ro_shu : forall Σ OW LB m ls PL EA SPX r a,
  AHEAP Σ OW LB m -> lib_state ls m OW PL EA -> frames_ok LB PL SPX USTACK_TOP -> frames_lb PL LB -> ref_at ls OW PL r a -> not_one r ->
  exists D, rw_cells bgbsegs m a (bn_cells D (getbn r ls)) /\ bg_ok (getbn r ls)
    /\ u64arr bgbsegs m D (wlimbs (bn_buf (getbn r ls)))
    /\ 0 < a /\ a + 24 <= ACEIL /\ 0 <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= ACEIL
    /\ acc bgbsegs m a 24 /\ a mod 8 = 0
    /\ acc bgbsegs m D (8 * Z.of_nat (bn_top (getbn r ls))) /\ D mod 8 = 0
    /\ ub_ptr_ok (Z.of_nat (bn_top (getbn r ls))) D /\ ub_ptr_ok (Z.of_nat (bn_dmax (getbn r ls))) D.
Proof.
  intros Σ OW LB m ls PL EA SPX r a HEAP LS FROK NOFR HA NRO.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_open [] ls m OW PL EA r a LS ND HA ltac:(intros []) NRO) as ((D & SA & ARR) & OK & _).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  destruct (ref_at_rangeF ls OW PL EA SPX USTACK_TOP Σ LB m r a HEAP PARTS FROK HA NRO) as (A0 & AC & _).
  destruct (bn_arr_facts_lin Σ OW LB m HEAP ls PL EA _ _ PARTS FROK r D HV NRO ARR) as (U & _ & D0 & DC & _ & _).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HA NRO) as (ACS & ALS & _).
  destruct (bn_arr_sh Σ OW LB m ls PL EA SPX USTACK_TOP r D HEAP PARTS FROK (proj2 NOFR) HV NRO ARR) as (ACD & ALD & _).
  pose proof OK as (_ & TD & _).
  exists D. do 7 (split; [assumption|]). split; [exact ACS|]. split; [exact ALS|].
  split; [eapply acc_sub; [exact ACD | lia | unfold bn_dmax in *; lia]|]. split; [exact ALD|].
  split; [apply (bn_arr_ub Σ OW LB m ls PL EA SPX r D _ HEAP PARTS FROK (proj2 NOFR) HV NRO ARR); unfold bn_dmax in *; lia
         | apply (bn_arr_ub Σ OW LB m ls PL EA SPX r D _ HEAP PARTS FROK (proj2 NOFR) HV NRO ARR); lia].
Qed.

Lemma ref_ubA : forall Σ OW LB m ls PL EA r a,
  AHEAP Σ OW LB m -> lib_state ls m OW PL EA -> frames_lb PL LB -> ref_at ls OW PL r a -> not_one r -> 0 < a /\ a mod 8 = 0 /\ a + 24 <= ACEIL.
Proof.
  intros Σ OW LB m ls PL EA r a HEAP LS NOFR HA NRO.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP PARTS NOFR HA NRO) as (q & A & n & Hin & R1 & R2).
  pose proof (AH_range_in _ _ _ _ _ _ _ HEAP Hin) as (A0 & _ & _ & AC & _).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HA NRO) as (_ & AL & _).
  split; [lia |]. split; [exact AL | lia].
Qed.

Lemma operand_view_shu : forall Σ OW LB m ls PL EA SPX rr R Dr x X k,
  AHEAP Σ OW LB m -> lib_state ls m OW PL EA -> frames_ok LB PL SPX USTACK_TOP -> frames_lb PL LB ->
  ref_at ls OW PL rr R -> not_one rr -> rw_cells bgbsegs m R (bn_cells Dr (getbn rr ls)) -> BnRepDefs.bn_arr m OW Dr (getbn rr ls) ->
  ref_at ls OW PL x X -> not_one x -> (k <= bn_top (getbn x ls))%nat ->
  exists Dx, (acc bgbsegs m Dx (8 * Z.of_nat k) /\ Dx mod 8 = 0) /\ rw_cells bgbsegs m X [C8 (wz Dx)] /\ limbs_at bgbsegs m Dx (firstn k (bn_buf (getbn x ls)))
    /\ 0 < X /\ X + 24 <= ACEIL /\ 0 <= Dx /\ Dx + 8 * Z.of_nat k <= ACEIL
    /\ (X = R \/ X + 24 <= R \/ R + 24 <= X)
    /\ (R + 24 <= Dx \/ Dx + 8 * Z.of_nat k <= R)
    /\ (Dx = Dr \/ Dr + 8 * Z.of_nat (bn_dmax (getbn rr ls)) <= Dx \/ Dx + 8 * Z.of_nat k <= Dr)
    /\ ub_ptr_ok (Z.of_nat k) Dx.
Proof.
  intros Σ OW LB m ls PL EA SPX rr R Dr x X k HEAP LS FROK NOFR HR NRR SR ARR HX NRX Hk.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX.
  destruct (arr0_facts Σ OW LB m ls PL EA SPX rr Dr HEAP PARTS FROK HVR ARR) as (UR & DR0 & DRC' & DSEPR).
  pose proof (st_wf_ok x ls WFS HVX NRX) as (_ & TDX & _).
  destruct (Nat.eq_dec x rr) as [->|NE].
  -
    pose proof (ref_at_fun _ _ _ _ _ _ ND HX HR) as ->.
    destruct (ref_at_rangeF ls OW PL EA SPX USTACK_TOP Σ LB m rr R HEAP PARTS FROK HR NRR) as (SA0 & SAC & _).
    exists Dr. split.
    { destruct (arr_shA _ _ _ _ _ _ HEAP ARR) as (ACD & ALD & _). split; [eapply acc_sub; [exact ACD | lia | unfold bn_dmax in *; lia] | exact ALD]. }
    unfold bn_cells in SR.
    change [C8 (wz Dr); C4 (wz (Z.of_nat (bn_top (getbn rr ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn rr ls))));
            C4 (wz (Z.b2z (bn_neg (getbn rr ls)))); C4 (wz (bn_flags (getbn rr ls)))]
      with ([C8 (wz Dr)] ++ [C4 (wz (Z.of_nat (bn_top (getbn rr ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn rr ls))));
            C4 (wz (Z.b2z (bn_neg (getbn rr ls)))); C4 (wz (bn_flags (getbn rr ls)))]) in SR.
    apply bk_rw_cells_app in SR. destruct SR as [SR1 _].
    split; [exact SR1|]. split; [apply limbs_at_firstn; exact UR|].
    specialize (DSEPR rr R HR NRR).
    assert (UBK : ub_ptr_ok (Z.of_nat k) Dr) by (apply (arr_ub_okA Σ OW LB m Dr (getbn rr ls) _ HEAP ARR); unfold bn_dmax in *; lia).
    unfold bn_dmax in *. repeat (split; [lia|]). exact UBK.
  - destruct (lib_state_open [] ls m OW PL EA x X LS ND HX ltac:(intros []) NRX) as ((Dx & SX & ARRX) & _ & _).
    destruct (bn_arr_facts_lin Σ OW LB m HEAP ls PL EA _ _ PARTS FROK x Dx HVX NRX ARRX) as (UX & LENX & DX0 & DXC' & _ & DSEPX).
    destruct (ref_at_rangeF ls OW PL EA SPX USTACK_TOP Σ LB m x X HEAP PARTS FROK HX NRX) as (SA0 & SAC & _).
    exists Dx. split.
    { destruct (bn_arr_sh Σ OW LB m ls PL EA SPX USTACK_TOP x Dx HEAP PARTS FROK (proj2 NOFR) HVX NRX ARRX) as (ACD & ALD & _). split; [eapply acc_sub; [exact ACD | lia | unfold bn_dmax in *; lia] | exact ALD]. }
    unfold bn_cells in SX.
    change [C8 (wz Dx); C4 (wz (Z.of_nat (bn_top (getbn x ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn x ls))));
            C4 (wz (Z.b2z (bn_neg (getbn x ls)))); C4 (wz (bn_flags (getbn x ls)))]
      with ([C8 (wz Dx)] ++ [C4 (wz (Z.of_nat (bn_top (getbn x ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn x ls))));
            C4 (wz (Z.b2z (bn_neg (getbn x ls)))); C4 (wz (bn_flags (getbn x ls)))]) in SX.
    apply bk_rw_cells_app in SX. destruct SX as [SX1 _].
    split; [exact SX1|]. split; [apply limbs_at_firstn; exact UX|].
    pose proof (struct_disj Σ OW LB m HEAP ls PL EA _ _ PARTS FROK x rr X R NE HX HR) as SD.
    specialize (DSEPX rr R HR). specialize (DSEPR x X HX NRX).
    pose proof (arr_arr0_disj Σ OW LB m ls PL EA SPX x rr Dx Dr HEAP PARTS FROK NE HVX HVR NRX ARRX ARR) as AD3.
    assert (UBK : ub_ptr_ok (Z.of_nat k) Dx) by (apply (bn_arr_ub Σ OW LB m ls PL EA SPX x Dx _ HEAP PARTS FROK (proj2 NOFR) HVX NRX ARRX); unfold bn_dmax in *; lia).
    unfold bn_dmax in *. repeat (split; [lia|]). exact UBK.
Qed.

End WithRT.
