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
From OSSVerify.Proofs.openssl.bndiv.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnModel BnTree BnInv BnSpecs BnMInv BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.U Require Import Layout Lib_iface Lib_kit.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnMem BnTacX.
From OSSVerify.Proofs.openssl.bndiv.lib.BnWU Require Import BnUTac.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bndiv.lib.BnU Require Import BnHeap BnRep BnIface BnUAlign.
From OSSVerify.Proofs.openssl.bndiv.lib.BnAU Require Import BnAKit.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma bn_arr_ualign : forall s OW LB m D (b : bignum bptr) n,
  RHEAP s (OW ++ LB) m -> bn_arr m OW D b -> (n <= bn_dmax b)%nat -> ub_ptr_ok (Z.of_nat n) D.
Proof.
  intros s OW LB m D b n HEAP ARR Hn Hpos. unfold bn_arr in ARR. destruct (bn_d b) as [p|].
  - destruct ARR as (Hin & _). exact (block_ualign _ _ _ _ _ _ _ HEAP Hin).
  - destruct ARR as (_ & E). unfold bn_dmax in Hn. rewrite E in Hn. cbn [length] in Hn. lia.
Qed.

Lemma open_ro_u : forall s OW LB m ls AD EA r a,
  RHEAP s (OW ++ LB) m -> lib_state ls m OW AD EA -> ref_at ls OW AD r a ->
  exists D, rw_cells usegs m a (bn_cells D (getbn r ls)) /\ bn_okm (getbn r ls)
    /\ u64arr usegs m D (wlimbs (bn_buf (getbn r ls)))
    /\ 0 < a /\ a + 24 <= alloc_ceiling /\ 0 <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= alloc_ceiling
    /\ hide (a mod 8 = 0) /\ ub_ptr_ok (Z.of_nat (bn_top (getbn r ls))) D.
Proof.
  intros s OW LB m ls AD EA r a HEAP LS HA.
  pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_open [] ls m OW AD EA r a LS ND HA ltac:(intros [])) as ((D & BN & ARR) & OK & _).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  destruct (ref_at_inb _ _ _ _ _ ADB HA) as (qs & As & ns & Eqs & Hins & Ra1 & Ra2).
  pose proof (RH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & SA16 & _ & SAC & SAI).
  destruct (bn_arr_facts s OW LB m HEAP ls AD EA IDS ADB r D HV ARR) as (U & LENW & D0 & DC & DI & DSEP).
  destruct (ref_at_ualign s OW LB m ls AD r a HEAP ADB HA) as (_ & AL).
  exists D. split; [exact BN|]. split; [exact OK|]. split; [exact U|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [apply hide_intro; exact AL|].
  destruct OK as (_ & TD & _). exact (bn_arr_ualign s OW LB m D _ _ HEAP ARR TD).
Qed.

(* [comment removed for export] *)
Lemma operand_view_u : forall s OW LB m ls AD EA rr R Dr x X k,
  RHEAP s (OW ++ LB) m -> lib_state ls m OW AD EA ->
  ref_at ls OW AD rr R -> rw_cells usegs m R (bn_cells Dr (getbn rr ls)) -> bn_arr m OW Dr (getbn rr ls) ->
  ref_at ls OW AD x X -> (k <= bn_top (getbn x ls))%nat ->
  exists Dx, rw_cells usegs m X [C8 (wz Dx)] /\ limbs_at usegs m Dx (firstn k (bn_buf (getbn x ls)))
    /\ 0 < X /\ X + 24 <= alloc_ceiling /\ 0 <= Dx /\ Dx + 8 * Z.of_nat k <= alloc_ceiling
    /\ (X = R \/ X + 24 <= R \/ R + 24 <= X)
    /\ (R + 24 <= Dx \/ Dx + 8 * Z.of_nat k <= R)
    /\ (Dx = Dr \/ Dr + 8 * Z.of_nat (bn_dmax (getbn rr ls)) <= Dx \/ Dx + 8 * Z.of_nat k <= Dr)
    /\ ub_ptr_ok (Z.of_nat k) Dx /\ hide (X mod 8 = 0).
Proof.
  intros s OW LB m ls AD EA rr R Dr x X k HEAP LS HR SR ARR HX Hk.
  pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX.
  destruct (bn_arr_facts s OW LB m HEAP ls AD EA IDS ADB rr Dr HVR ARR) as (UR & LENR & DR0 & DRC & _ & DSEPR).
  pose proof (st_okm_getbn x ls SOK HVX) as (_ & TDX & _).
  destruct (bnref_eq_dec x rr) as [->|NE].
  - (* [comment removed for export] *)
    pose proof (ref_at_fun _ _ _ _ _ _ ND HX HR) as ->.
    destruct (ref_at_inb _ _ _ _ _ ADB HR) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & _).
    assert (UPX : ub_ptr_ok (Z.of_nat k) Dr) by (apply (bn_arr_ualign s OW LB m Dr _ k HEAP ARR); lia).
    assert (ALX : hide (R mod 8 = 0)) by (apply hide_intro; exact (proj2 (ref_at_ualign s OW LB m ls AD rr R HEAP ADB HR))).
    exists Dr. unfold bn_cells in SR.
    change [C8 (wz Dr); C4 (wz (Z.of_nat (bn_top (getbn rr ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn rr ls))));
            C4 (wz (Z.b2z (bn_neg (getbn rr ls)))); C4 (wz (bn_flags (getbn rr ls)))]
      with ([C8 (wz Dr)] ++ [C4 (wz (Z.of_nat (bn_top (getbn rr ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn rr ls))));
            C4 (wz (Z.b2z (bn_neg (getbn rr ls)))); C4 (wz (bn_flags (getbn rr ls)))]) in SR.
    apply bk_rw_cells_app in SR. destruct SR as [SR1 _].
    split; [exact SR1|]. split; [apply limbs_at_firstn; exact UR|].
    specialize (DSEPR rr R HR). unfold bn_dmax in *.
    repeat (split; [lia|]). split; [exact UPX | exact ALX].
  - destruct (lib_state_open [] ls m OW AD EA x X LS ND HX ltac:(intros [])) as ((Dx & SX & ARRX) & _ & _).
    destruct (bn_arr_facts s OW LB m HEAP ls AD EA IDS ADB x Dx HVX ARRX) as (UX & LENX & DX0 & DXC & _ & DSEPX).
    destruct (ref_at_inb _ _ _ _ _ ADB HX) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & _).
    assert (UPX : ub_ptr_ok (Z.of_nat k) Dx) by (apply (bn_arr_ualign s OW LB m Dx _ k HEAP ARRX); lia).
    assert (ALX : hide (X mod 8 = 0)) by (apply hide_intro; exact (proj2 (ref_at_ualign s OW LB m ls AD x X HEAP ADB HX))).
    exists Dx. unfold bn_cells in SX.
    change [C8 (wz Dx); C4 (wz (Z.of_nat (bn_top (getbn x ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn x ls))));
            C4 (wz (Z.b2z (bn_neg (getbn x ls)))); C4 (wz (bn_flags (getbn x ls)))]
      with ([C8 (wz Dx)] ++ [C4 (wz (Z.of_nat (bn_top (getbn x ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn x ls))));
            C4 (wz (Z.b2z (bn_neg (getbn x ls)))); C4 (wz (bn_flags (getbn x ls)))]) in SX.
    apply bk_rw_cells_app in SX. destruct SX as [SX1 _].
    split; [exact SX1|]. split; [apply limbs_at_firstn; exact UX|].
    pose proof (struct_disj s OW LB m HEAP ls AD EA IDS ADB x rr X R NE HX HR) as SD.
    specialize (DSEPX rr R HR).
    assert (AD3 : Dx = Dr \/ Dr + 8 * Z.of_nat (bn_dmax (getbn rr ls)) <= Dx \/ Dx + 8 * Z.of_nat k <= Dr).
    { unfold bn_arr in ARR, ARRX.
      destruct (bn_d (getbn x ls)) as [px|] eqn:Edx, (bn_d (getbn rr ls)) as [pr|] eqn:Edr.
      - destruct ARR as [HinR _], ARRX as [HinX _].
        pose proof (limbs_limbs_disj s OW LB m HEAP ls AD EA IDS x rr px Dx _ pr Dr _ NE HVX HVR Edx Edr HinX HinR) as LD.
        unfold bn_dmax in *. lia.
      - destruct ARR as [-> Eb]. unfold bn_dmax. rewrite Eb. cbn [length]. lia.
      - destruct ARRX as [-> Eb]. unfold bn_dmax in TDX. rewrite Eb in TDX. cbn [length] in TDX. lia.
      - destruct ARR as [-> Eb]. unfold bn_dmax. rewrite Eb. cbn [length]. lia. }
    unfold bn_dmax in *.
    repeat (split; [lia|]). split; [exact UPX | exact ALX].
Qed.

End WithCeiling0.
