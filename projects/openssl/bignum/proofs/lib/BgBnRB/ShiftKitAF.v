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
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitAF W_expandAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Definition shift_res (rr : bnref) (ls : bstate bptr) (OW : list block) (PL : placement) : unit -> bstate bptr -> list block -> placement -> word -> Prop :=
  fun _ ls' OW' PL' a0' => PL' = PL /\ a0' = wz 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rr ls) <> Some q -> In (q, A, n) OW').

Lemma wexpand_keeps_topA : forall r words (ls ls' : bstate bptr) x, wexpand_res r words ls ls' -> vref r ls -> bn_top (getbn x ls') = bn_top (getbn x ls).
Proof.
  intros r words ls ls' x [[_ ->]|[_ [pn ->]]] HV; [reflexivity|].
  destruct (Nat.eq_dec r x) as [->|NE]; [rewrite getbn_setbn_same by exact HV; reflexivity | rewrite getbn_setbn_other by exact NE; reflexivity].
Qed.

Lemma bn_arr_base8A : forall s OW LB m st PL EA SPX BX r D,
  AHEAP s OW LB m -> lib_parts st OW PL EA -> frames_ok LB PL SPX BX -> frames_lb PL LB -> r <> ROne ->
  bn_arr m OW (pl_of PL r) D (getbn r st) -> (0 < length (bn_buf (getbn r st)))%nat -> 8 <= D.
Proof.
  intros s OW LB m st PL EA SPX BX r D HEAP PARTS FROK NOFR NRO ARR HL. pose proof PARTS as (_ & PWF & _).
  destruct (bn_arr_blk s OW LB m PL SPX BX r D (getbn r st) HEAP PWF FROK NRO ARR ltac:(unfold bn_dmax; exact HL)) as (_ & _ & _ & _ & P0 & _).
  assert (AL : D mod 8 = 0).
  { pose proof ARR as ARR'. unfold bn_arr in ARR'. destruct (bn_d (getbn r st)) as [p|] eqn:Ed.
    - destruct ARR' as [Hin _]. pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (_ & P16 & _). clear - P16. Z.div_mod_to_equations. lia.
    - destruct (pl_of PL r) as [[x q off|x|x d|x]|] eqn:Ep; try (exfalso; destruct ARR' as [_ Eb]; rewrite Eb in HL; cbn in HL; lia).
      + destruct ARR' as (-> & _ & _). apply (proj2 NOFR (d, d + TMOD_BUF_SZ)).
        destruct (pl_of_cases PL r _ Ep) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [contradiction| discriminate E'|].
        apply pl_frames_In. left. exists r. rewrite Eb. split; [exact (proj1 S)| right; left; reflexivity].
      + exfalso. destruct (pl_of_cases PL r _ Ep) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [contradiction| discriminate E'|].
        exact (proj2 (proj2 (proj2 (proj1 PWF r _ Eb)))). }
  clear - P0 AL. Z.div_mod_to_equations. lia.
Qed.

Lemma operand_cellsA : forall s OW LB m st PL EA SPX BX rr R Dr x X k,
  AHEAP s OW LB m -> lib_state st m OW PL EA -> frames_ok LB PL SPX BX -> frames_lb PL LB ->
  ref_at st OW PL rr R -> hpl PL rr -> rw_cells bgbsegs m R (bn_cells Dr (getbn rr st)) -> bn_arr m OW (pl_of PL rr) Dr (getbn rr st) ->
  ref_at st OW PL x X -> x <> ROne -> (k <= bn_top (getbn x st))%nat -> nbuf PL x ->
  exists Dx, BnRepDefs.bn_arr m OW Dx (getbn x st) /\ rw_cells bgbsegs m X (bn_cells Dx (getbn x st)) /\ bg_ok (getbn x st) /\ limbs_at bgbsegs m Dx (firstn k (bn_buf (getbn x st)))
    /\ 0 < X /\ (X + 24 <= ACEIL \/ (SPX <= X /\ X + 24 < 2^63))
    /\ 0 <= Dx /\ (Dx + 8 * Z.of_nat k <= ACEIL \/ (SPX <= Dx /\ Dx + 8 * Z.of_nat k < 2^63))
    /\ (X = R \/ X + 24 <= R \/ R + 24 <= X)
    /\ (R + 24 <= Dx \/ Dx + 8 * Z.of_nat k <= R)
    /\ (Dx = Dr \/ Dr + 8 * Z.of_nat (bn_dmax (getbn rr st)) <= Dx \/ Dx + 8 * Z.of_nat k <= Dr)
    /\ (X + 24 <= Dr \/ Dr + 8 * Z.of_nat (bn_dmax (getbn rr st)) <= X)
    /\ ((0 < k)%nat -> 8 <= Dx).
Proof.
  intros s OW LB m st PL EA SPX BX rr R Dr x X k HEAP LS FROK NOFR HR HP SR ARR HX NROX Hk NBX.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND. pose proof (proj1 HP) as NRO.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & _).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX.
  destruct (bn_arr_facts_w st OW PL EA SPX BX s LB m rr Dr HEAP PARTS FROK HVR (hpl_wref PL rr HP) ARR) as (UR & LENR & DR0 & DRC & _ & DSEPR).
  pose proof (st_wf_ok x st WFS HVX NROX) as OKX. pose proof OKX as (_ & TDX & _).
  pose proof (DSEPR x X HX) as D4.
  destruct (Nat.eq_dec x rr) as [->|NE].
  -
    pose proof (ref_at_fun _ _ _ _ _ _ ND HX HR) as ->.
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP PARTS HR HP) as (SA0 & SAC & _ & _).
    exists Dr. split; [exact (bn_arr_nofr PL rr m OW Dr _ (proj1 (proj2 PARTS)) NOFR NRO ARR ltac:(solve_nbuf))|]. split; [exact SR|]. split; [exact OKX|]. split; [apply limbs_at_firstn; exact UR|].
    pose proof (fun HL => bn_arr_base8A s OW LB m st PL EA SPX BX rr Dr HEAP PARTS FROK NOFR NRO ARR HL) as B8.
    specialize (DSEPR rr R HR). unfold bn_dmax in *. repeat split; try lia. all: intros Hk0; apply B8; lia.
  - destruct (lib_state_open [] st m OW PL EA x X LS ND HX ltac:(intros []) NROX) as ((Dx & SX & ARRX) & _ & _).
    destruct (bn_arr_facts s OW LB m HEAP st PL EA SPX BX PARTS FROK x Dx HVX NROX ARRX) as (UX & LENX & DX0 & DXC & _ & DSEPX).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HX NROX) as (SA0 & SAC & _).
    exists Dx. split; [exact (bn_arr_nofr PL x m OW Dx _ (proj1 (proj2 PARTS)) NOFR NROX ARRX ltac:(solve_nbuf))|]. split; [exact SX|]. split; [exact OKX|]. split; [apply limbs_at_firstn; exact UX|].
    pose proof (struct_disj s OW LB m HEAP st PL EA SPX BX PARTS FROK x rr X R NE HX HR) as SD.
    specialize (DSEPX rr R HR).
    assert (AD3 : Dx = Dr \/ Dr + 8 * Z.of_nat (bn_dmax (getbn rr st)) <= Dx \/ Dx + 8 * Z.of_nat k <= Dr).
    { pose proof ARR as ARR'. pose proof ARRX as ARRX'. unfold bn_arr in ARR', ARRX'.
      destruct (bn_d (getbn x st)) as [px|] eqn:Edx, (bn_d (getbn rr st)) as [pr|] eqn:Edr.
      - destruct ARR' as [HinR _], ARRX' as [HinX _].
        pose proof (limbs_limbs_disj s OW LB m HEAP st PL EA PARTS x rr px Dx _ pr Dr _ NE HVX HVR Edx Edr HinX HinR) as LD.
        unfold bn_dmax in *. lia.
      - destruct (bn_arr_null PL rr m OW Dr _ (proj1 (proj2 PARTS)) (hpl_wref PL rr HP) Edr ARR) as [-> Eb]. unfold bn_dmax. rewrite Eb. cbn [length]. lia.
      - right. destruct ARR' as [HinR _].
        pose proof (arr_arr_disj st OW PL EA SPX BX s LB m rr x pr Dr Dx HEAP PARTS FROK ltac:(congruence) HVR HVX NROX Edr HinR ARRX). unfold bn_dmax in *. lia.
      - destruct (bn_arr_null PL rr m OW Dr _ (proj1 (proj2 PARTS)) (hpl_wref PL rr HP) Edr ARR) as [-> Eb]. unfold bn_dmax. rewrite Eb. cbn [length]. lia. }
    pose proof (fun HL => bn_arr_base8A s OW LB m st PL EA SPX BX x Dx HEAP PARTS FROK NOFR NROX ARRX HL) as B8.
    unfold bn_dmax in *. repeat split; try lia. all: intros Hk0; apply B8; lia.
Qed.

End WithRT.
