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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnModel BnTree BnInv BnSpecs BnMInv BnBridge BgState BgInv BgLib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem BnCmp BnKaraMem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnAU Require Import BnAKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Lemma bg_okm : forall b : bignum bptr, bg_ok b -> bn_okm b.
Proof. intros b (H1 & H2 & H3 & H4). unfold bn_okm, BN_WORDS_MAX. unfold BG_DMAX in H3. repeat split; try assumption. lia. Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma bn_post_silent : forall {A : Type} (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (st : ST) (OW LB : list block) (lo B : Z) (m m' : mem) (PL : placement) (EA : BnRep.err_addrs)
    (RES : A -> ST -> list block -> placement -> word -> Prop) (res : A)
    (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (W : list (Z * Z)) (errv errv' : word) (stack : Z),
  bn_pre s st m OW LB PL EA sp lo B errv stack -> 0 <= stack ->
  munch W m m' -> wmono bgusegs m m' -> Forall (w_ok OW LB st PL EA (bv_unsigned sp) []) W -> Forall (w_lib st OW PL lo (bv_unsigned sp)) W ->
  stk bgusegs m' lo (bv_unsigned sp) -> rw_cells bgusegs m' LX_ERRNO [C4 errv'] -> mem_inv bgusegs m' ->
  RES res st OW PL a0 ->
  bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s st OW LB lo B m PL EA RES (res, st) s
    (MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc ra) fc None m' (seg_rom bgusegs)).
Proof.
  intros A ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s st OW LB lo B m m' PL EA RES res
         t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 W errv errv' stack
         (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) HS MU WM WOK WL ST' ERR' MI' HRES.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  unfold bn_post. exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', OW, PL, errv'.
  split; [reflexivity|]. cbn [fst snd].
  split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM WL CEIL)|].
  split; [exact (lib_state_frame s LB _ _ [] st m m' OW PL EA W HEAP LS MU WM FROK WOK)|].
  split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM WL SPB ltac:(lia)); unfold GLOBALS_TOP in *; lia|].
  split; [exact ST'|]. split; [exact ERR'|]. split; [exact MI'|].
  split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM WL CEIL); unfold GLOBALS_TOP in *; lia|].
  split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. exact HRES.
Qed.

Lemma open_ro : forall s OW LB m st PL EA SPX BX r a,
  RHEAP s (OW ++ LB) m -> lib_state st m OW PL EA -> frames_ok PL SPX BX -> ref_at st OW PL r a -> r <> ROne ->
  exists D, rw_cells bgusegs m a (bn_cells D (getbn r st)) /\ bg_ok (getbn r st)
    /\ u64arr bgusegs m D (wlimbs (bn_buf (getbn r st)))
    /\ 0 < a /\ (a + 24 <= alloc_ceiling \/ (SPX <= a /\ a + 24 < 2^63))
    /\ 0 <= D /\ (D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= alloc_ceiling \/ (SPX <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r st)) < 2^63)).
Proof.
  intros s OW LB m st PL EA SPX BX r a HEAP LS FROK HA NRO.
  pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_open [] st m OW PL EA r a LS ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & OK & _).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HA NRO) as (SA0 & SAC & _).
  destruct (bn_arr_facts s OW LB m HEAP st PL EA SPX BX PARTS FROK r D HV NRO ARR) as (U & LENW & D0 & DC & _ & _).
  exists D. split; [exact BN|]. split; [exact OK|]. split; [exact U|]. split; [exact SA0|]. split; [exact SAC|]. split; [exact D0| exact DC].
Qed.

Lemma operand_view : forall s OW LB m st PL EA SPX BX rr R Dr x X k,
  RHEAP s (OW ++ LB) m -> lib_state st m OW PL EA -> frames_ok PL SPX BX ->
  ref_at st OW PL rr R -> hpl PL rr -> rw_cells bgusegs m R (bn_cells Dr (getbn rr st)) -> bn_arr m OW (pl_of PL rr) Dr (getbn rr st) ->
  ref_at st OW PL x X -> x <> ROne -> (k <= bn_top (getbn x st))%nat ->
  exists Dx, rw_cells bgusegs m X [C8 (wz Dx)] /\ limbs_at bgusegs m Dx (firstn k (bn_buf (getbn x st)))
    /\ 0 < X /\ (X + 24 <= alloc_ceiling \/ (SPX <= X /\ X + 24 < 2^63))
    /\ 0 <= Dx /\ (Dx + 8 * Z.of_nat k <= alloc_ceiling \/ (SPX <= Dx /\ Dx + 8 * Z.of_nat k < 2^63))
    /\ (X = R \/ X + 24 <= R \/ R + 24 <= X)
    /\ (R + 24 <= Dx \/ Dx + 8 * Z.of_nat k <= R)
    /\ (Dx = Dr \/ Dr + 8 * Z.of_nat (bn_dmax (getbn rr st)) <= Dx \/ Dx + 8 * Z.of_nat k <= Dr).
Proof.
  intros s OW LB m st PL EA SPX BX rr R Dr x X k HEAP LS FROK HR HP SR ARR HX NROX Hk.
  pose proof (RH_nodup_l _ _ _ _ HEAP) as ND. pose proof (proj1 HP) as NRO.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & _).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX.
  destruct (bn_arr_facts_w st OW PL EA SPX BX s LB m rr Dr HEAP PARTS FROK HVR (hpl_wref PL rr HP) ARR) as (UR & LENR & DR0 & DRC & _ & DSEPR).
  pose proof (st_wf_ok x st WFS HVX NROX) as (_ & TDX & _).
  destruct (Nat.eq_dec x rr) as [->|NE].
  -
    pose proof (ref_at_fun _ _ _ _ _ _ ND HX HR) as ->.
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP PARTS HR HP) as (SA0 & SAC & _ & _).
    exists Dr. split; [exact (d_cell _ _ _ _ SR)|]. split; [apply limbs_at_firstn; exact UR|].
    specialize (DSEPR rr R HR). unfold bn_dmax in *. lia.
  - destruct (lib_state_open [] st m OW PL EA x X LS ND HX ltac:(intros []) NROX) as ((Dx & SX & ARRX) & _ & _).
    destruct (bn_arr_facts s OW LB m HEAP st PL EA SPX BX PARTS FROK x Dx HVX NROX ARRX) as (UX & LENX & DX0 & DXC & _ & DSEPX).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HX NROX) as (SA0 & SAC & _).
    exists Dx. split; [exact (d_cell _ _ _ _ SX)|]. split; [apply limbs_at_firstn; exact UX|].
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
    unfold bn_dmax in *. lia.
Qed.

Lemma operand_view_ne : forall s OW LB m st PL EA SPX BX rr R Dr x X k,
  RHEAP s (OW ++ LB) m -> lib_state st m OW PL EA -> frames_ok PL SPX BX ->
  ref_at st OW PL rr R -> hpl PL rr -> rw_cells bgusegs m R (bn_cells Dr (getbn rr st)) -> bn_arr m OW (pl_of PL rr) Dr (getbn rr st) ->
  ref_at st OW PL x X -> x <> ROne -> (k <= bn_top (getbn x st))%nat -> x <> rr ->
  exists Dx, rw_cells bgusegs m X [C8 (wz Dx)] /\ limbs_at bgusegs m Dx (firstn k (bn_buf (getbn x st)))
    /\ u64arr bgusegs m Dx (wlimbs (bn_buf (getbn x st))) /\ bn_arr m OW (pl_of PL x) Dx (getbn x st)
    /\ 0 < X /\ (X + 24 <= alloc_ceiling \/ (SPX <= X /\ X + 24 < 2^63))
    /\ 0 <= Dx /\ (Dx + 8 * Z.of_nat (bn_dmax (getbn x st)) <= alloc_ceiling \/ (SPX <= Dx /\ Dx + 8 * Z.of_nat (bn_dmax (getbn x st)) < 2^63))
    /\ (X + 24 <= R \/ R + 24 <= X)
    /\ (R + 24 <= Dx \/ Dx + 8 * Z.of_nat (bn_dmax (getbn x st)) <= R)
    /\ (X + 24 <= Dr \/ Dr + 8 * Z.of_nat (bn_dmax (getbn rr st)) <= X)
    /\ (Dr + 8 * Z.of_nat (bn_dmax (getbn rr st)) <= Dx \/ Dx + 8 * Z.of_nat (bn_dmax (getbn x st)) <= Dr).
Proof.
  intros s OW LB m st PL EA SPX BX rr R Dr x X k HEAP LS FROK HR HP SR ARR HX NROX Hk NE.
  pose proof (RH_nodup_l _ _ _ _ HEAP) as ND. pose proof (proj1 HP) as NRO.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & _).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX.
  destruct (bn_arr_facts_w st OW PL EA SPX BX s LB m rr Dr HEAP PARTS FROK HVR (hpl_wref PL rr HP) ARR) as (UR & LENR & DR0 & DRC & _ & DSEPR).
  destruct (lib_state_open [] st m OW PL EA x X LS ND HX ltac:(intros []) NROX) as ((Dx & SX & ARRX) & _ & _).
  destruct (bn_arr_facts s OW LB m HEAP st PL EA SPX BX PARTS FROK x Dx HVX NROX ARRX) as (UX & LENX & DX0 & DXC & _ & DSEPX).
  pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HX NROX) as (SA0 & SAC & _).
  exists Dx. split; [exact (d_cell _ _ _ _ SX)|]. split; [apply limbs_at_firstn; exact UX|]. split; [exact UX|]. split; [exact ARRX|].
  pose proof (struct_disj s OW LB m HEAP st PL EA SPX BX PARTS FROK x rr X R NE HX HR) as SD.
  pose proof (DSEPX rr R HR) as D1. pose proof (DSEPR x X HX) as D2.
  assert (AD3 : Dr + 8 * Z.of_nat (bn_dmax (getbn rr st)) <= Dx \/ Dx + 8 * Z.of_nat (bn_dmax (getbn x st)) <= Dr).
  { pose proof ARR as ARR'. unfold bn_arr in ARR'. destruct (bn_d (getbn rr st)) as [pr|] eqn:Edr.
    - destruct ARR' as [HinR _].
      exact (arr_arr_disj st OW PL EA SPX BX s LB m rr x pr Dr Dx HEAP PARTS FROK ltac:(congruence) HVR HVX NROX Edr HinR ARRX).
    - destruct (bn_arr_null PL rr m OW Dr _ (proj1 (proj2 PARTS)) (hpl_wref PL rr HP) Edr ARR) as [-> Eb]. unfold bn_dmax at 1. rewrite Eb. cbn [length]. lia. }
  lia.
Qed.

Lemma open_ro_u : forall s OW LB m st PL EA SPX BX r a,
  RHEAP s (OW ++ LB) m -> lib_state st m OW PL EA -> frames_ok PL SPX BX -> ref_at st OW PL r a -> r <> ROne ->
  exists D, rw_cells bgusegs m a (bn_cells D (getbn r st)) /\ bg_ok (getbn r st)
    /\ u64arr bgusegs m D (wlimbs (bn_buf (getbn r st)))
    /\ 0 < a /\ (a + 24 <= alloc_ceiling \/ (SPX <= a /\ a + 24 < 2^63))
    /\ 0 <= D /\ (D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= alloc_ceiling \/ (SPX <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r st)) < 2^63))
    /\ hide (a mod 8 = 0) /\ ub_ptr_ok (Z.of_nat (bn_top (getbn r st))) D.
Proof.
  intros s OW LB m st PL EA SPX BX r a HEAP LS FROK HA NRO.
  pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_open [] st m OW PL EA r a LS ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & OK & _).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HA NRO) as (SA0 & SAC & _).
  destruct (bn_arr_facts s OW LB m HEAP st PL EA SPX BX PARTS FROK r D HV NRO ARR) as (U & LENW & D0 & DC & _ & _).
  pose proof (ref_at_ualign s OW LB m st PL EA r a HEAP PARTS HA NRO) as (_ & AL).
  exists D. split; [exact BN|]. split; [exact OK|]. split; [exact U|]. split; [exact SA0|]. split; [exact SAC|]. split; [exact D0|].
  split; [exact DC|]. split; [apply hide_intro; exact AL|].
  unfold ub_ptr_ok. intros TP. destruct OK as (_ & TD & _).
  apply (bn_arr_ualign s OW LB m st PL EA r D _ HEAP PARTS ARR). lia.
Qed.

Lemma operand_view_u : forall s OW LB m st PL EA SPX BX rr R Dr x X k,
  RHEAP s (OW ++ LB) m -> lib_state st m OW PL EA -> frames_ok PL SPX BX ->
  ref_at st OW PL rr R -> hpl PL rr -> rw_cells bgusegs m R (bn_cells Dr (getbn rr st)) -> bn_arr m OW (pl_of PL rr) Dr (getbn rr st) ->
  ref_at st OW PL x X -> x <> ROne -> (k <= bn_top (getbn x st))%nat ->
  exists Dx, rw_cells bgusegs m X [C8 (wz Dx)] /\ limbs_at bgusegs m Dx (firstn k (bn_buf (getbn x st)))
    /\ 0 < X /\ (X + 24 <= alloc_ceiling \/ (SPX <= X /\ X + 24 < 2^63))
    /\ 0 <= Dx /\ (Dx + 8 * Z.of_nat k <= alloc_ceiling \/ (SPX <= Dx /\ Dx + 8 * Z.of_nat k < 2^63))
    /\ (X = R \/ X + 24 <= R \/ R + 24 <= X)
    /\ (R + 24 <= Dx \/ Dx + 8 * Z.of_nat k <= R)
    /\ (Dx = Dr \/ Dr + 8 * Z.of_nat (bn_dmax (getbn rr st)) <= Dx \/ Dx + 8 * Z.of_nat k <= Dr)
    /\ ub_ptr_ok (Z.of_nat k) Dx /\ hide (X mod 8 = 0).
Proof.
  intros s OW LB m st PL EA SPX BX rr R Dr x X k HEAP LS FROK HR HP SR ARR HX NROX Hk.
  pose proof (RH_nodup_l _ _ _ _ HEAP) as ND. pose proof (proj1 HP) as NRO.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & _).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX.
  destruct (bn_arr_facts_w st OW PL EA SPX BX s LB m rr Dr HEAP PARTS FROK HVR (hpl_wref PL rr HP) ARR) as (UR & LENR & DR0 & DRC & _ & DSEPR).
  pose proof (st_wf_ok x st WFS HVX NROX) as (_ & TDX & _).
  assert (ALX : hide (X mod 8 = 0)) by (apply hide_intro; exact (proj2 (ref_at_ualign s OW LB m st PL EA x X HEAP PARTS HX NROX))).
  destruct (Nat.eq_dec x rr) as [->|NE].
  -
    pose proof (ref_at_fun _ _ _ _ _ _ ND HX HR) as ->.
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP PARTS HR HP) as (SA0 & SAC & _ & _).
    assert (UPX : ub_ptr_ok (Z.of_nat k) Dr)
      by (unfold ub_ptr_ok; intros KP; apply (bn_arr_ualign s OW LB m st PL EA rr Dr _ HEAP PARTS ARR); lia).
    exists Dr. split; [exact (d_cell _ _ _ _ SR)|]. split; [apply limbs_at_firstn; exact UR|].
    specialize (DSEPR rr R HR). unfold bn_dmax in *.
    repeat (split; [lia|]). split; [exact UPX | exact ALX].
  - destruct (lib_state_open [] st m OW PL EA x X LS ND HX ltac:(intros []) NROX) as ((Dx & SX & ARRX) & _ & _).
    destruct (bn_arr_facts s OW LB m HEAP st PL EA SPX BX PARTS FROK x Dx HVX NROX ARRX) as (UX & LENX & DX0 & DXC & _ & DSEPX).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HX NROX) as (SA0 & SAC & _).
    assert (UPX : ub_ptr_ok (Z.of_nat k) Dx)
      by (unfold ub_ptr_ok; intros KP; apply (bn_arr_ualign s OW LB m st PL EA x Dx _ HEAP PARTS ARRX); lia).
    exists Dx. split; [exact (d_cell _ _ _ _ SX)|]. split; [apply limbs_at_firstn; exact UX|].
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
    unfold bn_dmax in *.
    repeat (split; [lia|]). split; [exact UPX | exact ALX].
Qed.

Lemma open_full : forall s OW LB m st PL EA SPX BX r a,
  RHEAP s (OW ++ LB) m -> lib_state st m OW PL EA -> frames_ok PL SPX BX -> ref_at st OW PL r a -> hpl PL r ->
  exists D, rw_cells bgusegs m a (bn_cells D (getbn r st)) /\ bn_arr m OW (pl_of PL r) D (getbn r st) /\ bg_ok (getbn r st)
    /\ u64arr bgusegs m D (wlimbs (bn_buf (getbn r st)))
    /\ 0 < a /\ a + 24 <= alloc_ceiling /\ 0 <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= alloc_ceiling
    /\ (forall r' a', ref_at st OW PL r' a' -> a' + 24 <= D \/ D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= a').
Proof.
  intros s OW LB m st PL EA SPX BX r a HEAP LS FROK HA HP.
  pose proof (RH_nodup_l _ _ _ _ HEAP) as ND. pose proof (proj1 HP) as NRO.
  destruct (lib_state_open [] st m OW PL EA r a LS ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & OK & _).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP PARTS HA HP) as (SA0 & SAC & _ & _).
  destruct (bn_arr_facts_w st OW PL EA SPX BX s LB m r D HEAP PARTS FROK HV (hpl_wref PL r HP) ARR) as (U & LENW & D0 & DC & DI & DSEP).
  exists D. split; [exact BN|]. split; [exact ARR|]. split; [exact OK|]. split; [exact U|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact DC | exact DSEP].
Qed.

Lemma bn_arr_none_cases : forall PL r m OW D (b : bignum bptr),
  pl_wf PL -> r <> ROne -> bn_d b = None -> bn_arr m OW (pl_of PL r) D b ->
  (exists x d, pl_bn PL r = Some (PFrameBuf x d) /\ D = d /\ length (bn_buf b) = 2%nat) \/ (D = 0 /\ bn_buf b = []).
Proof.
  intros PL r m OW D b PWF NRO Ed ARR. unfold bn_arr in ARR. rewrite Ed in ARR.
  destruct (pl_of PL r) as [p|] eqn:Ep; [|right; exact ARR].
  destruct (pl_of_cases PL r _ Ep) as [[-> _]|[(am & qm & _ & _ & -> & _)|[S Eb]]]; [exfalso; exact (NRO eq_refl)| right; exact ARR|].
  destruct p as [x q off|x|x d|x]; [right; exact ARR| right; exact ARR| |].
  - left. exists x, d. destruct ARR as (HD & _ & HL). auto.
  - exfalso. exact (proj2 (proj2 (proj2 (proj1 PWF r _ Eb)))).
Qed.

Lemma bn_arrs_disj : forall s OW LB m st PL EA SPX BX r1 r2 a1 a2 D1 D2,
  RHEAP s (OW ++ LB) m -> lib_state st m OW PL EA -> frames_ok PL SPX BX -> r1 <> r2 -> ref_at st OW PL r1 a1 -> ref_at st OW PL r2 a2 ->
  r1 <> ROne -> r2 <> ROne ->
  bn_arr m OW (pl_of PL r1) D1 (getbn r1 st) -> bn_arr m OW (pl_of PL r2) D2 (getbn r2 st) ->
  D1 + 8 * Z.of_nat (bn_dmax (getbn r1 st)) <= D2 \/ D2 + 8 * Z.of_nat (bn_dmax (getbn r2 st)) <= D1.
Proof.
  intros s OW LB m st PL EA SPX BX r1 r2 a1 a2 D1 D2 HEAP LS FROK NE H1 H2 N1 N2 ARR1 ARR2.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & PWF & _).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS H1) as HV1. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS H2) as HV2.
  destruct (bn_arr_facts s OW LB m HEAP st PL EA SPX BX PARTS FROK r1 D1 HV1 N1 ARR1) as (_ & _ & D10 & _).
  destruct (bn_arr_facts s OW LB m HEAP st PL EA SPX BX PARTS FROK r2 D2 HV2 N2 ARR2) as (_ & _ & D20 & _).
  pose proof ARR1 as ARR1'. pose proof ARR2 as ARR2'. unfold bn_arr in ARR1', ARR2'.
  destruct (bn_d (getbn r1 st)) as [p1|] eqn:E1, (bn_d (getbn r2 st)) as [p2|] eqn:E2.
  - destruct ARR1' as [Hin1 _], ARR2' as [Hin2 _].
    exact (limbs_limbs_disj s OW LB m HEAP st PL EA PARTS r1 r2 p1 D1 _ p2 D2 _ NE HV1 HV2 E1 E2 Hin1 Hin2).
  - destruct ARR1' as [Hin1 _]. exact (arr_arr_disj st OW PL EA SPX BX s LB m r1 r2 p1 D1 D2 HEAP PARTS FROK NE HV1 HV2 N2 E1 Hin1 ARR2).
  - destruct ARR2' as [Hin2 _].
    pose proof (arr_arr_disj st OW PL EA SPX BX s LB m r2 r1 p2 D2 D1 HEAP PARTS FROK ltac:(congruence) HV2 HV1 N1 E2 Hin2 ARR1). lia.
  - destruct (bn_arr_none_cases PL r1 m OW D1 _ PWF N1 E1 ARR1) as [(x & d & Eb1 & -> & L1)|[-> Eb1]];
      [| unfold bn_dmax at 1; rewrite Eb1; cbn [length]; lia].
    destruct (bn_arr_none_cases PL r2 m OW D2 _ PWF N2 E2 ARR2) as [(x' & d' & Eb2 & -> & L2)|[-> Eb2]];
      [| unfold bn_dmax at 2; rewrite Eb2; cbn [length]; lia].
    pose proof (proj1 (proj2 PWF) r1 r2 _ _ (d, d + TMOD_BUF_SZ) (d', d' + TMOD_BUF_SZ) NE Eb1 Eb2 ltac:(right; left; reflexivity) ltac:(right; left; reflexivity)) as AP.
    unfold iv_apart, TMOD_BUF_SZ, bn_dmax in *. cbn [fst snd] in AP. rewrite L1, L2. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.

End WithCeiling0.
