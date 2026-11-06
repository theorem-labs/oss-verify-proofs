(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge Arr. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout RT_iface D_defs.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnMem BnCmp BnKaraMem.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA AsStruct.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma bg_okm : forall b : bignum bptr, bg_ok b -> bn_okm b.
Proof. intros b (H1 & H2 & H3 & H4). unfold bn_okm, BN_WORDS_MAX. unfold BG_DMAX in H3. repeat split; try assumption. lia. Qed.

Lemma bn_arr_factsA : forall Σ OW LB m ls PL EA SPX r D,
  AHEAP Σ OW LB m -> lib_parts ls OW PL EA -> frames_ok PL SPX USTACK_TOP -> pl_frames PL = [] -> vref r ls -> not_one r ->
  bn_arr m OW (pl_of PL r) D (getbn r ls) ->
  u64arr bgbsegs m D (wlimbs (bn_buf (getbn r ls)))
  /\ Z.of_nat (length (wlimbs (bn_buf (getbn r ls)))) = Z.of_nat (bn_dmax (getbn r ls))
  /\ 0 <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= ACEIL
  /\ (D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= 0x10000 \/ 0xbf9000 <= D \/ bn_dmax (getbn r ls) = 0%nat)
  /\ (forall r' a', ref_at ls OW PL r' a' -> a' + 24 <= D \/ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= a').
Proof.
  intros Σ OW LB m ls PL EA SPX r D HEAP PARTS FROK NOFR HV NRO ARR.
  destruct (bn_arr_facts Σ OW LB m HEAP ls PL EA _ _ PARTS FROK r D HV NRO ARR) as (U & LENW & D0 & DC & DI & DSEP).
  pose proof PARTS as (WFS & PWF & _).
  assert (DC' : D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= ACEIL).
  { pose proof (bn_arr_nofr PL r m OW D _ PWF NOFR NRO ARR) as ARR0. unfold BnRepDefs.bn_arr in ARR0. destruct (bn_d (getbn r ls)) as [p|].
    - destruct ARR0 as [Hin _]. pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (_ & _ & _ & AC & _). exact AC.
    - destruct ARR0 as [-> Eb]. unfold bn_dmax. rewrite Eb. cbn. pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _). unfold SEGTOP_A in C1. lia. }
  split; [exact U|]. split; [exact LENW|]. split; [exact D0|]. split; [exact DC'|]. split; [exact DI| exact DSEP].
Qed.

Lemma arr_ceilA : forall Σ OW LB m D (b : bignum bptr), AHEAP Σ OW LB m -> BnRepDefs.bn_arr m OW D b -> 0 <= D /\ D + 8 * Z.of_nat (bn_dmax b) <= ACEIL.
Proof.
  intros Σ OW LB m D b HEAP ARR. unfold BnRepDefs.bn_arr in ARR. destruct (bn_d b) as [p|].
  - destruct ARR as [Hin _]. pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (A0 & _ & _ & AC & _). lia.
  - destruct ARR as [-> Eb]. unfold bn_dmax. rewrite Eb. cbn. pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _). unfold SEGTOP_A in C1. lia.
Qed.

Lemma bn_post_silentA : forall {A : Type} (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (lo : Z) (m m' : mem) (PL : placement) (EA : BnRepDefs.err_addrs) (cost : Z)
    (RES : A -> bstate bptr -> list block -> placement -> word -> Prop) (res : A)
    (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (W : list (Z * Z)) (stack : Z),
  bn_preA Σ ls m OW LB PL EA sp lo stack cost -> 0 <= stack -> 0 <= cost ->
  munch W m m' -> wmono bgbsegs m m' -> Forall (w_okc OW LB ls PL EA (bv_unsigned sp) false []) W -> Forall (w_lib ls OW PL lo (bv_unsigned sp)) W ->
  stk bgbsegs m' lo (bv_unsigned sp) -> mem_inv bgbsegs m' ->
  RES res ls OW PL a0 ->
  bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA cost RES (res, ls) Σ
    (MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc ra) fc None m' (seg_rom bgbsegs)).
Proof.
  intros A ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Σ ls OW LB lo m m' PL EA cost RES res
         t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 W stack
         (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR) HS HC MU WM WOK WL ST' MI' HRES.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  unfold bn_postA. exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F, fc, m', OW, PL.
  split; [reflexivity|]. cbn [fst snd].
  split; [eapply (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM WL CEIL); unfold USTACK_TOP in *; lia|].
  split; [exact (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m m' OW PL EA W HEAP LS MU WM FROK WOK)|].
  split; [exact ST'|]. split; [exact MI'|].
  split; [eapply (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WL CEIL); lia|].
  split; [lia|]. split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|]. exact HRES.
Qed.

Lemma ref_shA : forall Σ OW LB m cxo hs ls PL EA r a,
  AHEAP Σ OW LB m -> lib_state_hc cxo hs ls m OW PL EA -> pl_frames PL = [] -> ref_at ls OW PL r a -> not_one r ->
  acc bgbsegs m a 24 /\ a mod 8 = 0 /\ (a + 24 <= SHLO \/ SHHI <= a).
Proof.
  intros Σ OW LB m cxo hs ls PL EA r a HEAP LS NOFR HA NRO.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP PARTS NOFR HA NRO) as (qx & Ax & nx & Hinx & Rx1 & Rx2).
  assert (INX : In (qx, Ax, nx) (OW ++ LB)) by (apply in_or_app; left; exact Hinx).
  split; [exact (AH_acc_in _ _ _ _ (qx, Ax, nx) a 24 HEAP INX Rx1 Rx2)|].
  split; [exact (ref_at_al8A _ _ _ _ _ _ _ _ _ HEAP PARTS NOFR HA NRO)|].
  pose proof (AH_offsh _ _ _ _ (qx, Ax, nx) HEAP INX) as OX. cbn [blk_addr blk_size fst snd] in OX. lia.
Qed.

Lemma arr_shA : forall Σ OW LB m D (b : bignum bptr),
  AHEAP Σ OW LB m -> BnRepDefs.bn_arr m OW D b ->
  acc bgbsegs m D (8 * Z.of_nat (bn_dmax b)) /\ D mod 8 = 0 /\ (D + 8 * Z.of_nat (bn_dmax b) <= SHLO \/ SHHI <= D).
Proof.
  intros Σ OW LB m D b HEAP ARR. unfold BnRepDefs.bn_arr in ARR. destruct (bn_d b) as [p|] eqn:Ed.
  - destruct ARR as [Hin _]. assert (INX : In (p, D, 8 * Z.of_nat (bn_dmax b)) (OW ++ LB)) by (apply in_or_app; left; exact Hin).
    split; [exact (AH_acc_in _ _ _ _ (p, D, 8 * Z.of_nat (bn_dmax b)) D (8 * Z.of_nat (bn_dmax b)) HEAP INX ltac:(cbn [blk_addr blk_size fst snd]; lia) ltac:(cbn [blk_addr blk_size fst snd]; lia))|].
    pose proof (AH_okA _ _ _ _ _ _ _ HEAP Hin) as [H16 _].
    split; [clear - H16; Z.div_mod_to_equations; lia|].
    pose proof (AH_offsh _ _ _ _ (p, D, 8 * Z.of_nat (bn_dmax b)) HEAP INX) as OX. cbn [blk_addr blk_size fst snd] in OX. lia.
  - destruct ARR as [-> Eb]. unfold bn_dmax. rewrite Eb. cbn [length Z.of_nat].
    split; [intros i Hi; lia|]. split; [reflexivity|]. left. unfold SHLO. lia.
Qed.

Lemma limbs_at_firstn : forall m D (l : list Z) k, u64arr bgbsegs m D (wlimbs l) -> limbs_at bgbsegs m D (firstn k l).
Proof.
  intros m D l k U. destruct (Nat.le_gt_cases k (length l)) as [Hk|Hk].
  - apply (proj1 (limbarr_split bgbsegs m D l k Hk)) in U. destruct U as [U _]. apply limbs_at_of_u64arr. exact U.
  - rewrite firstn_all2 by lia. apply limbs_at_of_u64arr. exact U.
Qed.

Lemma open_full : forall Σ OW LB m ls PL EA SPX r a,
  AHEAP Σ OW LB m -> lib_state ls m OW PL EA -> frames_ok PL SPX USTACK_TOP -> pl_frames PL = [] -> ref_at ls OW PL r a -> not_one r ->
  exists D, rw_cells bgbsegs m a (bn_cells D (getbn r ls)) /\ BnRepDefs.bn_arr m OW D (getbn r ls) /\ bg_ok (getbn r ls)
    /\ u64arr bgbsegs m D (wlimbs (bn_buf (getbn r ls)))
    /\ 0 < a /\ a + 24 <= ACEIL /\ 0 <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= ACEIL
    /\ (forall r' a', ref_at ls OW PL r' a' -> a' + 24 <= D \/ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= a').
Proof.
  intros Σ OW LB m ls PL EA SPX r a HEAP LS FROK NOFR HA NRO.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_open [] ls m OW PL EA r a LS ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & OK & _).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
  destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP PARTS NOFR HA NRO) as (qs & As & ns & Hins & Ra1 & Ra2).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & SA16 & _ & SAC & SAI).
  destruct (bn_arr_facts Σ OW LB m HEAP ls PL EA _ _ PARTS FROK r D HV NRO ARR) as (U & LENW & D0 & DC & DI & DSEP).
  apply (bn_arr_nofr PL r m OW D _ PWF NOFR NRO) in ARR.
  pose proof (arr_ceilA _ _ _ _ _ _ HEAP ARR) as [_ DC'].
  exists D. split; [exact BN|]. split; [exact ARR|]. split; [exact OK|]. split; [exact U|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact DC' | exact DSEP].
Qed.

End WithRT.
