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
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout RT_iface D_defs.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnMem BnCmp BnKaraMem.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA AsStruct.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
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
  AHEAP Σ OW LB m -> lib_parts ls OW PL EA -> frames_ok LB PL SPX USTACK_TOP -> frames_lb PL LB -> vref r ls -> not_one r ->
  bn_arr m OW (pl_of PL r) D (getbn r ls) ->
  u64arr bgasegs m D (wlimbs (bn_buf (getbn r ls)))
  /\ Z.of_nat (length (wlimbs (bn_buf (getbn r ls)))) = Z.of_nat (bn_dmax (getbn r ls))
  /\ 0 <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= ACEIL
  /\ (D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= 0x10000 \/ 0xbc6000 <= D \/ bn_dmax (getbn r ls) = 0%nat)
  /\ (forall r' a', ref_at ls OW PL r' a' -> a' + 24 <= D \/ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= a').
Proof.
  intros Σ OW LB m ls PL EA SPX r D HEAP PARTS FROK NOFR HV NRO ARR.
  exact (bn_arr_facts_lin Σ OW LB m HEAP ls PL EA _ _ PARTS FROK r D HV NRO ARR).
Qed.

Lemma arr0_facts : forall Σ OW LB m ls PL EA SPX r D,
  AHEAP Σ OW LB m -> lib_parts ls OW PL EA -> frames_ok LB PL SPX USTACK_TOP -> vref r ls -> BnRepDefs.bn_arr m OW D (getbn r ls) ->
  u64arr bgasegs m D (wlimbs (bn_buf (getbn r ls)))
  /\ 0 <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= ACEIL
  /\ (forall r' a', ref_at ls OW PL r' a' -> not_one r' -> a' + 24 <= D \/ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= a').
Proof.
  intros Σ OW LB m ls PL EA SPX r D HEAP PARTS FROK HV ARR. unfold BnRepDefs.bn_arr in ARR. destruct (bn_d (getbn r ls)) as [p|] eqn:Ed.
  - destruct ARR as [Hin HU]. pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (B0 & _ & _ & BC & BI).
    split; [exact HU|]. split; [lia|]. split; [exact BC|].
    intros r' a' HA' _. exact (struct_limbs_disj Σ OW LB m HEAP ls PL EA _ _ PARTS FROK r' r a' p D _ HA' HV Ed Hin).
  - destruct ARR as [-> Eb]. unfold bn_dmax. rewrite Eb. cbn [length wlimbs map Z.of_nat].
    split. { split; [apply bytes_at_nil; lia|]. cbn [length]. split; [lia|]. split; [lia|]. intros i Hi. lia. }
    split; [lia|]. split; [pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _); unfold SEGTOP_A in C1; lia|].
    intros r' a' HA' NR'. right. destruct (ref_at_rangeF ls OW PL EA SPX USTACK_TOP Σ LB m r' a' HEAP PARTS FROK HA' NR') as (P0 & _). lia.
Qed.

Lemma arr_arr0_disj : forall Σ OW LB m ls PL EA SPX x rr Dx Dr,
  AHEAP Σ OW LB m -> lib_parts ls OW PL EA -> frames_ok LB PL SPX USTACK_TOP -> x <> rr -> vref x ls -> vref rr ls -> not_one x ->
  bn_arr m OW (pl_of PL x) Dx (getbn x ls) -> BnRepDefs.bn_arr m OW Dr (getbn rr ls) ->
  Dr + 8 * Z.of_nat (bn_dmax (getbn rr ls)) <= Dx \/ Dx + 8 * Z.of_nat (bn_dmax (getbn x ls)) <= Dr.
Proof.
  intros Σ OW LB m ls PL EA SPX x rr Dx Dr HEAP PARTS FROK NE HVX HVR NRX ARRX ARR.
  destruct (bn_arr_facts_lin Σ OW LB m HEAP ls PL EA _ _ PARTS FROK x Dx HVX NRX ARRX) as (_ & _ & DX0 & _).
  unfold BnRepDefs.bn_arr in ARR. destruct (bn_d (getbn rr ls)) as [pr|] eqn:Edr.
  - destruct ARR as [HinR _].
    pose proof (arr_arr_disj ls OW PL EA SPX USTACK_TOP Σ LB m rr x pr Dr Dx HEAP PARTS FROK ltac:(intros E; apply NE; symmetry; exact E) HVR HVX NRX Edr HinR ARRX) as DJ. lia.
  - destruct ARR as [-> Eb]. unfold bn_dmax at 1. rewrite Eb. cbn [length]. lia.
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
  munch W m m' -> wmono bgasegs m m' -> Forall (w_okc OW LB ls PL EA (bv_unsigned sp) false []) W -> Forall (w_lib ls OW PL lo (bv_unsigned sp)) W ->
  stk bgasegs m' lo (bv_unsigned sp) -> mem_inv bgasegs m' ->
  RES res ls OW PL a0 ->
  bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA cost RES (res, ls) Σ
    (MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc ra) fc None m' (seg_rom bgasegs)).
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
  AHEAP Σ OW LB m -> lib_state_hc cxo hs ls m OW PL EA -> frames_lb PL LB -> ref_at ls OW PL r a -> not_one r ->
  acc bgasegs m a 24 /\ a mod 8 = 0 /\ (a + 24 <= SHLO \/ SHHI <= a).
Proof.
  intros Σ OW LB m cxo hs ls PL EA r a HEAP LS NOFR HA NRO.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP PARTS NOFR HA NRO) as (qx & Ax & nx & INX & Rx1 & Rx2).
  split; [exact (AH_acc_in _ _ _ _ (qx, Ax, nx) a 24 HEAP INX Rx1 Rx2)|].
  split; [exact (ref_at_al8A _ _ _ _ _ _ _ _ _ HEAP PARTS NOFR HA NRO)|].
  pose proof (AH_offsh _ _ _ _ (qx, Ax, nx) HEAP INX) as OX. cbn [blk_addr blk_size fst snd] in OX. lia.
Qed.

Lemma arr_shA : forall Σ OW LB m D (b : bignum bptr),
  AHEAP Σ OW LB m -> BnRepDefs.bn_arr m OW D b ->
  acc bgasegs m D (8 * Z.of_nat (bn_dmax b)) /\ D mod 8 = 0 /\ (D + 8 * Z.of_nat (bn_dmax b) <= SHLO \/ SHHI <= D).
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

Lemma open_ro : forall Σ OW LB m ls PL EA SPX r a,
  AHEAP Σ OW LB m -> lib_state ls m OW PL EA -> frames_ok LB PL SPX USTACK_TOP -> frames_lb PL LB -> ref_at ls OW PL r a -> not_one r ->
  exists D, rw_cells bgasegs m a (bn_cells D (getbn r ls)) /\ bg_ok (getbn r ls)
    /\ u64arr bgasegs m D (wlimbs (bn_buf (getbn r ls)))
    /\ 0 < a /\ a + 24 <= ACEIL /\ 0 <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= ACEIL.
Proof.
  intros Σ OW LB m ls PL EA SPX r a HEAP LS FROK NOFR HA NRO.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_open [] ls m OW PL EA r a LS ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & OK & _).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
  destruct (ref_at_rangeF ls OW PL EA SPX USTACK_TOP Σ LB m r a HEAP PARTS FROK HA NRO) as (SA0 & SAC & SAI).
  destruct (bn_arr_facts_lin Σ OW LB m HEAP ls PL EA _ _ PARTS FROK r D HV NRO ARR) as (U & LENW & D0 & DC' & DI & DSEP).
  exists D. split; [exact BN|]. split; [exact OK|]. split; [exact U|]. lia.
Qed.

Lemma limbs_at_firstn : forall m D (l : list Z) k, u64arr bgasegs m D (wlimbs l) -> limbs_at bgasegs m D (firstn k l).
Proof.
  intros m D l k U. destruct (Nat.le_gt_cases k (length l)) as [Hk|Hk].
  - apply (proj1 (limbarr_split bgasegs m D l k Hk)) in U. destruct U as [U _]. apply limbs_at_of_u64arr. exact U.
  - rewrite firstn_all2 by lia. apply limbs_at_of_u64arr. exact U.
Qed.

Lemma operand_view_ne : forall Σ OW LB m ls PL EA SPX rr R Dr x X k,
  AHEAP Σ OW LB m -> lib_state ls m OW PL EA -> frames_ok LB PL SPX USTACK_TOP -> frames_lb PL LB ->
  ref_at ls OW PL rr R -> not_one rr -> rw_cells bgasegs m R (bn_cells Dr (getbn rr ls)) -> BnRepDefs.bn_arr m OW Dr (getbn rr ls) ->
  ref_at ls OW PL x X -> not_one x -> (k <= bn_top (getbn x ls))%nat -> x <> rr -> nbuf PL x ->
  exists Dx, rw_cells bgasegs m X [C8 (wz Dx)] /\ limbs_at bgasegs m Dx (firstn k (bn_buf (getbn x ls)))
    /\ u64arr bgasegs m Dx (wlimbs (bn_buf (getbn x ls))) /\ BnRepDefs.bn_arr m OW Dx (getbn x ls)
    /\ 0 < X /\ X + 24 <= ACEIL /\ 0 <= Dx /\ Dx + 8 * Z.of_nat (bn_dmax (getbn x ls)) <= ACEIL
    /\ (X + 24 <= R \/ R + 24 <= X)
    /\ (R + 24 <= Dx \/ Dx + 8 * Z.of_nat (bn_dmax (getbn x ls)) <= R)
    /\ (X + 24 <= Dr \/ Dr + 8 * Z.of_nat (bn_dmax (getbn rr ls)) <= X)
    /\ (Dr + 8 * Z.of_nat (bn_dmax (getbn rr ls)) <= Dx \/ Dx + 8 * Z.of_nat (bn_dmax (getbn x ls)) <= Dr).
Proof.
  intros Σ OW LB m ls PL EA SPX rr R Dr x X k HEAP LS FROK NOFR HR NRR SR ARR HX NRX Hk NE NBX.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX.
  destruct (arr0_facts Σ OW LB m ls PL EA SPX rr Dr HEAP PARTS FROK HVR ARR) as (UR & DR0 & DRC' & DSEPR).
  pose proof (st_wf_ok x ls WFS HVX NRX) as (_ & TDX & _).
  destruct (lib_state_open [] ls m OW PL EA x X LS ND HX ltac:(intros []) NRX) as ((Dx & SX & ARRX) & _ & _).
  destruct (bn_arr_facts_lin Σ OW LB m HEAP ls PL EA _ _ PARTS FROK x Dx HVX NRX ARRX) as (UX & LENX & DX0 & DXC' & _ & DSEPX).
  pose proof (arr_arr0_disj Σ OW LB m ls PL EA SPX x rr Dx Dr HEAP PARTS FROK NE HVX HVR NRX ARRX ARR) as AD3.
  apply (fun A_ => bn_arr_nofr PL x m OW Dx _ PWF NOFR NRX A_ NBX) in ARRX.
  destruct (ref_at_rangeF ls OW PL EA SPX USTACK_TOP Σ LB m x X HEAP PARTS FROK HX NRX) as (SA0 & SAC & _).
  exists Dx. unfold bn_cells in SX.
  change [C8 (wz Dx); C4 (wz (Z.of_nat (bn_top (getbn x ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn x ls))));
          C4 (wz (Z.b2z (bn_neg (getbn x ls)))); C4 (wz (bn_flags (getbn x ls)))]
    with ([C8 (wz Dx)] ++ [C4 (wz (Z.of_nat (bn_top (getbn x ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn x ls))));
          C4 (wz (Z.b2z (bn_neg (getbn x ls)))); C4 (wz (bn_flags (getbn x ls)))]) in SX.
  apply bk_rw_cells_app in SX. destruct SX as [SX1 _].
  split; [exact SX1|]. split; [apply limbs_at_firstn; exact UX|]. split; [exact UX|]. split; [exact ARRX|].
  pose proof (struct_disj Σ OW LB m HEAP ls PL EA _ _ PARTS FROK x rr X R NE HX HR) as SD.
  pose proof (DSEPX rr R HR) as D1. pose proof (DSEPR x X HX NRX) as D2.
  lia.
Qed.

Lemma arr_splice0 : forall W m m' D (buf w : list Z),
  u64arr bgasegs m D (wlimbs buf) -> munch W m m' -> wmono bgasegs m m' -> limbs_at bgasegs m' D w -> (length w <= length buf)%nat ->
  disjoint_from W D 0 ->
  disjoint_from W (D + 8 * Z.of_nat (length w)) (8 * Z.of_nat (length buf - length w)) ->
  u64arr bgasegs m' D (wlimbs (splice buf 0 w)).
Proof.
  intros W m m' D buf w UR MU WM HWL Hlen DJ0 DJ.
  apply (limbarr_limbs_at bgasegs) in UR. destruct UR as [HL1 HW1].
  assert (LS : length (splice buf 0 w) = length buf) by (apply splice_length; lia).
  pose proof (limbs_at_bound _ _ _ _ HL1) as BD.
  apply u64arr_of_limbs_at.
  - replace D with (D + 8 * Z.of_nat 0)%Z in HWL by lia.
    replace D with (D + 8 * Z.of_nat 0)%Z at 1 by lia. rewrite Z.add_0_r.
    eapply (BnKaraMem.limbs_at_splice bgasegs W m m' D buf 0 w HL1 MU); [lia | exact HWL | |].
    + replace (8 * Z.of_nat 0) with 0 by lia. exact DJ0.
    + exact DJ.
  - rewrite LS. eapply wr_at_transport; [exact HW1 | exact WM].
Qed.

Lemma open_full : forall Σ OW LB m ls PL EA SPX r a,
  AHEAP Σ OW LB m -> lib_state ls m OW PL EA -> frames_ok LB PL SPX USTACK_TOP -> frames_lb PL LB -> ref_at ls OW PL r a -> not_one r -> nbuf PL r ->
  exists D, rw_cells bgasegs m a (bn_cells D (getbn r ls)) /\ BnRepDefs.bn_arr m OW D (getbn r ls) /\ bg_ok (getbn r ls)
    /\ u64arr bgasegs m D (wlimbs (bn_buf (getbn r ls)))
    /\ 0 < a /\ a + 24 <= ACEIL /\ 0 <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= ACEIL
    /\ (forall r' a', ref_at ls OW PL r' a' -> a' + 24 <= D \/ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= a').
Proof.
  intros Σ OW LB m ls PL EA SPX r a HEAP LS FROK NOFR HA NRO NB.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_open [] ls m OW PL EA r a LS ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & OK & _).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
  destruct (ref_at_rangeF ls OW PL EA SPX USTACK_TOP Σ LB m r a HEAP PARTS FROK HA NRO) as (SA0 & SAC & SAI).
  destruct (bn_arr_facts_lin Σ OW LB m HEAP ls PL EA _ _ PARTS FROK r D HV NRO ARR) as (U & LENW & D0 & DC' & DI & DSEP).
  apply (fun A_ => bn_arr_nofr PL r m OW D _ PWF NOFR NRO A_ NB) in ARR.
  exists D. split; [exact BN|]. split; [exact ARR|]. split; [exact OK|]. split; [exact U|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact DC' | exact DSEP].
Qed.

Lemma bn_arrs_disj : forall Σ OW LB m ls PL EA r1 r2 a1 a2 D1 D2,
  AHEAP Σ OW LB m -> lib_state ls m OW PL EA -> r1 <> r2 -> ref_at ls OW PL r1 a1 -> ref_at ls OW PL r2 a2 ->
  BnRepDefs.bn_arr m OW D1 (getbn r1 ls) -> BnRepDefs.bn_arr m OW D2 (getbn r2 ls) ->
  D1 + 8 * Z.of_nat (bn_dmax (getbn r1 ls)) <= D2 \/ D2 + 8 * Z.of_nat (bn_dmax (getbn r2 ls)) <= D1.
Proof.
  intros Σ OW LB m ls PL EA r1 r2 a1 a2 D1 D2 HEAP LS NE H1 H2 ARR1 ARR2.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS H1) as HV1. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS H2) as HV2.
  pose proof (arr_ceilA _ _ _ _ _ _ HEAP ARR1) as [D10 _]. pose proof (arr_ceilA _ _ _ _ _ _ HEAP ARR2) as [D20 _].
  unfold BnRepDefs.bn_arr in ARR1, ARR2.
  destruct (bn_d (getbn r1 ls)) as [p1|] eqn:E1, (bn_d (getbn r2 ls)) as [p2|] eqn:E2.
  - destruct ARR1 as [Hin1 _], ARR2 as [Hin2 _].
    exact (limbs_limbs_disj Σ OW LB m HEAP ls PL EA PARTS r1 r2 p1 D1 _ p2 D2 _ NE HV1 HV2 E1 E2 Hin1 Hin2).
  - destruct ARR2 as [-> Eb]. unfold bn_dmax at 2. rewrite Eb. cbn [length]. lia.
  - destruct ARR1 as [-> Eb]. unfold bn_dmax at 1. rewrite Eb. cbn [length]. lia.
  - destruct ARR1 as [-> Eb]. unfold bn_dmax at 1. rewrite Eb. cbn [length]. lia.
Qed.

Lemma d_cell : forall m a D (b : bignum bptr), rw_cells bgasegs m a (bn_cells D b) -> rw_cells bgasegs m a [C8 (wz D)].
Proof.
  intros m a D b SX. unfold bn_cells in SX.
  change [C8 (wz D); C4 (wz (Z.of_nat (bn_top b))); C4 (wz (Z.of_nat (bn_dmax b))); C4 (wz (Z.b2z (bn_neg b))); C4 (wz (bn_flags b))]
    with ([C8 (wz D)] ++ [C4 (wz (Z.of_nat (bn_top b))); C4 (wz (Z.of_nat (bn_dmax b))); C4 (wz (Z.b2z (bn_neg b))); C4 (wz (bn_flags b))]) in SX.
  apply bk_rw_cells_app in SX. exact (proj1 SX).
Qed.

Lemma open_ro_sh : forall Σ OW LB m ls PL EA SPX r a,
  AHEAP Σ OW LB m -> lib_state ls m OW PL EA -> frames_ok LB PL SPX USTACK_TOP -> frames_lb PL LB -> ref_at ls OW PL r a -> not_one r ->
  exists D, rw_cells bgasegs m a (bn_cells D (getbn r ls)) /\ bg_ok (getbn r ls)
    /\ u64arr bgasegs m D (wlimbs (bn_buf (getbn r ls)))
    /\ 0 < a /\ a + 24 <= ACEIL /\ 0 <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= ACEIL
    /\ acc bgasegs m a 24 /\ a mod 8 = 0
    /\ acc bgasegs m D (8 * Z.of_nat (bn_top (getbn r ls))) /\ D mod 8 = 0.
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
  exists D. do 7 (split; [assumption|]). split; [exact ACS|]. split; [exact ALS|]. split; [|exact ALD].
  pose proof OK as (_ & TD & _). eapply acc_sub; [exact ACD | lia | unfold bn_dmax in *; lia].
Qed.

Lemma operand_view_sh : forall Σ OW LB m ls PL EA SPX rr R Dr x X k,
  AHEAP Σ OW LB m -> lib_state ls m OW PL EA -> frames_ok LB PL SPX USTACK_TOP -> frames_lb PL LB ->
  ref_at ls OW PL rr R -> not_one rr -> rw_cells bgasegs m R (bn_cells Dr (getbn rr ls)) -> BnRepDefs.bn_arr m OW Dr (getbn rr ls) ->
  ref_at ls OW PL x X -> not_one x -> (k <= bn_top (getbn x ls))%nat ->
  exists Dx, (acc bgasegs m Dx (8 * Z.of_nat k) /\ Dx mod 8 = 0) /\ rw_cells bgasegs m X [C8 (wz Dx)] /\ limbs_at bgasegs m Dx (firstn k (bn_buf (getbn x ls)))
    /\ 0 < X /\ X + 24 <= ACEIL /\ 0 <= Dx /\ Dx + 8 * Z.of_nat k <= ACEIL
    /\ (X = R \/ X + 24 <= R \/ R + 24 <= X)
    /\ (R + 24 <= Dx \/ Dx + 8 * Z.of_nat k <= R)
    /\ (Dx = Dr \/ Dr + 8 * Z.of_nat (bn_dmax (getbn rr ls)) <= Dx \/ Dx + 8 * Z.of_nat k <= Dr).
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
    specialize (DSEPR rr R HR NRR). unfold bn_dmax in *. lia.
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
    unfold bn_dmax in *. lia.
Qed.

End WithRT.
