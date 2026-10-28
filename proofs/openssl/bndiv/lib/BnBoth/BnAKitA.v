(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA ZBridge Arr.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Malloc Prog BnBase BnWords BnModel BnTree BnInv BnSpecs BnMInv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_defs.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnMem BnCmp BnKaraMem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA BnIfaceA AsStruct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnWU Require BnUTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Lemma bn_post_silentA : forall {A : Type} (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (lo : Z) (m m' : mem) (AD : bn_addrs) (EA : err_addrs) (cost : Z)
    (RES : A -> lstate bptr -> list block -> word -> Prop) (res : A)
    (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (W : list (Z * Z)) (stack : Z),
  bn_preA Σ ls m OW LB AD EA sp lo stack cost -> 0 <= stack -> 0 <= cost ->
  munch W m m' -> wmono bsegs m m' -> Forall (w_okc OW LB ls AD EA false []) W -> Forall (w_lib OW lo (bv_unsigned sp)) W ->
  stk bsegs m' lo (bv_unsigned sp) -> mem_inv bsegs m' ->
  RES res ls OW a0 ->
  bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA cost RES (res, ls) Σ
    (MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc ra) fc None m' (seg_rom bsegs)).
Proof.
  intros A ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Σ ls OW LB lo m m' AD EA cost RES res
         t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 W stack
         (HEAP & LS & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED) HS HC MU WM WOK WL ST' MI' HRES.
  unfold bn_postA. exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F, fc, m', OW.
  split; [reflexivity|]. cbn [fst snd].
  split; [eapply (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM WL CEIL); unfold USTACK_TOP in *; lia|].
  split; [exact (lib_state_frame Σ LB [] ls m m' OW AD EA W HEAP LS MU WM WOK)|].
  split; [exact ST'|]. split; [exact MI'|].
  split; [eapply (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP MU WL CEIL); lia|].
  split; [lia|]. split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|]. exact HRES.
Qed.

(* [comment removed for export] *)
Lemma ref_shA : forall Σ OW LB m cxo hs ls AD EA r a,
  AHEAP Σ OW LB m -> lib_state_hc cxo hs ls m OW AD EA -> ref_at ls OW AD r a ->
  acc bsegs m a 24 /\ a mod 8 = 0 /\ (a + 24 <= SHLO \/ SHHI <= a).
Proof.
  intros Σ OW LB m cxo hs ls AD EA r a HEAP LS HA.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  destruct (ref_at_inb _ _ _ _ _ ADB HA) as (qx & Ax & nx & Eqx & Hinx & Rx1 & Rx2).
  assert (INX : In (qx, Ax, nx) (OW ++ LB)) by (apply in_or_app; left; exact Hinx).
  split; [exact (AH_acc_in _ _ _ _ (qx, Ax, nx) a 24 HEAP INX Rx1 Rx2)|].
  split; [exact (ref_at_al8 _ _ _ _ _ _ _ _ HEAP ADB HA)|].
  pose proof (AH_offsh _ _ _ _ (qx, Ax, nx) HEAP INX) as OX. cbn [blk_addr blk_size fst snd] in OX. lia.
Qed.

Lemma arr_shA : forall Σ OW LB m D (b : bignum bptr),
  AHEAP Σ OW LB m -> bn_arr m OW D b ->
  acc bsegs m D (8 * Z.of_nat (bn_dmax b)) /\ D mod 8 = 0 /\ (D + 8 * Z.of_nat (bn_dmax b) <= SHLO \/ SHHI <= D).
Proof.
  intros Σ OW LB m D b HEAP ARR. unfold bn_arr in ARR. destruct (bn_d b) as [p|] eqn:Ed.
  - destruct ARR as [Hin _]. assert (INX : In (p, D, 8 * Z.of_nat (bn_dmax b)) (OW ++ LB)) by (apply in_or_app; left; exact Hin).
    split; [exact (AH_acc_in _ _ _ _ (p, D, 8 * Z.of_nat (bn_dmax b)) D (8 * Z.of_nat (bn_dmax b)) HEAP INX ltac:(cbn [blk_addr blk_size fst snd]; lia) ltac:(cbn [blk_addr blk_size fst snd]; lia))|].
    pose proof (AH_okA _ _ _ _ _ _ _ HEAP Hin) as [H16 _].
    split; [clear - H16; Z.div_mod_to_equations; lia|].
    pose proof (AH_offsh _ _ _ _ (p, D, 8 * Z.of_nat (bn_dmax b)) HEAP INX) as OX. cbn [blk_addr blk_size fst snd] in OX. lia.
  - destruct ARR as [-> Eb]. unfold bn_dmax. rewrite Eb. cbn [length Z.of_nat].
    split; [intros i Hi; lia|]. split; [reflexivity|]. left. unfold SHLO. lia.
Qed.

(* [comment removed for export] *)
Lemma open_ro : forall Σ OW LB m ls AD EA r a,
  AHEAP Σ OW LB m -> lib_state ls m OW AD EA -> ref_at ls OW AD r a ->
  exists D, rw_cells bsegs m a (bn_cells D (getbn r ls)) /\ bn_okm (getbn r ls)
    /\ u64arr bsegs m D (wlimbs (bn_buf (getbn r ls)))
    /\ 0 < a /\ a + 24 <= ACEIL /\ 0 <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= ACEIL.
Proof.
  intros Σ OW LB m ls AD EA r a HEAP LS HA.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_open [] ls m OW AD EA r a LS ND HA ltac:(intros [])) as ((D & BN & ARR) & OK & _).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  destruct (ref_at_inb _ _ _ _ _ ADB HA) as (qs & As & ns & Eqs & Hins & Ra1 & Ra2).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & SA16 & _ & SAC & SAI).
  destruct (bn_arr_facts Σ OW LB m HEAP ls AD EA IDS ADB r D HV ARR) as (U & LENW & D0 & DC & DI & DSEP).
  exists D. split; [exact BN|]. split; [exact OK|]. split; [exact U|]. lia.
Qed.

(* [comment removed for export] *)
Lemma limbs_at_firstn : forall m D (l : list Z) k, u64arr bsegs m D (wlimbs l) -> limbs_at bsegs m D (firstn k l).
Proof.
  intros m D l k U. destruct (Nat.le_gt_cases k (length l)) as [Hk|Hk].
  - apply (proj1 (limbarr_split bsegs m D l k Hk)) in U. destruct U as [U _]. apply limbs_at_of_u64arr. exact U.
  - rewrite firstn_all2 by lia. apply limbs_at_of_u64arr. exact U.
Qed.

(* [comment removed for export] *)
Lemma operand_view : forall Σ OW LB m ls AD EA rr R Dr x X k,
  AHEAP Σ OW LB m -> lib_state ls m OW AD EA ->
  ref_at ls OW AD rr R -> rw_cells bsegs m R (bn_cells Dr (getbn rr ls)) -> bn_arr m OW Dr (getbn rr ls) ->
  ref_at ls OW AD x X -> (k <= bn_top (getbn x ls))%nat ->
  exists Dx, rw_cells bsegs m X [C8 (wz Dx)] /\ limbs_at bsegs m Dx (firstn k (bn_buf (getbn x ls)))
    /\ 0 < X /\ X + 24 <= ACEIL /\ 0 <= Dx /\ Dx + 8 * Z.of_nat k <= ACEIL
    /\ (X = R \/ X + 24 <= R \/ R + 24 <= X)
    /\ (R + 24 <= Dx \/ Dx + 8 * Z.of_nat k <= R)
    /\ (Dx = Dr \/ Dr + 8 * Z.of_nat (bn_dmax (getbn rr ls)) <= Dx \/ Dx + 8 * Z.of_nat k <= Dr).
Proof.
  intros Σ OW LB m ls AD EA rr R Dr x X k HEAP LS HR SR ARR HX Hk.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX.
  destruct (bn_arr_facts Σ OW LB m HEAP ls AD EA IDS ADB rr Dr HVR ARR) as (UR & LENR & DR0 & DRC & _ & DSEPR).
  pose proof (st_okm_getbn x ls SOK HVX) as (_ & TDX & _).
  destruct (bnref_eq_dec x rr) as [->|NE].
  - (* [comment removed for export] *)
    pose proof (ref_at_fun _ _ _ _ _ _ ND HX HR) as ->.
    destruct (ref_at_inb _ _ _ _ _ ADB HR) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
    pose proof (AH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & _).
    exists Dr. unfold bn_cells in SR.
    change [C8 (wz Dr); C4 (wz (Z.of_nat (bn_top (getbn rr ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn rr ls))));
            C4 (wz (Z.b2z (bn_neg (getbn rr ls)))); C4 (wz (bn_flags (getbn rr ls)))]
      with ([C8 (wz Dr)] ++ [C4 (wz (Z.of_nat (bn_top (getbn rr ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn rr ls))));
            C4 (wz (Z.b2z (bn_neg (getbn rr ls)))); C4 (wz (bn_flags (getbn rr ls)))]) in SR.
    apply bk_rw_cells_app in SR. destruct SR as [SR1 _].
    split; [exact SR1|]. split; [apply limbs_at_firstn; exact UR|].
    specialize (DSEPR rr R HR). unfold bn_dmax in *. lia.
  - destruct (lib_state_open [] ls m OW AD EA x X LS ND HX ltac:(intros [])) as ((Dx & SX & ARRX) & _ & _).
    destruct (bn_arr_facts Σ OW LB m HEAP ls AD EA IDS ADB x Dx HVX ARRX) as (UX & LENX & DX0 & DXC & _ & DSEPX).
    destruct (ref_at_inb _ _ _ _ _ ADB HX) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
    pose proof (AH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & _).
    exists Dx. unfold bn_cells in SX.
    change [C8 (wz Dx); C4 (wz (Z.of_nat (bn_top (getbn x ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn x ls))));
            C4 (wz (Z.b2z (bn_neg (getbn x ls)))); C4 (wz (bn_flags (getbn x ls)))]
      with ([C8 (wz Dx)] ++ [C4 (wz (Z.of_nat (bn_top (getbn x ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn x ls))));
            C4 (wz (Z.b2z (bn_neg (getbn x ls)))); C4 (wz (bn_flags (getbn x ls)))]) in SX.
    apply bk_rw_cells_app in SX. destruct SX as [SX1 _].
    split; [exact SX1|]. split; [apply limbs_at_firstn; exact UX|].
    pose proof (struct_disj Σ OW LB m HEAP ls AD EA IDS ADB x rr X R NE HX HR) as SD.
    specialize (DSEPX rr R HR).
    assert (AD3 : Dx = Dr \/ Dr + 8 * Z.of_nat (bn_dmax (getbn rr ls)) <= Dx \/ Dx + 8 * Z.of_nat k <= Dr).
    { unfold bn_arr in ARR, ARRX.
      destruct (bn_d (getbn x ls)) as [px|] eqn:Edx, (bn_d (getbn rr ls)) as [pr|] eqn:Edr.
      - destruct ARR as [HinR _], ARRX as [HinX _].
        pose proof (limbs_limbs_disj Σ OW LB m HEAP ls AD EA IDS x rr px Dx _ pr Dr _ NE HVX HVR Edx Edr HinX HinR) as LD.
        unfold bn_dmax in *. lia.
      - destruct ARR as [-> Eb]. unfold bn_dmax. rewrite Eb. cbn [length]. lia.
      - destruct ARRX as [-> Eb]. unfold bn_dmax in TDX. rewrite Eb in TDX. cbn [length] in TDX. lia.
      - destruct ARR as [-> Eb]. unfold bn_dmax. rewrite Eb. cbn [length]. lia. }
    unfold bn_dmax in *. lia.
Qed.

(* [comment removed for export] *)
Lemma operand_view_ne : forall Σ OW LB m ls AD EA rr R Dr x X k,
  AHEAP Σ OW LB m -> lib_state ls m OW AD EA ->
  ref_at ls OW AD rr R -> rw_cells bsegs m R (bn_cells Dr (getbn rr ls)) -> bn_arr m OW Dr (getbn rr ls) ->
  ref_at ls OW AD x X -> (k <= bn_top (getbn x ls))%nat -> x <> rr ->
  exists Dx, rw_cells bsegs m X [C8 (wz Dx)] /\ limbs_at bsegs m Dx (firstn k (bn_buf (getbn x ls)))
    /\ u64arr bsegs m Dx (wlimbs (bn_buf (getbn x ls))) /\ bn_arr m OW Dx (getbn x ls)
    /\ 0 < X /\ X + 24 <= ACEIL /\ 0 <= Dx /\ Dx + 8 * Z.of_nat (bn_dmax (getbn x ls)) <= ACEIL
    /\ (X + 24 <= R \/ R + 24 <= X)
    /\ (R + 24 <= Dx \/ Dx + 8 * Z.of_nat (bn_dmax (getbn x ls)) <= R)
    /\ (X + 24 <= Dr \/ Dr + 8 * Z.of_nat (bn_dmax (getbn rr ls)) <= X)
    /\ (Dr + 8 * Z.of_nat (bn_dmax (getbn rr ls)) <= Dx \/ Dx + 8 * Z.of_nat (bn_dmax (getbn x ls)) <= Dr).
Proof.
  intros Σ OW LB m ls AD EA rr R Dr x X k HEAP LS HR SR ARR HX Hk NE.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX.
  destruct (bn_arr_facts Σ OW LB m HEAP ls AD EA IDS ADB rr Dr HVR ARR) as (UR & LENR & DR0 & DRC & _ & DSEPR).
  destruct (lib_state_open [] ls m OW AD EA x X LS ND HX ltac:(intros [])) as ((Dx & SX & ARRX) & _ & _).
  destruct (bn_arr_facts Σ OW LB m HEAP ls AD EA IDS ADB x Dx HVX ARRX) as (UX & LENX & DX0 & DXC & _ & DSEPX).
  destruct (ref_at_inb _ _ _ _ _ ADB HX) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & _).
  exists Dx. unfold bn_cells in SX.
  change [C8 (wz Dx); C4 (wz (Z.of_nat (bn_top (getbn x ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn x ls))));
          C4 (wz (Z.b2z (bn_neg (getbn x ls)))); C4 (wz (bn_flags (getbn x ls)))]
    with ([C8 (wz Dx)] ++ [C4 (wz (Z.of_nat (bn_top (getbn x ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn x ls))));
          C4 (wz (Z.b2z (bn_neg (getbn x ls)))); C4 (wz (bn_flags (getbn x ls)))]) in SX.
  apply bk_rw_cells_app in SX. destruct SX as [SX1 _].
  split; [exact SX1|]. split; [apply limbs_at_firstn; exact UX|]. split; [exact UX|]. split; [exact ARRX|].
  pose proof (struct_disj Σ OW LB m HEAP ls AD EA IDS ADB x rr X R NE HX HR) as SD.
  pose proof (DSEPX rr R HR) as D1. pose proof (DSEPR x X HX) as D2.
  assert (AD3 : Dr + 8 * Z.of_nat (bn_dmax (getbn rr ls)) <= Dx \/ Dx + 8 * Z.of_nat (bn_dmax (getbn x ls)) <= Dr).
  { unfold bn_arr in ARR, ARRX.
    destruct (bn_d (getbn x ls)) as [px|] eqn:Edx, (bn_d (getbn rr ls)) as [pr|] eqn:Edr.
    - destruct ARR as [HinR _], ARRX as [HinX _].
      pose proof (limbs_limbs_disj Σ OW LB m HEAP ls AD EA IDS x rr px Dx _ pr Dr _ NE HVX HVR Edx Edr HinX HinR) as LD. lia.
    - destruct ARR as [-> Eb]. unfold bn_dmax at 1. rewrite Eb. cbn [length]. lia.
    - destruct ARRX as [-> Eb]. unfold bn_dmax at 2. rewrite Eb. cbn [length]. lia.
    - destruct ARR as [-> Eb]. unfold bn_dmax at 1. rewrite Eb. cbn [length]. lia. }
  lia.
Qed.

(* [comment removed for export] *)
Lemma arr_splice0 : forall W m m' D (buf w : list Z),
  u64arr bsegs m D (wlimbs buf) -> munch W m m' -> wmono bsegs m m' -> limbs_at bsegs m' D w -> (length w <= length buf)%nat ->
  disjoint_from W D 0 ->
  disjoint_from W (D + 8 * Z.of_nat (length w)) (8 * Z.of_nat (length buf - length w)) ->
  u64arr bsegs m' D (wlimbs (splice buf 0 w)).
Proof.
  intros W m m' D buf w UR MU WM HWL Hlen DJ0 DJ.
  apply (limbarr_limbs_at bsegs) in UR. destruct UR as [HL1 HW1].
  assert (LS : length (splice buf 0 w) = length buf) by (apply splice_length; lia).
  pose proof (limbs_at_bound _ _ _ _ HL1) as BD.
  apply u64arr_of_limbs_at.
  - replace D with (D + 8 * Z.of_nat 0)%Z in HWL by lia.
    replace D with (D + 8 * Z.of_nat 0)%Z at 1 by lia. rewrite Z.add_0_r.
    eapply (BnKaraMem.limbs_at_splice bsegs W m m' D buf 0 w HL1 MU); [lia | exact HWL | |].
    + replace (8 * Z.of_nat 0) with 0 by lia. exact DJ0.
    + exact DJ.
  - rewrite LS. eapply wr_at_transport; [exact HW1 | exact WM].
Qed.

(* [comment removed for export] *)
Lemma open_full : forall Σ OW LB m ls AD EA r a,
  AHEAP Σ OW LB m -> lib_state ls m OW AD EA -> ref_at ls OW AD r a ->
  exists D, rw_cells bsegs m a (bn_cells D (getbn r ls)) /\ bn_arr m OW D (getbn r ls) /\ bn_okm (getbn r ls)
    /\ u64arr bsegs m D (wlimbs (bn_buf (getbn r ls)))
    /\ 0 < a /\ a + 24 <= ACEIL /\ 0 <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= ACEIL
    /\ (forall r' a', ref_at ls OW AD r' a' -> a' + 24 <= D \/ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= a').
Proof.
  intros Σ OW LB m ls AD EA r a HEAP LS HA.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_open [] ls m OW AD EA r a LS ND HA ltac:(intros [])) as ((D & BN & ARR) & OK & _).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  destruct (ref_at_inb _ _ _ _ _ ADB HA) as (qs & As & ns & Eqs & Hins & Ra1 & Ra2).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & SA16 & _ & SAC & SAI).
  destruct (bn_arr_facts Σ OW LB m HEAP ls AD EA IDS ADB r D HV ARR) as (U & LENW & D0 & DC & DI & DSEP).
  exists D. split; [exact BN|]. split; [exact ARR|]. split; [exact OK|]. split; [exact U|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact DC | exact DSEP].
Qed.

(* [comment removed for export] *)
Lemma bn_arrs_disj : forall Σ OW LB m ls AD EA r1 r2 a1 a2 D1 D2,
  AHEAP Σ OW LB m -> lib_state ls m OW AD EA -> r1 <> r2 -> ref_at ls OW AD r1 a1 -> ref_at ls OW AD r2 a2 ->
  bn_arr m OW D1 (getbn r1 ls) -> bn_arr m OW D2 (getbn r2 ls) ->
  D1 + 8 * Z.of_nat (bn_dmax (getbn r1 ls)) <= D2 \/ D2 + 8 * Z.of_nat (bn_dmax (getbn r2 ls)) <= D1.
Proof.
  intros Σ OW LB m ls AD EA r1 r2 a1 a2 D1 D2 HEAP LS NE H1 H2 ARR1 ARR2.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS H1) as HV1. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS H2) as HV2.
  destruct (bn_arr_facts Σ OW LB m HEAP ls AD EA IDS ADB r1 D1 HV1 ARR1) as (_ & _ & D10 & _).
  destruct (bn_arr_facts Σ OW LB m HEAP ls AD EA IDS ADB r2 D2 HV2 ARR2) as (_ & _ & D20 & _).
  unfold bn_arr in ARR1, ARR2.
  destruct (bn_d (getbn r1 ls)) as [p1|] eqn:E1, (bn_d (getbn r2 ls)) as [p2|] eqn:E2.
  - destruct ARR1 as [Hin1 _], ARR2 as [Hin2 _].
    exact (limbs_limbs_disj Σ OW LB m HEAP ls AD EA IDS r1 r2 p1 D1 _ p2 D2 _ NE HV1 HV2 E1 E2 Hin1 Hin2).
  - destruct ARR2 as [-> Eb]. unfold bn_dmax at 2. rewrite Eb. cbn [length]. lia.
  - destruct ARR1 as [-> Eb]. unfold bn_dmax at 1. rewrite Eb. cbn [length]. lia.
  - destruct ARR1 as [-> Eb]. unfold bn_dmax at 1. rewrite Eb. cbn [length]. lia.
Qed.

(* [comment removed for export] *)
Lemma d_cell : forall m a D (b : bignum bptr), rw_cells bsegs m a (bn_cells D b) -> rw_cells bsegs m a [C8 (wz D)].
Proof.
  intros m a D b SX. unfold bn_cells in SX.
  change [C8 (wz D); C4 (wz (Z.of_nat (bn_top b))); C4 (wz (Z.of_nat (bn_dmax b))); C4 (wz (Z.b2z (bn_neg b))); C4 (wz (bn_flags b))]
    with ([C8 (wz D)] ++ [C4 (wz (Z.of_nat (bn_top b))); C4 (wz (Z.of_nat (bn_dmax b))); C4 (wz (Z.b2z (bn_neg b))); C4 (wz (bn_flags b))]) in SX.
  apply bk_rw_cells_app in SX. exact (proj1 SX).
Qed.


(* [comment removed for export] *)
Lemma open_ro_sh : forall Σ OW LB m ls AD EA r a,
  AHEAP Σ OW LB m -> lib_state ls m OW AD EA -> ref_at ls OW AD r a ->
  exists D, rw_cells bsegs m a (bn_cells D (getbn r ls)) /\ bn_okm (getbn r ls)
    /\ u64arr bsegs m D (wlimbs (bn_buf (getbn r ls)))
    /\ 0 < a /\ a + 24 <= ACEIL /\ 0 <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= ACEIL
    /\ acc bsegs m a 24 /\ a mod 8 = 0
    /\ acc bsegs m D (8 * Z.of_nat (bn_top (getbn r ls))) /\ D mod 8 = 0.
Proof.
  intros Σ OW LB m ls AD EA r a HEAP LS HA.
  destruct (open_full Σ OW LB m ls AD EA r a HEAP LS HA) as (D & SA & ARR & OK & U & A0 & AC & D0 & DC & _).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS HA) as (ACS & ALS & _).
  destruct (arr_shA _ _ _ _ _ _ HEAP ARR) as (ACD & ALD & _).
  exists D. do 7 (split; [assumption|]). split; [exact ACS|]. split; [exact ALS|]. split; [|exact ALD].
  pose proof OK as (_ & TD & _). eapply acc_sub; [exact ACD | lia | unfold bn_dmax in *; lia].
Qed.


(* [comment removed for export] *)
Lemma operand_view_sh : forall Σ OW LB m ls AD EA rr R Dr x X k,
  AHEAP Σ OW LB m -> lib_state ls m OW AD EA ->
  ref_at ls OW AD rr R -> rw_cells bsegs m R (bn_cells Dr (getbn rr ls)) -> bn_arr m OW Dr (getbn rr ls) ->
  ref_at ls OW AD x X -> (k <= bn_top (getbn x ls))%nat ->
  exists Dx, (acc bsegs m Dx (8 * Z.of_nat k) /\ Dx mod 8 = 0) /\ rw_cells bsegs m X [C8 (wz Dx)] /\ limbs_at bsegs m Dx (firstn k (bn_buf (getbn x ls)))
    /\ 0 < X /\ X + 24 <= ACEIL /\ 0 <= Dx /\ Dx + 8 * Z.of_nat k <= ACEIL
    /\ (X = R \/ X + 24 <= R \/ R + 24 <= X)
    /\ (R + 24 <= Dx \/ Dx + 8 * Z.of_nat k <= R)
    /\ (Dx = Dr \/ Dr + 8 * Z.of_nat (bn_dmax (getbn rr ls)) <= Dx \/ Dx + 8 * Z.of_nat k <= Dr).
Proof.
  intros Σ OW LB m ls AD EA rr R Dr x X k HEAP LS HR SR ARR HX Hk.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX.
  destruct (bn_arr_facts Σ OW LB m HEAP ls AD EA IDS ADB rr Dr HVR ARR) as (UR & LENR & DR0 & DRC & _ & DSEPR).
  pose proof (st_okm_getbn x ls SOK HVX) as (_ & TDX & _).
  destruct (bnref_eq_dec x rr) as [->|NE].
  - (* [comment removed for export] *)
    pose proof (ref_at_fun _ _ _ _ _ _ ND HX HR) as ->.
    destruct (ref_at_inb _ _ _ _ _ ADB HR) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
    pose proof (AH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & _).
    exists Dr. split.
    { destruct (arr_shA _ _ _ _ _ _ HEAP ARR) as (ACD & ALD & _). split; [eapply acc_sub; [exact ACD | lia | unfold bn_dmax in *; lia] | exact ALD]. }
    unfold bn_cells in SR.
    change [C8 (wz Dr); C4 (wz (Z.of_nat (bn_top (getbn rr ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn rr ls))));
            C4 (wz (Z.b2z (bn_neg (getbn rr ls)))); C4 (wz (bn_flags (getbn rr ls)))]
      with ([C8 (wz Dr)] ++ [C4 (wz (Z.of_nat (bn_top (getbn rr ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn rr ls))));
            C4 (wz (Z.b2z (bn_neg (getbn rr ls)))); C4 (wz (bn_flags (getbn rr ls)))]) in SR.
    apply bk_rw_cells_app in SR. destruct SR as [SR1 _].
    split; [exact SR1|]. split; [apply limbs_at_firstn; exact UR|].
    specialize (DSEPR rr R HR). unfold bn_dmax in *. lia.
  - destruct (lib_state_open [] ls m OW AD EA x X LS ND HX ltac:(intros [])) as ((Dx & SX & ARRX) & _ & _).
    destruct (bn_arr_facts Σ OW LB m HEAP ls AD EA IDS ADB x Dx HVX ARRX) as (UX & LENX & DX0 & DXC & _ & DSEPX).
    destruct (ref_at_inb _ _ _ _ _ ADB HX) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
    pose proof (AH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & _).
    exists Dx. split.
    { destruct (arr_shA _ _ _ _ _ _ HEAP ARRX) as (ACD & ALD & _). split; [eapply acc_sub; [exact ACD | lia | unfold bn_dmax in *; lia] | exact ALD]. }
    unfold bn_cells in SX.
    change [C8 (wz Dx); C4 (wz (Z.of_nat (bn_top (getbn x ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn x ls))));
            C4 (wz (Z.b2z (bn_neg (getbn x ls)))); C4 (wz (bn_flags (getbn x ls)))]
      with ([C8 (wz Dx)] ++ [C4 (wz (Z.of_nat (bn_top (getbn x ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn x ls))));
            C4 (wz (Z.b2z (bn_neg (getbn x ls)))); C4 (wz (bn_flags (getbn x ls)))]) in SX.
    apply bk_rw_cells_app in SX. destruct SX as [SX1 _].
    split; [exact SX1|]. split; [apply limbs_at_firstn; exact UX|].
    pose proof (struct_disj Σ OW LB m HEAP ls AD EA IDS ADB x rr X R NE HX HR) as SD.
    specialize (DSEPX rr R HR).
    assert (AD3 : Dx = Dr \/ Dr + 8 * Z.of_nat (bn_dmax (getbn rr ls)) <= Dx \/ Dx + 8 * Z.of_nat k <= Dr).
    { unfold bn_arr in ARR, ARRX.
      destruct (bn_d (getbn x ls)) as [px|] eqn:Edx, (bn_d (getbn rr ls)) as [pr|] eqn:Edr.
      - destruct ARR as [HinR _], ARRX as [HinX _].
        pose proof (limbs_limbs_disj Σ OW LB m HEAP ls AD EA IDS x rr px Dx _ pr Dr _ NE HVX HVR Edx Edr HinX HinR) as LD.
        unfold bn_dmax in *. lia.
      - destruct ARR as [-> Eb]. unfold bn_dmax. rewrite Eb. cbn [length]. lia.
      - destruct ARRX as [-> Eb]. unfold bn_dmax in TDX. rewrite Eb in TDX. cbn [length] in TDX. lia.
      - destruct ARR as [-> Eb]. unfold bn_dmax. rewrite Eb. cbn [length]. lia. }
    unfold bn_dmax in *. lia.
Qed.

Lemma ref_ubA : forall Σ OW LB m ls AD EA r a,
  AHEAP Σ OW LB m -> lib_state ls m OW AD EA -> ref_at ls OW AD r a -> 0 < a /\ a mod 8 = 0 /\ a + 24 <= ACEIL.
Proof.
  intros Σ OW LB m ls AD EA r a HEAP LS HA.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  destruct (ref_at_inb _ _ _ _ _ ADB HA) as (q & A & n & _ & Hin & R1 & R2).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (A0 & _ & _ & AC & _).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS HA) as (_ & AL & _).
  split; [lia |]. split; [exact AL | lia].
Qed.

Lemma arr_pos_ubA : forall Σ OW LB m D (b : bignum bptr) n,
  AHEAP Σ OW LB m -> bn_arr m OW D b -> n <= Z.of_nat (bn_dmax b) -> BnUTac.ub_ptr_ok n D.
Proof.
  intros Σ OW LB m D b n HEAP ARR Hn Hpos. unfold bn_arr in ARR. destruct (bn_d b) as [p|] eqn:Ed.
  - destruct ARR as [Hin _]. pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (R0 & R16 & _).
    split; [exact R0|]. clear - R16. Z.div_mod_to_equations. lia.
  - destruct ARR as [_ Eb]. unfold bn_dmax in Hn. rewrite Eb in Hn. cbn in Hn. lia.
Qed.

Lemma operand_view_shu : forall Σ OW LB m ls AD EA rr R Dr x X k,
  AHEAP Σ OW LB m -> lib_state ls m OW AD EA ->
  ref_at ls OW AD rr R -> rw_cells bsegs m R (bn_cells Dr (getbn rr ls)) -> bn_arr m OW Dr (getbn rr ls) ->
  ref_at ls OW AD x X -> (k <= bn_top (getbn x ls))%nat ->
  exists Dx, (acc bsegs m Dx (8 * Z.of_nat k) /\ Dx mod 8 = 0) /\ rw_cells bsegs m X [C8 (wz Dx)] /\ limbs_at bsegs m Dx (firstn k (bn_buf (getbn x ls)))
    /\ 0 < X /\ X + 24 <= ACEIL /\ 0 <= Dx /\ Dx + 8 * Z.of_nat k <= ACEIL
    /\ (X = R \/ X + 24 <= R \/ R + 24 <= X)
    /\ (R + 24 <= Dx \/ Dx + 8 * Z.of_nat k <= R)
    /\ (Dx = Dr \/ Dr + 8 * Z.of_nat (bn_dmax (getbn rr ls)) <= Dx \/ Dx + 8 * Z.of_nat k <= Dr)
    /\ BnUTac.ub_ptr_ok (Z.of_nat k) Dx.
Proof.
  intros Σ OW LB m ls AD EA rr R Dr x X k HEAP LS HR SR ARR HX Hk.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX.
  destruct (bn_arr_facts Σ OW LB m HEAP ls AD EA IDS ADB rr Dr HVR ARR) as (UR & LENR & DR0 & DRC & _ & DSEPR).
  pose proof (st_okm_getbn x ls SOK HVX) as (_ & TDX & _).
  destruct (bnref_eq_dec x rr) as [->|NE].
  - pose proof (ref_at_fun _ _ _ _ _ _ ND HX HR) as ->.
    destruct (ref_at_inb _ _ _ _ _ ADB HR) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
    pose proof (AH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & _).
    exists Dr. split.
    { destruct (arr_shA _ _ _ _ _ _ HEAP ARR) as (ACD & ALD & _). split; [eapply acc_sub; [exact ACD | lia | unfold bn_dmax in *; lia] | exact ALD]. }
    unfold bn_cells in SR.
    change [C8 (wz Dr); C4 (wz (Z.of_nat (bn_top (getbn rr ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn rr ls))));
            C4 (wz (Z.b2z (bn_neg (getbn rr ls)))); C4 (wz (bn_flags (getbn rr ls)))]
      with ([C8 (wz Dr)] ++ [C4 (wz (Z.of_nat (bn_top (getbn rr ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn rr ls))));
            C4 (wz (Z.b2z (bn_neg (getbn rr ls)))); C4 (wz (bn_flags (getbn rr ls)))]) in SR.
    apply bk_rw_cells_app in SR. destruct SR as [SR1 _].
    split; [exact SR1|]. split; [apply limbs_at_firstn; exact UR|].
    specialize (DSEPR rr R HR).
    assert (UBK : BnUTac.ub_ptr_ok (Z.of_nat k) Dr) by (apply (arr_pos_ubA Σ OW LB m Dr (getbn rr ls) _ HEAP ARR); unfold bn_dmax in *; lia).
    unfold bn_dmax in *. repeat (split; [lia|]). exact UBK.
  - destruct (lib_state_open [] ls m OW AD EA x X LS ND HX ltac:(intros [])) as ((Dx & SX & ARRX) & _ & _).
    destruct (bn_arr_facts Σ OW LB m HEAP ls AD EA IDS ADB x Dx HVX ARRX) as (UX & LENX & DX0 & DXC & _ & DSEPX).
    destruct (ref_at_inb _ _ _ _ _ ADB HX) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
    pose proof (AH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & _).
    exists Dx. split.
    { destruct (arr_shA _ _ _ _ _ _ HEAP ARRX) as (ACD & ALD & _). split; [eapply acc_sub; [exact ACD | lia | unfold bn_dmax in *; lia] | exact ALD]. }
    unfold bn_cells in SX.
    change [C8 (wz Dx); C4 (wz (Z.of_nat (bn_top (getbn x ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn x ls))));
            C4 (wz (Z.b2z (bn_neg (getbn x ls)))); C4 (wz (bn_flags (getbn x ls)))]
      with ([C8 (wz Dx)] ++ [C4 (wz (Z.of_nat (bn_top (getbn x ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn x ls))));
            C4 (wz (Z.b2z (bn_neg (getbn x ls)))); C4 (wz (bn_flags (getbn x ls)))]) in SX.
    apply bk_rw_cells_app in SX. destruct SX as [SX1 _].
    split; [exact SX1|]. split; [apply limbs_at_firstn; exact UX|].
    pose proof (struct_disj Σ OW LB m HEAP ls AD EA IDS ADB x rr X R NE HX HR) as SD.
    specialize (DSEPX rr R HR).
    assert (AD3 : Dx = Dr \/ Dr + 8 * Z.of_nat (bn_dmax (getbn rr ls)) <= Dx \/ Dx + 8 * Z.of_nat k <= Dr).
    { unfold bn_arr in ARR, ARRX.
      destruct (bn_d (getbn x ls)) as [px|] eqn:Edx, (bn_d (getbn rr ls)) as [pr|] eqn:Edr.
      - destruct ARR as [HinR _], ARRX as [HinX _].
        pose proof (limbs_limbs_disj Σ OW LB m HEAP ls AD EA IDS x rr px Dx _ pr Dr _ NE HVX HVR Edx Edr HinX HinR) as LD.
        unfold bn_dmax in *. lia.
      - destruct ARR as [-> Eb]. unfold bn_dmax. rewrite Eb. cbn [length]. lia.
      - destruct ARRX as [-> Eb]. unfold bn_dmax in TDX. rewrite Eb in TDX. cbn [length] in TDX. lia.
      - destruct ARR as [-> Eb]. unfold bn_dmax. rewrite Eb. cbn [length]. lia. }
    assert (UBK : BnUTac.ub_ptr_ok (Z.of_nat k) Dx) by (apply (arr_pos_ubA Σ OW LB m Dx (getbn x ls) _ HEAP ARRX); unfold bn_dmax in *; lia).
    unfold bn_dmax in *. repeat (split; [lia|]). exact UBK.
Qed.

End WithRT.
