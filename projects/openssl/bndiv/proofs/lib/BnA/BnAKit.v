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
From OSSVerify.Proofs.openssl.bndiv.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnModel BnTree BnInv BnSpecs BnMInv BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Layout Lib_iface Lib_kit.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnMem BnCmp BnKaraMem.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnHeap BnArr BnRep BnIface.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

(* [comment removed for export] *)
Lemma cmp_words_range : forall a b, -1 <= cmp_words a b <= 1.
Proof.
  induction a as [|x a IH]; intros [|y b]; cbn [cmp_words]; try lia.
  specialize (IH b). destruct (cmp_words a b =? 0) eqn:E; [|lia].
  destruct (x =? y); [lia|]. destruct (y <? x); lia.
Qed.

Lemma ucmp_pure_range : forall (a b : bignum bptr), bn_okm a -> bn_okm b -> -2147483648 < ucmp_pure a b < 2147483648.
Proof.
  intros a b (_ & TA & DA & _) (_ & TB & DB & _). unfold ucmp_pure. cbv zeta. unfold BN_WORDS_MAX, bn_dmax in *.
  destruct (Z.of_nat (bn_top a) - Z.of_nat (bn_top b) =? 0); [|lia].
  pose proof (cmp_words_range (firstn (bn_top a) (bn_buf a)) (firstn (bn_top b) (bn_buf b))). lia.
Qed.

Lemma cmp_pure_range : forall (a b : bignum bptr), -1 <= cmp_pure a b <= 1.
Proof.
  intros a b. unfold cmp_pure. cbv zeta.
  destruct (negb (eqb (bn_neg a) (bn_neg b))); [destruct (bn_neg a); lia|].
  destruct (bn_top b <? bn_top a)%nat; [destruct (bn_neg a); lia|].
  destruct (bn_top a <? bn_top b)%nat; [destruct (bn_neg a); lia|].
  destruct (cmp_words _ _ =? 0); [lia|]. destruct (0 <? cmp_words _ _); destruct (bn_neg a); lia.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma bn_post_silent : forall {A : Type} (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (ls : lstate bptr) (OW LB : list block) (lo B : Z) (m m' : mem) (AD : bn_addrs) (EA : err_addrs)
    (RES : A -> lstate bptr -> list block -> word -> Prop) (res : A)
    (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (W : list (Z * Z)) (errv errv' : word) (stack : Z),
  bn_pre s ls m OW LB AD EA sp lo B errv stack -> 0 <= stack ->
  munch W m m' -> wmono psegs m m' -> Forall (w_ok OW LB ls AD EA []) W -> Forall (w_lib OW lo (bv_unsigned sp)) W ->
  stk psegs m' lo (bv_unsigned sp) -> rw_cells psegs m' LX_ERRNO [C4 errv'] -> mem_inv psegs m' ->
  RES res ls OW a0 ->
  bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA RES (res, ls) s
    (MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc ra) fc None m' (seg_rom psegs)).
Proof.
  intros A ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m m' AD EA RES res
         t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 W errv errv' stack
         (HEAP & LS & AUX & SPB & ST & CEIL & GLO & LO & ERR & MI) HS MU WM WOK WL ST' ERR' MI' HRES.
  unfold bn_post. exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', OW, errv'.
  split; [reflexivity|]. cbn [fst snd].
  split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM WL CEIL)|].
  split; [exact (lib_state_frame s LB [] ls m m' OW AD EA W HEAP LS MU WM WOK)|].
  split; [exact (seg_auxv _ _ _ _ _ _ _ _ _ HEAP AUX MU WM WL SPB GLO)|].
  split; [exact ST'|]. split; [exact ERR'|]. split; [exact MI'|].
  split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ HEAP MU WM WL CEIL GLO); lia|].
  split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. exact HRES.
Qed.

(* [comment removed for export] *)
Lemma open_ro : forall s OW LB m ls AD EA r a,
  RHEAP s (OW ++ LB) m -> lib_state ls m OW AD EA -> ref_at ls OW AD r a ->
  exists D, rw_cells psegs m a (bn_cells D (getbn r ls)) /\ bn_okm (getbn r ls)
    /\ u64arr psegs m D (wlimbs (bn_buf (getbn r ls)))
    /\ 0 < a /\ a + 24 <= alloc_ceiling /\ 0 <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= alloc_ceiling.
Proof.
  intros s OW LB m ls AD EA r a HEAP LS HA.
  pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_open [] ls m OW AD EA r a LS ND HA ltac:(intros [])) as ((D & BN & ARR) & OK & _).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  destruct (ref_at_inb _ _ _ _ _ ADB HA) as (qs & As & ns & Eqs & Hins & Ra1 & Ra2).
  pose proof (RH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & SA16 & _ & SAC & SAI).
  destruct (bn_arr_facts s OW LB m HEAP ls AD EA IDS ADB r D HV ARR) as (U & LENW & D0 & DC & DI & DSEP).
  exists D. split; [exact BN|]. split; [exact OK|]. split; [exact U|]. lia.
Qed.

(* [comment removed for export] *)
Lemma limbs_at_firstn : forall m D (l : list Z) k, u64arr psegs m D (wlimbs l) -> limbs_at psegs m D (firstn k l).
Proof.
  intros m D l k U. destruct (Nat.le_gt_cases k (length l)) as [Hk|Hk].
  - apply (proj1 (limbarr_split psegs m D l k Hk)) in U. destruct U as [U _]. apply limbs_at_of_u64arr. exact U.
  - rewrite firstn_all2 by lia. apply limbs_at_of_u64arr. exact U.
Qed.

(* [comment removed for export] *)
Lemma operand_view : forall s OW LB m ls AD EA rr R Dr x X k,
  RHEAP s (OW ++ LB) m -> lib_state ls m OW AD EA ->
  ref_at ls OW AD rr R -> rw_cells psegs m R (bn_cells Dr (getbn rr ls)) -> bn_arr m OW Dr (getbn rr ls) ->
  ref_at ls OW AD x X -> (k <= bn_top (getbn x ls))%nat ->
  exists Dx, rw_cells psegs m X [C8 (wz Dx)] /\ limbs_at psegs m Dx (firstn k (bn_buf (getbn x ls)))
    /\ 0 < X /\ X + 24 <= alloc_ceiling /\ 0 <= Dx /\ Dx + 8 * Z.of_nat k <= alloc_ceiling
    /\ (X = R \/ X + 24 <= R \/ R + 24 <= X)
    /\ (R + 24 <= Dx \/ Dx + 8 * Z.of_nat k <= R)
    /\ (Dx = Dr \/ Dr + 8 * Z.of_nat (bn_dmax (getbn rr ls)) <= Dx \/ Dx + 8 * Z.of_nat k <= Dr).
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
    exists Dr. unfold bn_cells in SR.
    change [C8 (wz Dr); C4 (wz (Z.of_nat (bn_top (getbn rr ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn rr ls))));
            C4 (wz (Z.b2z (bn_neg (getbn rr ls)))); C4 (wz (bn_flags (getbn rr ls)))]
      with ([C8 (wz Dr)] ++ [C4 (wz (Z.of_nat (bn_top (getbn rr ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn rr ls))));
            C4 (wz (Z.b2z (bn_neg (getbn rr ls)))); C4 (wz (bn_flags (getbn rr ls)))]) in SR.
    apply bk_rw_cells_app in SR. destruct SR as [SR1 _].
    split; [exact SR1|]. split; [apply limbs_at_firstn; exact UR|].
    specialize (DSEPR rr R HR). unfold bn_dmax in *. lia.
  - destruct (lib_state_open [] ls m OW AD EA x X LS ND HX ltac:(intros [])) as ((Dx & SX & ARRX) & _ & _).
    destruct (bn_arr_facts s OW LB m HEAP ls AD EA IDS ADB x Dx HVX ARRX) as (UX & LENX & DX0 & DXC & _ & DSEPX).
    destruct (ref_at_inb _ _ _ _ _ ADB HX) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & _).
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
    unfold bn_dmax in *. lia.
Qed.

(* [comment removed for export] *)
Lemma operand_view_ne : forall s OW LB m ls AD EA rr R Dr x X k,
  RHEAP s (OW ++ LB) m -> lib_state ls m OW AD EA ->
  ref_at ls OW AD rr R -> rw_cells psegs m R (bn_cells Dr (getbn rr ls)) -> bn_arr m OW Dr (getbn rr ls) ->
  ref_at ls OW AD x X -> (k <= bn_top (getbn x ls))%nat -> x <> rr ->
  exists Dx, rw_cells psegs m X [C8 (wz Dx)] /\ limbs_at psegs m Dx (firstn k (bn_buf (getbn x ls)))
    /\ u64arr psegs m Dx (wlimbs (bn_buf (getbn x ls))) /\ bn_arr m OW Dx (getbn x ls)
    /\ 0 < X /\ X + 24 <= alloc_ceiling /\ 0 <= Dx /\ Dx + 8 * Z.of_nat (bn_dmax (getbn x ls)) <= alloc_ceiling
    /\ (X + 24 <= R \/ R + 24 <= X)
    /\ (R + 24 <= Dx \/ Dx + 8 * Z.of_nat (bn_dmax (getbn x ls)) <= R)
    /\ (X + 24 <= Dr \/ Dr + 8 * Z.of_nat (bn_dmax (getbn rr ls)) <= X)
    /\ (Dr + 8 * Z.of_nat (bn_dmax (getbn rr ls)) <= Dx \/ Dx + 8 * Z.of_nat (bn_dmax (getbn x ls)) <= Dr).
Proof.
  intros s OW LB m ls AD EA rr R Dr x X k HEAP LS HR SR ARR HX Hk NE.
  pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX.
  destruct (bn_arr_facts s OW LB m HEAP ls AD EA IDS ADB rr Dr HVR ARR) as (UR & LENR & DR0 & DRC & _ & DSEPR).
  destruct (lib_state_open [] ls m OW AD EA x X LS ND HX ltac:(intros [])) as ((Dx & SX & ARRX) & _ & _).
  destruct (bn_arr_facts s OW LB m HEAP ls AD EA IDS ADB x Dx HVX ARRX) as (UX & LENX & DX0 & DXC & _ & DSEPX).
  destruct (ref_at_inb _ _ _ _ _ ADB HX) as (qs & As & ns & _ & Hins & Ra1 & Ra2).
  pose proof (RH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & _).
  exists Dx. unfold bn_cells in SX.
  change [C8 (wz Dx); C4 (wz (Z.of_nat (bn_top (getbn x ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn x ls))));
          C4 (wz (Z.b2z (bn_neg (getbn x ls)))); C4 (wz (bn_flags (getbn x ls)))]
    with ([C8 (wz Dx)] ++ [C4 (wz (Z.of_nat (bn_top (getbn x ls)))); C4 (wz (Z.of_nat (bn_dmax (getbn x ls))));
          C4 (wz (Z.b2z (bn_neg (getbn x ls)))); C4 (wz (bn_flags (getbn x ls)))]) in SX.
  apply bk_rw_cells_app in SX. destruct SX as [SX1 _].
  split; [exact SX1|]. split; [apply limbs_at_firstn; exact UX|]. split; [exact UX|]. split; [exact ARRX|].
  pose proof (struct_disj s OW LB m HEAP ls AD EA IDS ADB x rr X R NE HX HR) as SD.
  pose proof (DSEPX rr R HR) as D1. pose proof (DSEPR x X HX) as D2.
  assert (AD3 : Dr + 8 * Z.of_nat (bn_dmax (getbn rr ls)) <= Dx \/ Dx + 8 * Z.of_nat (bn_dmax (getbn x ls)) <= Dr).
  { unfold bn_arr in ARR, ARRX.
    destruct (bn_d (getbn x ls)) as [px|] eqn:Edx, (bn_d (getbn rr ls)) as [pr|] eqn:Edr.
    - destruct ARR as [HinR _], ARRX as [HinX _].
      pose proof (limbs_limbs_disj s OW LB m HEAP ls AD EA IDS x rr px Dx _ pr Dr _ NE HVX HVR Edx Edr HinX HinR) as LD. lia.
    - destruct ARR as [-> Eb]. unfold bn_dmax at 1. rewrite Eb. cbn [length]. lia.
    - destruct ARRX as [-> Eb]. unfold bn_dmax at 2. rewrite Eb. cbn [length]. lia.
    - destruct ARR as [-> Eb]. unfold bn_dmax at 1. rewrite Eb. cbn [length]. lia. }
  lia.
Qed.

(* [comment removed for export] *)
Lemma arr_splice0 : forall W m m' D (buf w : list Z),
  u64arr psegs m D (wlimbs buf) -> munch W m m' -> wmono psegs m m' -> limbs_at psegs m' D w -> (length w <= length buf)%nat ->
  disjoint_from W D 0 ->
  disjoint_from W (D + 8 * Z.of_nat (length w)) (8 * Z.of_nat (length buf - length w)) ->
  u64arr psegs m' D (wlimbs (splice buf 0 w)).
Proof.
  intros W m m' D buf w UR MU WM HWL Hlen DJ0 DJ.
  apply (limbarr_limbs_at psegs) in UR. destruct UR as [HL1 HW1].
  assert (LS : length (splice buf 0 w) = length buf) by (apply splice_length; lia).
  pose proof (limbs_at_bound _ _ _ _ HL1) as BD.
  apply u64arr_of_limbs_at.
  - replace D with (D + 8 * Z.of_nat 0)%Z in HWL by lia.
    replace D with (D + 8 * Z.of_nat 0)%Z at 1 by lia. rewrite Z.add_0_r.
    eapply (BnKaraMem.limbs_at_splice psegs W m m' D buf 0 w HL1 MU); [lia | exact HWL | |].
    + replace (8 * Z.of_nat 0) with 0 by lia. exact DJ0.
    + exact DJ.
  - rewrite LS. eapply wr_at_transport; [exact HW1 | exact WM].
Qed.

(* [comment removed for export] *)
Lemma open_full : forall s OW LB m ls AD EA r a,
  RHEAP s (OW ++ LB) m -> lib_state ls m OW AD EA -> ref_at ls OW AD r a ->
  exists D, rw_cells psegs m a (bn_cells D (getbn r ls)) /\ bn_arr m OW D (getbn r ls) /\ bn_okm (getbn r ls)
    /\ u64arr psegs m D (wlimbs (bn_buf (getbn r ls)))
    /\ 0 < a /\ a + 24 <= alloc_ceiling /\ 0 <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= alloc_ceiling
    /\ (forall r' a', ref_at ls OW AD r' a' -> a' + 24 <= D \/ D + 8 * Z.of_nat (bn_dmax (getbn r ls)) <= a').
Proof.
  intros s OW LB m ls AD EA r a HEAP LS HA.
  pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_open [] ls m OW AD EA r a LS ND HA ltac:(intros [])) as ((D & BN & ARR) & OK & _).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  destruct (ref_at_inb _ _ _ _ _ ADB HA) as (qs & As & ns & Eqs & Hins & Ra1 & Ra2).
  pose proof (RH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & SA16 & _ & SAC & SAI).
  destruct (bn_arr_facts s OW LB m HEAP ls AD EA IDS ADB r D HV ARR) as (U & LENW & D0 & DC & DI & DSEP).
  exists D. split; [exact BN|]. split; [exact ARR|]. split; [exact OK|]. split; [exact U|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact DC | exact DSEP].
Qed.

(* [comment removed for export] *)
Lemma bn_arrs_disj : forall s OW LB m ls AD EA r1 r2 a1 a2 D1 D2,
  RHEAP s (OW ++ LB) m -> lib_state ls m OW AD EA -> r1 <> r2 -> ref_at ls OW AD r1 a1 -> ref_at ls OW AD r2 a2 ->
  bn_arr m OW D1 (getbn r1 ls) -> bn_arr m OW D2 (getbn r2 ls) ->
  D1 + 8 * Z.of_nat (bn_dmax (getbn r1 ls)) <= D2 \/ D2 + 8 * Z.of_nat (bn_dmax (getbn r2 ls)) <= D1.
Proof.
  intros s OW LB m ls AD EA r1 r2 a1 a2 D1 D2 HEAP LS NE H1 H2 ARR1 ARR2.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS H1) as HV1. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS H2) as HV2.
  destruct (bn_arr_facts s OW LB m HEAP ls AD EA IDS ADB r1 D1 HV1 ARR1) as (_ & _ & D10 & _).
  destruct (bn_arr_facts s OW LB m HEAP ls AD EA IDS ADB r2 D2 HV2 ARR2) as (_ & _ & D20 & _).
  unfold bn_arr in ARR1, ARR2.
  destruct (bn_d (getbn r1 ls)) as [p1|] eqn:E1, (bn_d (getbn r2 ls)) as [p2|] eqn:E2.
  - destruct ARR1 as [Hin1 _], ARR2 as [Hin2 _].
    exact (limbs_limbs_disj s OW LB m HEAP ls AD EA IDS r1 r2 p1 D1 _ p2 D2 _ NE HV1 HV2 E1 E2 Hin1 Hin2).
  - destruct ARR2 as [-> Eb]. unfold bn_dmax at 2. rewrite Eb. cbn [length]. lia.
  - destruct ARR1 as [-> Eb]. unfold bn_dmax at 1. rewrite Eb. cbn [length]. lia.
  - destruct ARR1 as [-> Eb]. unfold bn_dmax at 1. rewrite Eb. cbn [length]. lia.
Qed.

(* [comment removed for export] *)
Lemma d_cell : forall m a D (b : bignum bptr), rw_cells psegs m a (bn_cells D b) -> rw_cells psegs m a [C8 (wz D)].
Proof.
  intros m a D b SX. unfold bn_cells in SX.
  change [C8 (wz D); C4 (wz (Z.of_nat (bn_top b))); C4 (wz (Z.of_nat (bn_dmax b))); C4 (wz (Z.b2z (bn_neg b))); C4 (wz (bn_flags b))]
    with ([C8 (wz D)] ++ [C4 (wz (Z.of_nat (bn_top b))); C4 (wz (Z.of_nat (bn_dmax b))); C4 (wz (Z.b2z (bn_neg b))); C4 (wz (bn_flags b))]) in SX.
  apply bk_rw_cells_app in SX. exact (proj1 SX).
Qed.

End WithCeiling0.
