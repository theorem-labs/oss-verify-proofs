(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnAddSpec BnMInv BnBridge BgState BgInv BgLib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnA Require Import W_uadd_core.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep BnLeaves.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnA Require Import BnAPure.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnAU Require Import BnAKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import W_expand BnCall BnRKit W_uadd_core.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Local Notation ops := (tree_ops bptr).

Definition uadd_body (rr ra rb : bnref) : BM (M := btree bptr) unit :=
  bbind ops (bget ops ra) (fun a => bbind ops (bget ops rb) (fun b =>
  let max := bn_top a in let min := bn_top b in
  bbind ops (bn_wexpand ops rr (max + 1)) (fun _ =>
  bbind ops (bbind ops (bget ops rr) (fun r => bset ops rr (bn_with_top r max))) (fun _ =>
  bbind ops (if (max =? 0)%nat then bret ops tt
             else bbind ops (bget ops ra) (fun a => bbind ops (bget ops rb) (fun b => bbind ops (bget ops rr) (fun r =>
                  let '(s, carry) := add_words (firstn min (bn_buf a)) (firstn min (bn_buf b)) in
                  let '(s2, carry) := add_carry_words (slice (bn_buf a) min (max - min)) carry in
                  bset ops rr (mkBN (bn_d r) (splice (bn_buf r) 0 (s ++ s2 ++ [carry])) (max + Z.to_nat carry) (bn_neg r) (bn_flags r))))))
    (fun _ => bbind ops (bget ops rr) (fun r => bset ops rr (bn_with_neg r false))))))).

Lemma BN_uadd_unfold : forall rr ra rb (bs : bstate bptr),
  BN_uadd ops rr ra rb bs =
  (if (bn_top (getbn ra bs) <? bn_top (getbn rb bs))%nat then uadd_body rr rb ra bs else uadd_body rr ra rb bs).
Proof.
  intros rr ra rb bs. unfold BN_uadd, bbind at 1 2. cbn [bind tree_ops bget tbind ret fst snd].
  destruct (bn_top (getbn ra bs) <? bn_top (getbn rb bs))%nat; reflexivity.
Qed.

Definition uadd_rest (rr x y : bnref) (max min : nat) : BM (M := btree bptr) unit :=
  bbind ops (bbind ops (bget ops rr) (fun r => bset ops rr (bn_with_top r max))) (fun _ =>
  bbind ops (if (max =? 0)%nat then bret ops tt
             else bbind ops (bget ops x) (fun a => bbind ops (bget ops y) (fun b => bbind ops (bget ops rr) (fun r =>
                  let '(s, carry) := add_words (firstn min (bn_buf a)) (firstn min (bn_buf b)) in
                  let '(s2, carry) := add_carry_words (slice (bn_buf a) min (max - min)) carry in
                  bset ops rr (mkBN (bn_d r) (splice (bn_buf r) 0 (s ++ s2 ++ [carry])) (max + Z.to_nat carry) (bn_neg r) (bn_flags r))))))
    (fun _ => bbind ops (bget ops rr) (fun r => bset ops rr (bn_with_neg r false)))).

Lemma uadd_body_eq : forall rr x y (bs : bstate bptr),
  uadd_body rr x y bs =
  tbind (bn_wexpand ops rr (bn_top (getbn x bs) + 1) bs) (fun p => uadd_rest rr x y (bn_top (getbn x bs)) (bn_top (getbn y bs)) (snd p)).
Proof. reflexivity. Qed.

Lemma buf_after_top : forall rr x (bs : bstate bptr) t, vref rr bs ->
  bn_buf (getbn x (setbn rr (bn_with_top (getbn rr bs) t) bs)) = bn_buf (getbn x bs).
Proof.
  intros rr x bs t HV. destruct (Nat.eq_dec rr x) as [->|NE].
  - rewrite getbn_setbn_same by exact HV. reflexivity.
  - rewrite getbn_setbn_other by exact NE. reflexivity.
Qed.

Lemma uadd_rest_eq : forall rr x y (bs : bstate bptr) max min,
  vref rr bs -> (min <= max)%nat -> (max <= length (bn_buf (getbn x bs)))%nat -> (min <= length (bn_buf (getbn y bs)))%nat ->
  uadd_rest rr x y max min bs =
  TRet (tt, setbn rr (uadd_bn (getbn rr bs) (firstn max (bn_buf (getbn x bs))) (firstn min (bn_buf (getbn y bs)))) bs).
Proof.
  intros rr x y bs max min HV Hmm Hx Hy.
  unfold uadd_rest, bbind, bget, bset, bret. cbn [bind ret tree_ops tbind fst snd].
  set (bs1 := setbn rr (bn_with_top (getbn rr bs) max) bs).
  assert (HV1 : vref rr bs1) by (unfold vref in *; subst bs1; rewrite length_setbn; exact HV).
  assert (LA : length (firstn max (bn_buf (getbn x bs))) = max) by (apply firstn_length_le; exact Hx).
  assert (LB : length (firstn min (bn_buf (getbn y bs))) = min) by (apply firstn_length_le; exact Hy).
  unfold uadd_bn, uadd_top, uadd_buf. rewrite LA.
  destruct (Nat.eqb_spec max 0) as [E0|N0].
  - cbn [tbind fst snd]. subst bs1. rewrite getbn_setbn_same by exact HV. rewrite setbn_setbn_same.
    unfold bn_with_neg, bn_with_top. cbn [bn_d bn_buf bn_top bn_neg bn_flags]. rewrite E0. reflexivity.
  - assert (EA : bn_buf (getbn x bs1) = bn_buf (getbn x bs)) by (apply buf_after_top; exact HV).
    assert (EB : bn_buf (getbn y bs1) = bn_buf (getbn y bs)) by (apply buf_after_top; exact HV).
    rewrite EA, EB. rewrite (slice_of_firstn (bn_buf (getbn x bs)) min max Hmm).
    unfold uadd_lists. rewrite LB. rewrite firstn_firstn, Nat.min_l by exact Hmm.
    destruct (add_words (firstn min (bn_buf (getbn x bs))) (firstn min (bn_buf (getbn y bs)))) as [sv cv].
    destruct (add_carry_words (skipn min (firstn max (bn_buf (getbn x bs)))) cv) as [sv2 cv2].
    cbn [tbind fst snd]. subst bs1. rewrite !getbn_setbn_same by (unfold vref in *; rewrite ?length_setbn; exact HV). rewrite !setbn_setbn_same.
    unfold bn_with_neg, bn_with_top. cbn [bn_d bn_buf bn_top bn_neg bn_flags fst snd]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma wexpand_res_top : forall r words (bs bs' : bstate bptr) x, wexpand_res r words bs bs' -> vref r bs ->
  bn_top (getbn x bs') = bn_top (getbn x bs).
Proof.
  intros r words bs bs' x [[_ ->]|[_ [pn ->]]] HV; [reflexivity|].
  destruct (Nat.eq_dec r x) as [->|NE]; [rewrite getbn_setbn_same by exact HV; reflexivity | rewrite getbn_setbn_other by exact NE; reflexivity].
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_UADD : Z := 0x10a834.
Definition BN_UADD_STACK : Z := 64 + BN_WEXPAND_STACK.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Definition uarith_res (rr : bnref) (bs : bstate bptr) (OW : list block) (PL : placement) : unit -> bstate bptr -> list block -> placement -> word -> Prop :=
    fun _ bs' OW' PL' a0' => PL' = PL /\ a0' = wz 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rr bs) <> Some q -> In (q, A, n) OW').

  Lemma uadd_tail : forall
      (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B : Z)
      (m1 : mem) (rr x y : bnref) (R X Y : Z)
      (x1 t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x19 x21 x22 t3 t4 t5 t6 : word),
    cenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] s bs m1 OW ->
    lib_state bs m1 OW PL EA ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BN_UADD_STACK -> bv_unsigned sp <= B -> frames_ok PL (bv_unsigned sp) B ->
    ref_at bs OW PL rr R -> hpl PL rr -> ref_at bs OW PL x X -> x <> ROne -> ref_at bs OW PL y Y -> y <> ROne ->
    (bn_top (getbn y bs) <= bn_top (getbn x bs))%nat ->
    implM bgusegs (interp (embed (uadd_body rr x y bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (uarith_res rr bs OW PL))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz RATP) t0 t1 t2 x8 (Z_to_bv 64 R) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 X) x19 (Z_to_bv 64 Y) x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x10a898) fc None m1 (seg_rom bgusegs)).
  Proof.
    intros until t6. intros ENV LS CEIL GLO LO SPB FROK HR HP HX NX HY NY HTOPS. pose proof (proj1 HP) as NRO.
    unfold BN_UADD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK in LO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (FBlo : lo <= bv_unsigned sp + -64) by lia.
    assert (FBsp : bv_unsigned sp + -64 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (cenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m CEIL GLO FBlo FBsp SPB SPR2 FROK) as CPRE.
    pose proof (cenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m CEIL GLO FBlo FBsp FROK) as CPOST.
    pose proof (fun A => @bn_post_cpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) CEIL FBlo FBsp SPR2 A) as BPC.

    pose proof ENV as (HEAP1 & _ & ST1 & _ & MI1 & _).
    destruct (open_ro s OW LB m1 bs PL EA (bv_unsigned sp) B x X HEAP1 LS FROK HX NX) as (Dx0 & SX & OKX & _ & X0 & XC & _).
    destruct (open_ro s OW LB m1 bs PL EA (bv_unsigned sp) B y Y HEAP1 LS FROK HY NY) as (Dy0 & SY & OKY & _ & Y0 & YC & _).
    pose proof OKX as (_ & TDX & DMX & _). pose proof OKY as (_ & TDY & DMY & _). unfold BG_DMAX in DMX, DMY.
    unfold bn_cells, MallocRep.wz in SX, SY.
    set (max := bn_top (getbn x bs)) in *. set (min := bn_top (getbn y bs)) in *.
    unfold implM. iprefix.
    zstep. rewrite (sx32_small (Z.of_nat max)) by (clear - TDX DMX; unfold bn_dmax in *; lia).
    zstep. rewrite (sx32_small (Z.of_nat min)) by (clear - TDY DMY; unfold bn_dmax in *; lia).
    zstep.
    zstep. rewrite (bn_swrap32_small (Z.of_nat max - Z.of_nat min)) by (clear - TDX DMX TDY DMY; unfold bn_dmax in *; lia).
    replace (Z.of_nat max + - Z.of_nat min)%Z with (Z.of_nat max - Z.of_nat min)%Z by (clear; lia).
    chk ltac:(fun C => clear - C; lia).
    zstep. rewrite (bn_swrap32_small (Z.of_nat max + 1)) by (clear - TDX DMX; unfold bn_dmax in *; lia).
    zstep. rewrite lts_small by (clear - TDX DMX; unfold bn_dmax in *; lia). if_cases C; [exfalso; zify_cond C; clear - C; lia | clear C].
    zstep. zstep.

    destruct (CPRE _ _ _ _ _ BN_WEXPAND_STACK ENV LS ltac:(unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia)) as (errv1 & PRE1).
    ihere. to_implM.
 rewrite uadd_body_eq. fold max min.
    eapply implM_embed_bind.
    { eapply (bn_wexpand_walk HM HF) with (lo := lo) (B := B) (errv := errv1) (OW := OW) (LB := LB) (PL := PL) (EA := EA)
        (r := rr) (a := R) (words := (max + 1)%nat);
        [exact PRE1 | reflexivity | exact HR | exact (hpl_wref PL rr HP) | reflexivity | unfold MallocRep.wz; f_equal; lia | clear - TDX DMX; unfold bn_dmax in *; lia]. }
    cbv beta. intros [u1 bs1] st1 ms1 PO.
 apply BPC in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & OW1 & PL1 & -> & CP & (EPL & -> & HDM & WRES & STAB)).
    subst PL1. specialize (CP eq_refl).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV CP) as (ENV1 & LS1).
    pose proof (cpost_refs LB PL EA lo B (bv_unsigned sp + -64) _ _ _ _ _ _ _ _ CP) as RS.
    cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 1091772)) with (Z_to_bv 64 1091772) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (ref_at_stable _ _ _ _ _ _ _ RS HR) as HR1. pose proof (ref_at_stable _ _ _ _ _ _ _ RS HX) as HX1. pose proof (ref_at_stable _ _ _ _ _ _ _ RS HY) as HY1.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS1 HR1) as HVR1.
    assert (ETX : bn_top (getbn x bs1) = max) by (apply (wexpand_res_top rr (max + 1) bs bs1 x WRES HVR)).
    assert (ETY : bn_top (getbn y bs1) = min) by (apply (wexpand_res_top rr (max + 1) bs bs1 y WRES HVR)).
    clear SX SY OKX OKY TDX TDY Dx0 Dy0 HEAP1 ST1 MI1 PRE1 CP.

    pose proof ENV1 as (HEAP2 & AUX2 & ST2 & (errv2 & ERR2) & MI2 & LXP2 & FA2 & SO2 & _ & FR2 & _).
    pose proof (RH_nodup_l _ _ _ _ HEAP2) as ND2.
    destruct (lib_state_open [] bs1 m2 OW1 PL EA rr R LS1 ND2 HR1 ltac:(intros []) NRO) as ((Dr & SR & ARR) & OKR' & LSH). pose proof (bg_okm _ OKR') as OKR.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS1) as PARTS1; pose proof PARTS1 as (WFS1 & PWF1 & IDS1 & PLB1 & ERRB1).
    destruct (bn_arr_facts_w bs1 OW1 PL EA (bv_unsigned sp) B st1 LB m2 rr Dr HEAP2 PARTS1 FROK HVR1 (hpl_wref PL rr HP) ARR) as (UR & LENR & DR0 & DRC & _ & DSEPR).
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 HR1 HP) as (SA0 & SAC & SAI & (qs & As & ns & Hins & Ra1 & Ra2)).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS1 HX1) as HVX1. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS1 HY1) as HVY1.
    pose proof (st_wf_ok x bs1 WFS1 HVX1 NX) as (LMX & TDX & _). pose proof (st_wf_ok y bs1 WFS1 HVY1 NY) as (LMY & TDY & _).
    destruct (operand_view_u st1 OW1 LB m2 bs1 PL EA (bv_unsigned sp) B rr R Dr x X max HEAP2 LS1 FROK HR1 HP SR ARR HX1 NX ltac:(rewrite ETX; lia))
      as (Dx & HXd & HLX & X0' & XC' & DX0 & DXC & SXR & SXA & ALX & UPX & _).
    destruct (operand_view_u st1 OW1 LB m2 bs1 PL EA (bv_unsigned sp) B rr R Dr y Y min HEAP2 LS1 FROK HR1 HP SR ARR HY1 NY ltac:(rewrite ETY; lia))
      as (Dy & HYd & HLY & Y0' & YC' & DY0 & DYC & SYR & SYA & ALY & UPY & _).
    set (br := getbn rr bs1) in *.
    set (la := firstn max (bn_buf (getbn x bs1))) in *. set (lb := firstn min (bn_buf (getbn y bs1))) in *.
    assert (LLA : length la = max) by (subst la; apply firstn_length_le; rewrite <- ETX; exact TDX).
    assert (LLB : length lb = min) by (subst lb; apply firstn_length_le; rewrite <- ETY; exact TDY).

    rewrite (uadd_rest_eq rr x y bs1 max min HVR1 HTOPS) by (unfold bn_dmax in *; lia). fold br la lb.
    cbn [embed interp]. apply implM_interp_ret.
    replace (Z_to_bv 64 (Z.of_nat max - Z.of_nat min)) with (Z_to_bv 64 (Z.of_nat (length la) - Z.of_nat (length lb))) by (rewrite LLA, LLB; reflexivity).
    replace (Z_to_bv 64 (Z.of_nat max)) with (Z_to_bv 64 (Z.of_nat (length la))) by (rewrite LLA; reflexivity).
    replace (Z_to_bv 64 (Z.of_nat min)) with (Z_to_bv 64 (Z.of_nat (length lb))) by (rewrite LLB; reflexivity).
    eapply evt_mono.
    { eapply (uadd_ucore ra sp gp (wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc) with (lo := lo) (R := R) (A := X) (B := Y)
        (Dr := Dr) (Da := Dx) (Db := Dy) (br := br) (la := la) (lb := lb).
      - unfold uadd_pre. rewrite LLA, LLB. specialize (DSEPR rr R HR1). fold br in DSEPR.
        split; [subst la; apply limbs_firstn; exact LMX|]. split; [subst lb; apply limbs_firstn; exact LMY|].
        split; [exact HTOPS|]. split; [exact OKR|]. split; [exact HDM|].
        split. { pose proof (proj2 (proj2 FROK)) as B63'. clear - SA0 SAC X0' XC' Y0' YC' DR0 DRC DX0 DXC DY0 DYC LO CEIL GLO SPR SPB B63' HDM LLA; unfold GLOBALS_TOP in *; repeat split; lia. }
        split; [clear - SXR; lia|]. split; [clear - SYR; lia|]. split; [exact DSEPR|]. split; [exact SXA|]. split; [exact SYA|].
        split; [exact ALX | exact ALY].
      - unfold uadd_upre. rewrite LLA, LLB.
        split; [apply hide_intro; exact (proj2 (ref_at_ualign st1 OW1 LB m2 bs1 PL EA rr R HEAP2 PARTS1 HR1 NRO))|].
        split; [unfold ub_ptr_ok; intros _; apply (bn_arr_ualign st1 OW1 LB m2 bs1 PL EA rr Dr br HEAP2 PARTS1 ARR); clear - HDM; lia|].
        split; [exact UPX|]. split; [exact UPY|]. lia.
      - unfold core_mem. split; [exact SR|]. split; [exact UR|]. split; [exact HXd|]. split; [exact HYd|].
        split; [exact HLX|]. split; [exact HLY|]. split; [exact FR2|]. split; [exact ST2 | exact MI2]. }

    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> & MU & WM & MI3 & SR3 & UR3 & ST3).
    clear XC YC XC' YC' DXC DYC ALX ALY SXR SYR SXA SYA HXd HYd HLX HLY.
    assert (HLla : limbs la) by (subst la; apply limbs_firstn; exact LMX).
    assert (HLlb : limbs lb) by (subst lb; apply limbs_firstn; exact LMY).
    assert (HMM : (length lb <= length la)%nat) by (rewrite LLA, LLB; exact HTOPS).
    assert (HDD : (length la + 1 <= bn_dmax br)%nat) by (rewrite LLA; exact HDM).
    pose proof (uadd_buf_length br la lb HLla HLlb HMM HDD) as LU.
    pose proof (uadd_bn_okm br la lb HLla HLlb HMM HDD OKR) as OKF.
    assert (OKF' : bg_ok (uadd_bn br la lb)).
    { destruct OKF as (K1 & K2 & _ & K4). destruct OKR' as (_ & _ & K3 & _). split; [exact K1|]. split; [exact K2|]. split; [|exact K4].
      unfold bn_dmax, uadd_bn in *. cbn [bn_buf] in *. rewrite LU. exact K3. }

    pose proof ARR as ARR'. unfold bn_arr in ARR'. destruct (bn_d br) as [pr|] eqn:Edr.
    2:{ exfalso. destruct (bn_arr_null PL rr m2 OW1 Dr br PWF1 (hpl_wref PL rr HP) Edr ARR) as [_ Eb]. unfold bn_dmax in HDD. rewrite Eb in HDD. cbn [length] in HDD. lia. }
    destruct ARR' as [HinR _].
    pose proof (RH_range _ _ _ _ _ _ _ HEAP2 HinR) as (_ & _ & _ & _ & DRI).
    rewrite LLA in MU.
    assert (HWL : Forall (w_lib bs1 OW1 PL lo (bv_unsigned sp)) [(Dr, Dr + 8 * (Z.of_nat max + 1)); (R, R + 24); (bv_unsigned sp - 144, bv_unsigned sp)]).
    { constructor; [right; left; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn [blk_addr blk_size fst snd]; split; [exact HinR | lia]|].
      constructor; [right; left; exists (qs, As, ns); cbn [blk_addr blk_size fst snd]; split; [exact Hins | lia]|].
      constructor; [left; cbn [fst snd]; lia | constructor]. }
    assert (WOK : Forall (w_ok OW1 LB bs1 PL EA (bv_unsigned sp) [rr]) [(Dr, Dr + 8 * (Z.of_nat max + 1)); (R, R + 24); (bv_unsigned sp - 144, bv_unsigned sp)]).
    { constructor; [eapply (w_limbs OW1 LB bs1 PL EA (bv_unsigned sp) false [rr] _ rr pr Dr); [left; reflexivity | exact HVR1 | exact Edr | exact HinR | cbn [fst snd]; lia | cbn [fst snd]; fold br; lia]|].
      constructor; [eapply (w_struct OW1 LB bs1 PL EA (bv_unsigned sp) false [rr] _ rr R); [left; reflexivity | exact HR1 | exact NRO | cbn; lia | cbn; lia]|].
      constructor; [apply w_stack; cbn; lia | constructor]. }
    unfold bn_post. exists t0', t1', t2', (Z_to_bv 64 1), a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m3, OW1, PL, errv2.
    split; [reflexivity|]. cbn [fst snd].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 FROK MU WM HWL CEIL)|].
    split.
    { unfold lib_state. eapply (lib_state_close [] bs1 m3 OW1 PL EA rr R); [| exact ND2 | exact HR1 | exact NRO | | exact OKF' |].
      - eapply (lib_state_frame _ LB (bv_unsigned sp) B); [exact HEAP2| exact LSH| exact MU| exact WM| exact FROK| exact WOK].
      - exists Dr. split; [exact SR3|]. unfold bn_arr, uadd_bn. cbn [bn_d]. rewrite Edr. unfold bn_dmax at 1. cbn [bn_buf]. rewrite LU.
        split; [exact HinR | exact UR3].
      - apply ids_ok_setbn_same; [exact IDS1 | exact HVR1 |]. unfold bn_blocks, uadd_bn, bn_dmax. cbn [bn_d bn_buf]. rewrite LU. reflexivity. }
    split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 FROK AUX2 MU WM HWL SPB ltac:(lia)); exact GLO|].
    split; [exact ST3|].
    split. { eapply rw_cells_transport; [exact ERR2 | exact MU | exact WM |]. unfold LX_ERRNO, RATP, GLOBALS_TOP in *. cbn. clear - DRI DR0 HDD LLA SAI SA0 GLO LO SPR FBlo; lia. }
    split; [exact MI3|].
    split. { eapply lx_pres_trans; [exact LXP2|]. apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 FROK MU WM HWL CEIL); [exact GLO| lia]. }
    split; [exact FA2|]. split; [exact SO2|].
    split. { eapply refs_stable_trans; [exact RS| apply refs_stable_setbn]. }
    unfold uarith_res. split; [reflexivity|]. split; [reflexivity | exact STAB].
  Qed.

  Lemma BN_uadd_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr ra_ rb_ : bnref) (R A Bb : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_UADD_STACK -> tp = wz RATP ->
    ref_at bs OW PL rr R -> hpl PL rr -> ref_at bs OW PL ra_ A -> ra_ <> ROne -> ref_at bs OW PL rb_ Bb -> rb_ <> ROne ->
    a0 = wz R -> a1 = wz A -> a2 = wz Bb ->
    implM bgusegs (interp (embed (BN_uadd (tree_ops bptr) rr ra_ rb_ bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (uarith_res rr bs OW PL))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_UADD) fc None m (seg_rom bgusegs)).
  Proof.
    intros until Bb. intros PRE -> HR HP HA NA HB NB -> -> ->.
    pose proof PRE as (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof LO as LO'. unfold BN_UADD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK in LO'.
    unfold BN_UADD, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    destruct (open_ro_u s OW LB m bs PL EA (bv_unsigned sp) B ra_ A HEAP LS FROK HA NA) as (Da0 & SA & OKA & _ & A0 & AC & _ & _ & ALA & _).
    destruct (open_ro_u s OW LB m bs PL EA (bv_unsigned sp) B rb_ Bb HEAP LS FROK HB NB) as (Db0 & SB & OKB & _ & B0 & BC & _ & _ & ALB & _).
    pose proof OKA as (_ & TDA & DMA & _). pose proof OKB as (_ & TDB & DMB & _). unfold BG_DMAX in DMA, DMB.
    unfold bn_cells, MallocRep.wz in SA, SB.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR. unfold GLOBALS_TOP in GLO.
    rewrite BN_uadd_unfold.
    unfold implM. iprefix.
    carve_frame 64%nat ST. do 10 zstep.
    chk ltac:(fun C => clear - C A0; lia).
    do 3 zstep. rewrite (land7 A (hide_elim _ ALA)). chk_lit.
    chk ltac:(fun C => clear - C B0; lia).
    zstep. rewrite (land7 Bb (hide_elim _ ALB)). chk_lit.
    zstep. rewrite (sx32_small (Z.of_nat (bn_top (getbn ra_ bs)))) by (clear - TDA DMA; unfold bn_dmax in *; lia).
    zstep. rewrite (sx32_small (Z.of_nat (bn_top (getbn rb_ bs)))) by (clear - TDB DMB; unfold bn_dmax in *; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
    assert (GLO' : GLOBALS_TOP <= lo) by (unfold GLOBALS_TOP; lia).
    lazymatch type of FR with rw_cells _ _ _ ?fr =>
      assert (ENV : cenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m fr s bs m1 OW)
    end.
    { unfold cenv. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); exact GLO'|].
      split; [exact ST|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); [exact GLO'| lia]|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FR| cbn; lia]. }
    zstep. rewrite lts_small by (clear - TDA DMA TDB DMB; unfold bn_dmax in *; lia).
    if_cases K; zify_cond K.
    -
      replace (bn_top (getbn ra_ bs) <? bn_top (getbn rb_ bs))%nat with true by (symmetry; apply Nat.ltb_lt; clear - K; lia).
      zstep. zstep.
      ihere. to_implM.
      eapply (uadd_tail ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s bs OW LB PL EA lo B m1 rr rb_ ra_ R Bb A);
        [exact ENV | exact LS1 | exact CEIL | exact GLO' | exact LO | exact SPB | exact FROK | exact HR | exact HP | exact HB | exact NB | exact HA | exact NA | clear - K; lia].
    - replace (bn_top (getbn ra_ bs) <? bn_top (getbn rb_ bs))%nat with false by (symmetry; apply Nat.ltb_ge; clear - K; lia).
      zstep. zstep.
      ihere. to_implM.
      eapply (uadd_tail ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s bs OW LB PL EA lo B m1 rr ra_ rb_ R A Bb);
        [exact ENV | exact LS1 | exact CEIL | exact GLO' | exact LO | exact SPB | exact FROK | exact HR | exact HP | exact HA | exact NA | exact HB | exact NB | clear - K; lia].
  Qed.
End Proofs.
End WithCeiling0.
