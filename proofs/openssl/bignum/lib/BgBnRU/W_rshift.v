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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnBridge BgState BgInv BgLib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit F_memset.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnArr ShiftPure.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap LshiftArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep BnLeaves.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnAU Require Import BnAKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require W_small W_rshift.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import BgLeaves W_expand BnCall BnRKit W_lshift RShiftArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Ltac bdec K F := repeat match goal with |- context [?a <? ?b] =>
  lazymatch constr:((a, b)) with context [K] =>
    first [replace (a <? b) with true by (symmetry; apply Z.ltb_lt; F) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; F)] end end.

Local Notation ops := (tree_ops bptr).

Definition rshift_rest (rr ra : bnref) (nw top : nat) (rb : Z) : BM (M := btree bptr) unit :=
  bbind ops (bget ops ra) (fun a => bbind ops (bget ops rr) (fun r =>
  bset ops rr (mkBN (bn_d r) (splice (bn_buf r) 0 (rshift_limbs (slice (bn_buf a) nw top) rb)) top (bn_neg a) (bn_flags r)))).

Lemma rshift_rest_eq : forall rr ra nw top rb (bs : bstate bptr),
  rshift_rest rr ra nw top rb bs =
  TRet (tt, setbn rr (mkBN (bn_d (getbn rr bs)) (splice (bn_buf (getbn rr bs)) 0 (rshift_limbs (slice (bn_buf (getbn ra bs)) nw top) rb))
                           top (bn_neg (getbn ra bs)) (bn_flags (getbn rr bs))) bs).
Proof. reflexivity. Qed.

Lemma rshift_eq_zero : forall rr ra n (bs : bstate bptr), 0 <= n -> (bn_top (getbn ra bs) <= Z.to_nat (n / 64))%nat ->
  bn_rshift_fixed_top ops rr ra n bs = BN_zero ops rr bs.
Proof.
  intros rr ra n bs Hn H. unfold bn_rshift_fixed_top. replace (n <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  unfold bbind, bget. cbn [bind ret tree_ops tbind fst snd].
  replace (bn_top (getbn ra bs) <=? Z.to_nat (n / 64))%nat with true by (symmetry; apply Nat.leb_le; exact H). reflexivity.
Qed.

Lemma rshift_eq_shift : forall rr ra n (bs : bstate bptr), 0 <= n -> (Z.to_nat (n / 64) < bn_top (getbn ra bs))%nat ->
  bn_rshift_fixed_top ops rr ra n bs =
  tbind ((if (rr =? ra)%nat then bret ops tt else bn_wexpand ops rr (bn_top (getbn ra bs) - Z.to_nat (n / 64))) bs)
        (fun p => rshift_rest rr ra (Z.to_nat (n / 64)) (bn_top (getbn ra bs) - Z.to_nat (n / 64)) (n mod 64) (snd p)).
Proof.
  intros rr ra n bs Hn H. unfold bn_rshift_fixed_top. replace (n <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  unfold bbind, bget. cbn [bind ret tree_ops tbind fst snd].
  replace (bn_top (getbn ra bs) <=? Z.to_nat (n / 64))%nat with false by (symmetry; apply Nat.leb_gt; exact H). reflexivity.
Qed.

Lemma land_m64 : forall x, 0 <= x < 18446744073709551616 -> Z.land x 18446744073709551615 = x.
Proof. intros x H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 64) with 18446744073709551616. lia. Qed.

Lemma signed_lit63 : forall x, -9223372036854775808 <= x < 9223372036854775808 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. rewrite Z_to_bv_signed.
  apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64 `div` 2)%Z with 9223372036854775808%Z. lia.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_RSHIFT : Z := 0x10a56c.
Definition BN_RSHIFT_STACK : Z := 64 + BN_WEXPAND_STACK.

Lemma operand_cells_al : forall s OW LB m st PL EA SPX BX rr R Dr x X k,
  RHEAP s (OW ++ LB) m -> lib_state st m OW PL EA -> frames_ok PL SPX BX ->
  ref_at st OW PL rr R -> hpl PL rr -> rw_cells bgusegs m R (bn_cells Dr (getbn rr st)) -> bn_arr m OW (pl_of PL rr) Dr (getbn rr st) ->
  ref_at st OW PL x X -> x <> ROne -> (k <= bn_top (getbn x st))%nat ->
  exists Dx, rw_cells bgusegs m X (bn_cells Dx (getbn x st)) /\ bg_ok (getbn x st) /\ limbs_at bgusegs m Dx (firstn k (bn_buf (getbn x st)))
    /\ 0 < X /\ (X + 24 <= alloc_ceiling \/ (SPX <= X /\ X + 24 < 2^63))
    /\ 0 <= Dx /\ (Dx + 8 * Z.of_nat k <= alloc_ceiling \/ (SPX <= Dx /\ Dx + 8 * Z.of_nat k < 2^63))
    /\ (X = R \/ X + 24 <= R \/ R + 24 <= X)
    /\ (R + 24 <= Dx \/ Dx + 8 * Z.of_nat k <= R)
    /\ (Dx = Dr \/ Dr + 8 * Z.of_nat (bn_dmax (getbn rr st)) <= Dx \/ Dx + 8 * Z.of_nat k <= Dr)
    /\ (X + 24 <= Dr \/ Dr + 8 * Z.of_nat (bn_dmax (getbn rr st)) <= X)
    /\ ((0 < k)%nat -> 8 <= Dx) /\ ((0 < k)%nat -> Dx mod 8 = 0).
Proof.
  intros s OW LB m st PL EA SPX BX rr R Dr x X k HEAP LS FROK HR HP SR ARR HX NROX Hk.
  pose proof (RH_nodup_l _ _ _ _ HEAP) as ND. pose proof (proj1 HP) as NRO.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & _).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX.
  destruct (bn_arr_facts_w st OW PL EA SPX BX s LB m rr Dr HEAP PARTS FROK HVR (hpl_wref PL rr HP) ARR) as (UR & LENR & DR0 & DRC & _ & DSEPR).
  pose proof (st_wf_ok x st WFS HVX NROX) as OKX. pose proof OKX as (_ & TDX & _).
  pose proof (DSEPR x X HX) as D4.
  destruct (Nat.eq_dec x rr) as [->|NE].
  -
    pose proof (ref_at_fun _ _ _ _ _ _ ND HX HR) as ->.
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP PARTS HR HP) as (SA0 & SAC & _ & _).
    exists Dr. split; [exact SR|]. split; [exact OKX|]. split; [apply limbs_at_firstn; exact UR|].
    pose proof (fun HL => bn_arr_base8 s OW LB m st PL EA SPX BX rr Dr HEAP PARTS FROK NRO ARR HL) as B8.
    specialize (DSEPR rr R HR). unfold bn_dmax in *. repeat split; try lia. all: intros Hk0; first [apply B8; lia | exact (proj2 (bn_arr_ualign s OW LB m st PL EA rr Dr _ HEAP PARTS ARR ltac:(unfold bn_dmax; lia)))].
  - destruct (lib_state_open [] st m OW PL EA x X LS ND HX ltac:(intros []) NROX) as ((Dx & SX & ARRX) & _ & _).
    destruct (bn_arr_facts s OW LB m HEAP st PL EA SPX BX PARTS FROK x Dx HVX NROX ARRX) as (UX & LENX & DX0 & DXC & _ & DSEPX).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HX NROX) as (SA0 & SAC & _).
    exists Dx. split; [exact SX|]. split; [exact OKX|]. split; [apply limbs_at_firstn; exact UX|].
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
    pose proof (fun HL => bn_arr_base8 s OW LB m st PL EA SPX BX x Dx HEAP PARTS FROK NROX ARRX HL) as B8.
    unfold bn_dmax in *. repeat split; try lia. all: intros Hk0; first [apply B8; lia | exact (proj2 (bn_arr_ualign s OW LB m st PL EA x Dx _ HEAP PARTS ARRX ltac:(unfold bn_dmax; lia)))].
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma bn_rshift_fixed_top_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rx : bnref) (R X : Z) (n : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_RSHIFT_STACK -> tp = wz RATP ->
    ref_at bs OW PL rr R -> hpl PL rr -> ref_at bs OW PL rx X -> rx <> ROne ->
    a0 = wz R -> a1 = wz X -> a2 = wz n -> 0 <= n < 2^30 ->
    implM bgusegs (interp (embed (bn_rshift_fixed_top ops rr rx n bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (shift_res rr bs OW PL))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_RSHIFT) fc None m (seg_rom bgusegs)).
  Proof.
    intros until n. intros PRE -> HR HP HX NX -> -> -> Hn. pose proof (proj1 HP) as NRO.
    pose proof PRE as (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof LO as LO'. unfold BN_RSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK in LO'.
    unfold BN_RSHIFT, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    set (nw := Z.to_nat (n / 64)). set (rb := n mod 64).
    assert (Hnw : 0 <= n / 64 < 2^24). { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
    assert (Enw : Z.of_nat nw = n / 64) by (subst nw; apply Z2Nat.id; lia).
    assert (Hrb : 0 <= rb < 64) by (subst rb; apply Z.mod_pos_bound; lia).
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.

    destruct (open_ro s OW LB m bs PL EA (bv_unsigned sp) B rx X HEAP LS FROK HX NX) as (Dx0 & SX & OKX & _ & X0 & XC & _).
    pose proof OKX as (_ & TDX & DMX & _). unfold BG_DMAX in DMX.
    unfold bn_cells, MallocRep.wz in SX.
    set (topx := bn_top (getbn rx bs)) in *.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR. unfold GLOBALS_TOP in GLO.
    unfold implM. iprefix.
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HX NX) as (AX0 & AX8).
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HR NRO) as (AR0 & AR8).
    carve_frame 64%nat ST. do 9 step.
    chk ltac:(fun C => rewrite ?unsigned_lit in C by lia; lia).
    do 2 step. zstep. rewrite (land7 X) by exact AX8.
    chk ltac:(fun C => clear - C; lia).
    step. zstep.
    step. rewrite (sx32_small (Z.of_nat topx)) by (clear - TDX DMX; unfold bn_dmax in *; lia).
    do 3 zstep.
    setreg 21%Z (Z_to_bv 64 (Z.of_nat nw)) ltac:(rewrite Enw; f_equal; symmetry; apply (nw_m_eq n); lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
    assert (GLO' : GLOBALS_TOP <= lo) by (unfold GLOBALS_TOP; lia).
    pose proof (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL) as HEAP1.
    assert (AUX1 : rauxv_ok m1 B) by (apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); exact GLO').
    assert (LXP1 : lx_pres LB (bv_unsigned sp) (XW PL) m m1) by (apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); [exact GLO'| lia]).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).

    lazymatch type of FR with rw_cells _ _ _ ?fr =>
    assert (EPI : forall (st1 : PState) (bs1 : bstate bptr) (m2 : mem) (OW2 : list block) (errv2 : word)
                         (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word),
      RHEAP st1 (OW2 ++ LB) m2 -> lib_state bs1 m2 OW2 PL EA -> rauxv_ok m2 B -> stk bgusegs m2 lo (bv_unsigned sp + -64) ->
      rw_cells bgusegs m2 3346164 [C4 errv2] -> mem_inv bgusegs m2 -> lx_pres LB (bv_unsigned sp) (XW PL) m m2 ->
      ps_fa st1 = ps_fa s -> ps_so st1 = ps_so s -> refs_stable bs OW bs1 OW2 ->
      (forall q A n, In (q, A, n) OW -> bn_d (getbn rr bs) <> Some q -> In (q, A, n) OW2) ->
      rw_cells bgusegs m2 (bv_unsigned sp + -64) fr ->
      evt bgusegs
        (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (shift_res rr bs OW PL) (tt, bs1) st1)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RATP) x5 x6 x7 sp x9 (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x10a71c) fc None m2 (seg_rom bgusegs)))
    end.
    { intros st1 bs1 m2 OW2 errv2 x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31
             HEAP2 LS2 AUX2 ST2 ERR2 MI2 LXP2 FA2 SO2 RST2 BST FR2.
      clear SX MU WM ST ERR MI FR HWL WOK LS1 HEAP1 AUX1 LXP1 XC.
      do 7 step. release_frame FR2 ST2 (bv_unsigned sp). step. step.
      apply evt_done.
      unfold bn_post. do 15 eexists. exists m2, OW2, PL, errv2. split; [reflexivity|]. cbn [fst snd].
      split; [exact HEAP2|]. split; [exact LS2|]. split; [exact AUX2|]. split; [exact ST2|]. split; [unfold LX_ERRNO, RATP; exact ERR2|]. split; [exact MI2|].
      split; [exact LXP2|]. split; [exact FA2|]. split; [exact SO2|]. split; [exact RST2|].
      unfold shift_res. split; [reflexivity|]. split; [reflexivity| exact BST]. }
    zstep. rewrite lts_signed by (clear - Hnw Enw TDX DMX; unfold bn_dmax in *; lia). if_cases KT; zify_cond KT; rewrite ?signed_lit63 in KT by (clear - Hnw Enw TDX DMX; unfold bn_dmax in *; lia).
    -
      ihere. to_implM.
      rewrite (rshift_eq_zero rr rx n bs) by (fold topx nw; clear - KT Hn; lia).
      unfold BN_zero, bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
      cbn [embed interp]. apply implM_interp_ret.
      destruct (lib_state_open [] bs m1 OW PL EA rr R LS1 ND HR ltac:(intros []) NRO) as ((Dr & SR & ARR) & OKR' & LSH).
      set (br := getbn rr bs) in *.
      pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP1 PARTS HR HP) as (SA0 & SAC & SAI & (qs & As & ns & Hins & Ra1 & Ra2)).
      clear SX XC X0.
      do 2 zstep.
      eapply evt_cut.
      { eapply BgBnU.W_rshift.BN_zero_ex_spec with (lo := lo) (A := R) (D := Dr) (b := br);
          [exact SR | split; [exact AR0 | exact AR8] | rewrite ESP; exact ST | rewrite ESP; clear - LO'; lia | exact MI | rewrite ESP; clear - SAC CEIL LO'; lia | reflexivity]. }
      intros ms' PO. unfold BgBnU.W_small.bn_small_post in PO.
      destruct PO as (u0' & u1' & u2' & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3' & u4' & u5' & u6' & m3 & E & MUc & WMc & MI3 & ST3 & BNz).
      subst ms'. rewrite ESP in *.
      lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
      eapply (rw_cells_transport bgusegs _ _ m3) in FR; [| exact MUc | exact WMc | cbn; clear - SAC CEIL LO'; lia].
      eapply (rw_cells_transport bgusegs _ _ m3) in ERR; [| exact MUc | exact WMc | cbn; clear - SAI LO' GLO; lia].
      destruct (bn_arr_facts_w bs OW PL EA (bv_unsigned sp) B s LB m1 rr Dr HEAP1 PARTS FROK HVR (hpl_wref PL rr HP) ARR) as (UR & LENR & DR0 & DRC & DRI & DSEPR).
      pose proof (DSEPR rr R HR) as SEPrr. fold br in SEPrr, LENR, DRC, DRI.
      eapply (u64arr_transport bgusegs _ _ m3) in UR; [| exact MUc | exact WMc | cbn [disjoint_from]; rewrite wlimbs_len; change (length (bn_buf (getbn rr bs))) with (bn_dmax br); clear - SEPrr DRC CEIL LO'; lia].
      clear ST MI SR.
      do 2 zstep.
      assert (MUT : munch [(bv_unsigned sp - 80, bv_unsigned sp); (R, R + 24)]%Z m m3).
      { eapply munch_trans; [eapply munch_weaken; [|exact MU]| eapply munch_weaken; [|exact MUc]]; unfold sub_fp; intros x Hx; cbn [outside] in *; clear - Hx; lia. }
      assert (WMT : wmono bgusegs m m3) by (eapply wmono_trans; [exact WM| exact WMc]).
      assert (HWLT : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp - 80, bv_unsigned sp); (R, R + 24)]).
      { constructor; [left; cbn; clear - LO'; lia|]. constructor; [right; left; exists (qs, As, ns); cbn [blk_addr blk_size fst snd]; split; [exact Hins | clear - Ra1 Ra2; lia]| constructor]. }
      assert (WOKc : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) [rr]) [(bv_unsigned sp - 80, bv_unsigned sp); (R, R + 24)]).
      { constructor; [apply w_stack; cbn; clear - LO' CEIL; lia|]. constructor; [eapply (w_struct OW LB bs PL EA (bv_unsigned sp) false [rr] _ rr R); [left; reflexivity| exact HR| exact NRO| cbn; clear; lia| cbn; clear; lia]| constructor]. }
      pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as (WFS0 & PWF0 & IDS0 & _).
      eapply (EPI s (setbn rr (bn_zero_pure br) bs) m3 OW errv);
        [ exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MUT WMT HWLT CEIL)
        | | apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MUT WMT HWLT SPB ltac:(clear - SPR; lia)); exact GLO'
        | exact ST3 | exact ERR | exact MI3
        | apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MUT WMT HWLT CEIL); [exact GLO'| clear - LO'; lia]
        | reflexivity | reflexivity | apply refs_stable_setbn
        | intros q0 A0 n0 Hq0 _; exact Hq0 | exact FR ].
      unfold lib_state. eapply (lib_state_close [] bs m3 OW PL EA rr R); [| exact ND| exact HR| exact NRO| | |].
      + eapply (lib_state_frame s LB (bv_unsigned sp) B); [exact HEAP1| exact LSH| | exact WMc| exact FROK| exact WOKc].
        eapply munch_weaken; [|exact MUc]. unfold sub_fp; intros x Hx; cbn [outside] in *; clear - Hx; lia.
      + exists Dr. split; [exact BNz|]. unfold bn_zero_pure. eapply bn_arr_of_u64arr; [exact ARR|]. cbn [bn_buf]. exact UR.
      + pose proof OKR' as (OKq1 & OKq2 & OKq3 & OKq4). unfold bg_ok, bn_zero_pure, bn_dmax in *. cbn [bn_buf bn_top bn_flags]. split; [exact OKq1|]. split; [clear; lia|]. split; [exact OKq3| exact OKq4].
      + apply ids_ok_setbn_same; [exact IDS0| exact HVR| reflexivity].
    -
      assert (NTOP : (nw < topx)%nat) by (clear - KT; lia).
      set (top' := (topx - nw)%nat).
      assert (Etop' : Z.of_nat top' = Z.of_nat topx - Z.of_nat nw) by (subst top'; clear - NTOP; lia).

      lazymatch type of FR with rw_cells _ _ _ ?fr =>
      assert (COMMON : forall (st1 : PState) (bs1 : bstate bptr) (m2 : mem) (OW1 : list block) (errv2 : word)
                         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
          RHEAP st1 (OW1 ++ LB) m2 -> lib_state bs1 m2 OW1 PL EA -> rauxv_ok m2 B -> stk bgusegs m2 lo (bv_unsigned sp + -64) ->
          rw_cells bgusegs m2 3346164 [C4 errv2] -> mem_inv bgusegs m2 -> lx_pres LB (bv_unsigned sp) (XW PL) m m2 ->
          ps_fa st1 = ps_fa s -> ps_so st1 = ps_so s -> refs_stable bs OW bs1 OW1 ->
          (forall q A n, In (q, A, n) OW -> bn_d (getbn rr bs) <> Some q -> In (q, A, n) OW1) ->
          rw_cells bgusegs m2 (bv_unsigned sp + -64) fr ->
          ref_at bs1 OW1 PL rr R -> ref_at bs1 OW1 PL rx X ->
          bn_top (getbn rx bs1) = topx -> (top' <= bn_dmax (getbn rr bs1))%nat ->
          implM bgusegs (interp (embed (rshift_rest rr rx nw top' rb bs1))) st1
            (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (shift_res rr bs OW PL))
            (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RATP) x5 x6 x7 sp (Z_to_bv 64 R) x10 x11 x12 x13 x14 x15 x16 x17
                     (Z_to_bv 64 X) (Z_to_bv 64 (Z.of_nat top')) (Z_to_bv 64 n) (Z_to_bv 64 (Z.of_nat nw)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                F (Z_to_bv 64 0x10a5e0) fc None m2 (seg_rom bgusegs)))
      end.
      { intros st1 bs1 m2 OW1 errv2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
               HEAP2 LS2 AUX2 ST2 ERR2 MI2 LXP2 FA2 SO2 RS STAB FR2 HR1 HX1 ETX HDM.
        clear SX MU WM ST ERR MI FR HWL WOK LS1 HEAP1 AUX1 LXP1 XC X0 KT OKX Dx0.
        pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HR1) as HVR1. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HX1) as HVX1.
        pose proof (RH_nodup_l _ _ _ _ HEAP2) as ND2.
        destruct (lib_state_open [] bs1 m2 OW1 PL EA rr R LS2 ND2 HR1 ltac:(intros []) NRO) as ((Dr & SR & ARR) & OKR' & LSH).
        pose proof OKR' as (OKq1 & OKq2 & OKq3 & OKq4). unfold BG_DMAX in OKq3.
        pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS1; pose proof PARTS1 as (WFS1 & PWF1 & IDS1 & PLB1 & ERRB1).
        destruct (bn_arr_facts_w bs1 OW1 PL EA (bv_unsigned sp) B st1 LB m2 rr Dr HEAP2 PARTS1 FROK HVR1 (hpl_wref PL rr HP) ARR) as (UR & LENR & DR0 & DRC & DRI & DSEPR).
        pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 HR1 HP) as (SA0 & SAC & SAI & (qs & As & ns & Hins & Ra1 & Ra2)).
        destruct (operand_cells_al st1 OW1 LB m2 bs1 PL EA (bv_unsigned sp) B rr R Dr rx X topx HEAP2 LS2 FROK HR1 HP SR ARR HX1 NX ltac:(rewrite ETX; lia))
          as (Dx & SX & OKX & HLX & X0' & XC' & DX0 & DXC & SXR & SRX & ALX & SXD & DX8 & DXA).
        set (br := getbn rr bs1) in *. set (bx := getbn rx bs1) in *.
        pose proof OKX as (OKx1 & OKx2 & OKx3 & OKx4). unfold BG_DMAX in OKx3.

        set (f := slice (bn_buf bx) nw top') in *.
        assert (Lf : length f = top').
        { subst f. unfold slice. apply firstn_length_le. rewrite length_skipn. clear - OKx2 ETX NTOP. unfold bn_dmax in OKx2. subst top'. lia. }
        assert (EFX : firstn topx (bn_buf bx) = firstn nw (bn_buf bx) ++ f).
        { subst f. unfold slice. rewrite <- (firstn_skipn nw (firstn topx (bn_buf bx))). f_equal.
          - rewrite firstn_firstn. f_equal. clear - NTOP. lia.
          - rewrite skipn_firstn_comm. reflexivity. }
        assert (HLF : limbs_at bgusegs m2 (Dx + 8 * Z.of_nat nw) f).
        { rewrite EFX in HLX. apply limbs_at_app in HLX. destruct HLX as [_ H2].
          rewrite firstn_length_le in H2 by (clear - OKx2 ETX NTOP; unfold bn_dmax in OKx2; lia). exact H2. }
        pose proof (DSEPR rr R HR1) as SEPrr. fold br in SEPrr.
        unfold bn_cells, MallocRep.wz in SX, SR.
        rewrite (rshift_rest_eq rr rx nw top' rb bs1). fold br bx f.
        cbn [embed interp]. apply implM_interp_ret.

        pose proof ARR as ARR'. unfold bn_arr in ARR'. destruct (bn_d br) as [pr|] eqn:Edr.
        2:{ exfalso. destruct (bn_arr_null PL rr m2 OW1 Dr br PWF1 (hpl_wref PL rr HP) Edr ARR) as [_ Eb]. unfold bn_dmax in HDM. fold br in HDM. rewrite Eb in HDM. cbn [length] in HDM. clear - HDM NTOP. subst top'. lia. }
        destruct ARR' as [Hinpr _].
        assert (LBr : length (bn_buf br) = bn_dmax br) by reflexivity.
        fold br in HDM.
        destruct (proj1 (limbarr_split bgusegs m2 Dr (bn_buf br) top' ltac:(rewrite LBr; exact HDM)) UR) as (Ulo & Uhi).
        destruct (proj1 (limbarr_limbs_at bgusegs m2 _ _) Ulo) as (_ & WRlo).
        rewrite firstn_length_le in WRlo by (rewrite LBr; exact HDM). rewrite <- Lf in WRlo.
        clear Ulo UR.
        pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp); (R, R + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m2) as MU3.
        pose proof (wmono_refl bgusegs m2) as WM3.
        rewrite ETX in SX.
        assert (LfZ : Z.of_nat (length f) = Z.of_nat top') by (rewrite Lf; reflexivity).
        assert (HDMZ : Z.of_nat top' <= Z.of_nat (bn_dmax br)) by (clear - HDM; lia).
        assert (LUhi : Z.of_nat (length (wlimbs (skipn top' (bn_buf br)))) = Z.of_nat (bn_dmax br) - Z.of_nat top') by (rewrite wlimbs_len, length_skipn, LBr; clear - HDM; lia).
        assert (DXP : 8 <= Dx) by (apply DX8; clear - NTOP; lia).
        assert (DXM : Dx mod 8 = 0) by (apply DXA; clear - NTOP; lia).
        assert (FPC : Dx + 8 * Z.of_nat nw + 8 * Z.of_nat top' < 2 ^ 63) by (clear - DXC Etop' NTOP CEIL; lia).
        assert (FPM : (Dx + 8 * Z.of_nat nw) mod 8 = 0) by (clear - DXM; Z.div_mod_to_equations; lia).
        assert (HN31 : 0 <= n < 2147483648) by (clear - Hn; lia).
        pose proof (block_ualign _ _ _ _ _ _ _ HEAP2 Hinpr) as (DRP & DR8).
        assert (UBT : 0 < Dr /\ Dr mod 8 = 0 /\ 0 < Dx + 8 * Z.of_nat nw /\ (Dx + 8 * Z.of_nat nw) mod 8 = 0) by (clear - DRP DR8 DXP FPM; lia).
        repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
        chk ltac:(fun C => rewrite ?unsigned_lit in C by (clear - AR0 SAC CEIL; lia); clear - C AR0; lia).
        zstep. rewrite (land7 R) by exact AR8.
        chk ltac:(fun C => clear - C; lia).
        step. zstep.
        try replace (Z.shiftl (Z.of_nat nw) 3) with (8 * Z.of_nat nw) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
        repeat match goal with |- context [Z.land ?e ?k] => lazymatch e with context [Z.of_nat nw] => rewrite (land_m64 e) by (clear - Hnw Enw; lia) end end.
        do 3 zstep.
        repeat match goal with |- context [Z.land ?e ?k] => lazymatch e with context [Dx] => rewrite (land_m64 e) by (clear - DXP FPC; lia) end end.
        bdec Dx ltac:(clear - DXP FPC Etop' NTOP; lia). cbn [Z.b2z].
        chk ltac:(fun C => clear - C; lia).
        do 4 zstep.
        rewrite (lxor_signbit63' n) by (clear - HN31; lia).
        bdec n ltac:(clear - HN31; lia). bdec Dx ltac:(clear - DXP FPC Etop' NTOP; lia). cbn [Z.b2z Z.lxor].
        chk ltac:(fun C => clear - C; lia).
        chk ltac:(fun C => rewrite ?unsigned_lit in C by (clear - DXP FPC; lia); clear - C DXP; lia).
        zstep. rewrite (land7 (Dx + 8 * Z.of_nat nw)) by exact FPM.
        chk ltac:(fun C => clear - C; lia).
        zstep. rewrite (bk_swrap32_small (Z.of_nat top' + -1)) by (clear - Etop' NTOP TDX DMX Hnw Enw; unfold bn_dmax in *; lia).
        zstep. rewrite lts_signed by (clear - Etop' NTOP TDX DMX Hnw Enw; unfold bn_dmax in *; lia). if_cases KO; zify_cond KO. { exfalso. clear - KO NTOP Etop'. lia. } clear KO.
        replace (Z.of_nat top' + -1) with (Z.of_nat top' - 1) by (clear; lia).
        repeat match goal with H : hide _ |- _ => apply hide_elim in H end.
        replace (Z.of_nat top') with (Z.of_nat (length f)) by exact LfZ.
        assert (ERB : Z.land n 63 = rb) by (subst rb; change 63 with (Z.ones 6); apply Z.land_ones; clear; lia).
        assert (ENN : Z.land (bv_swrap 32 (0 - n) mod 18446744073709551616) 63 = (64 - rb) mod 64).
        { change (bv_swrap 32 (0 - n) mod 18446744073709551616) with (negw_m n). change 63 with (Z.ones 6). rewrite Z.land_ones by (clear; lia).
          change (2 ^ 6) with 64. subst rb. apply negw_m_eq. clear - Hn. lia. }
        assert (LMf : limbs f) by (subst f; unfold slice; apply limbs_firstn; apply limbs_skipn; exact OKx1).
        assert (HTOP : 1 <= Z.of_nat (length f) < 2147483647) by (clear - LfZ Etop' NTOP TDX DMX; unfold bn_dmax in *; lia).
        assert (HNW : 0 <= Z.of_nat nw < 2147483648) by (clear - Hnw Enw; lia).
        assert (DISJ : Dr <= Dx + 8 * Z.of_nat nw \/ Dx + 8 * Z.of_nat nw + 8 * Z.of_nat (length f) <= Dr) by (clear - ALX HDMZ LfZ Etop'; lia).
        clear XC' X0' DXC SXR SRX ALX DX8 DSEPR OKq2 OKq4 OKx1 OKx2 OKx4 EFX HLX.
        eapply rshg_block with (m := m2) (f := f) (fp := Dx + 8 * Z.of_nat nw) (T := Dr) (RS := R) (n := n) (rb := rb).
        all: try first [exact HN31 | exact Hrb | exact ERB | exact ENN | exact LMf | exact HTOP | exact DISJ | exact UBT | exact HLF | exact WRlo | exact MI2 | exact SR].
        intros m3 z5 z6 z7 z11 z13 z14 z15 z16 z17 z29 z30 z31 I.

        pose proof I as (_ & _ & _ & _ & MU1 & WM1).
        pose proof SX as SX1. eapply (rw_cells_transport bgusegs _ m2 m3) in SX1; [| exact MU1 | exact WM1 | cbn [disjoint_from]; cbn; clear - SXD HDMZ LfZ; lia].
        step. rewrite (sx32_small (Z.b2z (bn_neg bx))) by (destruct (bn_neg bx); cbn; clear; lia).
        clear SX1 MU1 WM1.
        eapply rshg_last with (m := m2) (f := f) (fp := Dx + 8 * Z.of_nat nw) (T := Dr) (RS := R) (n := n) (rb := rb);
          try first [exact HN31 | exact Hrb | exact ERB | exact ENN | exact LMf | exact HTOP | exact DISJ | exact UBT | exact I].
        clear I. intros m4 z10 HRES MI4 MU4 WM4.
        clear HLF.
        transport_after_call bgusegs m2 m4 MU4 WM4.
        destruct (rshift_limbs_spec f rb LMf Hrb) as (RS1 & RS2 & _).
        assert (Ures : u64arr bgusegs m4 Dr (wlimbs (rshift_limbs f rb))).
        { apply limbarr_limbs_at. split; [rewrite rshift_limbs_seq; exact HRES| rewrite RS2; exact WRlo]. }
        assert (LUres : Z.of_nat (length (wlimbs (rshift_limbs f rb))) = Z.of_nat top') by (rewrite wlimbs_len, RS2, Lf; reflexivity).
        clear HRES WRlo SX SXD DISJ ENN ERB HN31 HNW HTOP MU4 WM4.
        step. step. zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
        set (nb := splice (bn_buf br) 0 (rshift_limbs f rb)).
        assert (Lnb : length nb = bn_dmax br) by (subst nb; rewrite splice_length; [exact LBr| rewrite RS2, Lf, LBr; cbn [Nat.add]; exact HDM]).
        assert (LMnb : limbs nb) by (subst nb; apply splice_limbs; [exact OKq1| exact RS1]).
        assert (UF : u64arr bgusegs mF Dr (wlimbs nb)).
        { subst nb. unfold splice. change (firstn 0 (bn_buf br)) with (@nil Z). cbn [app Nat.add]. rewrite RS2, Lf.
          apply limbarr_app. split; [exact Ures|]. rewrite RS2, Lf. exact Uhi. }
        assert (HWL3 : Forall (w_lib bs1 OW1 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp); (R, R + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
        { constructor; [left; cbn; clear - LO'; lia|]. constructor; [right; left; exists (qs, As, ns); cbn [blk_addr blk_size fst snd]; split; [exact Hins | clear - Ra1 Ra2; lia]|].
          constructor; [right; left; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn [blk_addr blk_size fst snd]; split; [exact Hinpr| clear; lia]| constructor]. }
        assert (WOK3 : Forall (w_ok OW1 LB bs1 PL EA (bv_unsigned sp) [rr]) [(bv_unsigned sp + -64, bv_unsigned sp); (R, R + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
        { constructor; [apply w_stack; cbn; clear - LO' CEIL; lia|].
          constructor; [eapply (w_struct OW1 LB bs1 PL EA (bv_unsigned sp) false [rr] _ rr R); [left; reflexivity| exact HR1| exact NRO| cbn; clear; lia| cbn; clear; lia]|].
          constructor; [eapply (w_limbs OW1 LB bs1 PL EA (bv_unsigned sp) false [rr] _ rr pr Dr); [left; reflexivity| exact HVR1| exact Edr| exact Hinpr| cbn [fst snd]; clear; lia| cbn [fst snd]; fold br; clear; lia]| constructor]. }
        assert (OKF : bg_ok (mkBN (Some pr) nb top' (bn_neg bx) (bn_flags br))).
        { unfold bg_ok, bn_dmax, BG_DMAX. cbn [bn_buf bn_top bn_flags]. rewrite Lnb.
          split; [exact LMnb|]. split; [exact HDM|]. split; [clear - OKq3; lia| exact (proj2 (proj2 (proj2 OKR')))]. }
        eapply (EPI st1 _ mF OW1 errv2);
          [ exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 FROK MU3 WM3 HWL3 CEIL)
          |
          | apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 FROK AUX2 MU3 WM3 HWL3 SPB ltac:(clear - SPR; lia)); exact GLO'
          | exact ST2 | exact ERR2 | assumption
          | eapply lx_pres_trans; [exact LXP2|]; apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 FROK MU3 WM3 HWL3 CEIL); [exact GLO'| clear - LO'; lia]
          | exact FA2 | exact SO2
          | eapply refs_stable_trans; [exact RS| apply refs_stable_setbn]
          | exact STAB | exact FR2 ].
        unfold lib_state. eapply (lib_state_close [] bs1 mF OW1 PL EA rr R); [| exact ND2| exact HR1| exact NRO| | exact OKF|].
        - eapply (lib_state_frame _ LB (bv_unsigned sp) B); [exact HEAP2| exact LSH| exact MU3| exact WM3| exact FROK| exact WOK3].
        - exists Dr. split.
          + unfold bn_cells, bn_dmax, MallocRep.wz. cbn [bn_top bn_buf bn_neg bn_flags]. rewrite Lnb. rewrite <- LfZ. exact SR.
          + unfold bn_arr, bn_dmax. cbn [bn_d bn_buf]. rewrite Lnb. split; [exact Hinpr| exact UF].
        - apply ids_ok_setbn_same; [exact IDS1| exact HVR1|]. fold br. unfold bn_blocks, bn_dmax. cbn [bn_d bn_buf]. rewrite Edr, Lnb. reflexivity. }
      zstep.
      setreg 19%Z (Z_to_bv 64 (Z.of_nat top')) ltac:(f_equal; rewrite bk_swrap32_small by (clear - NTOP TDX DMX Hnw Enw; unfold bn_dmax in *; lia); clear - Etop'; lia).
      pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP PARTS HR HP) as (SA0e & SACe & _).
      zstep. chk ltac:(fun C => rewrite ?unsigned_lit in C by (clear - Etop' NTOP TDX DMX Hnw Enw; unfold bn_dmax in *; lia); clear - C Etop' NTOP TDX DMX; unfold bn_dmax in *; lia).
      zstep. if_cases KE; zify_cond KE; rewrite ?(land_m64 R) in KE by (clear - SA0e SACe; lia); rewrite ?(land_m64 X) in KE by (clear - X0 XC SPR B63; lia).
      +
        assert (ERX : rr = rx).
        { destruct (Nat.eq_dec rr rx) as [E|NE]; [exact E|]. exfalso.
          pose proof (struct_disj s OW LB m HEAP bs PL EA (bv_unsigned sp) B PARTS FROK rr rx R X NE HR HX) as SD.
          clear - KE SD. lia. }
        clear KE. subst rx.
        ihere. to_implM.
        rewrite (rshift_eq_shift rr rr n bs) by (fold topx nw; clear - NTOP Hn; lia).
        rewrite Nat.eqb_refl. unfold bret. cbn [ret tree_ops tbind fst snd]. fold topx nw rb top'.
        eapply (COMMON s bs m1 OW errv);
          [ exact HEAP1 | exact LS1 | exact AUX1 | exact ST | exact ERR | exact MI | exact LXP1 | reflexivity | reflexivity | apply refs_stable_refl
          | intros q0 A0 n0 Hq0 _; exact Hq0 | exact FR | exact HR | exact HX | reflexivity | subst top'; clear - TDX; unfold bn_dmax in *; lia ].
      +
        assert (NRX : rr <> rx).
        { intros E. subst rx. pose proof (ref_at_fun _ _ _ _ _ _ ND HR HX) as E. apply KE. rewrite E. reflexivity. }
        clear KE.
        do 3 zstep.
        lazymatch type of FR with rw_cells _ _ _ ?fr =>
          assert (ENV : cenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m fr s bs m1 OW)
        end.
        { unfold cenv. split; [exact HEAP1|]. split; [exact AUX1|].
          split; [exact ST|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
          split; [exact LXP1|].
          split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FR| cbn; clear - LO'; lia]. }
        assert (FBlo : lo <= bv_unsigned sp + -64) by (clear - LO'; lia).
        assert (FBsp : bv_unsigned sp + -64 <= bv_unsigned sp) by (clear; lia).
        assert (SPR2 : bv_unsigned sp < 2 ^ 64) by (clear - SPR; lia).
        pose proof (cenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m CEIL GLO' FBlo FBsp SPB SPR2 FROK) as CPRE.
        pose proof (cenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m CEIL GLO' FBlo FBsp FROK) as CPOST.
        pose proof (fun A => @bn_post_cpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) CEIL FBlo FBsp SPR2 A) as BPC.
        destruct (CPRE _ _ _ _ _ BN_WEXPAND_STACK ENV LS1 ltac:(unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; clear - LO'; lia)) as (errv1 & PRE1).
        ihere. to_implM.
        rewrite (rshift_eq_shift rr rx n bs) by (fold topx nw; clear - NTOP Hn; lia).
        replace (rr =? rx)%nat with false by (symmetry; apply Nat.eqb_neq; exact NRX). fold topx nw rb top'.
        eapply implM_embed_bind.
        { eapply (bn_wexpand_walk HM HF) with (lo := lo) (B := B) (errv := errv1) (OW := OW) (LB := LB) (PL := PL) (EA := EA)
            (r := rr) (a := R) (words := top');
            [exact PRE1 | reflexivity | exact HR | exact (hpl_wref PL rr HP) | reflexivity | f_equal | clear - Etop' TDX DMX Hnw Enw; unfold bn_dmax in *; lia]. }
        cbv beta. intros [u1 bs1] st1 ms1 PO.
        apply BPC in PO.
        destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & OW1 & PL1 & -> & CP & (EPL & -> & HDM & WRES & STAB)).
        subst PL1. specialize (CP eq_refl).
        destruct (CPOST _ _ _ _ _ _ _ _ _ ENV CP) as (ENV1 & LS2).
        pose proof (cpost_refs LB PL EA lo B (bv_unsigned sp + -64) _ _ _ _ _ _ _ _ CP) as RS.
        cbn [fst snd] in *.
        lazymatch goal with |- implM _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
          replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
        pose proof (ref_at_stable _ _ _ _ _ _ _ RS HR) as HR1. pose proof (ref_at_stable _ _ _ _ _ _ _ RS HX) as HX1.
        assert (ETX : bn_top (getbn rx bs1) = topx) by (apply (wexpand_keeps_top rr top' bs bs1 rx WRES HVR)).
        pose proof ENV1 as (HEAP2 & AUX2 & ST2 & (errv2 & ERR2) & MI2 & LXP2 & FA2 & SO2 & _ & FR2 & _).
        unfold LX_ERRNO, RATP in ERR2. change (3346328 - 164) with 3346164 in ERR2.
        pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP PARTS HR HP) as (SA0 & SAC & _).
        unfold implM. iprefix.
        zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by (clear - SA0 SAC; lia). clear - KZ SA0; lia. }
        clear KZ.
        ihere. to_implM.
        eapply (COMMON st1 bs1 m2 OW1 errv2);
          [ exact HEAP2 | exact LS2 | exact AUX2 | exact ST2 | exact ERR2 | exact MI2 | exact LXP2 | exact FA2 | exact SO2 | exact RS
          | exact STAB | exact FR2 | exact HR1 | exact HX1 | exact ETX | exact HDM ].
  Qed.
End Proofs.
End WithCeiling0.
