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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import BgLeaves W_expand BnCall BnRKit ShiftArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Lemma swrap32_small : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (Z.of_N 32 - 1) with 31. change (2^31) with 2147483648 in *.
  rewrite Z.mod_small by lia. lia.
Qed.

Definition nw_m (n : Z) : Z :=
  bv_swrap 32 (Z.shiftr (bv_swrap 32 (Z.land (n + Z.shiftr (Z.land (Z.shiftl n 1) 18446744073709551615) 58) 18446744073709551615)) 6).
Lemma nw_m_eq : forall n, 0 <= n < 2^31 -> nw_m n = n / 64.
Proof.
  intros n H. unfold nw_m.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  change 18446744073709551615 with (Z.ones 64). rewrite !Z.land_ones by lia.
  rewrite (Z.mod_small (n * 2)) by lia.
  rewrite (Z.shiftr_div_pow2 (n * 2)) by lia. rewrite (Z.div_small (n * 2)) by (change (2 ^ 58) with 288230376151711744; lia).
  rewrite Z.add_0_r. rewrite Z.mod_small by lia.
  rewrite (swrap32_small n) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 6) with 64.
  apply swrap32_small. split; [|apply Z.div_lt_upper_bound; lia]. pose proof (Z.div_pos n 64). lia.
Qed.

Definition negw_m (n : Z) : Z := (bv_swrap 32 (0 - n)) mod 18446744073709551616.
Lemma negw_m_eq : forall n, 0 <= n < 2^31 -> negw_m n mod 64 = (64 - n mod 64) mod 64.
Proof.
  intros n H. unfold negw_m. rewrite swrap32_small by lia.
  rewrite Z.mod_mod_divide by (exists (2^58); reflexivity).
  assert (E : (64 - n mod 64) mod 64 = (- (n mod 64)) mod 64).
  { replace (64 - n mod 64) with (- (n mod 64) + 1 * 64) by lia. rewrite Z.mod_add by lia. reflexivity. }
  rewrite E. replace (0 - n) with (- n) by lia. rewrite <- (Z.sub_0_l n), <- (Z.sub_0_l (n mod 64)). rewrite Zminus_mod_idemp_r. reflexivity.
Qed.

Lemma nw_zero_iff : forall n, 0 <= n -> (n + 63 < 127 <-> n / 64 = 0).
Proof. intros n H. split; intro K; [apply Z.div_small; lia|]. pose proof (Z.div_mod n 64 ltac:(lia)). pose proof (Z.mod_pos_bound n 64 ltac:(lia)). lia. Qed.

Local Notation ops := (tree_ops bptr).

Definition lshift_buf (r a : bignum bptr) (nw : nat) (lb : Z) : list Z :=
  let buf := if (bn_top a =? 0)%nat then upd (bn_buf r) nw 0
             else let '(ls, mo) := lshift_limbs (firstn (bn_top a) (bn_buf a)) lb 0 in
                  splice (bn_buf r) nw (ls ++ [mo]) in
  if (nw =? 0)%nat then buf else splice buf 0 (repeat 0 nw).

Definition lshift_rest (rr ra : bnref) (nw : nat) (lb : Z) : BM (M := btree bptr) unit :=
  bbind ops (bget ops ra) (fun a => bbind ops (bget ops rr) (fun r =>
  bset ops rr (mkBN (bn_d r) (lshift_buf r a nw lb) (bn_top a + nw + 1) (bn_neg a) (bn_flags r)))).

Lemma lshift_eq : forall rr ra n (bs : bstate bptr), 0 <= n ->
  bn_lshift_fixed_top ops rr ra n bs =
  tbind (bn_wexpand ops rr (bn_top (getbn ra bs) + Z.to_nat (n / 64) + 1) bs) (fun p => lshift_rest rr ra (Z.to_nat (n / 64)) (n mod 64) (snd p)).
Proof.
  intros rr ra n bs Hn. unfold bn_lshift_fixed_top. replace (n <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma lshift_rest_eq : forall rr ra nw lb (bs : bstate bptr),
  lshift_rest rr ra nw lb bs =
  TRet (tt, setbn rr (mkBN (bn_d (getbn rr bs)) (lshift_buf (getbn rr bs) (getbn ra bs) nw lb) (bn_top (getbn ra bs) + nw + 1)
                           (bn_neg (getbn ra bs)) (bn_flags (getbn rr bs))) bs).
Proof. reflexivity. Qed.

Lemma wexpand_keeps_top : forall r words (bs bs' : bstate bptr) x, wexpand_res r words bs bs' -> vref r bs ->
  bn_top (getbn x bs') = bn_top (getbn x bs).
Proof.
  intros r words bs bs' x [[_ ->]|[_ [pn ->]]] HV; [reflexivity|].
  destruct (Nat.eq_dec r x) as [->|NE]; [rewrite getbn_setbn_same by exact HV; reflexivity | rewrite getbn_setbn_other by exact NE; reflexivity].
Qed.

Definition lshift_mid (a : bignum bptr) (lb : Z) : list Z :=
  if (bn_top a =? 0)%nat then [0] else let '(ls, mo) := lshift_limbs (firstn (bn_top a) (bn_buf a)) lb 0 in ls ++ [mo].
Lemma lshift_buf_parts : forall (r a : bignum bptr) nw lb,
  length (lshift_mid a lb) = (bn_top a + 1)%nat -> (nw + bn_top a + 1 <= length (bn_buf r))%nat ->
  lshift_buf r a nw lb = repeat 0 nw ++ lshift_mid a lb ++ skipn (nw + bn_top a + 1) (bn_buf r).
Proof.
  intros r a nw lb Lm HL. unfold lshift_buf, lshift_mid in *.
  assert (E : (if (bn_top a =? 0)%nat then upd (bn_buf r) nw 0
               else let '(ls, mo) := lshift_limbs (firstn (bn_top a) (bn_buf a)) lb 0 in splice (bn_buf r) nw (ls ++ [mo]))
              = splice (bn_buf r) nw (if (bn_top a =? 0)%nat then [0] else let '(ls, mo) := lshift_limbs (firstn (bn_top a) (bn_buf a)) lb 0 in ls ++ [mo])).
  { destruct (bn_top a =? 0)%nat; [reflexivity|]. destruct (lshift_limbs (firstn (bn_top a) (bn_buf a)) lb 0) as [ls mo]. reflexivity. }
  rewrite E. clear E.
  set (mid := if (bn_top a =? 0)%nat then [0] else let '(ls, mo) := lshift_limbs (firstn (bn_top a) (bn_buf a)) lb 0 in ls ++ [mo]) in *.
  unfold splice. rewrite Lm. replace (nw + (bn_top a + 1))%nat with (nw + bn_top a + 1)%nat by lia.
  destruct (nw =? 0)%nat eqn:En.
  - apply Nat.eqb_eq in En. subst nw. reflexivity.
  - cbn [firstn app Nat.add]. rewrite repeat_length.
    rewrite firstn_O. cbn [app]. rewrite skipn_app. rewrite length_firstn. replace (Nat.min nw (length (bn_buf r))) with nw by lia.
    rewrite Nat.sub_diag. cbn [skipn]. rewrite skipn_all2 by (rewrite length_firstn; lia). reflexivity.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_LSHIFT : Z := 0x10a26c.
Definition BN_LSHIFT_STACK : Z := 64 + BN_WEXPAND_STACK.

Lemma bn_arr_base8 : forall s OW LB m st PL EA SPX BX r D,
  RHEAP s (OW ++ LB) m -> lib_parts st OW PL EA -> frames_ok PL SPX BX -> r <> ROne ->
  bn_arr m OW (pl_of PL r) D (getbn r st) -> (0 < length (bn_buf (getbn r st)))%nat -> 8 <= D.
Proof.
  intros s OW LB m st PL EA SPX BX r D HEAP PARTS FROK NRO ARR HL. pose proof PARTS as (_ & PWF & _).
  pose proof ARR as ARR'. unfold bn_arr in ARR'. destruct (bn_d (getbn r st)) as [p|] eqn:Ed.
  - destruct ARR' as [Hin _]. pose proof (RH_range _ _ _ _ _ _ _ HEAP Hin) as (P0 & P16 & _). clear - P0 P16. Z.div_mod_to_equations. lia.
  - destruct (bn_arr_none_cases PL r m OW D _ PWF NRO Ed ARR) as [(x & d & Eb & -> & _)|[_ Eb]]; [| rewrite Eb in HL; cbn in HL; lia].
    pose proof (proj1 PWF r _ Eb) as (Hr & _).
    assert (HFd : In (d, d + TMOD_BUF_SZ) (pl_frames PL)).
    { apply pl_frames_In. left. exists r. rewrite Eb. split; [exact Hr| right; left; reflexivity]. }
    destruct (frame_iv_range _ _ _ _ _ _ PARTS FROK _ HFd) as (Cd & _ & _). cbn [fst] in Cd. lia.
Qed.

Lemma operand_cells_u : forall s OW LB m st PL EA SPX BX rr R Dr x X k,
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
    /\ ((0 < k)%nat -> 8 <= Dx)
    /\ ub_ptr_ok (Z.of_nat (bn_top (getbn x st))) Dx.
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
    assert (XU : ub_ptr_ok (Z.of_nat (bn_top (getbn rr st))) Dr).
    { unfold ub_ptr_ok. intros TP. apply (bn_arr_ualign s OW LB m st PL EA rr Dr _ HEAP PARTS ARR). clear - TP TDX. unfold bn_dmax in *. lia. }
    exists Dr. split; [exact SR|]. split; [exact OKX|]. split; [apply limbs_at_firstn; exact UR|].
    pose proof (fun HL => bn_arr_base8 s OW LB m st PL EA SPX BX rr Dr HEAP PARTS FROK NRO ARR HL) as B8.
    specialize (DSEPR rr R HR). unfold bn_dmax in *.
    assert (B8' : (0 < k)%nat -> 8 <= Dr) by (intros Hk0; apply B8; lia).
    do 8 (split; [lia|]). split; [exact B8'|]. exact XU.
  - destruct (lib_state_open [] st m OW PL EA x X LS ND HX ltac:(intros []) NROX) as ((Dx & SX & ARRX) & _ & _).
    destruct (bn_arr_facts s OW LB m HEAP st PL EA SPX BX PARTS FROK x Dx HVX NROX ARRX) as (UX & LENX & DX0 & DXC & _ & DSEPX).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HX NROX) as (SA0 & SAC & _).
    assert (XU : ub_ptr_ok (Z.of_nat (bn_top (getbn x st))) Dx).
    { unfold ub_ptr_ok. intros TP. apply (bn_arr_ualign s OW LB m st PL EA x Dx _ HEAP PARTS ARRX). clear - TP TDX. unfold bn_dmax in *. lia. }
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
    assert (B8' : (0 < k)%nat -> 8 <= Dx) by (intros Hk0; unfold bn_dmax in *; apply B8; lia).
    unfold bn_dmax in *. do 8 (split; [lia|]). split; [exact B8'|]. exact XU.
Qed.

Lemma operand_cells : forall s OW LB m st PL EA SPX BX rr R Dr x X k,
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
    /\ ((0 < k)%nat -> 8 <= Dx).
Proof.
  intros s OW LB m st PL EA SPX BX rr R Dr x X k HEAP LS FROK HR HP SR ARR HX NROX Hk.
  destruct (operand_cells_u s OW LB m st PL EA SPX BX rr R Dr x X k HEAP LS FROK HR HP SR ARR HX NROX Hk)
    as (Dx & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & _).
  exists Dx. repeat (split; [assumption|]). exact A12.
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Definition shift_res (rr : bnref) (bs : bstate bptr) (OW : list block) (PL : placement) : unit -> bstate bptr -> list block -> placement -> word -> Prop :=
    fun _ bs' OW' PL' a0' => PL' = PL /\ a0' = wz 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rr bs) <> Some q -> In (q, A, n) OW').

  Lemma bn_lshift_fixed_top_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rx : bnref) (R X : Z) (n : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_LSHIFT_STACK -> tp = wz RATP ->
    ref_at bs OW PL rr R -> hpl PL rr -> ref_at bs OW PL rx X -> rx <> ROne ->
    a0 = wz R -> a1 = wz X -> a2 = wz n -> 0 <= n < 2^30 ->
    implM bgusegs (interp (embed (bn_lshift_fixed_top ops rr rx n bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (shift_res rr bs OW PL))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_LSHIFT) fc None m (seg_rom bgusegs)).
  Proof.
    intros until n. intros PRE -> HR HP HX NX -> -> -> Hn. pose proof (proj1 HP) as NRO.
    pose proof PRE as (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof LO as LO'. unfold BN_LSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK in LO'.
    unfold BN_LSHIFT, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    set (nw := Z.to_nat (n / 64)). set (lb := n mod 64).
    assert (Hnw : 0 <= n / 64 < 2^24). { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
    assert (Enw : Z.of_nat nw = n / 64) by (subst nw; apply Z2Nat.id; lia).
    assert (Hlb : 0 <= lb < 64) by (subst lb; apply Z.mod_pos_bound; lia).

    destruct (open_ro s OW LB m bs PL EA (bv_unsigned sp) B rx X HEAP LS FROK HX NX) as (Dx0 & SX & OKX & _ & X0 & XC & _).
    pose proof OKX as (_ & TDX & DMX & _). unfold BG_DMAX in DMX.
    unfold bn_cells, MallocRep.wz in SX.
    set (topx := bn_top (getbn rx bs)) in *.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR. unfold GLOBALS_TOP in GLO.
    rewrite (lshift_eq rr rx n bs) by lia. fold topx nw lb.
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
    setreg 20%Z (Z_to_bv 64 (Z.of_nat nw)) ltac:(rewrite Enw; f_equal; symmetry; apply (nw_m_eq n); lia).
    do 2 zstep.
    repeat (rewrite bk_swrap32_small by (clear - TDX DMX Hnw Enw; unfold bn_dmax in *; lia)).
    chk ltac:(fun C => clear - C TDX DMX Hnw Enw; unfold bn_dmax in *; lia).
    do 2 zstep.
    repeat (rewrite bk_swrap32_small by (clear - TDX DMX Hnw Enw; unfold bn_dmax in *; lia)).
    zstep. rewrite lts_signed by (clear - TDX DMX Hnw Enw; unfold bn_dmax in *; lia).
    if_cases KO; zify_cond KO. { exfalso. clear - KO TDX DMX Hnw Enw; unfold bn_dmax in *; lia. } clear KO.
    do 2 zstep.
    setreg 11%Z (Z_to_bv 64 (Z.of_nat (topx + nw + 1))) ltac:(f_equal; lia).
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
    assert (FBlo : lo <= bv_unsigned sp + -64) by lia.
    assert (FBsp : bv_unsigned sp + -64 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (cenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m CEIL GLO' FBlo FBsp SPB SPR2 FROK) as CPRE.
    pose proof (cenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m CEIL GLO' FBlo FBsp FROK) as CPOST.
    pose proof (fun A => @bn_post_cpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) CEIL FBlo FBsp SPR2 A) as BPC.

    destruct (CPRE _ _ _ _ _ BN_WEXPAND_STACK ENV LS1 ltac:(unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia)) as (errv1 & PRE1).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply (bn_wexpand_walk HM HF) with (lo := lo) (B := B) (errv := errv1) (OW := OW) (LB := LB) (PL := PL) (EA := EA)
        (r := rr) (a := R) (words := (topx + nw + 1)%nat);
        [exact PRE1 | reflexivity | exact HR | exact (hpl_wref PL rr HP) | reflexivity | reflexivity | clear - TDX DMX Hnw Enw; unfold bn_dmax in *; lia]. }
    cbv beta. intros [u1 bs1] st1 ms1 PO.
    apply BPC in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & OW1 & PL1 & -> & CP & (EPL & -> & HDM & WRES & STAB)).
    subst PL1. specialize (CP eq_refl).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV CP) as (ENV1 & LS2).
    pose proof (cpost_refs LB PL EA lo B (bv_unsigned sp + -64) _ _ _ _ _ _ _ _ CP) as RS.
    cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 1090268)) with (Z_to_bv 64 1090268) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (ref_at_stable _ _ _ _ _ _ _ RS HR) as HR1. pose proof (ref_at_stable _ _ _ _ _ _ _ RS HX) as HX1.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HR1) as HVR1. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HX1) as HVX1.
    assert (ETX : bn_top (getbn rx bs1) = topx) by (apply (wexpand_keeps_top rr (topx + nw + 1) bs bs1 rx WRES HVR)).
    assert (TOPB : Z.of_nat topx + Z.of_nat nw + 2 < 2^31) by (clear - TDX DMX Hnw Enw; unfold bn_dmax in *; lia).
    clear SX OKX TDX Dx0 PRE1 CP CPRE.

    pose proof ENV1 as (HEAP2 & AUX2 & ST2 & (errv2 & ERR2) & MI2 & LXP2 & FA2 & SO2 & _ & FR2 & _).
    pose proof (RH_nodup_l _ _ _ _ HEAP2) as ND2.
    destruct (lib_state_open [] bs1 m2 OW1 PL EA rr R LS2 ND2 HR1 ltac:(intros []) NRO) as ((Dr & SR & ARR) & OKR' & LSH).
    pose proof OKR' as (OKq1 & OKq2 & OKq3 & OKq4). unfold BG_DMAX in OKq3.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS1; pose proof PARTS1 as (WFS1 & PWF1 & IDS1 & PLB1 & ERRB1).
    destruct (bn_arr_facts_w bs1 OW1 PL EA (bv_unsigned sp) B st1 LB m2 rr Dr HEAP2 PARTS1 FROK HVR1 (hpl_wref PL rr HP) ARR) as (UR & LENR & DR0 & DRC & DRI & DSEPR).
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 HR1 HP) as (SA0 & SAC & SAI & (qs & As & ns & Hins & Ra1 & Ra2)).
    destruct (operand_cells_u st1 OW1 LB m2 bs1 PL EA (bv_unsigned sp) B rr R Dr rx X topx HEAP2 LS2 FROK HR1 HP SR ARR HX1 NX ltac:(rewrite ETX; lia))
      as (Dx & SX & OKX & HLX & X0' & XC' & DX0 & DXC & SXR & SRX & ALX & SXD & DX8 & DXU).
    set (br := getbn rr bs1) in *. set (bx := getbn rx bs1) in *.
    pose proof OKX as (OKx1 & OKx2 & OKx3 & OKx4). unfold BG_DMAX in OKx3.
    set (f := firstn topx (bn_buf bx)) in *.
    assert (Lf : length f = topx) by (subst f; apply firstn_length_le; rewrite <- ETX; exact OKx2).
    pose proof (DSEPR rr R HR1) as SEPrr. fold br in SEPrr.
    unfold bn_cells, MallocRep.wz in SX, SR.

    rewrite (lshift_rest_eq rr rx nw lb bs1). fold br bx.
    cbn [embed interp]. apply implM_interp_ret.

    pose proof ARR as ARR'. unfold bn_arr in ARR'. destruct (bn_d br) as [pr|] eqn:Edr.
    2:{ exfalso. destruct (bn_arr_null PL rr m2 OW1 Dr br PWF1 (hpl_wref PL rr HP) Edr ARR) as [_ Eb]. unfold bn_dmax in HDM. rewrite Eb in HDM. cbn [length] in HDM. lia. }
    destruct ARR' as [Hinpr _].
    assert (LBr : length (bn_buf br) = bn_dmax br) by reflexivity.
    destruct (proj1 (limbarr_limbs_at bgusegs m2 Dr (bn_buf br)) UR) as (LAr & WRr). rewrite LBr in WRr.

    destruct (proj1 (limbarr_split bgusegs m2 Dr (bn_buf br) nw ltac:(rewrite LBr; clear - HDM; lia)) UR) as (Ulo & Urest).
    destruct (proj1 (limbarr_split bgusegs m2 (Dr + 8 * Z.of_nat nw) (skipn nw (bn_buf br)) (topx + 1) ltac:(rewrite length_skipn, LBr; clear - HDM; lia)) Urest) as (Umid & Uhi).
    pose proof (limbarr_CB bgusegs m2 _ _ Ulo) as CBlo.
    rewrite firstn_length_le in CBlo by (rewrite LBr; clear - HDM; lia).
    replace (8 * nw)%nat with (Z.to_nat (8 * Z.of_nat nw)) in CBlo by (clear; lia).
    replace (Dr + 8 * Z.of_nat nw + 8 * Z.of_nat (topx + 1)) with (Dr + 8 * Z.of_nat (nw + topx + 1)) in Uhi by (clear; lia).
    rewrite skipn_skipn in Uhi. replace (topx + 1 + nw)%nat with (nw + topx + 1)%nat in Uhi by (clear; lia).
    clear Ulo Urest UR.
    pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp); (R, R + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m2) as MU3.
    pose proof (wmono_refl bgusegs m2) as WM3.
    unfold LX_ERRNO, RATP in ERR2. change (3346328 - 164) with 3346164 in ERR2.
    rewrite ETX in SX. rewrite ETX.
    unfold MallocRep.wz in *.
    zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by (clear - SA0 SAC; lia). clear - KZ SA0; lia. }
    clear KZ.
    step. rewrite (sx32_small (Z.of_nat topx)) by (clear - OKx2 OKx3 ETX; unfold bn_dmax in *; lia).
    zstep. replace (Z.of_nat nw ≪ 3) with (8 * Z.of_nat nw) by (rewrite Z.shiftl_mul_pow2 by (clear; lia); clear; lia).

    lazymatch type of FR2 with rw_cells _ _ _ ?fr =>
    assert (TAIL : forall mT (nb : list Z) (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word),
              length nb = bn_dmax br -> limbs nb ->
              u64arr bgusegs mT Dr (wlimbs nb) ->
              rw_cells bgusegs mT X [C8 (Z_to_bv 64 Dx); C4 (Z_to_bv 64 (Z.of_nat topx)); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax bx)));
                                   C4 (Z_to_bv 64 (Z.b2z (bn_neg bx))); C4 (Z_to_bv 64 (bn_flags bx))] ->
              rw_cells bgusegs mT R [C8 (Z_to_bv 64 Dr); C4 (Z_to_bv 64 (Z.of_nat (bn_top br))); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax br)));
                                   C4 (Z_to_bv 64 (Z.b2z (bn_neg br))); C4 (Z_to_bv 64 (bn_flags br))] ->
              rw_cells bgusegs mT (bv_unsigned sp + -64) fr ->
              rw_cells bgusegs mT 3346164 [C4 errv2] -> stk bgusegs mT lo (bv_unsigned sp + -64) -> mem_inv bgusegs mT ->
              munch [(bv_unsigned sp + -64, bv_unsigned sp); (R, R + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m2 mT -> wmono bgusegs m2 mT ->
              evt bgusegs
                (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (shift_res rr bs OW PL)
                   (tt, setbn rr (mkBN (bn_d br) nb (topx + nw + 1) (bn_neg bx) (bn_flags br)) bs1) st1)
                (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RATP) x5 x6 x7 sp (Z_to_bv 64 R)
                         (Z_to_bv 64 Dr) (Z_to_bv 64 (Z.of_nat topx)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 X) (Z_to_bv 64 n)
                        (Z_to_bv 64 (Z.of_nat nw)) x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x10a49c) fc None mT (seg_rom bgusegs)))
    end.
    { intros mT nb x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 Lnb LMnb UF SXF SRF FRF ERRF STF MIF MUF WMF.
      clear SX SR FR2 ERR2 ST2 MI2 MU3 WM3 LAr WRr CBlo Umid Uhi HLX.

      clear XC XC' X0 X0' DXC SXR SRX ALX SXD DX8 DRI DSEPR DX0 OKq1 OKq2 OKq4 OKx1 OKx2 OKx3 OKx4 CPOST BPC ENV ENV1 HWL WOK PRE.
      assert (LENnb : Z.of_nat (length (wlimbs nb)) = Z.of_nat (bn_dmax br)) by (rewrite wlimbs_len, Lnb; reflexivity).
      step. rewrite (sx32_small (Z.b2z (bn_neg bx))) by (destruct (bn_neg bx); cbn; clear; lia).
      do 2 zstep.
      repeat (rewrite bk_swrap32_small by (clear - TOPB; lia)).
      step.
      chk ltac:(fun C => clear - C TOPB; lia).
      do 2 zstep.
      repeat (rewrite bk_swrap32_small by (clear - TOPB; lia)).
      zstep. rewrite lts_signed by (clear - TOPB; lia).
      if_cases KO; zify_cond KO. { exfalso. clear - KO TOPB; lia. } clear KO.
      try clear SXF.
      step. zstep.
      do 7 step. release_frame FRF STF (bv_unsigned sp). step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mG end.
      apply evt_done.
      assert (HWL3 : Forall (w_lib bs1 OW1 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp); (R, R + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
      { constructor; [left; cbn; clear - LO'; lia|]. constructor; [right; left; exists (qs, As, ns); cbn [blk_addr blk_size fst snd]; split; [exact Hins | clear - Ra1 Ra2; lia]|].
        constructor; [right; left; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn [blk_addr blk_size fst snd]; split; [exact Hinpr| clear; lia]| constructor]. }
      assert (WOK3 : Forall (w_ok OW1 LB bs1 PL EA (bv_unsigned sp) [rr]) [(bv_unsigned sp + -64, bv_unsigned sp); (R, R + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
      { constructor; [apply w_stack; cbn; clear - LO' CEIL; lia|].
        constructor; [eapply (w_struct OW1 LB bs1 PL EA (bv_unsigned sp) false [rr] _ rr R); [left; reflexivity| exact HR1| exact NRO| cbn; clear; lia| cbn; clear; lia]|].
        constructor; [eapply (w_limbs OW1 LB bs1 PL EA (bv_unsigned sp) false [rr] _ rr pr Dr); [left; reflexivity| exact HVR1| exact Edr| exact Hinpr| cbn [fst snd]; clear; lia| cbn [fst snd]; fold br; clear; lia]| constructor]. }
      assert (OKF : bg_ok (mkBN (bn_d br) nb (topx + nw + 1) (bn_neg bx) (bn_flags br))).
      { unfold bg_ok, bn_dmax, BG_DMAX. cbn [bn_buf bn_top bn_flags]. rewrite Lnb.
        split; [exact LMnb|]. split; [clear - HDM; lia|]. split; [clear - OKq3; lia| exact (proj2 (proj2 (proj2 OKR')))]. }
      unfold bn_post. do 15 eexists. exists mG, OW1, PL, errv2. split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 FROK MUF WMF HWL3 CEIL)|].
      split.
      { unfold lib_state. eapply (lib_state_close [] bs1 mG OW1 PL EA rr R); [| exact ND2| exact HR1| exact NRO| | exact OKF|].
        - eapply (lib_state_frame _ LB (bv_unsigned sp) B); [exact HEAP2| exact LSH| exact MUF| exact WMF| exact FROK| exact WOK3].
        - exists Dr. split.
          + unfold bn_cells, bn_dmax, MallocRep.wz. cbn [bn_top bn_buf bn_neg bn_flags]. rewrite Lnb.
            lazymatch type of SRF with rw_cells _ _ _ (_ :: C4 (Z_to_bv 64 ?t) :: _) =>
              replace (Z.of_nat (topx + nw + 1)) with t by (clear; lia) end. exact SRF.
          + unfold bn_arr, bn_dmax. cbn [bn_d bn_buf]. rewrite Edr, Lnb. split; [exact Hinpr| exact UF].
        - apply ids_ok_setbn_same; [exact IDS1| exact HVR1|]. fold br. unfold bn_blocks, bn_dmax. cbn [bn_d bn_buf]. rewrite Edr, Lnb. reflexivity. }
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 FROK AUX2 MUF WMF HWL3 SPB ltac:(clear - SPR; lia)); exact GLO'|].
      split; [exact STF|]. split; [unfold LX_ERRNO, RATP; exact ERRF|]. split; [exact MIF|].
      split. { eapply lx_pres_trans; [exact LXP2|]. apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 FROK MUF WMF HWL3 CEIL); [exact GLO'| clear - LO'; lia]. }
      split; [exact FA2|]. split; [exact SO2|].
      split. { eapply refs_stable_trans; [exact RS| apply refs_stable_setbn]. }
      unfold shift_res. split; [reflexivity|]. split; [reflexivity| exact STAB]. }

    lazymatch type of FR2 with rw_cells _ _ _ ?fr =>
    assert (FIN : forall mF (mid : list Z) (x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
              length mid = (topx + 1)%nat -> limbs mid ->
              lshift_buf br bx nw lb = repeat 0 nw ++ mid ++ skipn (nw + topx + 1) (bn_buf br) ->
              rw_cells bgusegs mF Dr [CB (Z.to_nat (8 * Z.of_nat nw)) (u64s (wlimbs (firstn nw (bn_buf br))))] ->
              u64arr bgusegs mF (Dr + 8 * Z.of_nat nw) (wlimbs mid) ->
              u64arr bgusegs mF (Dr + 8 * Z.of_nat (nw + topx + 1)) (wlimbs (skipn (nw + topx + 1) (bn_buf br))) ->
              rw_cells bgusegs mF X [C8 (Z_to_bv 64 Dx); C4 (Z_to_bv 64 (Z.of_nat topx)); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax bx)));
                                   C4 (Z_to_bv 64 (Z.b2z (bn_neg bx))); C4 (Z_to_bv 64 (bn_flags bx))] ->
              rw_cells bgusegs mF R [C8 (Z_to_bv 64 Dr); C4 (Z_to_bv 64 (Z.of_nat (bn_top br))); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax br)));
                                   C4 (Z_to_bv 64 (Z.b2z (bn_neg br))); C4 (Z_to_bv 64 (bn_flags br))] ->
              rw_cells bgusegs mF (bv_unsigned sp + -64) fr ->
              rw_cells bgusegs mF 3346164 [C4 errv2] -> stk bgusegs mF lo (bv_unsigned sp + -64) -> mem_inv bgusegs mF ->
              munch [(bv_unsigned sp + -64, bv_unsigned sp); (R, R + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m2 mF -> wmono bgusegs m2 mF ->
              evt bgusegs
                (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (shift_res rr bs OW PL)
                   (tt, setbn rr (mkBN (bn_d br) (lshift_buf br bx nw lb) (topx + nw + 1) (bn_neg bx) (bn_flags br)) bs1) st1)
                (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RATP) x5 x6 x7 sp (Z_to_bv 64 R)
                         (Z_to_bv 64 Dr) (Z_to_bv 64 (Dr + 8 * Z.of_nat nw)) (Z_to_bv 64 (8 * Z.of_nat nw)) x13 x14 x15 x16 x17 (Z_to_bv 64 X) (Z_to_bv 64 n)
                         (Z_to_bv 64 (Z.of_nat nw)) (Z_to_bv 64 (Z.land R 7)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x10a470) fc None mF (seg_rom bgusegs)))
    end.
    { intros mF mid x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 Lmid LMmid EBUF CBF UMF UHF SXF SRF FRF ERRF STF MIF MUF WMF.
      clear SX SR FR2 ERR2 ST2 MI2 MU3 WM3 LAr WRr CBlo Umid Uhi HLX.

      clear XC XC' X0 X0' DXC SXR SRX ALX DX8 DSEPR DX0 OKq2 OKq4 OKx1 OKx2 OKx4 CPOST BPC ENV ENV1 HWL WOK PRE.
      assert (Lnb : length (lshift_buf br bx nw lb) = bn_dmax br).
      { rewrite EBUF, !length_app, repeat_length, Lmid, length_skipn, LBr. clear - HDM. lia. }
      assert (LMnb : limbs (lshift_buf br bx nw lb)).
      { rewrite EBUF. apply limbs_app; [apply limbs_repeat; unfold limb; rewrite BnArith.BW_lit; clear; lia|]. apply limbs_app; [exact LMmid| apply limbs_skipn; exact OKq1]. }
      zstep. rewrite (swrap32_small (n + 63)) by (clear - Hn; lia).
      step. zstep. if_cases KZ; zify_cond KZ.
      -
        assert (ENW0 : nw = 0%nat) by (clear - KZ Hn Enw; pose proof (proj1 (nw_zero_iff n ltac:(lia)) KZ); lia).
        chk ltac:(fun C => rewrite ?unsigned_lit in C by (clear - AR0 SA0 SAC; lia); clear - C AR0; lia).
        chk ltac:(fun C => rewrite ?unsigned_lit in C by (clear - AR0 SA0 SAC; lia); rewrite ?(land7 R AR8) in C; clear - C; lia).
        step. rewrite ?(sx32_small (Z.of_nat topx)) by (clear - TOPB; lia).
        eapply (TAIL mF (lshift_buf br bx nw lb)); try eassumption.
        rewrite EBUF. rewrite ENW0 in *. cbn [repeat app].
        apply limbarr_app. split.
        + replace (Dr + 8 * Z.of_nat 0) with Dr in UMF by (clear; lia). exact UMF.
        + rewrite Lmid. replace (Dr + 8 * Z.of_nat (topx + 1)) with (Dr + 8 * Z.of_nat (0 + topx + 1)) by (clear; lia). exact UHF.
      -
        assert (NW1 : (1 <= nw)%nat).
        { clear - KZ Hn Enw. destruct (Nat.eq_dec nw 0) as [E|E]; [|lia]. exfalso. pose proof (proj2 (nw_zero_iff n ltac:(lia)) ltac:(lia)). lia. }
        chk ltac:(fun C => rewrite ?unsigned_lit in C by (clear - AR0 SA0 SAC; lia); clear - C AR0; lia).
        chk ltac:(fun C => rewrite ?unsigned_lit in C by (clear - AR0 SA0 SAC; lia); rewrite ?(land7 R AR8) in C; clear - C; lia).
        step. step. step.
        eapply evt_cut.
        { eapply (memset_callZ _ (Z_to_bv 64 (bv_unsigned sp + -64))) with (D := Dr) (C := 0) (N := 8 * Z.of_nat nw);
            [ exact CBF | exact MIF | exact DR0 | clear - Hnw Enw; lia | clear - DRC HDM DR0; lia | clear; lia ]. }
        post_call bgusegs mF.
        lazymatch goal with P : rw_cells bgusegs _ Dr [CB _ (repeat _ _)] |- _ => rename P into PZ end.
        change (0 mod 256) with 0 in PZ. replace (Z.to_nat (8 * Z.of_nat nw)) with (8 * nw)%nat in PZ by (clear; lia).
        chk ltac:(fun C => rewrite ?unsigned_lit in C by (clear - AR0 SA0 SAC; lia); clear - C AR0; lia).
        chk ltac:(fun C => rewrite ?unsigned_lit in C by (clear - AR0 SA0 SAC; lia); rewrite ?(land7 R AR8) in C; clear - C; lia).
        step. rewrite ?(sx32_small (Z.of_nat topx)) by (clear - OKx3 ETX OKX; destruct OKX as (_ & OK2 & _); unfold bn_dmax in *; lia).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mM end.
        eapply (TAIL mM (lshift_buf br bx nw lb)); try eassumption.
        rewrite EBUF. apply limbarr_app. split.
        + eapply CB_u64arr. rewrite lbytes_repeat0. exact PZ.
        + rewrite repeat_length. apply limbarr_app. split; [exact UMF|].
          rewrite Lmid. replace (Dr + 8 * Z.of_nat nw + 8 * Z.of_nat (topx + 1)) with (Dr + 8 * Z.of_nat (nw + topx + 1)) by (clear; lia). exact UHF. }

    rewrite <- Edr.
    assert (HDM' : (nw + bn_top bx + 1 <= length (bn_buf br))%nat) by (rewrite ETX, LBr; clear - HDM; lia).
    clear TAIL.
    do 2 zstep. if_cases KT; zify_cond KT.
    -
      assert (ETOP : topx = 0%nat) by (clear - KT; lia).
      assert (EMID : lshift_mid bx lb = [0]) by (unfold lshift_mid; rewrite ETX, ETOP; reflexivity).
      pose proof (lshift_buf_parts br bx nw lb ltac:(rewrite EMID, ETX, ETOP; reflexivity) HDM') as EBUF. rewrite EMID, ETX in EBUF.
      chk ltac:(fun C => rewrite ?unsigned_lit in C by (clear - AR0 SA0 SAC; lia); clear - C AR0; lia).
      chk ltac:(fun C => rewrite (land7 R AR8) in C; clear - C; lia).
      pose proof (block_ualign _ _ _ _ _ _ _ HEAP2 Hinpr) as (DRP & DRA8).
      assert (DNA8 : (Dr + 8 * Z.of_nat nw) mod 8 = 0) by (clear - DRA8; Z.div_mod_to_equations; lia).
      step. zstep.
      try replace (Z.of_nat nw ≪ 3) with (8 * Z.of_nat nw) in * by (rewrite Z.shiftl_mul_pow2 by (clear; lia); clear; lia).
      do 2 zstep.
      zstep. if_cases C448; [ exfalso; zify_cond C448;
        rewrite (proj2 (Z.ltb_lt 0 Dr) DRP), (proj2 (Z.ltb_ge (Dr + 8 * Z.of_nat nw) 1) ltac:(clear - DRP; lia)) in C448;
        cbn [Z.b2z] in C448; clear - C448; lia | clear C448 ].
      do 4 zstep.
      chk ltac:(fun C => rewrite (lxor_signbit63' n) in C by (clear - Hn; lia);
                         repeat match type of C with context [Z.ltb ?a ?b] =>
                           first [ rewrite (proj2 (Z.ltb_ge a b) ltac:(clear - Hn DRP; lia)) in C
                                 | rewrite (proj2 (Z.ltb_lt a b) ltac:(clear - Hn DRP; lia)) in C ] end;
                         cbn [Z.b2z] in C; vm_compute in C; discriminate C).
      chk ltac:(fun C => clear - C DRP; lia).
      zstep.
      chk ltac:(fun C => rewrite (land7 (Dr + 8 * Z.of_nat nw) DNA8) in C; clear - C; lia).
      assert (L1 : length (firstn (topx + 1) (skipn nw (bn_buf br))) = 1%nat) by (rewrite firstn_length_le by (rewrite length_skipn, LBr; clear - HDM; lia); clear - ETOP; lia).
      destruct (firstn (topx + 1) (skipn nw (bn_buf br))) as [|y0' [|? ?]] eqn:EF1; cbn [length] in L1; try (exfalso; clear - L1; lia). clear L1.
      assert (IDX : 0 <= 0 < Z.of_nat (length (wlimbs [y0']))) by (cbn; clear; lia).
      pose proof (u64arr_store_ok bgusegs m2 (Dr + 8 * Z.of_nat nw) _ 0 (wa (Dr + 8 * Z.of_nat nw + 8 * 0)) Umid IDX eq_refl) as SOKW.
      pose proof (u64arr_write bgusegs m2 (Dr + 8 * Z.of_nat nw) _ 0 (Z_to_bv 64 0) Umid IDX) as U2.
      replace (Dr + 8 * Z.of_nat nw + 8 * 0) with (Dr + 8 * Z.of_nat nw) in SOKW, U2 by (clear; lia).
      change (Arr.upd (wlimbs [y0']) (Z.to_nat 0) (Z_to_bv 64 0)) with (wlimbs [0]) in U2.
      assert (HDMZ : Z.of_nat nw + Z.of_nat topx + 1 <= Z.of_nat (bn_dmax br)) by (clear - HDM; lia).
      assert (LUhi : Z.of_nat (length (wlimbs (skipn (nw + topx + 1) (bn_buf br)))) = Z.of_nat (bn_dmax br) - (Z.of_nat nw + Z.of_nat topx + 1)) by (rewrite wlimbs_len, length_skipn, LBr; clear - HDM; lia).
      assert (ETOPZ : Z.of_nat topx = 0) by (clear - ETOP; lia).
      clear Umid LAr WRr HLX XC XC' X0 X0' DXC SXR SRX ALX DX8 DSEPR DX0 OKq2 OKq4 OKx1 OKx2 OKx4 CPOST BPC ENV ENV1 HWL WOK PRE IDX EF1.
      step. change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). store_done.
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      eapply (FIN m3 [0]); try eassumption.
      + rewrite ETOP. reflexivity.
      + constructor; [unfold limb; rewrite BnArith.BW_lit; clear; lia| constructor].
    -
      assert (NTOP : (1 <= topx)%nat) by (clear - KT; lia).

      destruct (proj1 (limbarr_limbs_at bgusegs m2 _ _) Umid) as (_ & WRmid).
      rewrite firstn_length_le in WRmid by (rewrite length_skipn, LBr; clear - HDM; lia).
      replace (8 * Z.of_nat (topx + 1)) with (8 * (Z.of_nat (length f) + 1)) in WRmid by (rewrite Lf; clear; lia).
      assert (HDMZ : Z.of_nat nw + Z.of_nat topx + 1 <= Z.of_nat (bn_dmax br)) by (clear - HDM; lia).
      assert (LUhi : Z.of_nat (length (wlimbs (skipn (nw + topx + 1) (bn_buf br)))) = Z.of_nat (bn_dmax br) - (Z.of_nat nw + Z.of_nat topx + 1)) by (rewrite wlimbs_len, length_skipn, LBr; clear - HDM; lia).
      assert (LfZ : Z.of_nat (length f) = Z.of_nat topx) by (rewrite Lf; reflexivity).

      assert (LMf : limbs f) by (subst f; apply limbs_firstn; exact OKx1).
      pose proof (lshift_limbs_seq f lb) as ESEQ.
      pose proof (lshift_limbs_spec f lb 0 LMf Hlb ltac:(split; [clear; lia| apply Z.pow_pos_nonneg; clear - Hlb; lia])) as LSP.
      destruct (lshift_limbs f lb 0) as [ls0 mo] eqn:ELS. cbn [fst snd] in ESEQ. destruct LSP as (LS0 & LL0 & LMO & _).
      assert (Lnew : length (ls0 ++ [mo]) = (topx + 1)%nat) by (rewrite length_app, LL0, Lf; cbn [length]; clear; lia).
      assert (LIMBnew : limbs (ls0 ++ [mo])).
      { apply limbs_app; [exact LS0|]. apply limbs_cons; [|apply limbs_nil]. unfold limb. rewrite BW_pow.
        split; [clear - LMO; lia|]. apply Z.lt_le_trans with (2 ^ lb); [clear - LMO; lia|]. apply Z.pow_le_mono_r; clear - Hlb; lia. }
      assert (EMID : lshift_mid bx lb = ls0 ++ [mo]).
      { unfold lshift_mid. rewrite ETX. replace (topx =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; clear - NTOP; lia). fold f. rewrite ELS. reflexivity. }
      pose proof (lshift_buf_parts br bx nw lb ltac:(rewrite EMID, ETX; exact Lnew) HDM') as EBUF. rewrite EMID, ETX in EBUF.
      assert (DISJ : Dx <= Dr + 8 * Z.of_nat nw \/ Dr + 8 * Z.of_nat nw + 8 * (Z.of_nat (length f) + 1) <= Dx) by (clear - ALX HDMZ LfZ; lia).
      assert (HTOP : 1 <= Z.of_nat (length f) < 2147483647) by (clear - LfZ NTOP OKx2 OKx3 ETX; unfold bn_dmax in *; lia).
      assert (HFP : 8 <= Dx) by (apply DX8; clear - NTOP; lia).
      assert (ELB : Z.land n 63 = lb) by (subst lb; change 63 with (Z.ones 6); apply Z.land_ones; clear; lia).
      assert (HNN : 0 <= negw_m n < 18446744073709551616) by (unfold negw_m; apply Z.mod_pos_bound; clear; lia).
      assert (ENN : negw_m n mod 64 = (64 - lb) mod 64) by (subst lb; apply negw_m_eq; clear - Hn; lia).
      assert (HN31 : 0 <= n < 2147483648) by (clear - Hn; lia).
      pose proof (block_ualign _ _ _ _ _ _ _ HEAP2 Hinpr) as (DRP & DR8).
      assert (DXA : 0 < Dx /\ Dx mod 8 = 0) by (apply DXU; rewrite ETX; clear - NTOP; lia).
      clear Umid LAr WRr XC XC' X0 X0' SXR SRX ALX DX8 DSEPR OKq2 OKq4 OKx1 OKx2 OKx4 CPOST BPC ENV ENV1 HWL WOK PRE ELS.
      chk ltac:(fun C => rewrite ?unsigned_lit in C by lia; lia).
      chk ltac:(fun C => rewrite ?unsigned_lit in C by (pose proof (Z.land_nonneg R 7); lia); rewrite (land7 R) in C by (clear - AR8; lia); clear - C; lia).
      zstep. do 3 zstep.
      replace (Dr + Z.of_nat nw ≪ 3) with (Dr + 8 * Z.of_nat nw) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      rewrite ?land64_small by lia.
      replace (0 <? Dr) with true by (symmetry; apply Z.ltb_lt; exact DRP).
      replace (Dr + 8 * Z.of_nat nw <? 1) with false by (symmetry; apply Z.ltb_ge; clear - DRP; lia).
      cbn [Z.b2z].
      chk ltac:(fun C => clear - C; lia).
      do 4 zstep.
      replace (Z.of_nat nw ≪ 3) with (8 * Z.of_nat nw) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      rewrite (lxor_signbit63' n) by lia.
      rewrite ?land64_small by lia.
      replace (n + 9223372036854775808 <? 9223372036854775745) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (Dr + 8 * Z.of_nat nw <? 8 * Z.of_nat nw) with false by (symmetry; apply Z.ltb_ge; clear - DRP; lia).
      cbn [Z.b2z Z.lxor].
      chk ltac:(fun C => clear - C; lia).
      zstep.
      rewrite (bk_swrap32_small (Z.of_nat topx + -1)) by lia.
      zstep. rewrite lts_signed by lia. if_cases KO; zify_cond KO. { exfalso. clear - KO. lia. } clear KO.
      step. do 2 zstep.
      replace (Dx + (Z.of_nat topx + -1) ≪ 3) with (Dx + 8 * (Z.of_nat topx - 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      do 2 zstep.
      rewrite ?land64_small by lia.
      replace (0 <? Dx) with true by (symmetry; apply Z.ltb_lt; exact (proj1 DXA)).
      replace (Dx + 8 * (Z.of_nat topx - 1) <? 1) with false by (symmetry; apply Z.ltb_ge; clear - DXA NTOP; lia).
      cbn [Z.b2z].
      chk ltac:(fun C => clear - C; lia).
      do 4 zstep.
      rewrite (lxor_signbit63' (Z.of_nat topx + -1)) by lia.
      replace (Z.of_nat topx + -1 + 9223372036854775808 <? 9223372036854775808) with false by (symmetry; apply Z.ltb_ge; clear - NTOP; lia).
      replace (Dx + 8 * (Z.of_nat topx - 1) <? Dx) with false by (symmetry; apply Z.ltb_ge; clear - NTOP; lia).
      cbn [Z.b2z Z.lxor].
      chk ltac:(fun C => clear - C; lia).
      chk ltac:(fun C => rewrite ?unsigned_lit in C by lia; lia).
      zstep. rewrite (land7 (Dx + 8 * (Z.of_nat topx - 1))) by (clear - DXA; Z.div_mod_to_equations; lia).
      chk ltac:(fun C => clear - C; lia).
      do 3 zstep.
      replace (Dr + 8 * Z.of_nat nw + Z.of_nat topx ≪ 3) with (Dr + 8 * Z.of_nat nw + 8 * Z.of_nat topx) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      rewrite ?land64_small by lia.
      replace (Dr + 8 * Z.of_nat nw + 8 * Z.of_nat topx <? 1) with false by (symmetry; apply Z.ltb_ge; clear - DRP; lia).
      cbn [Z.b2z].
      chk ltac:(fun C => clear - C; lia).
      do 4 zstep.
      rewrite (lxor_signbit63' (Z.of_nat topx)) by lia.
      replace (Z.of_nat topx + 9223372036854775808 <? 9223372036854775808) with false by (symmetry; apply Z.ltb_ge; clear; lia).
      replace (Dr + 8 * Z.of_nat nw + 8 * Z.of_nat topx <? Dr + 8 * Z.of_nat nw) with false by (symmetry; apply Z.ltb_ge; clear; lia).
      cbn [Z.b2z Z.lxor].
      chk ltac:(fun C => clear - C; lia).
      zstep. rewrite (land7 (Dr + 8 * Z.of_nat nw + 8 * Z.of_nat topx)) by (clear - DR8; Z.div_mod_to_equations; lia).
      chk ltac:(fun C => clear - C; lia).
      replace (Z.of_nat topx + -1) with (Z.of_nat topx - 1) by (clear; lia).
      replace (Z.of_nat topx) with (Z.of_nat (length f)) by (rewrite Lf; reflexivity).
      eapply (lshg_block _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 f Dx Dr (8 * Z.of_nat nw) n lb (negw_m n) HN31 Hlb ELB HNN ENN LMf HTOP HFP DR0 ltac:(clear; lia) DISJ
                ltac:(clear - DRP DR8 DXA; repeat split; Z.div_mod_to_equations; lia));
        [ exact HLX | exact WRmid | exact MI2 |].
      intros m3 z5 z6 z7 z13 z16 z17 z28 z29 z30 z31 HRES MI3 MUb WMb.
      transport_after_call bgusegs m2 m3 MUb WMb.
      eapply (FIN m3 (ls0 ++ [mo])); try eassumption.
      apply limbarr_limbs_at. split; [rewrite ESEQ; exact HRES|].
      rewrite Lnew. replace (8 * Z.of_nat (topx + 1)) with (8 * (Z.of_nat (length f) + 1)) by (rewrite Lf; clear; lia). exact WRmid.
  Qed.
End Proofs.
End WithCeiling0.
