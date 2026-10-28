(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnBridge BgState BgInv BgLib BgWordSpec.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit F_memset F_memcpy.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnArith BnMem BnTac BnTacX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_crypto.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep BnLeaves BnAssoc W_rshift W_small2.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import BgLeaves W_expand.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Walk.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac to_implM :=
  lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
    lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_SUB_WORD : Z := 0x10b154.
Definition BN_IS_ZERO : Z := 0xfde2c.
Definition BN_SUB_WORD_STACK : Z := 64.

Definition sw_l (b : bignum bptr) (w : Z) : list Z := fst (sub_word_limbs (firstn (bn_top b) (bn_buf b)) w 0).
Definition sw_i (b : bignum bptr) (w : Z) : nat := snd (sub_word_limbs (firstn (bn_top b) (bn_buf b)) w 0).
Definition sw_buf (b : bignum bptr) (w : Z) : list Z := splice (bn_buf b) 0 (sw_l b w).
Definition sw_top (b : bignum bptr) (w : Z) : nat :=
  if (nth (sw_i b w) (sw_buf b w) 0 =? 0) && (sw_i b w =? bn_top b - 1)%nat then (bn_top b - 1)%nat else bn_top b.
Definition sw_bn (b : bignum bptr) (w : Z) : bignum bptr := mkBN (bn_d b) (sw_buf b w) (sw_top b w) (bn_neg b) (bn_flags b).

Lemma sw_top_le : forall b w, (sw_top b w <= bn_top b)%nat.
Proof. intros b w. unfold sw_top. destruct (_ && _); lia. Qed.
Lemma sw_top_keep : forall b w, nth (sw_i b w) (sw_buf b w) 0 <> 0 \/ sw_i b w <> (bn_top b - 1)%nat -> sw_top b w = bn_top b.
Proof.
  intros b w H. unfold sw_top. destruct (Z.eqb_spec (nth (sw_i b w) (sw_buf b w) 0) 0) as [E|E]; [| reflexivity].
  destruct (Nat.eqb_spec (sw_i b w) (bn_top b - 1)) as [E2|E2]; [| reflexivity]. exfalso. destruct H as [H|H]; [exact (H E)| exact (H E2)].
Qed.
Lemma sw_top_dec : forall b w, nth (sw_i b w) (sw_buf b w) 0 = 0 -> sw_i b w = (bn_top b - 1)%nat -> sw_top b w = (bn_top b - 1)%nat.
Proof. intros b w H1 H2. unfold sw_top. rewrite H1, H2, Z.eqb_refl, Nat.eqb_refl. reflexivity. Qed.

Lemma wlimbs_upd : forall l (i : nat) v, (i < length l)%nat -> Arr.upd (wlimbs l) i (Z_to_bv 64 v) = wlimbs (upd l i v).
Proof.
  induction l as [|y l IH]; intros i v H; cbn [length] in H; [lia|].
  destruct i as [|i']; [reflexivity|].
  unfold wlimbs in *. cbn [map Arr.upd]. rewrite (IH i' v) by lia.
  unfold upd, splice. cbn [firstn length Nat.add skipn app map]. reflexivity.
Qed.

Lemma wlimbs_nth : forall buf (i : nat), (i < length buf)%nat -> nth_error (wlimbs buf) (Z.to_nat (Z.of_nat i)) = Some (Z_to_bv 64 (nth i buf 0)).
Proof. intros buf i H. rewrite Nat2Z.id. unfold wlimbs. rewrite nth_error_map. rewrite (nth_error_nth' buf 0) by lia. reflexivity. Qed.

Lemma upd_mid : forall (pre : list Z) x post v, upd (pre ++ x :: post) (length pre) v = pre ++ v :: post.
Proof.
  intros pre x post v. unfold upd, splice. rewrite firstn_app, Nat.sub_diag, firstn_O, firstn_all2, app_nil_r by lia.
  rewrite skipn_app, skipn_all2 by (cbn [length]; lia). replace (length pre + length [v] - length pre)%nat with 1%nat by (cbn [length]; lia).
  cbn [skipn app]. reflexivity.
Qed.

Lemma Z_to_bv_subw : forall x w, Z_to_bv 64 (x - w) = Z_to_bv 64 (subw x w).
Proof. intros. unfold subw. rewrite BW_lit. symmetry. apply (ZBridge.Z_to_bv_mod64 (x - w)). Qed.

Lemma sub_word_limbs_ge : forall x l w i, w <= x -> sub_word_limbs (x :: l) w i = ((x - w) :: l, i).
Proof. intros x l w i H. cbn [sub_word_limbs]. replace (w <=? x) with true by (symmetry; apply Z.leb_le; exact H). reflexivity. Qed.

Lemma sub_word_limbs_lt : forall x l w i, x < w ->
  sub_word_limbs (x :: l) w i = (subw x w :: fst (sub_word_limbs l 1 (S i)), snd (sub_word_limbs l 1 (S i))).
Proof.
  intros x l w i H. cbn [sub_word_limbs]. replace (w <=? x) with false by (symmetry; apply Z.leb_gt; exact H).
  destruct (sub_word_limbs l 1 (S i)). reflexivity.
Qed.

Lemma sub_word_limbs_zeros : forall zs y l i, Forall (fun z => z = 0) zs -> 1 <= y ->
  sub_word_limbs (zs ++ y :: l) 1 i = (repeat 18446744073709551615 (length zs) ++ (y - 1) :: l, (i + length zs)%nat).
Proof.
  induction zs as [|z zs IH]; intros y l i HZ Hy.
  - cbn [app length repeat]. rewrite sub_word_limbs_ge by exact Hy. f_equal. lia.
  - inversion HZ as [|z' zs' Hz HZ' E1]; subst. cbn [app length repeat]. rewrite sub_word_limbs_lt by lia.
    rewrite (IH y l (S i) HZ' Hy). cbn [fst snd]. f_equal; first [reflexivity | lia].
Qed.

Lemma sw_loop : forall (Q : machine_state -> Prop) (F : bvmap 5 word) (fc : bv 32)
    (x1 x2 gp tp x5 x6 x7 x8 x9 x10 x16 x17 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (D n : Z) (m0 : mem) (rest la pre : list Z) (x v : Z) (m1 : mem) (x13 x14 x15 : word),
  x13 = Z_to_bv 64 (D + 8 * Z.of_nat (length pre)) ->
  limbs pre -> limbs (x :: la) -> limbs rest -> 1 <= v < 18446744073709551616 -> v <= lval (x :: la) ->
  n = Z.of_nat (length pre + 1 + length la) -> Z.of_nat (length pre + 1 + length la + length rest) < 2 ^ 28 ->
  0 < D -> D mod 8 = 0 -> D + 8 * n < 2 ^ 63 ->
  munch [(D, D + 8 * n)] m0 m1 -> wmono bgusegs m0 m1 ->
  u64arr bgusegs m1 D (wlimbs (pre ++ x :: la ++ rest)) -> mem_inv bgusegs m1 ->
  (forall (m' : mem) (A Bs : list Z) (y w2 : Z) (q15 : word),
      pre ++ fst (sub_word_limbs (x :: la) v (length pre)) ++ rest = A ++ (y - w2) :: Bs ->
      length A = snd (sub_word_limbs (x :: la) v (length pre)) ->
      1 <= w2 <= y -> y < 18446744073709551616 ->
      u64arr bgusegs m' D (wlimbs (A ++ (y - w2) :: Bs)) ->
      munch [(D, D + 8 * n)] m0 m' -> wmono bgusegs m0 m' -> mem_inv bgusegs m' ->
      evt bgusegs Q (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 D) (Z_to_bv 64 (Z.of_nat (length A))) (Z_to_bv 64 (D + 8 * Z.of_nat (length A)))
                              (Z_to_bv 64 y) q15 x16 x17 (Z_to_bv 64 w2) x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                         F (Z_to_bv 64 0x10b294) fc None m' (seg_rom bgusegs))) ->
  evt bgusegs Q (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 D) (Z_to_bv 64 (Z.of_nat (length pre))) x13
                          x14 x15 x16 x17 (Z_to_bv 64 v) x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x10b248) fc None m1 (seg_rom bgusegs)).
Proof.
  intros Q F fc x1 x2 gp tp x5 x6 x7 x8 x9 x10 x16 x17 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 D n m0 rest.
  induction la as [|y0 la IH]; intros pre x v m1 x13 x14 x15 E13 Lpre Lxla Lrest HV HL EN L28 D0 D8 DB MU WM U MI K; subst x13.
  -
    pose proof (u64arr_bound bgusegs _ _ _ U) as UB. rewrite wlimbs_len, length_app in UB. cbn [length] in UB. rewrite length_app in UB. cbn [length] in UB, L28, EN.
    apply limbs_cons_inv in Lxla. destruct Lxla as [[Hx0 Hx1] Lla]. rewrite BW_lit in Hx1.
    assert (NTH : nth_error (wlimbs (pre ++ x :: [] ++ rest)) (Z.to_nat (Z.of_nat (length pre))) = Some (Z_to_bv 64 x)).
    { replace x with (nth (length pre) (pre ++ x :: [] ++ rest) 0) at 2 by (rewrite app_nth2 by lia; rewrite Nat.sub_diag; reflexivity).
      apply wlimbs_nth. rewrite length_app. cbn [length]. rewrite length_app. cbn [length]. lia. }
    cbn [lval] in HL. rewrite BW_lit in HL.
    assert (GE : v <= x) by lia.
    pose proof (u64arr_read bgusegs m1 D _ (Z.of_nat (length pre)) _ (wa (D + 8 * Z.of_nat (length pre))) U NTH ltac:(lia) eq_refl) as RD.
    step. ub_chk.
    step. clear RD.
    step. rewrite ?(unsigned_lit v) by lia. rewrite ?(unsigned_lit x) by lia.
    assert (IDX : 0 <= Z.of_nat (length pre) < Z.of_nat (length (wlimbs (pre ++ x :: [] ++ rest)))) by (rewrite wlimbs_len, length_app; cbn [length app]; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (u64arr_store_ok bgusegs mx D _ (Z.of_nat (length pre)) (wa (D + 8 * Z.of_nat (length pre))) U IDX eq_refl) as SOKW;
      pose proof (u64arr_write bgusegs mx D _ (Z.of_nat (length pre)) (Z_to_bv 64 (x - v)) U IDX) as U2 end.
    rewrite Nat2Z.id, wlimbs_upd in U2 by (rewrite length_app; cbn [length]; lia). rewrite upd_mid in U2.
    setreg 15%Z (Z_to_bv 64 (x - v)) ltac:(f_equal; clear; lia).
    clear U. step. store_done.
    step. if_cases KG; zify_cond KG; [| exfalso; rewrite ?unsigned_lit in KG by lia; lia]. clear KG.
    rewrite (sub_word_limbs_ge x [] v (length pre) GE) in K. cbn [fst snd] in K.
    eapply (K _ pre ([] ++ rest) x v); [reflexivity | reflexivity | lia | lia | exact U2 | eassumption | eassumption | assumption].
  -
    pose proof (u64arr_bound bgusegs _ _ _ U) as UB. rewrite wlimbs_len, length_app in UB. cbn [length] in UB. rewrite length_app in UB. cbn [length] in UB, L28, EN.
    apply limbs_cons_inv in Lxla. destruct Lxla as [[Hx0 Hx1] Lla]. rewrite BW_lit in Hx1.
    assert (NTH : nth_error (wlimbs (pre ++ x :: (y0 :: la) ++ rest)) (Z.to_nat (Z.of_nat (length pre))) = Some (Z_to_bv 64 x)).
    { replace x with (nth (length pre) (pre ++ x :: (y0 :: la) ++ rest) 0) at 2 by (rewrite app_nth2 by lia; rewrite Nat.sub_diag; reflexivity).
      apply wlimbs_nth. rewrite length_app. cbn [length]. rewrite length_app. cbn [length]. lia. }
    pose proof (u64arr_read bgusegs m1 D _ (Z.of_nat (length pre)) _ (wa (D + 8 * Z.of_nat (length pre))) U NTH ltac:(lia) eq_refl) as RD.
    step. ub_chk.
    step. clear RD.
    step. rewrite ?(unsigned_lit v) by lia. rewrite ?(unsigned_lit x) by lia.
    assert (IDX : 0 <= Z.of_nat (length pre) < Z.of_nat (length (wlimbs (pre ++ x :: (y0 :: la) ++ rest)))) by (rewrite wlimbs_len, length_app; cbn [length]; rewrite length_app; cbn [length]; lia).
    destruct (Z_le_gt_dec v x) as [GE|LT].
    +
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (u64arr_store_ok bgusegs mx D _ (Z.of_nat (length pre)) (wa (D + 8 * Z.of_nat (length pre))) U IDX eq_refl) as SOKW;
        pose proof (u64arr_write bgusegs mx D _ (Z.of_nat (length pre)) (Z_to_bv 64 (x - v)) U IDX) as U2 end.
      rewrite Nat2Z.id, wlimbs_upd in U2 by (rewrite length_app; cbn [length]; lia). rewrite upd_mid in U2.
      setreg 15%Z (Z_to_bv 64 (x - v)) ltac:(f_equal; clear; lia).
      clear U. step. store_done.
      step. if_cases KG; zify_cond KG; [| exfalso; rewrite ?unsigned_lit in KG by lia; lia]. clear KG.
      rewrite (sub_word_limbs_ge x (y0 :: la) v (length pre) GE) in K. cbn [fst snd] in K.
      eapply (K _ pre ((y0 :: la) ++ rest) x v); [reflexivity | reflexivity | lia | lia | exact U2 | eassumption | eassumption | assumption].
    +
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (u64arr_store_ok bgusegs mx D _ (Z.of_nat (length pre)) (wa (D + 8 * Z.of_nat (length pre))) U IDX eq_refl) as SOKW;
        pose proof (u64arr_write bgusegs mx D _ (Z.of_nat (length pre)) (Z_to_bv 64 (subw x v)) U IDX) as U2 end.
      rewrite Nat2Z.id, wlimbs_upd in U2 by (rewrite length_app; cbn [length]; lia). rewrite upd_mid in U2.
      setreg 15%Z (Z_to_bv 64 (subw x v)) ltac:(symmetry; replace (x + - v) with (x - v) by (clear; lia); apply Z_to_bv_subw).
      clear U. step. store_done.
      step. if_cases KG; zify_cond KG; [exfalso; rewrite ?unsigned_lit in KG by lia; lia|]. clear KG.
      assert (HSV : 0 <= subw x v < 18446744073709551616) by (unfold subw; rewrite BW_lit; apply Z.mod_pos_bound; clear; lia).
      assert (LV1 : 1 <= lval (y0 :: la)).
      { cbn [lval] in HL. rewrite BW_lit in HL. pose proof (lval_nonneg (y0 :: la) Lla) as LN. cbn [lval] in LN |- *. rewrite BW_lit in LN |- *. clear - HL LT LN Hx0. lia. }
      step. rewrite ?(unsigned_lit (Z.of_nat (length pre))) by lia. rewrite ?(bn_swrap32_small (Z.of_nat (length pre) + 1)) by lia.
      ub_chk.
      step. step. step.
      setreg 13%Z (Z_to_bv 64 (D + 8 * (Z.of_nat (length pre) + 1))) ltac:(f_equal; rewrite ?unsigned_lit by lia; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); lia).
      step. step. step.
      ub_chk.
      step. step.
      step. if_cases KZ; zify_cond KZ; [| exfalso; rewrite ?ub_land64_small in KZ by lia; rewrite ?unsigned_lit in KZ by lia; lia]. clear KZ.
      setreg 13%Z (Z_to_bv 64 (D + 8 * Z.of_nat (length (pre ++ [subw x v])))) ltac:(f_equal; rewrite length_app; cbn [length]; lia).
      setreg 12%Z (Z_to_bv 64 (Z.of_nat (length (pre ++ [subw x v])))) ltac:(f_equal; rewrite length_app; cbn [length]; lia).
      replace (pre ++ subw x v :: (y0 :: la) ++ rest) with ((pre ++ [subw x v]) ++ y0 :: la ++ rest) in U2 by (rewrite <- app_assoc; reflexivity).
      eapply (IH (pre ++ [subw x v]) y0 1);
        [ reflexivity | apply limbs_app; [exact Lpre| constructor; [unfold limb; rewrite BW_lit; lia| constructor]] | exact Lla | exact Lrest | lia | exact LV1
        | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia | exact D0 | exact D8 | exact DB | eassumption | eassumption | exact U2 | assumption | ].
      intros m' A Bs y w2 q15 EQ LA HWY HY U' MU' WM' MI'.
      rewrite (sub_word_limbs_lt x (y0 :: la) v (length pre) ltac:(lia)) in K. cbn [fst snd] in K.
      replace (length (pre ++ [subw x v])) with (S (length pre)) in EQ, LA by (rewrite length_app; cbn [length]; lia).
      eapply (K m' A Bs y w2); [rewrite <- EQ, <- app_assoc; reflexivity | exact LA | exact HWY | exact HY | exact U' | exact MU' | exact WM' | exact MI'].
Qed.

  Lemma BN_sub_word_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rx : bnref) (ax w : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_SUB_WORD_STACK -> tp = wz RATP ->
    ref_at bs OW PL rx ax -> wref PL rx -> a0 = wz ax -> a1 = wz w -> 0 <= w < 2^64 ->
    w <= lval (firstn (bn_top (getbn rx bs)) (bn_buf (getbn rx bs))) ->
    implM bgusegs (interp (embed (BN_sub_word (tree_ops bptr) rx w bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = wz 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW')))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_SUB_WORD) fc None m (seg_rom bgusegs)).
  Proof.
    intros until w. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> HAx WRx -> -> HW HMAG. pose proof (proj1 WRx) as NROx.
    unfold BN_SUB_WORD_STACK, BN_SUB_WORD, BN_IS_ZERO, GLOBALS_TOP, MallocRep.wz in *.
    change (2 ^ 64) with 18446744073709551616 in HW.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    destruct (lib_state_open [] bs m OW PL EA rx ax LS ND HAx ltac:(intros []) NROx) as ((Dx & BNx & ARRx) & (OKx1 & OKx2 & OKx3 & OKx4) & LSH).
    destruct (bn_arr_facts s OW LB m HEAP bs PL EA _ _ PARTS FROK rx Dx ltac:(eapply ref_at_valid; [exact LS| exact HAx]) NROx ARRx) as (Ux & LENx & Dx0 & DxC & DxI & DSEPx).
    set (bx := getbn rx bs) in *.
    pose proof (DSEPx rx ax HAx) as SEPxx.
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAx NROx) as (XA0 & XAC & XAI).
    assert (ALX : 0 < ax /\ ax mod 8 = 0) by (eapply ref_at_ualign; [exact HEAP| exact PARTS| exact HAx| exact NROx]). pose proof ALX as (AX0 & AX8).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAx) as HVx.
    unfold bn_cells in BNx. unfold BG_DMAX in OKx3.
    assert (LBX : length (bn_buf bx) = bn_dmax bx) by reflexivity.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    unfold BN_sub_word, bbind, bget, bset, bret. cbn [bind ret tree_ops tbind fst snd].
    unfold implM. iprefix.
    carve_frame 48%nat ST. do 6 step. step.
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).

    assert (EPI : forall (st1 : PState) (bs1 : bstate bptr) (m2 : mem) (OW2 : list block) (errv2 : word) (jk : list byte)
                         (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
      RHEAP st1 (OW2 ++ LB) m2 -> lib_state bs1 m2 OW2 PL EA -> rauxv_ok m2 B -> stk bgusegs m2 lo (bv_unsigned sp + -48) ->
      rw_cells bgusegs m2 3346164 [C4 errv2] -> mem_inv bgusegs m2 -> lx_pres LB (bv_unsigned sp) (XW PL) m m2 ->
      ps_fa st1 = ps_fa s -> ps_so st1 = ps_so s -> refs_stable bs OW bs1 OW2 ->
      (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW2) ->
      rw_cells bgusegs m2 (bv_unsigned sp + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      implM bgusegs (interp (embed (TRet (tt, bs1)))) st1
        (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
                 (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW')))
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 RATP) x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x10b1e4) fc None m2 (seg_rom bgusegs))).
    { intros st1 bs1 m2 OW2 errv2 jk x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31
             HEAP2 LS2 AUX2 ST2 ERR2 MI2 LXP2 FA2 SO2 RST2 BST FR2.
      clear BNx ARRx Ux MU WM ST ERR MI FR HWL WOK LSH.
      cbn [embed interp]. apply implM_ret.
      step. do 5 step. release_frame FR2 ST2 (bv_unsigned sp). step. step.
      apply evt_done.
      unfold bn_post. do 15 eexists. exists m2, OW2, PL, errv2. split; [reflexivity|]. cbn [fst snd].
      split; [exact HEAP2|]. split; [exact LS2|]. split; [exact AUX2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact MI2|].
      split; [exact LXP2|]. split; [exact FA2|]. split; [exact SO2|]. split; [exact RST2|].
      split; [reflexivity|]. split; [reflexivity| exact BST]. }
    step. if_cases KW; zify_cond KW.
    -
      assert (EW : w = 0) by (rewrite ?unsigned_lit in KW by lia; lia).
      replace (w =? 0) with true by (symmetry; apply Z.eqb_eq; exact EW).
      step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      ihere. to_implM.
      eapply (EPI s bs m1 OW errv);
        [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)
        | exact (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK)
        | apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia
        | exact ST | exact ERR | exact MI
        | apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); unfold GLOBALS_TOP; lia
        | reflexivity | reflexivity | apply refs_stable_refl
        | intros q0 A0 n0 Hq0 _; exact Hq0 | exact FR].
    -
      assert (NW : w <> 0) by (rewrite ?unsigned_lit in KW by lia; lia).
      replace (w =? 0) with false by (symmetry; apply Z.eqb_neq; exact NW).
      cbn [tbind fst snd]. fold bx.

      destruct (bn_top bx =? 0)%nat eqn:ET.
      { ihere. to_implM. unfold bunr. cbn [unreachable tree_ops embed interp]. apply implM_interp_unr. }
      apply Nat.eqb_neq in ET.
      assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).

      step. step. step.
      eapply evt_cut.
      { eapply BgBnU.W_small2.BN_is_zero_spec with (lo := lo) (A := ax) (D := Dx) (b := bx);
          [exact BNx | exact ALX | lia | rewrite ESP; exact ST | rewrite ESP; lia | exact MI | rewrite ESP; lia | reflexivity]. }
      intros ms' PO. unfold BgBnU.W_small.bn_small_post in PO.
      destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & STc & ->).
      subst ms'. rewrite ESP in *.
      lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
      eapply (rw_cells_transport bgusegs _ _ m2) in FR; [| exact MUc | exact WMc | cbn; lia].
      eapply (rw_cells_transport bgusegs _ _ m2) in ERR; [| exact MUc | exact WMc | cbn; lia].
      eapply (rw_cells_transport bgusegs _ _ m2) in BNx; [| exact MUc | exact WMc | cbn; lia].
      eapply (u64arr_transport bgusegs _ _ m2) in Ux; [| exact MUc | exact WMc | cbn [disjoint_from]; rewrite wlimbs_len; fold (bn_dmax bx); lia].

      assert (HDx : exists px, bn_d bx = Some px /\ In (px, Dx, 8 * Z.of_nat (bn_dmax bx)) OW).
      { pose proof ARRx as ARRx'. unfold bn_arr in ARRx'. destruct (bn_d bx) as [px|] eqn:Edx0; [exists px; split; [reflexivity| exact (proj1 ARRx')]|].
        exfalso. destruct (bn_arr_null PL rx m OW Dx bx PWF WRx Edx0 ARRx) as [_ E]. unfold bn_dmax in OKx2. rewrite E in OKx2. cbn in OKx2. lia. }
      destruct HDx as (px & Edx & Hinpx).
      assert (ALD : 0 < Dx /\ Dx mod 8 = 0) by (eapply block_ualign; [exact HEAP| exact Hinpx]). destruct ALD as (DX0 & DX8).
      assert (MU2 : munch [(bv_unsigned sp - 64, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]%Z m m2).
      { eapply munch_trans; [eapply munch_weaken; [|exact MU]| eapply munch_weaken; [|exact MUc]]; unfold sub_fp; intros x Hx; cbn [outside] in *; lia. }
      assert (WM2 : wmono bgusegs m m2) by (eapply wmono_trans; [exact WM| exact WMc]).
      clear ST MI MU WM MUc WMc HWL WOK.
      replace (bn_top bx =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; exact ET). cbn [Z.b2z].
      step. if_cases KT; zify_cond KT; [| exfalso; rewrite ?unsigned_lit in KT by lia; cbn in KT; lia]. clear KT.
      destruct (bn_neg bx) eqn:EN.
      { ihere. to_implM. unfold bunr. cbn [unreachable tree_ops embed interp]. apply implM_interp_unr. }
      cbn [Z.b2z] in BNx.
      ub_chk. step. ub_chk. step. step. if_cases KN; zify_cond KN; [| exfalso; rewrite ?unsigned_lit in KN by lia; cbn in KN; lia]. clear KN.

      set (top := bn_top bx) in *. set (buf := bn_buf bx) in *.
      assert (TOPD : (top <= length buf)%nat) by (unfold top, buf; unfold bn_dmax in OKx2; exact OKx2).
      assert (HFS : firstn top buf = nth 0 buf 0 :: skipn 1 (firstn top buf)).
      { destruct buf as [|b0 buf']; [cbn [length] in TOPD; lia|]. destruct top as [|top']; [lia|]. reflexivity. }
      set (d0 := nth 0 buf 0) in *. set (la := skipn 1 (firstn top buf)) in *.
      pose proof (limbs_firstn top buf OKx1) as LFS. rewrite HFS in LFS. apply limbs_cons_inv in LFS. destruct LFS as [[Hd0 Hd1] Lla]. rewrite BW_lit in Hd1.
      assert (LLA : length la = (top - 1)%nat) by (unfold la; rewrite length_skipn, firstn_length_le by exact TOPD; reflexivity).
      pose proof (lval_nonneg la Lla) as LAN.
      rewrite HFS in HMAG. cbn [lval] in HMAG. rewrite BW_lit in HMAG.
      assert (Hcase : ((top =? 1)%nat && (d0 <? w)) = false).
      { destruct (Nat.eqb_spec top 1) as [E1|E1]; [| reflexivity]. cbn [andb]. apply Z.ltb_ge.
        destruct la as [|y t]; [cbn [lval] in HMAG; lia| cbn [length] in LLA; lia]. }
      rewrite Hcase.
      pose proof (sub_word_limbs_spec (firstn top buf) w 0 (limbs_firstn top buf OKx1) ltac:(rewrite BW_lit; lia) ltac:(rewrite HFS; cbn [lval]; rewrite BW_lit; exact HMAG)) as SWS.
      destruct (sub_word_limbs (firstn top buf) w 0) as [l i] eqn:ESW.
      destruct SWS as (Ll & LENl & _ & _ & Hi & _). rewrite firstn_length_le in LENl, Hi by exact TOPD.
      assert (Hi' : (i < top)%nat) by (apply Hi; rewrite HFS; discriminate). clear Hi.
      assert (EBN : mkBN (bn_d bx) (splice buf 0 l) (if (nth i (splice buf 0 l) 0 =? 0) && (i =? top - 1)%nat then (top - 1)%nat else top) false (bn_flags bx) = sw_bn bx w).
      { unfold sw_bn, sw_top, sw_buf, sw_l, sw_i. fold top buf. rewrite ESW, EN. cbn [fst snd]. reflexivity. }
      rewrite EBN. clear EBN.
      assert (ESB : sw_buf bx w = l ++ skipn top buf).
      { unfold sw_buf, sw_l. fold top buf. rewrite ESW. cbn [fst]. unfold splice. rewrite firstn_O, LENl. reflexivity. }
      assert (ESI : sw_i bx w = i) by (unfold sw_i; fold top buf; rewrite ESW; reflexivity).
      assert (LSB : length (sw_buf bx w) = bn_dmax bx).
      { rewrite ESB, length_app, length_skipn, LENl. unfold bn_dmax. fold buf. lia. }
      assert (LMSB : limbs (sw_buf bx w)) by (rewrite ESB; apply limbs_app; [exact Ll| apply limbs_skipn; exact OKx1]).

      step. step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat top)) by (unfold top; lia).
      assert (NTH0 : nth_error (wlimbs buf) (Z.to_nat 0) = Some (Z_to_bv 64 d0)) by (apply (wlimbs_nth buf 0); lia).
      step.
      pose proof (RH_range _ _ _ _ _ _ _ HEAP Hinpx) as (BA0 & BA16 & _ & BAC & BAI).
      assert (HWL3 : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp - 64, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]).
      { constructor; [left; cbn; lia|]. constructor; [right; right; exists rx, ax; split; [exact HAx|]; split; [exact NROx|]; cbn; lia|].
        constructor; [| constructor]. right; left; exists (px, Dx, 8 * Z.of_nat (bn_dmax bx)); cbn; split; [exact Hinpx| clear; lia]. }
      assert (WOK3 : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) [rx]) [(bv_unsigned sp - 64, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]).
      { constructor; [apply w_stack; cbn; lia|]. constructor; [eapply (w_struct OW LB bs PL EA (bv_unsigned sp) false [rx] _ rx ax); [left; reflexivity| exact HAx| exact NROx| cbn; lia| cbn; lia]|].
        constructor; [| constructor].
        eapply (w_limbs OW LB bs PL EA (bv_unsigned sp) false [rx] _ rx px Dx); [left; reflexivity| exact HVx| exact Edx| exact Hinpx| cbn [fst snd]; fold bx; clear; lia| cbn [fst snd]; fold bx; clear; lia]. }

      assert (CLOSE : forall m5, rw_cells bgusegs m5 ax (bn_cells Dx (sw_bn bx w)) -> u64arr bgusegs m5 Dx (wlimbs (sw_buf bx w)) ->
                       munch [(bv_unsigned sp - 64, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]%Z m m5 -> wmono bgusegs m m5 ->
                       lib_state (setbn rx (sw_bn bx w) bs) m5 OW PL EA).
      { intros m5 BN5 U5 MU5 WM5. unfold lib_state. eapply (lib_state_close [] bs m5 OW PL EA rx ax); [| exact ND| exact HAx| exact NROx| | |].
        - exact (lib_state_frame s LB _ _ [rx] bs m m5 OW PL EA _ HEAP LSH MU5 WM5 FROK WOK3).
        - exists Dx. split; [exact BN5|]. unfold bn_arr, sw_bn, bn_dmax. cbn [bn_d bn_buf]. rewrite Edx. fold (bn_dmax bx). unfold bn_dmax in LSB. rewrite LSB. split; [exact Hinpx| exact U5].
        - unfold bg_ok, sw_bn, bn_dmax in *. cbn [bn_buf bn_top bn_flags]. rewrite LSB. split; [exact LMSB|]. split; [pose proof (sw_top_le bx w) as STL; clear - OKx2 STL; unfold top in *; lia|]. split; [unfold BG_DMAX; exact OKx3| exact OKx4].
        - apply ids_ok_setbn_same; [exact IDS| exact HVx|]. unfold bn_blocks, sw_bn, bn_dmax in *. cbn [bn_d bn_buf]. rewrite LSB. reflexivity. }

      lazymatch goal with |- evt _ ?Q _ => lazymatch type of FR with rw_cells _ _ _ ?frc =>
      assert (FIN : forall (m3 : mem) (A Bs : list Z) (y w' : Z) (q15 : word),
        sw_buf bx w = A ++ (y - w') :: Bs -> length A = i -> 1 <= w' <= y -> y < 18446744073709551616 ->
        u64arr bgusegs m3 Dx (wlimbs (sw_buf bx w)) ->
        rw_cells bgusegs m3 ax [C8 (wz Dx); C4 (wz (Z.of_nat top)); C4 (wz (Z.of_nat (bn_dmax bx))); C4 (wz 0); C4 (wz (bn_flags bx))] ->
        rw_cells bgusegs m3 (bv_unsigned sp + -48) frc ->
        rw_cells bgusegs m3 3346164 [C4 errv] -> stk bgusegs m3 lo (bv_unsigned sp + -48) -> mem_inv bgusegs m3 ->
        munch [(bv_unsigned sp - 64, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]%Z m m3 -> wmono bgusegs m m3 ->
        evt bgusegs Q (MS (mkR (Z_to_bv 64 1094016) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 ax) (Z_to_bv 64 (Z.of_nat top))
                            (Z_to_bv 64 Dx) (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 (Dx + 8 * Z.of_nat i)) (Z_to_bv 64 y) q15 v6 v7 (Z_to_bv 64 w') s3 s4
                            s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 0x10b294) fc None m3 (seg_rom bgusegs)))
      end end.
      { intros m3 A Bs y w' q15 EQB LA HWY HY U4 BN3 FR3 ERR3 ST3 MI3 MU3 WM3.
        clear Ux BNx FR ERR STc MIc MU2 WM2 NTH0.
        assert (NTHI : nth i (sw_buf bx w) 0 = y - w') by (rewrite EQB, app_nth2, LA, Nat.sub_diag by lia; reflexivity).
        step.
        assert (ECELL : forall tp', sw_top bx w = tp' ->
                  bn_cells Dx (sw_bn bx w) = [C8 (wz Dx); C4 (wz (Z.of_nat tp')); C4 (wz (Z.of_nat (bn_dmax bx))); C4 (wz 0); C4 (wz (bn_flags bx))]).
        { intros tp' Etp. unfold bn_cells, sw_bn, bn_dmax. cbn [bn_d bn_buf bn_top bn_neg bn_flags]. unfold bn_dmax in LSB. rewrite LSB, EN, Etp. reflexivity. }
        step. if_cases KY; zify_cond KY.
        -
          assert (NY : y <> w') by (rewrite ?unsigned_lit in KY by lia; lia). clear KY.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
          ihere. to_implM.
          eapply (EPI s (setbn rx (sw_bn bx w) bs) m5 OW errv);
            [ exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU3 WM3 HWL3 CEIL)
            | apply CLOSE; [| exact U4| exact MU3| exact WM3]
            | apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU3 WM3 HWL3 SPB ltac:(lia)); unfold GLOBALS_TOP; lia
            | exact ST3 | exact ERR3 | exact MI3
            | apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU3 WM3 HWL3 CEIL); unfold GLOBALS_TOP; lia
            | reflexivity | reflexivity | apply refs_stable_setbn
            | intros q0 A0 n0 Hq0 _; exact Hq0 | exact FR3 ].
          rewrite (ECELL top); [exact BN3|]. apply sw_top_keep. left. rewrite ESI, NTHI. lia.
        -
          assert (EY : y = w') by (rewrite ?unsigned_lit in KY by lia; lia). clear KY.
          step. rewrite (unsigned_lit (Z.of_nat top)) by (unfold top; lia). rewrite (bn_swrap32_small (Z.of_nat top + -1)) by (unfold top; lia).
          ub_chk.
          step. if_cases KI; zify_cond KI.
          +
            assert (NI : i <> (top - 1)%nat) by (rewrite ?unsigned_lit in KI by (unfold top; lia); lia). clear KI.
            lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
            ihere. to_implM.
            eapply (EPI s (setbn rx (sw_bn bx w) bs) m5 OW errv);
              [ exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU3 WM3 HWL3 CEIL)
              | apply CLOSE; [| exact U4| exact MU3| exact WM3]
              | apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU3 WM3 HWL3 SPB ltac:(lia)); unfold GLOBALS_TOP; lia
              | exact ST3 | exact ERR3 | exact MI3
              | apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU3 WM3 HWL3 CEIL); unfold GLOBALS_TOP; lia
              | reflexivity | reflexivity | apply refs_stable_setbn
              | intros q0 A0 n0 Hq0 _; exact Hq0 | exact FR3 ].
            rewrite (ECELL top); [exact BN3|]. apply sw_top_keep. right. rewrite ESI. exact NI.
          +
            assert (EI : i = (top - 1)%nat) by (rewrite ?unsigned_lit in KI by (unfold top; lia); lia). clear KI.
            assert (LMSBZ : Z.of_nat (length (wlimbs (sw_buf bx w))) = Z.of_nat (bn_dmax bx)) by (rewrite wlimbs_len, LSB; reflexivity).
            step. step.
            lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
            ihere. to_implM.
            eapply (EPI s (setbn rx (sw_bn bx w) bs) m5 OW errv);
              [ exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU3 WM3 HWL3 CEIL)
              | apply CLOSE; [| assumption| exact MU3| exact WM3]
              | apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU3 WM3 HWL3 SPB ltac:(lia)); unfold GLOBALS_TOP; lia
              | assumption | exact ERR3 | assumption
              | apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU3 WM3 HWL3 CEIL); unfold GLOBALS_TOP; lia
              | reflexivity | reflexivity | apply refs_stable_setbn
              | intros q0 A0 n0 Hq0 _; exact Hq0 | exact FR3 ].
            rewrite (ECELL i); [exact BN3|]. rewrite EI. apply sw_top_dec; [rewrite ESI, NTHI; lia| rewrite ESI; exact EI]. }
      assert (EBUF : buf = d0 :: la ++ skipn top buf) by (rewrite <- (firstn_skipn top buf) at 1; rewrite HFS; reflexivity).
      assert (LRS : length (skipn top buf) = (bn_dmax bx - top)%nat) by (rewrite length_skipn; reflexivity).

      lazymatch goal with |- evt _ ?Q (MS _ ?FF _ ?fcc None ?mm ?rom) =>
        let r1 := Walk.getreg 1%Z in let r2 := Walk.getreg 2%Z in let r3 := Walk.getreg 3%Z in let r4 := Walk.getreg 4%Z in let r5 := Walk.getreg 5%Z in
        let r6 := Walk.getreg 6%Z in let r7 := Walk.getreg 7%Z in let r8 := Walk.getreg 8%Z in let r9 := Walk.getreg 9%Z in let r10 := Walk.getreg 10%Z in
        let r11 := Walk.getreg 11%Z in let r13 := Walk.getreg 13%Z in let r14 := Walk.getreg 14%Z in let r15 := Walk.getreg 15%Z in
        let r16 := Walk.getreg 16%Z in let r17 := Walk.getreg 17%Z in let r18 := Walk.getreg 18%Z in let r19 := Walk.getreg 19%Z in let r20 := Walk.getreg 20%Z in
        let r21 := Walk.getreg 21%Z in let r22 := Walk.getreg 22%Z in let r23 := Walk.getreg 23%Z in let r24 := Walk.getreg 24%Z in let r25 := Walk.getreg 25%Z in
        let r26 := Walk.getreg 26%Z in let r27 := Walk.getreg 27%Z in let r28 := Walk.getreg 28%Z in let r29 := Walk.getreg 29%Z in let r30 := Walk.getreg 30%Z in
        let r31 := Walk.getreg 31%Z in
        assert (C74 : forall q12 : word, evt bgusegs Q (MS (mkR r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 q12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31)
                                                         FF (Z_to_bv 64 0x10b240) fcc None mm rom)) end.
      { intros q12. step. step.
        assert (DB : Dx + 8 * Z.of_nat top < 2 ^ 63) by (clear - DxC OKx2; unfold top in *; lia).
        pose proof (munch_refl [(Dx, Dx + 8 * Z.of_nat top)]%Z m2) as MUL. pose proof (wmono_refl bgusegs m2) as WML.
        setreg 12%Z (Z_to_bv 64 (Z.of_nat (length (@nil Z)))) ltac:(f_equal; cbn [length]; lia).
        eapply (sw_loop _ F fc) with (D := Dx) (n := Z.of_nat top) (m0 := m2) (rest := skipn top buf) (la := la) (pre := []) (x := d0) (v := w) (m1 := m2);
          [ f_equal; cbn [length]; lia
          | constructor | constructor; [unfold limb; rewrite BW_lit; lia | exact Lla] | apply limbs_skipn; exact OKx1 | lia | cbn [lval]; rewrite BW_lit; exact HMAG
          | cbn [length]; rewrite LLA; unfold top in *; lia | cbn [length]; rewrite LLA, LRS; clear - OKx2 OKx3 ET; unfold top in *; lia
          | exact DX0 | exact DX8 | exact DB | exact MUL | exact WML | cbn [app]; rewrite <- EBUF; exact Ux | exact MIc | ].
        intros m3 A Bs y w2 q15 EQ LA HWY HY U3 MU3 WM3 MI3. cbn [app length] in EQ, LA.
        rewrite <- HFS, ESW in EQ, LA. cbn [fst snd] in EQ, LA. rewrite <- ESB in EQ.
        eapply (rw_cells_transport bgusegs _ m2 m3) in FR; [| exact MU3 | exact WM3 | cbn; clear - BAC CEIL LO OKx2; unfold top in *; lia].
        eapply (rw_cells_transport bgusegs _ m2 m3) in ERR; [| exact MU3 | exact WM3 | cbn; clear - DxI Dx0 OKx2 ET; unfold top in *; lia].
        eapply (rw_cells_transport bgusegs _ m2 m3) in BNx; [| exact MU3 | exact WM3 | cbn; clear - SEPxx OKx2; unfold top in *; lia].
        eapply (stk_transport_disjoint bgusegs _ m2 m3) in STc; [| exact MU3 | exact WM3 | cbn [disjoint_from]; clear - BAC CEIL LO OKx2; unfold top in *; lia].
        assert (MUT : munch [(bv_unsigned sp - 64, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]%Z m m3).
        { eapply munch_trans; [exact MU2|]. eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]; intros x Hx. clear - Hx OKx2. unfold top in *. lia. }
        assert (WMT : wmono bgusegs m m3) by (eapply wmono_trans; [exact WM2| exact WM3]).
        rewrite LA.
        eapply (FIN m3 A Bs y w2);
          [ exact EQ | exact LA | exact HWY | exact HY | rewrite EQ; exact U3 | exact BNx | exact FR | exact ERR | exact STc | exact MI3 | exact MUT | exact WMT ]. }
      step. if_cases K1; zify_cond K1; [ub_chk; exact (C74 _)|].
      ub_chk. step. ub_chk.
      pose proof (u64arr_read bgusegs m2 Dx _ 0 _ (wa Dx) Ux NTH0 ltac:(lia) ltac:(f_equal; lia)) as RD.
      step. clear RD.
      step. if_cases K2; zify_cond K2; [exact (C74 _)|].
      exfalso. rewrite ?unsigned_lit in K1, K2 by (unfold top; lia).
      assert (E1 : top = 1%nat) by lia. rewrite E1 in Hcase. cbn [Nat.eqb andb] in Hcase. apply Z.ltb_ge in Hcase. lia.
  Qed.

End WithCeiling0.
