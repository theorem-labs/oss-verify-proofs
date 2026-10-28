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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU2 Require Import W_set_word.
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

Definition BN_ADD_WORD : Z := 0x10afb8.
Definition BN_IS_ZERO : Z := 0xfde2c.
Definition BN_ADD_WORD_STACK : Z := 48 + BN_WEXPAND_STACK.

Definition add_word_hi (b : bignum bptr) (top : nat) (c : Z) : bignum bptr :=
  mkBN (bn_d b) (upd (bn_buf b) top c) (top + 1) (bn_neg b) (bn_flags b).

Lemma wlimbs_upd : forall l (i : nat) v, (i < length l)%nat -> Arr.upd (wlimbs l) i (Z_to_bv 64 v) = wlimbs (upd l i v).
Proof.
  induction l as [|y l IH]; intros i v H; cbn [length] in H; [lia|].
  destruct i as [|i']; [reflexivity|].
  unfold wlimbs in *. cbn [map Arr.upd]. rewrite (IH i' v) by lia.
  unfold upd, splice. cbn [firstn length Nat.add skipn app map]. reflexivity.
Qed.

Lemma wlimbs_nth : forall buf (i : nat), (i < length buf)%nat -> nth_error (wlimbs buf) (Z.to_nat (Z.of_nat i)) = Some (Z_to_bv 64 (nth i buf 0)).
Proof. intros buf i H. rewrite Nat2Z.id. unfold wlimbs. rewrite nth_error_map. rewrite (nth_error_nth' buf 0) by lia. reflexivity. Qed.

Lemma add_word_limbs_cons : forall x l w, w <> 0 ->
  add_word_limbs (x :: l) w = (addw x w :: fst (add_word_limbs l (if addw x w <? w then 1 else 0)), snd (add_word_limbs l (if addw x w <? w then 1 else 0))).
Proof.
  intros x l w Hw. cbn [add_word_limbs]. replace (w =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hw).
  destruct (add_word_limbs l _). reflexivity.
Qed.

Lemma add_word_limbs_0 : forall l, add_word_limbs l 0 = (l, 0).
Proof. intros [|x l]; reflexivity. Qed.

Lemma add_word_limbs_length : forall l w, length (fst (add_word_limbs l w)) = length l.
Proof.
  induction l as [|x l IH]; intros w; [reflexivity|]. cbn [add_word_limbs]. destruct (w =? 0); [reflexivity|].
  specialize (IH (if addw x w <? w then 1 else 0)). destruct (add_word_limbs l _). cbn [fst length] in *. lia.
Qed.

Lemma add_word_limbs_limbs : forall l w, limbs l -> 0 <= w < 18446744073709551616 ->
  limbs (fst (add_word_limbs l w)) /\ 0 <= snd (add_word_limbs l w) < 18446744073709551616.
Proof.
  induction l as [|x l IH]; intros w Hl Hw; [cbn; split; [constructor| exact Hw]|].
  cbn [add_word_limbs]. destruct (w =? 0); [cbn [fst snd]; split; [exact Hl| exact Hw]|].
  apply limbs_cons_inv in Hl. destruct Hl as [Hx Hl].
  assert (HC : 0 <= (if addw x w <? w then 1 else 0) < 18446744073709551616) by (destruct (addw x w <? w); lia).
  specialize (IH _ Hl HC). destruct (add_word_limbs l _) as [r w']. cbn [fst snd] in *. destruct IH as [IH1 IH2].
  split; [| exact IH2]. constructor; [| exact IH1]. unfold limb, addw. apply Z.mod_pos_bound. rewrite BW_lit. lia.
Qed.

Lemma addw_carry : forall x w, 0 <= x < 18446744073709551616 -> 0 < w < 18446744073709551616 ->
  (addw x w <? x) = (addw x w <? w).
Proof.
  intros x w Hx Hw. unfold addw. rewrite BW_lit.
  destruct (Z.ltb_spec ((x + w) mod 18446744073709551616) x), (Z.ltb_spec ((x + w) mod 18446744073709551616) w); try reflexivity; exfalso; Z.div_mod_to_equations; lia.
Qed.

Lemma Z_to_bv_addw : forall x w, Z_to_bv 64 (x + w) = Z_to_bv 64 (addw x w).
Proof. intros. unfold addw. rewrite BW_lit. symmetry. apply (ZBridge.Z_to_bv_mod64 (x + w)). Qed.

Lemma aw_loop : forall (Q : machine_state -> Prop) (F : bvmap 5 word) (fc : bv 32)
    (x1 x2 gp tp x5 x6 x7 x8 x9 x10 x17 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (ax D : Z) (c1 c2 c3 c4 : word) (top : nat) (rest la pre : list Z) (m1 : mem) (wi : Z) (x12 x13 x14 x15 x16 : word),
  limbs pre -> limbs la -> limbs rest -> 0 < wi < 18446744073709551616 -> (length pre + length la = top)%nat -> Z.of_nat (top + length rest) < 2 ^ 28 ->
  rw_cells bgusegs m1 ax [C8 (Z_to_bv 64 D); C4 c1; C4 c2; C4 c3; C4 c4] -> (ax + 24 <= D \/ D + 8 * Z.of_nat (top + length rest) <= ax) ->
  u64arr bgusegs m1 D (wlimbs (pre ++ la ++ rest)) -> mem_inv bgusegs m1 -> 0 < D -> D mod 8 = 0 -> D + 8 * Z.of_nat top < 2 ^ 63 ->
  x10 = Z_to_bv 64 (8 * Z.of_nat top + 8) ->
  (forall (m' : mem) (y13 y14 y15 y16 : word),
      u64arr bgusegs m' D (wlimbs (pre ++ fst (add_word_limbs la wi) ++ rest)) ->
      munch [(D + 8 * Z.of_nat (length pre), D + 8 * Z.of_nat top)] m1 m' -> wmono bgusegs m1 m' -> mem_inv bgusegs m' ->
      snd (add_word_limbs la wi) <> 0 ->
      evt bgusegs Q (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (8 * Z.of_nat top)) (Z_to_bv 64 (8 * Z.of_nat top + 8)) y13 y14 y15 y16 x17
                              (Z_to_bv 64 (snd (add_word_limbs la wi))) (Z_to_bv 64 ax) x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                         F (Z_to_bv 64 0x10b0cc) fc None m' (seg_rom bgusegs))) ->
  (forall (m' : mem) (y11 y12 y13 y14 y15 y16 : word),
      u64arr bgusegs m' D (wlimbs (pre ++ fst (add_word_limbs la wi) ++ rest)) ->
      munch [(D + 8 * Z.of_nat (length pre), D + 8 * Z.of_nat top)] m1 m' -> wmono bgusegs m1 m' -> mem_inv bgusegs m' ->
      snd (add_word_limbs la wi) = 0 ->
      evt bgusegs Q (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 y11 y12 y13 y14 y15 y16 x17
                              (Z_to_bv 64 1) (Z_to_bv 64 ax) x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                         F (Z_to_bv 64 0x10b0c4) fc None m' (seg_rom bgusegs))) ->
  evt bgusegs Q (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (8 * Z.of_nat (length pre))) x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 wi) (Z_to_bv 64 ax) x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x10b078) fc None m1 (seg_rom bgusegs)).
Proof.
  intros Q F fc x1 x2 gp tp x5 x6 x7 x8 x9 x10 x17 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 ax D c1 c2 c3 c4 top rest.
  induction la as [|x la IH]; intros pre m1 wi x12 x13 x14 x15 x16 Lpre Lla Lrest HW LEN L28 BN SEP U MI D0 D8 DB -> KC KN.
  -
    pose proof (u64arr_bound bgusegs _ _ _ U) as UB. rewrite wlimbs_len, !length_app in UB. cbn [length] in LEN, UB.
    step. step. if_cases KE; zify_cond KE; [| exfalso; rewrite ?unsigned_lit in KE by lia; lia]. clear KE.
    replace (length pre) with top by lia.
    eapply KC; [exact U| apply munch_refl| apply wmono_refl| exact MI| cbn; lia].
  - pose proof (u64arr_bound bgusegs _ _ _ U) as UB. rewrite wlimbs_len, !length_app in UB. cbn [length] in LEN, UB.
    assert (LM : Z.of_nat (length (wlimbs (pre ++ (x :: la) ++ rest))) = Z.of_nat (top + length rest)) by (rewrite wlimbs_len, !length_app; cbn [length]; lia).
    apply limbs_cons_inv in Lla. destruct Lla as [[Hx0 Hx1] Lla]. rewrite BW_lit in Hx1.
    step. step. if_cases KE; zify_cond KE; [exfalso; rewrite ?unsigned_lit in KE by lia; lia|]. clear KE.
    step. step.
    ub_chk. step. step. step. ub_chk. ub_chk. step. step. ub_chk.
    assert (NTH : nth_error (wlimbs (pre ++ (x :: la) ++ rest)) (Z.to_nat (Z.of_nat (length pre))) = Some (Z_to_bv 64 x)).
    { rewrite <- (app_nth2_plus pre ((x :: la) ++ rest)) at 2 || idtac.
      replace x with (nth (length pre) (pre ++ (x :: la) ++ rest) 0) at 2 by (rewrite app_nth2, Nat.sub_diag by lia; reflexivity).
      apply wlimbs_nth. rewrite !length_app. cbn [length]. lia. }
    pose proof (u64arr_read bgusegs m1 D _ (Z.of_nat (length pre)) _ (wa (D + 8 * Z.of_nat (length pre))) U NTH ltac:(lia) eq_refl) as RD.
    step. clear RD. step. setreg 15%Z (Z_to_bv 64 (addw x wi)) ltac:(symmetry; apply Z_to_bv_addw).
    pose proof (conj (Z.mod_pos_bound (x + wi) BW ltac:(rewrite BW_lit; lia)) I) as HS. unfold addw in HS |- *. rewrite BW_lit in HS |- *.
    set (sx := (x + wi) mod 18446744073709551616) in *. destruct HS as [HS _].
    assert (IDX : 0 <= Z.of_nat (length pre) < Z.of_nat (length (wlimbs (pre ++ (x :: la) ++ rest)))) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (u64arr_store_ok bgusegs mx D _ (Z.of_nat (length pre)) (wa (D + 8 * Z.of_nat (length pre))) U IDX eq_refl) as SOKW;
      pose proof (u64arr_write bgusegs mx D _ (Z.of_nat (length pre)) (Z_to_bv 64 sx) U IDX) as U2 end.
    rewrite Nat2Z.id, wlimbs_upd in U2 by (rewrite !length_app; cbn [length]; lia).
    replace (upd (pre ++ (x :: la) ++ rest) (length pre) sx) with ((pre ++ [sx]) ++ la ++ rest) in U2
      by (unfold upd, splice; rewrite firstn_app, Nat.sub_diag, firstn_O, firstn_all2, app_nil_r by lia;
          rewrite skipn_app, skipn_all2 by lia; replace (length pre + 1 - length pre)%nat with 1%nat by lia; cbn [skipn app]; rewrite <- app_assoc; reflexivity).
    pose proof (munch_refl [(D + 8 * Z.of_nat (length pre), D + 8 * Z.of_nat top)] m1) as MU. pose proof (wmono_refl bgusegs m1) as WM.
    clear U. step. store_done.
    step. step.
    step.
    pose proof (addw_carry x wi ltac:(lia) ltac:(lia)) as EC. unfold addw in EC. rewrite BW_lit in EC. fold sx in EC.
    rewrite (add_word_limbs_cons x la wi) in KC, KN by lia. cbn [fst snd] in KC, KN. unfold addw in KC, KN. rewrite BW_lit in KC, KN. fold sx in KC, KN.
    rewrite <- EC in KC, KN.
    if_cases KCY; zify_cond KCY.
    +
      replace (sx <? x) with true in KC, KN by (symmetry; apply Z.ltb_lt; exact KCY).
      replace (8 * Z.of_nat (length pre) + 8) with (8 * Z.of_nat (length (pre ++ [sx]))) by (rewrite length_app; cbn [length]; lia).
      eapply (IH (pre ++ [sx])); [apply limbs_app; [exact Lpre| constructor; [unfold limb; rewrite BW_lit; lia| constructor]] | exact Lla | exact Lrest | lia
        | rewrite length_app; cbn [length]; lia | exact L28 | eassumption | exact SEP | exact U2 | assumption | exact D0 | exact D8 | exact DB | reflexivity | |].
      * intros m' y13 y14 y15 y16 U' MU' WM' MI' NC.
        eapply KC; [rewrite <- app_assoc in U'; exact U'| | eapply wmono_trans; [eassumption| exact WM']| exact MI'| exact NC].
        eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU']]; unfold sub_fp; cbn [outside]; intros z [Hz _]; split; [| exact I]; intros Hc; apply Hz; rewrite length_app in Hc; cbn [length] in Hc; clear - Hc; lia.
      * intros m' y11 y12 y13 y14 y15 y16 U' MU' WM' MI' NC.
        eapply KN; [rewrite <- app_assoc in U'; exact U'| | eapply wmono_trans; [eassumption| exact WM']| exact MI'| exact NC].
        eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU']]; unfold sub_fp; cbn [outside]; intros z [Hz _]; split; [| exact I]; intros Hc; apply Hz; rewrite length_app in Hc; cbn [length] in Hc; clear - Hc; lia.
    +
      replace (sx <? x) with false in KN by (symmetry; apply Z.ltb_ge; lia). rewrite add_word_limbs_0 in KN. cbn [fst snd] in KN.
      eapply KN; [rewrite <- app_assoc in U2; exact U2| exact MU| assumption| assumption| reflexivity].
Qed.

Lemma aw_bound_machine : forall top, 0 < top < 2147483648 ->
  Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (0 + - bv_unsigned (v_slt (Z_to_bv 64 0) (Z_to_bv 64 top))))) (bv_unsigned (Z_to_bv 64 top))))) 3 + 8) = Z_to_bv 64 (8 * top + 8).
Proof.
  intros top Ht. rewrite v_slt_b2z. rewrite (unsigned_lit 0), (unsigned_lit top) by lia.
  rewrite Z.lxor_0_l, (zb_lxor_pow2_small top 63) by lia.
  replace (2 ^ 63 <? top + 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  rewrite (unsigned_lit 1) by lia. change (0 + - (1)) with (-1).
  rewrite (unsigned_lit_land (-1)). change (Z.land (-1) 18446744073709551615) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones, Z.mod_small by lia. rewrite unsigned_lit by lia.
  rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia.
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma BN_add_word_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rx : bnref) (ax w : Z),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_ADD_WORD_STACK -> tp = wz RATP ->
    ref_at bs OW PL rx ax -> wref PL rx -> a0 = wz ax -> a1 = wz w -> 0 <= w < 2^64 ->
    implM bgusegs (interp (embed (BN_add_word (tree_ops bptr) rx w bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = wz 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW')))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_ADD_WORD) fc None m (seg_rom bgusegs)).
  Proof.
    intros until w. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> HAx WRx -> -> HW. pose proof (proj1 WRx) as NROx.
    unfold BN_ADD_WORD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, BN_ADD_WORD, BN_IS_ZERO, GLOBALS_TOP, MallocRep.wz in *.
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
    unfold BN_add_word, BN_zero, bbind, bget, bset, bret. cbn [bind ret tree_ops tbind fst snd].
    unfold implM. iprefix.
    carve_frame 48%nat ST. do 7 step. step. step.
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    assert (WOKh : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) [rx]) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).

    assert (EPI : forall (st1 : PState) (bs1 : bstate bptr) (m2 : mem) (OW2 : list block) (errv2 : word)
                         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word),
      RHEAP st1 (OW2 ++ LB) m2 -> lib_state bs1 m2 OW2 PL EA -> rauxv_ok m2 B -> stk bgusegs m2 lo (bv_unsigned sp + -48) ->
      rw_cells bgusegs m2 3346164 [C4 errv2] -> mem_inv bgusegs m2 -> lx_pres LB (bv_unsigned sp) (XW PL) m m2 ->
      ps_fa st1 = ps_fa s -> ps_so st1 = ps_so s -> refs_stable bs OW bs1 OW2 ->
      (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW2) ->
      rw_cells bgusegs m2 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      implM bgusegs (interp (embed (TRet (tt, bs1)))) st1
        (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
                 (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx bs) <> Some q -> In (q, A, n) OW')))
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 RATP) x5 x6 x7 sp (Z_to_bv 64 1) x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x10b12c) fc None m2 (seg_rom bgusegs))).
    { intros st1 bs1 m2 OW2 errv2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31
             HEAP2 LS2 AUX2 ST2 ERR2 MI2 LXP2 FA2 SO2 RST2 BST FR2.
      clear BNx ARRx Ux MU WM ST ERR MI FR HWL WOK WOKh LSH.
      cbn [embed interp]. apply implM_ret.
      step. do 6 step. release_frame FR2 ST2 (bv_unsigned sp). step. step.
      apply evt_done.
      unfold bn_post. do 15 eexists. exists m2, OW2, PL, errv2. split; [reflexivity|]. cbn [fst snd].
      split; [exact HEAP2|]. split; [exact LS2|]. split; [exact AUX2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact MI2|].
      split; [exact LXP2|]. split; [exact FA2|]. split; [exact SO2|]. split; [exact RST2|].
      split; [reflexivity|]. split; [reflexivity| exact BST]. }
    step. if_cases KW; zify_cond KW.
    -
      assert (EW : w = 0) by (rewrite ?unsigned_lit in KW by lia; lia).
      replace (w =? 0) with true by (symmetry; apply Z.eqb_eq; exact EW).
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
      assert (MU2 : munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m2).
      { eapply munch_trans; [eapply munch_weaken; [|exact MU]| eapply munch_weaken; [|exact MUc]]; unfold sub_fp; intros x Hx; cbn [outside] in *; lia. }
      assert (WM2 : wmono bgusegs m m2) by (eapply wmono_trans; [exact WM| exact WMc]).
      assert (HWL2 : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp - 64, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
      assert (WOK2 : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp - 64, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
      assert (WOKh2 : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) [rx]) [(bv_unsigned sp - 64, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
      clear ST MI MU WM MUc WMc HWL WOK WOKh.
      destruct (bn_top bx =? 0)%nat eqn:ET; step; if_cases KT; zify_cond KT; try (exfalso; rewrite ?unsigned_lit in KT by lia; cbn in KT; lia).
      +
        apply Nat.eqb_eq in ET. clear KT.
        do 8 step. release_frame FR STc (bv_unsigned sp). step. step.
        ihere. to_implM.
        eapply implM_mono.
        { eapply (BN_set_word_walk HM HF ra sp) with (lo := lo) (B := B) (errv := errv) (rx := rx) (ax := ax) (w := w) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
            [| reflexivity | exact HAx | exact WRx | reflexivity | reflexivity | lia].
          unfold bn_pre.
          split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU2 WM2 HWL2 CEIL)|].
          split; [exact (lib_state_frame s LB _ _ [] bs m m2 OW PL EA _ HEAP LS MU2 WM2 FROK WOK2)|]. split; [exact FROK|].
          split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU2 WM2 HWL2 SPB ltac:(lia)); unfold GLOBALS_TOP; lia|]. split; [exact SPB|]. split; [exact B63|].
          split; [exact STc|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|]. split; [unfold BN_SET_WORD_STACK, BN_EXPAND2_STACK; lia|].
          split; [unfold LX_ERRNO, RATP; exact ERR| exact MIc]. }
        cbv beta. intros [u bs'] st' ms' PO. unfold bn_post in *. cbn [fst snd] in *.
        destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m' & OW' & PL' & errv' & -> & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11).
        do 15 eexists. exists m', OW', PL', errv'. split; [reflexivity|].
        do 6 (split; [assumption|]). split; [|split; [assumption| split; [assumption| split; [assumption| exact P11]]]].
        eapply lx_pres_trans; [|exact P7]. apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU2 WM2 HWL2 CEIL); unfold GLOBALS_TOP; lia.
      +
        apply Nat.eqb_neq in ET. clear KT.
        destruct (bn_neg bx) eqn:EN.
        {
          ihere. to_implM. unfold bunr. cbn [unreachable tree_ops embed interp]. apply implM_interp_unr. }
        cbn [Z.b2z] in BNx.
        ub_chk. step. ub_chk. step. step. if_cases KN; zify_cond KN; [| exfalso; rewrite ?unsigned_lit in KN by lia; cbn in KN; lia]. clear KN.
        step. step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_top bx))) by lia.
        step. step. step. step. step.
        setreg 10%Z (Z_to_bv 64 (8 * Z.of_nat (bn_top bx) + 8)) ltac:(symmetry; apply aw_bound_machine; lia).
        setreg 11%Z (Z_to_bv 64 0) ltac:(reflexivity).

        assert (HDx : exists px, bn_d bx = Some px /\ In (px, Dx, 8 * Z.of_nat (bn_dmax bx)) OW).
        { pose proof ARRx as ARRx'. unfold bn_arr in ARRx'. destruct (bn_d bx) as [px|] eqn:Edx0; [exists px; split; [reflexivity| exact (proj1 ARRx')]|].
          exfalso. destruct (bn_arr_null PL rx m OW Dx bx PWF WRx Edx0 ARRx) as [_ E]. unfold bn_dmax in OKx2. rewrite E in OKx2. cbn in OKx2. lia. }
        destruct HDx as (px & Edx & Hinpx).
        assert (ALD : 0 < Dx /\ Dx mod 8 = 0) by (eapply block_ualign; [exact HEAP| exact Hinpx]). destruct ALD as (DX0 & DX8).
        pose proof (add_word_limbs_length (firstn (bn_top bx) (bn_buf bx)) w) as LENl. rewrite firstn_length_le in LENl by lia.
        pose proof (add_word_limbs_limbs (firstn (bn_top bx) (bn_buf bx)) w (limbs_firstn _ _ OKx1) ltac:(lia)) as [Ll Lw'].
        destruct (add_word_limbs (firstn (bn_top bx) (bn_buf bx)) w) as [l w'] eqn:EAW. cbn [fst snd] in LENl, Ll, Lw'.

        set (nb := splice (bn_buf bx) 0 l).
        assert (Enb : nb = l ++ skipn (bn_top bx) (bn_buf bx)) by (subst nb; unfold splice; rewrite firstn_O, LENl; reflexivity).
        assert (Lnb : length nb = bn_dmax bx) by (subst nb; rewrite splice_length; [exact LBX| rewrite LENl, LBX; lia]).
        assert (LMnb : limbs nb) by (subst nb; apply splice_limbs; [exact OKx1| exact Ll]).

        assert (AFTER : forall m3, u64arr bgusegs m3 Dx (wlimbs nb) -> munch [(Dx, Dx + 8 * Z.of_nat (bn_top bx))] m2 m3 -> wmono bgusegs m2 m3 -> mem_inv bgusegs m3 ->
                  let bs2 := setbn rx (bn_with_buf bx nb) bs in
                  RHEAP s (OW ++ LB) m3 /\ lib_state bs2 m3 OW PL EA /\ rauxv_ok m3 B /\ stk bgusegs m3 lo (bv_unsigned sp + -48)
                  /\ rw_cells bgusegs m3 3346164 [C4 errv] /\ lx_pres LB (bv_unsigned sp) (XW PL) m m3
                  /\ rw_cells bgusegs m3 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
        { intros m3 U3 MU3 WM3 MI3 bs2.
          assert (MUT : munch [(bv_unsigned sp - 64, bv_unsigned sp); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]%Z m m3).
          { eapply munch_trans; [eapply munch_weaken; [|exact MU2]| eapply munch_weaken; [|exact MU3]]; unfold sub_fp; intros x Hx; cbn [outside] in *; lia. }
          assert (WMT : wmono bgusegs m m3) by (eapply wmono_trans; [exact WM2| exact WM3]).
          assert (HWLT : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp - 64, bv_unsigned sp); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]).
          { constructor; [left; cbn; lia|]. constructor; [| constructor]. right; left; exists (px, Dx, 8 * Z.of_nat (bn_dmax bx)); cbn; split; [exact Hinpx| clear; lia]. }
          assert (WOKc : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) [rx]) [(bv_unsigned sp - 64, bv_unsigned sp); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]).
          { constructor; [apply w_stack; cbn; lia|]. constructor; [| constructor].
            eapply (w_limbs OW LB bs PL EA (bv_unsigned sp) false [rx] _ rx px Dx); [left; reflexivity| exact HVx| exact Edx| exact Hinpx| cbn [fst snd]; fold bx; clear; lia| cbn [fst snd]; fold bx; clear; lia]. }
          eapply (rw_cells_transport bgusegs _ m2 m3) in FR; [| exact MU3 | exact WM3 | cbn; lia].
          eapply (rw_cells_transport bgusegs _ m2 m3) in ERR; [| exact MU3 | exact WM3 | cbn; lia].
          eapply (rw_cells_transport bgusegs _ m2 m3) in BNx; [| exact MU3 | exact WM3 | cbn; lia].
          split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MUT WMT HWLT CEIL)|].
          split.
          { unfold lib_state. eapply (lib_state_close [] bs m3 OW PL EA rx ax); [| exact ND| exact HAx| exact NROx| | |].
            - exact (lib_state_frame s LB _ _ [rx] bs m m3 OW PL EA _ HEAP LSH MUT WMT FROK WOKc).
            - exists Dx. split.
              + unfold bn_cells, bn_dmax, bn_with_buf. cbn [bn_top bn_buf bn_neg bn_flags bn_d]. rewrite Lnb, EN. exact BNx.
              + unfold bn_arr, bn_dmax, bn_with_buf. cbn [bn_d bn_buf]. rewrite Edx, Lnb. split; [exact Hinpx| exact U3].
            - unfold bg_ok, bn_dmax, bn_with_buf. cbn [bn_buf bn_top bn_flags]. rewrite Lnb. unfold BG_DMAX in *.
              split; [exact LMnb|]. split; [exact OKx2|]. split; [clear - OKx3; unfold bn_dmax in *; lia| exact OKx4].
            - apply ids_ok_setbn_same; [exact IDS| exact HVx|]. unfold bn_blocks, bn_dmax, bn_with_buf. cbn [bn_d bn_buf]. rewrite Lnb. reflexivity. }
          split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MUT WMT HWLT SPB ltac:(lia)); unfold GLOBALS_TOP; lia|].
          split; [eapply stk_transport_disjoint; [exact STc| exact MU3| exact WM3| cbn [disjoint_from]; lia]|].
          split; [exact ERR|].
          split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MUT WMT HWLT CEIL); unfold GLOBALS_TOP; lia| exact FR]. }
        set (bs2 := setbn rx (bn_with_buf bx nb) bs) in *.
        assert (RST2 : refs_stable bs OW bs2 OW) by (apply refs_stable_setbn).
        eapply (aw_loop _ F fc) with (ax := ax) (D := Dx) (top := bn_top bx) (rest := skipn (bn_top bx) (bn_buf bx)) (la := firstn (bn_top bx) (bn_buf bx)) (pre := []) (wi := w) (m1 := m2);
          [ constructor | apply limbs_firstn; exact OKx1 | apply limbs_skipn; exact OKx1 | lia | cbn [length]; rewrite firstn_length_le by lia; lia
          | rewrite length_skipn, LBX; clear - OKx2 OKx3; unfold bn_dmax in *; lia | exact BNx | rewrite length_skipn, LBX; clear - SEPxx OKx2; unfold bn_dmax in *; lia
          | cbn [app]; rewrite firstn_skipn; exact Ux | exact MIc | exact DX0 | exact DX8 | clear - DxC OKx2; unfold bn_dmax in *; lia | reflexivity | | ]; rewrite EAW; cbn [fst snd app length].
        *
          intros m3 y13 y14 y15 y16 U3 MU3 WM3 MI3 NC. rewrite <- Enb in U3.
          replace (Dx + 8 * Z.of_nat 0) with Dx in MU3 by lia.
          destruct (AFTER m3 U3 MU3 WM3 MI3) as (HEAP3 & LS3 & AUX3 & ST3 & ERR3 & LXP3 & FR3).
          replace (w' =? 0) with false by (symmetry; apply Z.eqb_neq; exact NC).
          assert (HAx2 : ref_at bs2 OW PL rx ax) by (eapply ref_at_stable; [exact RST2| exact HAx]).
          assert (HVx2 : vref rx bs2) by (eapply ref_at_valid; [exact LS3| exact HAx2]).
          assert (ETOP2 : bn_top (getbn rx bs2) = bn_top bx) by (subst bs2; rewrite getbn_setbn_same by exact HVx; reflexivity).
          assert (OK22 : (bn_top (getbn rx bs2) <= bn_dmax (getbn rx bs2))%nat).
          { subst bs2. rewrite getbn_setbn_same by exact HVx. unfold bn_with_buf, bn_dmax. cbn [bn_top bn_buf]. rewrite Lnb. exact OKx2. }
          clear AFTER BNx Ux STc ERR FR MIc MU2 WM2 MU3 WM3 U3 HWL2 WOK2 WOKh2 LSH.
          step. if_cases KS; zify_cond KS; [exfalso; rewrite ?unsigned_lit in KS by lia; cbn in KS; lia|]. clear KS.
          step. rewrite (unsigned_lit (Z.of_nat (bn_top bx))) by lia. rewrite (bn_swrap32_small (Z.of_nat (bn_top bx) + 1)) by lia.
          ub_chk.
          step. step.
          ihere. to_implM.
          eapply implM_embed_bind.
          { eapply BnLeaves.implM_embed_leaves; [apply (bn_wexpand_leaves rx (bn_top bx + 1) bs2 HVx2 OK22)|].
            eapply (bn_wexpand_walk HM HF) with (lo := lo) (B := B) (errv := errv) (r := rx) (a := ax) (OW := OW) (LB := LB) (PL := PL) (EA := EA) (words := (bn_top bx + 1)%nat);
              [| reflexivity | exact HAx2 | exact WRx | reflexivity | unfold MallocRep.wz; f_equal; lia | lia].
            unfold bn_pre. rewrite ESP.
            split; [exact HEAP3|]. split; [exact LS3|]. split; [eapply frames_ok_call; [exact FROK| exact CEIL| lia| lia]|]. split; [exact AUX3|]. split; [lia|]. split; [exact B63|].
            split; [exact ST3|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|]. split; [unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia|].
            split; [unfold LX_ERRNO, RATP; exact ERR3| exact MI3]. }
          cbv beta. intros [u bs3] st3 ms3 [PO LEAF]. unfold bn_post in PO. cbn [fst snd] in *.
          destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13' & y14' & m4 & OW4 & PL4 & errv4 & -> & HEAP4 & LS4 & AUX4 & ST4 & ERR4
                          & MI4 & LXP4 & FA4 & SO4 & RST4 & -> & -> & HDM & WRES & BST4).
          rewrite ESP in *. unfold LX_ERRNO, RATP in ERR4. change (3346328 - 164) with 3346164 in ERR4.
          lazymatch goal with |- implM _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
            replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
          destruct LEAF as (LF1 & LF2 & LF3 & LF4 & LF5 & LF6). cbn [snd] in *. rewrite ETOP2 in LF2.
          lazymatch type of FR3 with rw_cells _ _ ?adr ?cells => assert (FR4 : rw_cells bgusegs m4 adr cells) end.
          { eapply rw_cells_agree; [apply agree_of_lx_pres; exact LXP4 | exact FR3 |].
            intros a Ha. cbn in Ha. eapply (xw_client PL LB _ (bv_unsigned sp) B); [exact (proj1 FROK)| lia|].
            unfold LIBW_bgr, BnRep.LIBW_bn, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. lia. }
          clear FR3 ERR3 ST3 MI3.

          assert (FROK4 : frames_ok PL (bv_unsigned sp) B) by exact FROK.
          pose proof (ref_at_stable _ _ _ _ _ _ _ RST4 HAx2) as HAx4.
          pose proof (RH_nodup_l _ _ _ _ HEAP4) as ND4.
          pose proof (lib_state_h_parts _ _ _ _ _ _ LS4) as PARTS4; pose proof PARTS4 as (WFS4 & PWF4 & IDS4 & PLB4 & ERRB4).
          pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS4 HAx4) as HVx4.
          destruct (lib_state_open [] bs3 m4 OW4 PL EA rx ax LS4 ND4 HAx4 ltac:(intros []) NROx) as ((Dr & BNr & ARRr) & (OKq1 & OKq2 & OKq3 & OKq4) & LSH4).
          destruct (bn_arr_facts st3 OW4 LB m4 HEAP4 bs3 PL EA _ _ PARTS4 FROK4 rx Dr HVx4 ltac:(assumption) ARRr) as (Ur & LENr & Dr0 & DrC & DrI & DSEPr).
          set (br := getbn rx bs3) in *.
          pose proof (DSEPr rx ax HAx4) as SEPrr.
          pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP4 PARTS4 FROK4 HAx4 NROx) as (XB0 & XBC & XBI).
          unfold bn_cells in BNr. unfold BG_DMAX in OKq3. rewrite LF2 in BNr.
          assert (HDr : exists pr, bn_d br = Some pr /\ In (pr, Dr, 8 * Z.of_nat (bn_dmax br)) OW4).
          { pose proof ARRr as ARRr'. unfold bn_arr in ARRr'. destruct (bn_d br) as [pr|] eqn:Edr0; [exists pr; split; [reflexivity| exact (proj1 ARRr')]|].
            exfalso. destruct (bn_arr_null PL rx m4 OW4 Dr br PWF4 WRx Edr0 ARRr) as [_ E]. unfold bn_dmax in HDM. rewrite E in HDM. cbn in HDM. lia. }
          destruct HDr as (pr & Edr & Hinpr).
          assert (ALR : 0 < Dr /\ Dr mod 8 = 0) by (eapply block_ualign; [exact HEAP4| exact Hinpr]). destruct ALR as (DR0 & DR8).

          clear LENx Dx0 DxC DxI SEPxx DSEPx XA0 XAC XAI KW Hinpx Edx Lnb LMnb Enb.
          assert (LBR : length (bn_buf br) = bn_dmax br) by reflexivity.
          pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m4) as MU5.
          pose proof (wmono_refl bgusegs m4) as WM5.
          unfold implM. iprefix.
          step. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by lia; lia|]. clear KZ.

          step. step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_top bx))) by lia.
          ub_chk. step. step. step.
          setreg 10%Z (Z_to_bv 64 (Dr + 8 * Z.of_nat (bn_top bx))) ltac:(f_equal; rewrite (unsigned_lit (Z.of_nat (bn_top bx))) by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
          step. replace (Z.of_nat (bn_top bx) + 1) with (Z.of_nat (bn_top bx + 1)) in BNr by lia.
          ub_chk. step. step. step. ub_chk. ub_chk. step. ub_chk.
          assert (IDX : 0 <= Z.of_nat (bn_top bx) < Z.of_nat (length (wlimbs (bn_buf br)))) by (rewrite wlimbs_len, LBR; unfold bn_dmax in HDM; lia).
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
            pose proof (u64arr_store_ok bgusegs mx Dr _ (Z.of_nat (bn_top bx)) (wa (Dr + 8 * Z.of_nat (bn_top bx))) Ur IDX eq_refl) as SOKW;
            pose proof (u64arr_write bgusegs mx Dr _ (Z.of_nat (bn_top bx)) (Z_to_bv 64 w') Ur IDX) as U6 end.
          rewrite Nat2Z.id, (wlimbs_upd (bn_buf br) (bn_top bx)) in U6 by (rewrite LBR; unfold bn_dmax in HDM; lia).
          clear Ur. step. store_done.
          step.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
          set (nb2 := upd (bn_buf br) (bn_top bx) w') in *.
          assert (Lnb2 : length nb2 = bn_dmax br) by (subst nb2; rewrite upd_length by (rewrite LBR; unfold bn_dmax in HDM; lia); exact LBR).
          assert (LMnb2 : limbs nb2) by (subst nb2; apply upd_limbs; [exact OKq1| unfold limb; rewrite BW_lit; exact Lw']).
          assert (HWL5 : Forall (w_lib bs3 OW4 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -48, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
          { constructor; [left; cbn; lia|]. constructor; [right; right; exists rx, ax; split; [exact HAx4|]; split; [exact NROx|]; cbn; lia|].
            constructor; [| constructor]. right; left; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn; split; [exact Hinpr| clear; lia]. }
          assert (WOK5 : Forall (w_ok OW4 LB bs3 PL EA (bv_unsigned sp) [rx]) [(bv_unsigned sp + -48, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
          { constructor; [apply w_stack; cbn; lia|]. constructor; [eapply (w_struct OW4 LB bs3 PL EA (bv_unsigned sp) false [rx] _ rx ax); [left; reflexivity| exact HAx4| assumption| cbn; lia| cbn; lia]|].
            constructor; [| constructor].
            eapply (w_limbs OW4 LB bs3 PL EA (bv_unsigned sp) false [rx] _ rx pr Dr); [left; reflexivity| exact HVx4| exact Edr| exact Hinpr| cbn [fst snd]; fold br; clear; lia| cbn [fst snd]; fold br; clear; lia]. }
          ihere. to_implM. cbn [tbind fst snd]. fold br.
          change (mkBN (bn_d br) (upd (bn_buf br) (bn_top bx) w') (bn_top bx + 1) (bn_neg br) (bn_flags br)) with (add_word_hi br (bn_top bx) w').
          eapply (EPI st3 (setbn rx (add_word_hi br (bn_top bx) w') bs3) m6 OW4 errv4);
            [ exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP4 PARTS4 FROK4 MU5 WM5 HWL5 CEIL)
            | | apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP4 PARTS4 FROK4 AUX4 MU5 WM5 HWL5 SPB ltac:(lia)); unfold GLOBALS_TOP; lia
            | assumption | exact ERR4 | assumption
            | eapply lx_pres_trans; [exact LXP3|]; eapply lx_pres_trans; [eapply lx_pres_weaken; [exact LXP4| lia | intros b0 Hb0; exact Hb0 | intros q0 Hq0; exact Hq0]|];
              apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP4 PARTS4 FROK4 MU5 WM5 HWL5 CEIL); unfold GLOBALS_TOP; lia
            | congruence | congruence
            | eapply refs_stable_trans; [exact RST2|]; eapply refs_stable_trans; [exact RST4| apply refs_stable_setbn]
            | intros q0 A0 n0 Hq0 Hne; apply BST4; [exact Hq0|]; subst bs2; rewrite getbn_setbn_same by exact HVx; unfold bn_with_buf; cbn [bn_d]; exact Hne
            | exact FR4 ].
          unfold lib_state. eapply (lib_state_close [] bs3 m6 OW4 PL EA rx ax); [| exact ND4| exact HAx4| exact NROx| | |].
          -- exact (lib_state_frame st3 LB _ _ [rx] bs3 m4 m6 OW4 PL EA _ HEAP4 LSH4 MU5 WM5 FROK WOK5).
          -- exists Dr. split.
             ++ unfold bn_cells, bn_dmax, add_word_hi. cbn [bn_top bn_buf bn_neg bn_flags bn_d]. fold nb2. rewrite Lnb2. exact BNr.
             ++ unfold bn_arr, bn_dmax, add_word_hi. cbn [bn_d bn_buf]. fold nb2. rewrite Edr, Lnb2. split; [exact Hinpr| exact U6].
          -- unfold bg_ok, bn_dmax, add_word_hi. cbn [bn_buf bn_top bn_flags]. fold nb2. rewrite Lnb2. unfold BG_DMAX in *.
             split; [exact LMnb2|]. split; [unfold bn_dmax in HDM; lia|]. split; [clear - OKq3; unfold bn_dmax in *; lia| exact OKq4].
          -- apply ids_ok_setbn_same; [exact IDS4| exact HVx4|]. unfold bn_blocks, bn_dmax, add_word_hi. cbn [bn_d bn_buf]. fold nb2. rewrite Lnb2. reflexivity.
        *
          intros m3 y11 y12 y13 y14 y15 y16 U3 MU3 WM3 MI3 NC. rewrite <- Enb in U3.
          replace (Dx + 8 * Z.of_nat 0) with Dx in MU3 by lia.
          destruct (AFTER m3 U3 MU3 WM3 MI3) as (HEAP3 & LS3 & AUX3 & ST3 & ERR3 & LXP3 & FR3).
          replace (w' =? 0) with true by (symmetry; apply Z.eqb_eq; exact NC).
          step. step.
          ihere. to_implM.
          eapply (EPI s bs2 m3 OW errv);
            [exact HEAP3 | exact LS3 | exact AUX3 | exact ST3 | exact ERR3 | exact MI3 | exact LXP3
            | reflexivity | reflexivity | exact RST2 | intros q0 A0 n0 Hq0 _; exact Hq0 | exact FR3].
  Qed.
End Proofs.
End WithCeiling0.
