(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr ZBridge.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BgWords.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnW Require Import W_mul_words W_mul_add_words W_mul_normal.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnWU Require Import WU_mul_add_words.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Lemma firstn_S_nth : forall (l : list Z) j, (j < length l)%nat -> firstn (S j) l = firstn j l ++ [nth j l 0%Z].
Proof.
  intros l. induction l as [|x l IH]; intros j Hj; [cbn in Hj; lia|]. destruct j as [|j]; [reflexivity|].
  cbn [firstn nth]. cbn in Hj. rewrite (IH j) by lia. reflexivity.
Qed.

Lemma skipn_S_cons : forall (l : list Z) j, (j < length l)%nat -> skipn j l = nth j l 0%Z :: skipn (S j) l.
Proof.
  intros l. induction l as [|x l IH]; intros j Hj; [cbn in Hj; lia|]. destruct j as [|j]; [reflexivity|].
  cbn [skipn nth]. cbn in Hj. apply IH. lia.
Qed.

Definition mixl (j : nat) (F B : list Z) : list Z := firstn j F ++ skipn j B.

Lemma mixl_length : forall j F B, length F = length B -> (j <= length B)%nat -> length (mixl j F B) = length B.
Proof. intros j F B HL Hj. unfold mixl. rewrite length_app, length_firstn, length_skipn. lia. Qed.

Lemma mixl_0 : forall F B, mixl 0 F B = B. Proof. intros. reflexivity. Qed.

Lemma mixl_all : forall j F B, length F = length B -> (length B <= j)%nat -> mixl j F B = F.
Proof. intros j F B HL Hj. unfold mixl. rewrite firstn_all2, skipn_all2 by lia. apply app_nil_r. Qed.

Lemma mixl_nth : forall j F B i, length F = length B -> (j <= length B)%nat ->
  nth i (mixl j F B) 0%Z = (if (i <? j)%nat then nth i F 0%Z else nth i B 0%Z).
Proof.
  intros j F B i HL Hj. unfold mixl. destruct (Nat.ltb_spec i j) as [L|G].
  - rewrite app_nth1 by (rewrite length_firstn; lia). rewrite nth_firstn. destruct (Nat.ltb_spec i j); [reflexivity| lia].
  - rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn, Nat.min_l by lia. rewrite nth_skipn. f_equal. lia.
Qed.

Lemma mixl_nth_ge : forall j F B i, length F = length B -> (j <= i)%nat -> (j <= length B)%nat -> nth i (mixl j F B) 0%Z = nth i B 0%Z.
Proof. intros j F B i HL Hi Hj. rewrite mixl_nth by assumption. destruct (Nat.ltb_spec i j); [lia| reflexivity]. Qed.

Lemma updw_app_mid : forall {X} (l1 : list X) x l2 v, Arr.upd (l1 ++ x :: l2) (length l1) v = l1 ++ v :: l2.
Proof. induction l1 as [|y l1 IH]; intros x l2 v; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma updw_app_mid_len : forall {X} (l1 : list X) x l2 v j, length l1 = j -> Arr.upd (l1 ++ x :: l2) j v = l1 ++ v :: l2.
Proof. intros X l1 x l2 v j <-. apply updw_app_mid. Qed.

Lemma mixl_step : forall j F B, length F = length B -> (j < length B)%nat ->
  Arr.upd (wlimbs (mixl j F B)) j (Z_to_bv 64 (nth j F 0%Z)) = wlimbs (mixl (S j) F B).
Proof.
  intros j F B HL Hj. unfold mixl. rewrite (firstn_S_nth F j) by lia. rewrite (skipn_S_cons B j) by lia.
  unfold wlimbs. rewrite !map_app. cbn [map].
  rewrite (updw_app_mid_len _ _ _ _ j) by (rewrite length_map, length_firstn; lia). rewrite <- app_assoc. reflexivity.
Qed.

Definition clear_top (B : list Z) (rtop mx : nat) : list Z := splice B rtop (repeat 0%Z (mx - rtop)).

Lemma clear_top_length : forall B rtop mx, (mx <= length B)%nat -> length (clear_top B rtop mx) = length B.
Proof.
  intros B rtop mx H. unfold clear_top, splice. rewrite !length_app, length_firstn, repeat_length, length_skipn. lia.
Qed.

Lemma clear_top_limbs : forall B rtop mx, limbs B -> limbs (clear_top B rtop mx).
Proof. intros. unfold clear_top. apply splice_limbs; [assumption|]. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst x. unfold limb, BW. lia. Qed.

Lemma clear_top_nth : forall B rtop mx i, (mx <= length B)%nat -> (i < mx)%nat ->
  nth i (clear_top B rtop mx) 0%Z = (if (i <? rtop)%nat then nth i B 0%Z else 0%Z).
Proof.
  intros B rtop mx i Hmx Hi. unfold clear_top.
  destruct (Nat.ltb_spec i rtop) as [L|G].
  - unfold splice. rewrite app_nth1 by (rewrite length_firstn; lia). rewrite nth_firstn. destruct (Nat.ltb_spec i rtop); [reflexivity| lia].
  - replace i with (rtop + (i - rtop))%nat at 1 by lia. rewrite nth_splice_same by (rewrite ?repeat_length; lia).
    rewrite nth_repeat. reflexivity.
Qed.

Lemma clear_top_above : forall B rtop mx, (mx <= length B)%nat -> (rtop <= length B)%nat -> mixl mx (clear_top B rtop mx) B = clear_top B rtop mx.
Proof.
  intros B rtop mx Hmx Hrt. pose proof (clear_top_length B rtop mx Hmx) as HL.
  apply (nth_ext _ _ 0%Z 0%Z); [rewrite mixl_length; lia|]. intros i Hi. rewrite mixl_length in Hi by lia.
  rewrite mixl_nth by lia. destruct (Nat.ltb_spec i mx) as [L|G]; [reflexivity|].
  unfold clear_top. symmetry. apply nth_splice_other; rewrite repeat_length; lia.
Qed.

Lemma select_words_length : forall mk a r, length (select_words mk a r) = Nat.min (length a) (length r).
Proof. intros mk a. induction a as [|x a IH]; intros [|y r]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma select_words_nth : forall mk a r j, (j < length a)%nat -> (j < length r)%nat ->
  nth j (select_words mk a r) 0%Z = Z.lor (Z.land mk (nth j a 0%Z)) (Z.land (BW - 1 - mk) (nth j r 0%Z)).
Proof.
  intros mk a. induction a as [|x a IH]; intros [|y r] j Ha Hr; cbn in Ha, Hr; try lia.
  destruct j as [|j]; [reflexivity|]. cbn [select_words nth]. apply IH; lia.
Qed.

Lemma land_le_r : forall a b, (0 <= b)%Z -> (Z.land a b <= b)%Z.
Proof.
  intros a b Hb. rewrite Z.land_comm. pose proof (Z.sub_land_same_l b a) as H.
  assert (0 <= Z.land b (Z.lnot a))%Z by (apply Z.land_nonneg; left; lia). lia.
Qed.

Lemma lor_lt_pow2 : forall a b n, (0 <= a < 2^n)%Z -> (0 <= b < 2^n)%Z -> (0 <= Z.lor a b < 2^n)%Z.
Proof.
  intros a b n Ha Hb. assert (Hn : (0 <= n \/ n < 0)%Z) by lia. destruct Hn as [Hn|Hn]; [| rewrite Z.pow_neg_r in Ha by lia; lia].
  split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec a 0) as [->|Na]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|Nb]; [rewrite Z.lor_0_r; lia|].
  apply Z.log2_lt_cancel. rewrite Z.log2_lor by lia. rewrite Z.log2_pow2 by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma sel_limb : forall mk x y, (0 <= mk < 18446744073709551616)%Z -> (0 <= x < 18446744073709551616)%Z -> (0 <= y < 18446744073709551616)%Z ->
  (0 <= Z.lor (Z.land mk x) (Z.land (18446744073709551616 - 1 - mk) y) < 18446744073709551616)%Z.
Proof.
  intros mk x y Hm Hx Hy. change 18446744073709551616%Z with (2^64)%Z in *.
  apply lor_lt_pow2; (split; [apply Z.land_nonneg; lia|]); eapply Z.le_lt_trans; [apply land_le_r; lia| lia| apply land_le_r; lia| lia].
Qed.

Lemma select_words_limbs : forall mk a r, (0 <= mk < BW)%Z -> limbs a -> limbs r -> limbs (select_words mk a r).
Proof.
  intros mk a. induction a as [|x a IH]; intros [|y r] Hm Ha Hr; cbn [select_words]; try constructor.
  - apply limbs_cons_lit in Ha. apply limbs_cons_lit in Hr. unfold limb, BW in *. apply sel_limb; tauto.
  - apply limbs_cons_lit in Ha. apply limbs_cons_lit in Hr. apply IH; tauto.
Qed.

Lemma sra31_mask : forall z x, (-2147483648 <= z < 2147483648)%Z -> (0 <= x < 18446744073709551616)%Z ->
  Z.land ((bv_swrap 32 (Z.shiftr (bv_swrap 32 (z mod 18446744073709551616)) 31)) mod 18446744073709551616) x = (if z <? 0 then x else 0)%Z.
Proof.
  intros z x Hz Hx.
  assert (E1 : bv_swrap 32 (z mod 18446744073709551616) = z).
  { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 `div` 2)%Z with 2147483648%Z.
    Z.div_mod_to_equations. lia. }
  rewrite E1. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 31)%Z with 2147483648%Z.
  destruct (Z.ltb_spec z 0) as [L|G].
  - replace (z / 2147483648)%Z with (-1)%Z by (Z.div_mod_to_equations; lia).
    rewrite bn_swrap32_small by lia. change ((-1) mod 18446744073709551616)%Z with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
  - replace (z / 2147483648)%Z with 0%Z by (Z.div_mod_to_equations; lia).
    rewrite bn_swrap32_small by lia. reflexivity.
Qed.

Section CarryZ.
Open Scope Z_scope.

Lemma mont_carry_eq : forall v C old, (0 <= v < 18446744073709551616)%Z -> (0 <= C <= 1)%Z -> (0 <= old < 18446744073709551616)%Z ->
  Z.land (Z.lxor (Z.b2z (old <? (v + C + old) mod 18446744073709551616)%Z) 1%Z) (Z.lor (Z.b2z (0 <? (v + C) mod 18446744073709551616)%Z) C)
  = (let vn := addw (addw v C) old in if vn <? old then 1 else if vn =? old then C else 0)%Z.
Proof.
  intros v C old Hv HC Ho. unfold addw, BW. cbn zeta.
  set (t := (v + C) mod 18446744073709551616).
  assert (Ht : 0 <= t < 18446744073709551616) by (subst t; apply Z.mod_pos_bound; lia).
  assert (Et : (v + C + old) mod 18446744073709551616 = (t + old) mod 18446744073709551616).
  { subst t. rewrite Zplus_mod_idemp_l. reflexivity. }
  rewrite Et.
  assert (HC01 : C = 0 \/ C = 1) by lia.
  destruct (Z.eq_dec t 0) as [T0|T1].
  - rewrite T0. cbn [Z.ltb Z.b2z]. rewrite Z.add_0_l, Z.mod_small by lia.
    replace (old <? old) with false by (symmetry; apply Z.ltb_irrefl). rewrite Z.eqb_refl. cbn [Z.b2z Z.lxor].
    destruct HC01 as [-> | ->]; reflexivity.
  - assert (E1 : Z.b2z (0 <? t) = 1) by (destruct (Z.ltb_spec 0 t); [reflexivity| lia]). rewrite E1.
    assert (EL : Z.lor 1 C = 1) by (destruct HC01 as [-> | ->]; reflexivity). rewrite EL.
    destruct (Z_lt_dec (t + old) 18446744073709551616) as [L|G].
    + rewrite (Z.mod_small (t + old)) by lia.
      destruct (Z.ltb_spec old (t + old)); [| lia]. destruct (Z.ltb_spec (t + old) old); [lia|]. destruct (Z.eqb_spec (t + old) old); [lia|]. reflexivity.
    + replace ((t + old) mod 18446744073709551616) with (t + old - 18446744073709551616) by (Z.div_mod_to_equations; lia).
      destruct (Z.ltb_spec old (t + old - 18446744073709551616)); [lia|]. destruct (Z.ltb_spec (t + old - 18446744073709551616) old); [| lia]. reflexivity.
Qed.

End CarryZ.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 1048592 => 1
  | 1048648 => 1
  | 1048652 => 2
  | 1048656 => 1
  | 1048660 => 1
  | 1048664 => 1
  | 1048668 => 2
  | 1048680 => 1
  | 1048684 => 1
  | 1048688 => 2
  | 1048692 => 1
  | 1048696 => 1
  | 1048700 => 1
  | 1048704 => 1
  | 1048716 => 1
  | 1048720 => 2
  | 1048744 => 1
  | 1048752 => 1
  | 1048764 => 1
  | 1048768 => 1
  | 1048772 => 1
  | 1048776 => 1
  | 1048780 => 1
  | 1048784 => 1
  | 1048788 => 1
  | 1048792 => 2
  | 1048796 => 1
  | 1048800 => 1
  | 1048804 => 2
  | 1048808 => 2
  | 1048816 => 1
  | 1048820 => 1
  | 1048824 => 1
  | 1048828 => 1
  | 1048832 => 1
  | 1048840 => 1
  | 1048852 => 1
  | 1048864 => 1
  | 1048868 => 1
  | 1048872 => 1
  | 1048876 => 1
  | 1048880 => 2
  | 1048884 => 2
  | 1048892 => 1
  | 1048896 => 1
  | 1048904 => 1
  | 1048912 => 2
  | 1048916 => 1
  | 1048924 => 1
  | 1048928 => 1
  | 1048936 => 2
  | 1048940 => 1
  | 1048944 => 1
  | 1048948 => 1
  | 1048952 => 1
  | 1048956 => 1
  | 1048960 => 1
  | 1048964 => 1
  | 1048968 => 1
  | 1048976 => 1
  | 1048980 => 1
  | 1048992 => 2
  | 1048996 => 1
  | 1049000 => 2
  | 1049020 => 2
  | 1049024 => 1
  | 1049028 => 1
  | 1049032 => 2
  | 1049036 => 1
  | 1049040 => 1
  | 1049044 => 1
  | 1049048 => 1
  | 1049052 => 2
  | 1049060 => 1
  | 1049064 => 1
  | 1049072 => 1
  | 1049080 => 1
  | 1049084 => 1
  | 1049092 => 1
  | 1049096 => 1
  | 1049100 => 1
  | 1049104 => 1
  | 1049108 => 1
  | 1049112 => 1
  | 1049116 => 1
  | 1049120 => 1
  | 1049124 => 1
  | 1049128 => 2
  | 1049132 => 2
  | 1049136 => 1
  | 1049140 => 2
  | 1049144 => 1
  | 1049148 => 1
  | 1049152 => 2
  | 1049156 => 2
  | 1049160 => 1
  | 1049172 => 1
  | 1049176 => 1
  | 1049180 => 1
  | 1049184 => 1
  | 1049204 => 2
  | 1049208 => 1
  | 1049212 => 2
  | 1049220 => 1
  | 1049276 => 1
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).

Section WithRegs.

  Variables (sp gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Notation SP := (bv_unsigned sp).

  Section ClearLoop.
    Variables (ra t0 t1 t2 s1 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
              (m : word -> option byte) (lo RP : Z) (B : list Z) (rtop mx : nat).
    Hypothesis LB : limbs B.
    Hypothesis MX : (1 <= mx <= length B)%nat.
    Hypothesis MX31 : (Z.of_nat mx < 2^31)%Z.
    Hypothesis RT31 : (Z.of_nat rtop < 2^31)%Z.
    Hypothesis RTB : (rtop <= length B)%nat.
    Hypothesis UBR : ub_ptr_ok (Z.of_nat mx) RP.

    Definition cl_post : machine_state -> Prop :=
      fun ms' => exists x12 x13 x16 x17 m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) (Z_to_bv 64 1) x12 x13 (Z_to_bv 64 (RP + 8 * Z.of_nat mx)) (Z_to_bv 64 (RP + 8 * Z.of_nat mx)) x16 x17
                      s2 s3 s4 (Z_to_bv 64 RP) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x100110) fc None m' (seg_rom bgusegs)
        /\ munch [(RP, RP + 8 * Z.of_nat mx)]%Z m m' /\ wmono bgusegs m m' /\ mem_inv bgusegs m'
        /\ u64arr bgusegs m' RP (wlimbs (clear_top B rtop mx)) /\ stk bgusegs m' lo SP.

    Definition CINV (m1 : word -> option byte) (j : nat) : Prop :=
      u64arr bgusegs m1 RP (wlimbs (mixl j (clear_top B rtop mx) B)) /\ mem_inv bgusegs m1
      /\ munch [(RP, RP + 8 * Z.of_nat mx)]%Z m m1 /\ wmono bgusegs m m1 /\ stk bgusegs m1 lo SP.

    Lemma CINV_init : u64arr bgusegs m RP (wlimbs B) -> mem_inv bgusegs m -> stk bgusegs m lo SP -> CINV m 0.
    Proof. intros U MI ST. split; [rewrite mixl_0; exact U|]. split; [exact MI|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact ST]. Qed.

    Lemma clear_loop : forall K j m1 (x16 x17 : word),
      (mx - j = K)%nat -> (j < mx)%nat -> CINV m1 j ->
      evt bgusegs cl_post
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 (Z.of_nat j - Z.of_nat rtop)) (Z_to_bv 64 (Z.of_nat mx - Z.of_nat j))
                 (Z_to_bv 64 (RP + 8 * Z.of_nat j)) (Z_to_bv 64 (RP + 8 * Z.of_nat j)) x16 x17
                 s2 s3 s4 (Z_to_bv 64 RP) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1000d8) fc None m1 (seg_rom bgusegs)).
    Proof.
      intros K. induction K as [|K IH]; intros j m1 x16 x17 HK Hj (U & MI & MU & WM & ST); [lia|].
      pose proof (u64arr_bound _ _ _ _ U) as BU. rewrite wlimbs_len, mixl_length in BU by (try apply clear_top_length; lia).
      pose proof (wr_at_below bgusegs m1 RP _ MI (proj2 U) ltac:(rewrite wlimbs_len, mixl_length by (try apply clear_top_length; lia); lia)) as TOPB.
      rewrite wlimbs_len, mixl_length in TOPB by (try apply clear_top_length; lia). unfold UTOP in TOPB.
      destruct (UBR ltac:(lia)) as [RP0 RP8].
      assert (NTH : nth_error (wlimbs (mixl j (clear_top B rtop mx) B)) (Z.to_nat (Z.of_nat j)) = Some (Z_to_bv 64 (nth j B 0%Z))).
      { rewrite Nat2Z.id. unfold wlimbs. erewrite map_nth_error; [reflexivity|]. rewrite (nth_error_nth' _ 0%Z) by (rewrite mixl_length by (try apply clear_top_length; lia); lia).
        f_equal. apply mixl_nth_ge; [apply clear_top_length; lia| lia| lia]. }
      assert (Rx : (0 <= nth j B 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact LB).
      ub.
      (let ad := cur_mem_addr in
       pose proof (u64arr_read bgusegs m1 RP _ (Z.of_nat j) _ ad U NTH ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD); zstep; clear RD.
      ub.
      rewrite (sra31_mask (Z.of_nat j - Z.of_nat rtop) (nth j B 0%Z)) by lia.
      set (v := (if (Z.of_nat j - Z.of_nat rtop <? 0) then nth j B 0 else 0)%Z).
      assert (Ev : v = nth j (clear_top B rtop mx) 0%Z).
      { subst v. rewrite clear_top_nth by lia. destruct (Z.ltb_spec (Z.of_nat j - Z.of_nat rtop) 0); destruct (Nat.ltb_spec j rtop); try reflexivity; lia. }
      assert (IDX : (0 <= Z.of_nat j < Z.of_nat (length (wlimbs (mixl j (clear_top B rtop mx) B))))%Z) by (rewrite wlimbs_len, mixl_length by (try apply clear_top_length; lia); lia).
      pose proof (u64arr_store_ok bgusegs m1 RP _ (Z.of_nat j) (wa (RP + 8 * Z.of_nat j)) U IDX eq_refl) as SOKW.
      pose proof (u64arr_write bgusegs m1 RP _ (Z.of_nat j) (Z_to_bv 64 v) U IDX) as U2. clear U.
      zstep. store_done.
      rewrite Nat2Z.id, Ev, mixl_step in U2 by (try apply clear_top_length; lia).
      clear NTH IDX Ev Rx. subst v.
      zstep.
      replace (RP + 8 * Z.of_nat j + 8)%Z with (RP + 8 * Z.of_nat (S j))%Z by lia.
      replace (Z.of_nat j - Z.of_nat rtop + 1)%Z with (Z.of_nat (S j) - Z.of_nat rtop)%Z by lia.
      replace (Z.of_nat mx - Z.of_nat j + -1)%Z with (Z.of_nat mx - Z.of_nat (S j))%Z by lia.
      zstep. if_cases KB; zify_cond KB; rewrite ?unsigned_lit, ?Z.mod_small in KB by lia.
      -
        eapply (IH (S j)); [lia| lia|]. split; [exact U2|]. split; [exact MI|]. split; [exact MU|]. split; [exact WM| exact ST].
      -
        assert (EJ : S j = mx) by lia. rewrite EJ. apply evt_done.
        unfold cl_post. do 5 eexists. split; [reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [| exact ST].
        rewrite EJ, clear_top_above in U2 by lia. exact U2.
    Qed.

    Lemma clear_loop_walk : forall (x16 x17 : word),
      u64arr bgusegs m RP (wlimbs B) -> mem_inv bgusegs m -> stk bgusegs m lo SP ->
      evt bgusegs cl_post
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 (0 - Z.of_nat rtop)) (Z_to_bv 64 (Z.of_nat mx)) (Z_to_bv 64 RP) (Z_to_bv 64 RP) x16 x17
                 s2 s3 s4 (Z_to_bv 64 RP) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1000d8) fc None m (seg_rom bgusegs)).
    Proof.
      intros x16 x17 U MI ST.
      pose proof (clear_loop (mx - 0)%nat 0%nat m x16 x17 ltac:(lia) ltac:(lia) (CINV_init U MI ST)) as H.
      replace (RP + 8 * Z.of_nat 0)%Z with RP in H by lia. replace (Z.of_nat mx - Z.of_nat 0)%Z with (Z.of_nat mx) in H by lia.
      exact H.
    Qed.
  End ClearLoop.

  Section SelectLoop.
    Variables (ra s2 s4 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
              (m : word -> option byte) (lo RPr AP mk : Z) (R P : list Z) (nl : nat).
    Hypothesis LR : limbs R.
    Hypothesis LP : limbs P.
    Hypothesis NL : (1 <= nl)%nat.
    Hypothesis LENP : length P = nl.
    Hypothesis LENR : (nl <= length R)%nat.
    Hypothesis MK : (0 <= mk < 18446744073709551616)%Z.
    Hypothesis DJ : (AP + 8 * Z.of_nat nl <= RPr \/ RPr + 8 * Z.of_nat (length R) <= AP)%Z.
    Hypothesis UBR : ub_ptr_ok (Z.of_nat nl) RPr.

    Definition sel_res : list Z := select_words mk P (firstn nl R) ++ skipn nl R.

    Lemma sel_res_length : length sel_res = length R.
    Proof. unfold sel_res. rewrite length_app, select_words_length, length_firstn, length_skipn, LENP. lia. Qed.

    Lemma sel_res_nth : forall j, (j < nl)%nat ->
      nth j sel_res 0%Z = Z.lor (Z.land mk (nth j P 0%Z)) (Z.land (18446744073709551616 - 1 - mk) (nth j R 0%Z)).
    Proof.
      intros j Hj. unfold sel_res. rewrite app_nth1 by (rewrite select_words_length, length_firstn, LENP; lia).
      rewrite select_words_nth by (rewrite ?length_firstn, ?LENP; lia). rewrite nth_firstn. unfold BW.
      destruct (Nat.ltb_spec j nl); [reflexivity| lia].
    Qed.

    Lemma sel_res_mixl : mixl nl sel_res R = sel_res.
    Proof.
      unfold mixl, sel_res. rewrite firstn_app, select_words_length, length_firstn, LENP.
      replace (Nat.min nl (Nat.min nl (length R))) with nl by lia. rewrite Nat.sub_diag, firstn_O, app_nil_r.
      rewrite firstn_all2 by (rewrite select_words_length, length_firstn, LENP; lia). reflexivity.
    Qed.

    Definition sl_post : machine_state -> Prop :=
      fun ms' => exists x5 x6 x7 x12 x28 m',
        ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 (Z_to_bv 64 RPr) (Z_to_bv 64 1) (Z_to_bv 64 mk) x12 (Z_to_bv 64 (18446744073709551616 - 1 - AP))
                      (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 (18446744073709551616 - 1 - mk)) (Z_to_bv 64 1)
                      s2 (Z_to_bv 64 AP) s4 (Z_to_bv 64 (8 * Z.of_nat nl)) s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
                 F (Z_to_bv 64 0x100270) fc None m' (seg_rom bgusegs)
        /\ munch [(RPr, RPr + 8 * Z.of_nat nl); (AP, AP + 8 * Z.of_nat nl)]%Z m m' /\ wmono bgusegs m m' /\ mem_inv bgusegs m'
        /\ u64arr bgusegs m' RPr (wlimbs sel_res) /\ u64arr bgusegs m' AP (wlimbs (repeat 0%Z nl)) /\ stk bgusegs m' lo SP.

    Definition SLINV (m1 : word -> option byte) (j : nat) : Prop :=
      u64arr bgusegs m1 RPr (wlimbs (mixl j sel_res R)) /\ u64arr bgusegs m1 AP (wlimbs (mixl j (repeat 0%Z nl) P)) /\ mem_inv bgusegs m1
      /\ munch [(RPr, RPr + 8 * Z.of_nat nl); (AP, AP + 8 * Z.of_nat nl)]%Z m m1 /\ wmono bgusegs m m1 /\ stk bgusegs m1 lo SP.

    Lemma select_loop : forall K j m1 (x5 x6 x7 x28 : word),
      (nl - j = K)%nat -> (j < nl)%nat -> SLINV m1 j ->
      evt bgusegs sl_post
        (MS (mkR ra sp gp tp x5 x6 x7 s0 (Z_to_bv 64 RPr) (Z_to_bv 64 1) (Z_to_bv 64 mk) (Z_to_bv 64 (8 * Z.of_nat j)) (Z_to_bv 64 (18446744073709551616 - 1 - AP))
                 (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 (18446744073709551616 - 1 - mk)) (Z_to_bv 64 1)
                 s2 (Z_to_bv 64 AP) s4 (Z_to_bv 64 (8 * Z.of_nat nl)) s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
            F (Z_to_bv 64 0x100228) fc None m1 (seg_rom bgusegs)).
    Proof.
      intros K. induction K as [|K IH]; intros j m1 x5 x6 x7 x28 HK Hj (UR & UP & MI & MU & WM & ST); [lia|].
      pose proof sel_res_length as LS.
      pose proof (u64arr_bound _ _ _ _ UR) as BR. rewrite wlimbs_len, mixl_length in BR by lia.
      pose proof (u64arr_bound _ _ _ _ UP) as BP. rewrite wlimbs_len, mixl_length in BP by (rewrite ?repeat_length; lia).
      pose proof (wr_at_below bgusegs m1 RPr _ MI (proj2 UR) ltac:(rewrite wlimbs_len, mixl_length by lia; lia)) as TOPR.
      rewrite wlimbs_len, mixl_length in TOPR by lia. unfold UTOP in TOPR.
      pose proof (wr_at_below bgusegs m1 AP _ MI (proj2 UP) ltac:(rewrite wlimbs_len, mixl_length by (rewrite ?repeat_length; lia); lia)) as TOPA.
      rewrite wlimbs_len, mixl_length in TOPA by (rewrite ?repeat_length; lia). unfold UTOP in TOPA.
      destruct (UBR ltac:(lia)) as [RP0 RP8].
      assert (Rx : (0 <= nth j P 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact LP).
      assert (Ry : (0 <= nth j R 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact LR).
      assert (NTHP : nth_error (wlimbs (mixl j (repeat 0%Z nl) P)) (Z.to_nat (Z.of_nat j)) = Some (Z_to_bv 64 (nth j P 0%Z))).
      { rewrite Nat2Z.id. unfold wlimbs. erewrite map_nth_error; [reflexivity|]. rewrite (nth_error_nth' _ 0%Z) by (rewrite mixl_length by (rewrite ?repeat_length; lia); lia).
        f_equal. apply mixl_nth_ge; [rewrite repeat_length; lia| lia| lia]. }
      assert (NTHR : nth_error (wlimbs (mixl j sel_res R)) (Z.to_nat (Z.of_nat j)) = Some (Z_to_bv 64 (nth j R 0%Z))).
      { rewrite Nat2Z.id. unfold wlimbs. erewrite map_nth_error; [reflexivity|]. rewrite (nth_error_nth' _ 0%Z) by (rewrite mixl_length by lia; lia).
        f_equal. apply mixl_nth_ge; lia. }
      ub.
      (let ad := cur_mem_addr in
       pose proof (u64arr_read bgusegs m1 RPr _ (Z.of_nat j) _ ad UR NTHR ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD); zstep; clear RD.
      (let ad := cur_mem_addr in
       pose proof (u64arr_read bgusegs m1 AP _ (Z.of_nat j) _ ad UP NTHP ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD); zstep; clear RD.
      ub.
      set (v := Z.lor (Z.land (nth j R 0%Z) (18446744073709551615 - mk)) (Z.land (nth j P 0%Z) mk)).
      assert (Ev : v = nth j sel_res 0%Z).
      { subst v. rewrite sel_res_nth by lia. rewrite Z.lor_comm. rewrite (Z.land_comm (nth j P 0%Z) mk), (Z.land_comm (nth j R 0%Z)).
        replace (18446744073709551616 - 1 - mk)%Z with (18446744073709551615 - mk)%Z by lia. reflexivity. }
      assert (IDXR : (0 <= Z.of_nat j < Z.of_nat (length (wlimbs (mixl j sel_res R))))%Z) by (rewrite wlimbs_len, mixl_length by lia; lia).
      pose proof (u64arr_store_ok bgusegs m1 RPr _ (Z.of_nat j) (wa (RPr + 8 * Z.of_nat j)) UR IDXR eq_refl) as SOKW.
      pose proof (u64arr_write bgusegs m1 RPr _ (Z.of_nat j) (Z_to_bv 64 v) UR IDXR) as UR2.
      pose proof (u64arr_frame bgusegs m1 AP _ (RPr + 8 * Z.of_nat j) (le8 (Z_to_bv 64 v)) UP ltac:(lia) ltac:(rewrite length_le8; lia)
                    ltac:(rewrite length_le8, wlimbs_len, mixl_length by (rewrite ?repeat_length; lia); lia)) as UP2.
      clear UR UP.
      zstep. store_done.
      rewrite Nat2Z.id, Ev, mixl_step in UR2 by lia.

      assert (IDXP : (0 <= Z.of_nat j < Z.of_nat (length (wlimbs (mixl j (repeat 0%Z nl) P))))%Z) by (rewrite wlimbs_len, mixl_length by (rewrite ?repeat_length; lia); lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (u64arr_store_ok bgusegs mx AP _ (Z.of_nat j) (wa (AP + 8 * Z.of_nat j)) UP2 IDXP eq_refl) as SOKW2;
        pose proof (u64arr_write bgusegs mx AP _ (Z.of_nat j) (Z_to_bv 64 0) UP2 IDXP) as UP3;
        pose proof (u64arr_frame bgusegs mx RPr _ (AP + 8 * Z.of_nat j) (le8 (Z_to_bv 64 0)) UR2 ltac:(lia) ltac:(rewrite length_le8; lia)
                      ltac:(rewrite length_le8, wlimbs_len, mixl_length by lia; lia)) as UR3 end.
      clear UR2 UP2.
      zstep. change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). store_done.
      rewrite Nat2Z.id in UP3. replace (Z_to_bv 64 0) with (Z_to_bv 64 (nth j (repeat 0%Z nl) 0%Z)) in UP3 by (rewrite nth_repeat; reflexivity).
      rewrite mixl_step in UP3 by (rewrite ?repeat_length; lia).
      clear NTHP NTHR IDXR IDXP Ev Rx Ry. subst v.
      replace (8 * Z.of_nat j + 8)%Z with (8 * Z.of_nat (S j))%Z by lia.
      zstep. if_cases KB; zify_cond KB; rewrite ?unsigned_lit, ?Z.mod_small in KB by lia.
      - eapply (IH (S j)); [lia| lia|]. split; [exact UR3|]. split; [exact UP3|]. split; [exact MI|]. split; [exact MU|]. split; [exact WM| exact ST].
      - assert (EJ : S j = nl) by lia. apply evt_done.
        unfold sl_post. do 6 eexists. split; [reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
        rewrite EJ, sel_res_mixl in UR3. rewrite EJ, mixl_all in UP3 by (rewrite ?repeat_length; lia).
        split; [exact UR3|]. split; [exact UP3| exact ST].
    Qed.

    Lemma select_loop_walk : forall (x5 x6 x7 x28 : word),
      u64arr bgusegs m RPr (wlimbs R) -> u64arr bgusegs m AP (wlimbs P) -> mem_inv bgusegs m -> stk bgusegs m lo SP ->
      evt bgusegs sl_post
        (MS (mkR ra sp gp tp x5 x6 x7 s0 (Z_to_bv 64 RPr) (Z_to_bv 64 1) (Z_to_bv 64 mk) (Z_to_bv 64 0) (Z_to_bv 64 (18446744073709551616 - 1 - AP))
                 (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 (18446744073709551616 - 1 - mk)) (Z_to_bv 64 1)
                 s2 (Z_to_bv 64 AP) s4 (Z_to_bv 64 (8 * Z.of_nat nl)) s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
            F (Z_to_bv 64 0x100228) fc None m (seg_rom bgusegs)).
    Proof.
      intros x5 x6 x7 x28 UR UP MI ST.
      apply (select_loop (nl - 0)%nat 0%nat m x5 x6 x7 x28); [lia| lia|].
      split; [rewrite mixl_0; exact UR|]. split; [rewrite mixl_0; exact UP|]. split; [exact MI|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact ST].
    Qed.
  End SelectLoop.

  Section ReduceLoop.
    Variables (s1 s3 : word) (m : word -> option byte) (lo RP NP n0 : Z) (np : list Z) (nl LB : nat).
    Notation W := [(RP, RP + 8 * (2 * Z.of_nat nl)); (bv_unsigned sp - 112, bv_unsigned sp)]%Z.
    Hypothesis LNP : limbs np.
    Hypothesis LENNP : length np = nl.
    Hypothesis NL : (1 <= nl)%nat.
    Hypothesis NL30 : (Z.of_nat nl < 2^30)%Z.
    Hypothesis LB2 : (2 * nl <= LB)%nat.
    Hypothesis N0 : (0 <= n0 < 18446744073709551616)%Z.
    Hypothesis DJ : (NP + 8 * Z.of_nat nl <= RP \/ RP + 8 * Z.of_nat LB <= NP)%Z.
    Hypothesis LO : (lo <= SP - 112)%Z.
    Hypothesis SEPR : (RP + 8 * Z.of_nat LB <= SP - 112 \/ SP + 8 <= RP)%Z.
    Hypothesis SEPN : (NP + 8 * Z.of_nat nl <= SP - 112 \/ SP <= NP)%Z.
    Hypothesis UBR : ub_ptr_ok (Z.of_nat nl) RP.
    Hypothesis UBN : ub_ptr_ok (Z.of_nat nl) NP.
    Hypothesis S0 : bv_unsigned s0 = (SP + 112)%Z.
    Hypothesis SLOT : limbs_at bgusegs m SP [NP].

    Definition RB (m1 : word -> option byte) (B : list Z) : Prop :=
      limbs B /\ length B = LB /\ limbs_at bgusegs m1 RP B /\ limbs_at bgusegs m1 NP np /\ wr_at bgusegs m1 RP (8 * Z.of_nat LB)
      /\ stk bgusegs m1 lo SP /\ mem_inv bgusegs m1 /\ munch W m m1 /\ wmono bgusegs m m1.

    Lemma RB_init : forall B, limbs B -> length B = LB -> u64arr bgusegs m RP (wlimbs B) -> limbs_at bgusegs m NP np ->
      stk bgusegs m lo SP -> mem_inv bgusegs m -> RB m B.
    Proof.
      intros B L1 L2 U HN ST MI. apply limbarr_limbs_at in U. destruct U as [HB WB]. rewrite L2 in WB.
      split; [exact L1|]. split; [exact L2|]. split; [exact HB|]. split; [exact HN|]. split; [exact WB|]. split; [exact ST|]. split; [exact MI|].
      split; [apply munch_refl| apply wmono_refl].
    Qed.

    Lemma rb_upd : forall m1 B k v ad,
      RB m1 B -> (k < 2 * nl)%nat -> (0 <= v < 18446744073709551616)%Z -> ad = (RP + 8 * Z.of_nat k)%Z ->
      store_ok bgusegs m1 (Z_to_bv 64 ad) 8 = true /\
      RB (write_to_mem m1 (Z_to_bv 64 ad) (le8 (Z_to_bv 64 v))) (upd B k v).
    Proof using LENNP NL LB2 DJ SEPR SEPN.
      intros m1 B k v ad (LBl & LenB & HR & HN & WR & ST & MI & MU & WM) Hk Hv ->.
      pose proof (limbs_at_bound _ _ _ _ HN) as BN. rewrite LENNP in BN.
      destruct WR as (W0 & W1 & WR'). pose proof (conj W0 (conj W1 WR')) as WR.
      change (2 ^ 64)%Z with 18446744073709551616%Z in *.
      assert (L8 : length (le8 (Z_to_bv 64 v)) = 8%nat) by apply length_le8.
      assert (SOK : store_ok bgusegs m1 (Z_to_bv 64 (RP + 8 * Z.of_nat k)) 8 = true).
      { change (Z_to_bv 64 (RP + 8 * Z.of_nat k)) with (wa (RP + 8 * Z.of_nat k)). apply (wr_at_store_ok bgusegs m1 RP (8 * Z.of_nat LB)); [exact WR | lia | lia]. }
      split; [exact SOK|].
      change (Z_to_bv 64 (RP + 8 * Z.of_nat k)) with (wa (RP + 8 * Z.of_nat k)).
      pose proof (zr_word sp) as RSP. unfold inr64 in RSP. change (2 ^ 64)%Z with 18446744073709551616%Z in RSP.
      assert (ER : B = firstn k B ++ [nth k B 0%Z] ++ skipn (S k) B).
      { rewrite app_assoc, <- firstn_S_nth by lia. symmetry. apply firstn_skipn. }
      assert (EU : upd B k v = firstn k B ++ [v] ++ skipn (S k) B).
      { unfold upd, splice. cbn [length app]. rewrite Nat.add_1_r. reflexivity. }
      unfold RB.
      split. { apply upd_limbs; [exact LBl | unfold limb, BW; exact Hv]. }
      split. { rewrite upd_length by lia. exact LenB. }
      split.
      { rewrite EU. rewrite ER in HR. apply limbs_at_app in HR. destruct HR as [H1 H23]. apply limbs_at_app in H23. destruct H23 as [H2 H3].
        rewrite length_firstn in H2, H3. cbn [length] in H3. replace (Nat.min k (length B)) with k in H2, H3 by lia.
        rewrite app_assoc. apply limbs_at_app. split.
        - replace (RP + 8 * Z.of_nat k)%Z with (RP + 8 * Z.of_nat (length (firstn k B)))%Z by (rewrite length_firstn; f_equal; lia).
          apply limbs_at_snoc_write; [exact H1 | rewrite length_firstn; lia].
        - rewrite length_app, length_firstn. cbn [length]. replace (Nat.min k (length B) + 1)%nat with (S k) by lia.
          replace (RP + 8 * Z.of_nat k + 8 * Z.of_nat 1)%Z with (RP + 8 * Z.of_nat (S k))%Z in H3 by lia.
          apply limbs_at_write_other; [exact H3 | lia | rewrite L8; lia | rewrite L8, length_skipn; lia]. }
      split. { apply limbs_at_write_other; [exact HN | lia | rewrite L8; lia | rewrite L8, LENNP; lia]. }
      split. { apply wr_at_write. exact WR. }
      split. { apply stk_write; [exact ST | lia | rewrite L8; lia]. }
      split. { apply mem_inv_store; [exact MI | rewrite L8; exact SOK]. }
      split. { apply munch_write; [exact MU | lia | rewrite L8; lia | rewrite L8; cbn [inside]; left; lia]. }
      apply wmono_write. exact WM.
    Qed.

    Lemma rb_call : forall m1 m2 B (st : nat) seg,
      RB m1 B -> (st + length seg <= 2 * nl)%nat ->
      munch [(RP + 8 * Z.of_nat st, RP + 8 * Z.of_nat st + 8 * Z.of_nat (length seg)); (SP - 112, SP)]%Z m1 m2 ->
      wmono bgusegs m1 m2 -> mem_inv bgusegs m2 -> limbs_at bgusegs m2 (RP + 8 * Z.of_nat st) seg -> stk bgusegs m2 lo SP ->
      limbs seg ->
      RB m2 (splice B st seg).
    Proof using LENNP NL LB2 DJ SEPR SEPN.
      intros m1 m2 B st seg (LBl & LenB & HR & HN & WR & ST & MI & MU & WM) Hst MUc WMc MIc HS STc LS.
      pose proof (limbs_at_bound _ _ _ _ HN) as BN. rewrite LENNP in BN.
      destruct WR as (W0 & W1 & WR'). pose proof (conj W0 (conj W1 WR')) as WR.
      change (2 ^ 64)%Z with 18446744073709551616%Z in *.
      pose proof (zr_word sp) as RSP. unfold inr64 in RSP. change (2 ^ 64)%Z with 18446744073709551616%Z in RSP.
      unfold RB.
      split. { apply splice_limbs; [exact LBl | exact LS]. }
      split. { rewrite splice_length by lia. exact LenB. }
      split.
      { unfold splice. rewrite <- (firstn_skipn st B) in HR. apply limbs_at_app in HR. destruct HR as [H1 H23].
        rewrite <- (firstn_skipn (length seg) (skipn st B)) in H23. apply limbs_at_app in H23. destruct H23 as [_ H3].
        rewrite !length_firstn, length_skipn, skipn_skipn in H3.
        replace (Nat.min st (length B)) with st in H3 by lia. replace (Nat.min (length seg) (length B - st)) with (length seg) in H3 by lia.
        replace (length seg + st)%nat with (st + length seg)%nat in H3 by lia.
        apply limbs_at_app. split.
        - eapply limbs_at_transport; [exact H1 | exact MUc | cbn [disjoint_from]; rewrite length_firstn; lia].
        - rewrite length_firstn. replace (Nat.min st (length B)) with st by lia. apply limbs_at_app. split; [exact HS|].
          eapply limbs_at_transport; [exact H3 | exact MUc | cbn [disjoint_from]; rewrite length_skipn; lia]. }
      split. { eapply limbs_at_transport; [exact HN | exact MUc | cbn [disjoint_from]; rewrite LENNP; lia]. }
      split. { eapply wr_at_transport; [exact WR | exact WMc]. }
      split; [exact STc|]. split; [exact MIc|].
      split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
      eapply wmono_trans; [exact WM | exact WMc].
    Qed.

    Definition mr_post (B : list Z) (C : Z) : machine_state -> Prop :=
      fun ms' => exists ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) s3 (Z_to_bv 64 (Z.of_nat nl)) (Z_to_bv 64 (RP + 8 * Z.of_nat nl))
                      (Z_to_bv 64 n0) (Z_to_bv 64 C) (Z_to_bv 64 0) (Z_to_bv 64 (8 * Z.of_nat nl)) (Z_to_bv 64 (18446744073709551615 - (RP + 8 * Z.of_nat nl)))
                      (Z_to_bv 64 18446744073709551607) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x100190) fc None m' (seg_rom bgusegs)
        /\ munch W m m' /\ wmono bgusegs m m' /\ mem_inv bgusegs m'
        /\ limbs_at bgusegs m' RP B /\ wr_at bgusegs m' RP (8 * Z.of_nat LB) /\ limbs_at bgusegs m' NP np /\ stk bgusegs m' lo SP
        /\ limbs B /\ length B = LB /\ (0 <= C <= 1)%Z.

    Definition mr_step (i : nat) (B : list Z) (C : Z) : list Z * Z :=
      let w := mulw (nth i B 0%Z) n0 in
      let '(seg, v) := mul_add_words (slice B i nl) np w in
      let B0 := splice B i seg in
      let old := nth (i + nl) B0 0%Z in
      let vn := addw (addw v C) old in
      let Cn := (if vn <? old then 1 else if vn =? old then C else 0)%Z in
      (upd B0 (i + nl) vn, Cn).

    Lemma mr_step_eq : forall c i B C, mont_reduce_loop np n0 nl (S c) i B C = (let '(Bn, Cn) := mr_step i B C in mont_reduce_loop np n0 nl c (S i) Bn Cn).
    Proof. intros c i B C. cbn [mont_reduce_loop]. unfold mr_step. destruct (mul_add_words (slice B i nl) np (mulw (nth i B 0%Z) n0)) as [seg v]. reflexivity. Qed.

    Definition body_post (i : nat) (Bn : list Z) (Cn : Z) : machine_state -> Prop :=
      fun ms' => exists ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat nl - Z.of_nat (S i))) s3 (Z_to_bv 64 (Z.of_nat nl)) (Z_to_bv 64 (RP + 8 * Z.of_nat (S i)))
                      (Z_to_bv 64 n0) (Z_to_bv 64 Cn) (Z_to_bv 64 0) (Z_to_bv 64 (8 * Z.of_nat nl)) (Z_to_bv 64 (18446744073709551615 - (RP + 8 * Z.of_nat (S i))))
                      (Z_to_bv 64 18446744073709551607) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x10018c) fc None m2 (seg_rom bgusegs)
        /\ RB m2 Bn /\ (0 <= Cn <= 1)%Z.

    Lemma reduce_body : forall i m1 B C (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      (i < nl)%nat -> RB m1 B -> (0 <= C <= 1)%Z ->
      evt bgusegs (let '(Bn, Cn) := mr_step i B C in body_post i Bn Cn)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat nl - Z.of_nat i)) s3 (Z_to_bv 64 (Z.of_nat nl)) (Z_to_bv 64 (RP + 8 * Z.of_nat i))
                 (Z_to_bv 64 n0) (Z_to_bv 64 C) (Z_to_bv 64 0) (Z_to_bv 64 (8 * Z.of_nat nl)) (Z_to_bv 64 (18446744073709551615 - (RP + 8 * Z.of_nat i)))
                 (Z_to_bv 64 18446744073709551607) t3 t4 t5 t6)
            F (Z_to_bv 64 0x100130) fc None m1 (seg_rom bgusegs)).
    Proof.
      intros i m1 B C ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hi I HC.
      pose proof I as (LBl & LenB & HR & HN & WR & ST & MI & MU & WM).
      pose proof (limbs_at_bound _ _ _ _ HN) as BN. rewrite LENNP in BN. pose proof (limbs_at_bound _ _ _ _ HR) as BRR. rewrite LenB in BRR.
      pose proof (wr_at_below bgusegs m1 RP _ MI WR ltac:(lia)) as TOPR. unfold UTOP in TOPR.
      pose proof (zr_word sp) as RSP. unfold inr64 in RSP.
      destruct (UBR ltac:(lia)) as [RP0 RP8]. destruct (UBN ltac:(lia)) as [NP0 NP8].
      assert (SL1 : limbs_at bgusegs m1 SP [NP]).
      { eapply limbs_at_transport; [exact SLOT | exact MU | cbn [disjoint_from length]; lia]. }
      assert (NI : nth_error B i = Some (nth i B 0%Z)) by (apply nth_error_nth'; lia).
      assert (Rx : (0 <= nth i B 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact LBl).
      ub.
      (let ad := cur_mem_addr in
       pose proof (limbs_at_read_nth bgusegs _ RP B i _ ad HR NI ltac:(unfold wa; f_equal; lia)) as RD); zstep; clear RD.
      ub.
      (let ad := cur_mem_addr in
       pose proof (limbs_at_read_nth bgusegs _ SP [NP] 0 _ ad SL1 eq_refl ltac:(unfold wa; f_equal; lia)) as RD); zstep; clear RD.
      ub.
      zstep.

      set (w := mulw (nth i B 0%Z) n0).
      assert (Rw : (0 <= w < 18446744073709551616)%Z) by (subst w; unfold mulw, BW; apply Z.mod_pos_bound; lia).
      assert (Ew : bv_unsigned (Z_to_bv 64 (nth i B 0%Z * n0)) = w) by (subst w; unfold mulw, BW; rewrite Z_to_bv_unsigned; reflexivity).
      assert (Erp : bv_unsigned (Z_to_bv 64 (RP + 8 * Z.of_nat i)) = (RP + 8 * Z.of_nat i)%Z) by (apply unsigned_lit; lia).
      assert (Enp : bv_unsigned (Z_to_bv 64 NP) = NP) by (apply unsigned_lit; lia).
      assert (Enl : bv_unsigned (Z_to_bv 64 (Z.of_nat nl)) = Z.of_nat nl) by (apply unsigned_lit; lia).
      assert (LS : length (slice B i nl) = length np) by (rewrite slice_length, LENNP by lia; reflexivity).
      pose proof (mul_add_words_spec (slice B i nl) np w (slice_limbs _ _ _ LBl) LNP LS ltac:(unfold limb, BW; exact Rw)) as MSP.
      assert (HRi : limbs_at bgusegs m1 (RP + 8 * Z.of_nat i) (slice B i nl)).
      { unfold slice. rewrite <- (firstn_skipn i B) in HR. apply limbs_at_app in HR. destruct HR as [_ HR2].
        rewrite <- (firstn_skipn nl (skipn i B)) in HR2. apply limbs_at_app in HR2. destruct HR2 as [HR2 _].
        rewrite length_firstn in HR2. replace (Nat.min i (length B)) with i in HR2 by lia. exact HR2. }
      eapply evt_cut.
      { eapply bn_mul_add_words_uspec with (a := np) (r := slice B i nl) (lo := lo) (m := m1).
        - exact LNP.
        - apply slice_limbs. exact LBl.
        - exact LS.
        - rewrite LENNP. lia.
        - rewrite Enl, LENNP. reflexivity.
        - rewrite Enp. exact HN.
        - rewrite Erp. exact HRi.
        - rewrite Erp, LENNP. apply (wr_at_sub bgusegs m1 RP (8 * Z.of_nat LB) (8 * Z.of_nat i) (8 * Z.of_nat nl) WR); lia.
        - rewrite Erp, Enp, LENNP. unfold alias_ok. right. lia.
        - exact ST.
        - exact LO.
        - rewrite Erp, LENNP. lia.
        - rewrite Enp, LENNP. lia.
        - exact MI.
        - rewrite Erp, LENNP. intros _. split; [lia| Z.div_mod_to_equations; lia].
        - rewrite Enp, LENNP. exact UBN. }
      intros ms' PO. unfold maw_upost, wl_post in PO.
      destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HS & STc).
      subst ms'. rewrite Erp, Ew, LENNP in *. rewrite (ret_pc_even 0x100150) by lia.
      destruct (mul_add_words (slice B i nl) np w) as [seg v] eqn:EMA. cbn [fst snd] in *.
      destruct MSP as (Lseg & Eseg & Lv & _). unfold limb, BW in Lv. try rewrite LENNP in Eseg. try rewrite LS, LENNP in Eseg.
      assert (I2 : RB m2 (splice B i seg)).
      { eapply (rb_call m1 m2 B i seg I); [rewrite Eseg; lia| rewrite Eseg; exact MUc| exact WMc| exact MIc| exact HS| exact STc| exact Lseg]. }
      clear I HR HN WR ST MI MU WM MUc WMc MIc HS STc HRi NI SL1.
      pose proof I2 as (LB0 & LenB0 & HR0 & HN0 & WR0 & ST0 & MI0 & MU0 & WM0).

      ub.
      set (B0 := splice B i seg) in *.
      assert (LenS : length B0 = LB) by exact LenB0.
      set (old := nth (i + nl) B0 0%Z).
      assert (NI2 : nth_error B0 (i + nl) = Some old) by (subst old; apply nth_error_nth'; lia).
      assert (Ro : (0 <= old < 18446744073709551616)%Z) by (subst old; rewrite <- BW_lit; apply limbs_nth; exact LB0).
      (let ad := cur_mem_addr in
       pose proof (limbs_at_read_nth bgusegs _ RP B0 (i + nl) _ ad HR0 NI2 ltac:(unfold wa; f_equal; lia)) as RD); zstep; clear RD.
      ub.
      replace (old + (v + C))%Z with (v + C + old)%Z by lia.
      set (vn := addw (addw v C) old).
      assert (Evn : Z_to_bv 64 (v + C + old) = Z_to_bv 64 vn).
      { subst vn. unfold addw, BW. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
        rewrite Zplus_mod_idemp_l, Z.mod_mod by lia. reflexivity. }
      rewrite Evn.
      assert (Rvn : (0 <= vn < 18446744073709551616)%Z) by (subst vn; unfold addw, BW; apply Z.mod_pos_bound; lia).

      destruct (rb_upd m2 B0 (i + nl) vn (RP + 8 * Z.of_nat i + 8 * Z.of_nat nl) I2 ltac:(lia) Rvn ltac:(lia)) as [SOK I3].
      zstep. clear SOK I2 HR0 HN0 WR0 ST0 MI0 MU0 WM0.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => let m' := fresh "m" in gen_mem mx m' end.
      ub.
      set (Cn := (if vn <? old then 1 else if vn =? old then C else 0)%Z).
      assert (HCn : (0 <= Cn <= 1)%Z) by (subst Cn; destruct (vn <? old); [lia|]; destruct (vn =? old); lia).
      assert (EC : Z.land (Z.lxor (Z.b2z (old <? vn)) 1) (Z.lor (Z.b2z (0 <? (v + C) mod 18446744073709551616)) C) = Cn).
      { subst Cn. pose proof (mont_carry_eq v C old ltac:(lia) HC Ro) as E. cbn zeta in E.
        replace ((v + C + old) mod 18446744073709551616)%Z with vn in E by (subst vn; unfold addw, BW; rewrite Zplus_mod_idemp_l; reflexivity).
        exact E. }
      rewrite EC. clear EC.
      rewrite (bn_swrap32_small (Z.of_nat nl - Z.of_nat i + -1)) by lia.
      replace (Z.of_nat nl - Z.of_nat i + -1)%Z with (Z.of_nat nl - Z.of_nat (S i))%Z by lia.
      replace (18446744073709551615 - (RP + 8 * Z.of_nat i) + -8)%Z with (18446744073709551615 - (RP + 8 * Z.of_nat (S i)))%Z by lia.
      replace (RP + 8 * Z.of_nat i + 8)%Z with (RP + 8 * Z.of_nat (S i))%Z by lia.
      apply evt_done. unfold mr_step. fold w. rewrite EMA. fold B0. fold old. fold vn. fold Cn.
      unfold body_post. do 16 eexists. eexists. split; [reflexivity|]. split; [exact I3| exact HCn].
    Qed.

    Lemma reduce_loop : forall cnt i m1 B C (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      (S cnt + i = nl)%nat -> RB m1 B -> (0 <= C <= 1)%Z ->
      evt bgusegs (let '(Bn, Cn) := mont_reduce_loop np n0 nl (S cnt) i B C in mr_post Bn Cn)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat nl - Z.of_nat i)) s3 (Z_to_bv 64 (Z.of_nat nl)) (Z_to_bv 64 (RP + 8 * Z.of_nat i))
                 (Z_to_bv 64 n0) (Z_to_bv 64 C) (Z_to_bv 64 0) (Z_to_bv 64 (8 * Z.of_nat nl)) (Z_to_bv 64 (18446744073709551615 - (RP + 8 * Z.of_nat i)))
                 (Z_to_bv 64 18446744073709551607) t3 t4 t5 t6)
            F (Z_to_bv 64 0x100130) fc None m1 (seg_rom bgusegs)).
    Proof.
      intros cnt. induction cnt as [|cnt IH]; intros i m1 B C ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hi I HC;
        rewrite mr_step_eq; (eapply evt_cut; [eapply (reduce_body i m1 B C); [lia| exact I| exact HC]|]);
        destruct (mr_step i B C) as [Bn Cn]; intros ms' PO; unfold body_post in PO;
        destruct PO as (r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & r8 & r9 & r10 & r11 & r12 & r13 & r14 & r15 & m2 & -> & I2 & HCn);
        pose proof I2 as (LBl & LenB & HR & HN & WR & ST & MI & MU & WM);
        pose proof (limbs_at_bound _ _ _ _ HR) as BRR; rewrite LenB in BRR;
        pose proof (wr_at_below bgusegs m2 RP _ MI WR ltac:(lia)) as TOPR; unfold UTOP in TOPR;
        zstep; if_cases KB; zify_cond KB; rewrite ?unsigned_lit, ?Z.mod_small in KB by lia.
      - exfalso. lia.
      -
        cbn [mont_reduce_loop]. apply evt_done. unfold mr_post.
        replace (S i) with nl by lia. replace (Z.of_nat nl - Z.of_nat nl)%Z with 0%Z by lia.
        do 16 eexists. exists m2. split; [reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HR|]. split; [exact WR|]. split; [exact HN|]. split; [exact ST|].
        split; [exact LBl|]. split; [exact LenB| exact HCn].
      - eapply (IH (S i)); [lia| exact I2| exact HCn].
      - exfalso. lia.
    Qed.

    Lemma reduce_loop_walk : forall B (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      limbs B -> length B = LB -> u64arr bgusegs m RP (wlimbs B) -> limbs_at bgusegs m NP np -> stk bgusegs m lo SP -> mem_inv bgusegs m ->
      evt bgusegs (let '(Bn, Cn) := mont_reduce_loop np n0 nl nl 0 B 0 in mr_post Bn Cn)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat nl)) s3 (Z_to_bv 64 (Z.of_nat nl)) (Z_to_bv 64 RP)
                 (Z_to_bv 64 n0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (8 * Z.of_nat nl)) (Z_to_bv 64 (18446744073709551615 - RP))
                 (Z_to_bv 64 18446744073709551607) t3 t4 t5 t6)
            F (Z_to_bv 64 0x100130) fc None m (seg_rom bgusegs)).
    Proof.
      intros B ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 L1 L2 U HN ST MI.
      replace (mont_reduce_loop np n0 nl nl 0 B 0%Z) with (mont_reduce_loop np n0 nl (S (nl - 1)) 0 B 0%Z) by (f_equal; lia).
      pose proof (reduce_loop (nl - 1)%nat 0%nat m B 0%Z ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ltac:(lia) ltac:(apply RB_init; assumption) ltac:(lia)) as H.
      replace (RP + 8 * Z.of_nat 0)%Z with RP in H by lia. replace (Z.of_nat nl - Z.of_nat 0)%Z with (Z.of_nat nl) in H by lia.
      exact H.
    Qed.
  End ReduceLoop.
End WithRegs.
