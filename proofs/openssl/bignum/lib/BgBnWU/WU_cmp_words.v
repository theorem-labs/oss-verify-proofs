(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnCmp.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnW Require Import W_cmp_words.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition bn_cmp_words_uentry := 0xff514%Z.

(* [comment removed for export] *)
Lemma lxor_signbit' : forall x, (0 <= x < 9223372036854775808 -> Z.lxor x 9223372036854775808 = x + 9223372036854775808)%Z.
Proof.
  intros x Hx. symmetry. apply Z.add_nocarry_lxor.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0. change 9223372036854775808%Z with (2^63)%Z. rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 63 i) as [<-|]; [|apply andb_false_r]. rewrite andb_true_r.
  destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma lxor_ones64' : forall x, (0 <= x < 18446744073709551616 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x)%Z.
Proof.
  intros x Hx. change 18446744073709551615%Z with (Z.ones 64) at 1.
  assert (E : Z.lxor x (Z.ones 64) = Z.land (Z.lnot x) (Z.ones 64)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
    destruct (Z.lt_ge_cases i 64) as [H|H].
    - rewrite Z.ones_spec_low by lia. rewrite andb_true_r, xorb_true_r. reflexivity.
    - rewrite Z.ones_spec_high by lia. rewrite andb_false_r, xorb_false_r.
      destruct (Z.eq_dec x 0) as [->|Nx]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. assert (Z.log2 x < 64)%Z by (apply Z.log2_lt_pow2; lia). lia. }
  rewrite E, Z.land_ones by lia. unfold Z.lnot, Z.pred. change (2 ^ 64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. lia.
Qed.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b : list Z) (lo : Z).
  Notation ap := (bv_unsigned a0).
  Notation bp := (bv_unsigned a1).
  Notation n := (Z.of_nat (length a)).
  Notation SP := (bv_unsigned sp).
  Hypothesis LA : limbs a.
  Hypothesis LB : limbs b.
  Hypothesis LEN : length b = length a.
  Hypothesis N31 : (n < 2^31)%Z.
  Hypothesis A2 : bv_unsigned a2 = n.
  Hypothesis RA : limbs_at bgusegs m ap a.
  Hypothesis RB : limbs_at bgusegs m bp b.
  Hypothesis STK : stk bgusegs m lo SP.
  Hypothesis LO : (lo <= SP - 16)%Z.
  Hypothesis SEPA : (ap + 8 * n <= SP - 16 \/ SP <= ap)%Z.
  Hypothesis SEPB : (bp + 8 * n <= SP - 16 \/ SP <= bp)%Z.
  Hypothesis MI0 : mem_inv bgusegs m.
  Hypothesis UBA : ub_ptr_ok n ap.
  Hypothesis UBB : ub_ptr_ok n bp.

  Notation POST := (ro_post bgusegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 16%Z (cmp_words a b) lo m).

  (* [comment removed for export] *)
  Notation ST pc mm x5 x6 x8 x10 x11 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 t2 x8 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgusegs)).

  (* [comment removed for export] *)
  Definition UCINV (m1 : word -> option byte) : Prop :=
    limbs_at bgusegs m1 ap a /\ limbs_at bgusegs m1 bp b /\
    rw_cells bgusegs m1 (SP + -16) [C8 s0; C8 ra] /\ stk bgusegs m1 lo (SP + -16) /\
    mem_inv bgusegs m1 /\ munch [(SP + -16, SP)]%Z m m1 /\ wmono bgusegs m m1.

  (* [comment removed for export] *)
  Definition uptrs : Prop := (0 < ap /\ ap mod 8 = 0 /\ ap + 8 * n <= 18446744073709551616 /\
                              0 < bp /\ bp mod 8 = 0 /\ bp + 8 * n <= 18446744073709551616)%Z.

  (* [comment removed for export] *)
  Lemma ucw_ret : forall m1 res x5 x6 x8 x11 x12 x13 x14 x15 x16 x17, UCINV m1 -> res = cmp_words a b ->
    evt bgusegs POST (ST 0xff5a8 m1 x5 x6 x8 (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17).
  Proof.
    intros m1 res x5 x6 x8 x11 x12 x13 x14 x15 x16 x17 (HA & HB & FR & ST & MI & MU & WM) ->.
    do 4 zstep.
    release_frame FR ST (bv_unsigned sp).
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma ucw_differ : forall m1 x y x5 x6 x8 x11 x12 x13 x14 x15 x16 x17, UCINV m1 ->
    (0 <= x < 18446744073709551616)%Z -> (0 <= y < 18446744073709551616)%Z -> x <> y -> cmp1 x y = cmp_words a b ->
    evt bgusegs POST (ST 0xff5a0 m1 x5 x6 x8 (Z_to_bv 64 (Z.b2z (y <? x)%Z)) x11 x12 x13 x14 x15 x16 x17).
  Proof.
    intros m1 x y x5 x6 x8 x11 x12 x13 x14 x15 x16 x17 I Rx Ry NE E.
    do 2 zstep.
    setreg 10%Z (Z_to_bv 64 (cmp1 x y))
      ltac:(unfold cmp1; destruct (Z.eqb_spec x y) as [|_]; [contradiction|]; destruct (y <? x)%Z; apply Z_to_bv_eqm; vm_compute; reflexivity).
    eapply ucw_ret; [exact I | exact E].
  Qed.

  (* [comment removed for export] *)
  Lemma ucw_zero : forall m1 x5 x6 x8 x10 x11 x12 x13 x14 x15 x16 x17, UCINV m1 -> cmp_words a b = 0%Z ->
    evt bgusegs POST (ST 0xff5f4 m1 x5 x6 x8 x10 x11 x12 x13 x14 x15 x16 x17).
  Proof.
    intros m1 x5 x6 x8 x10 x11 x12 x13 x14 x15 x16 x17 I E.
    do 2 zstep.
    eapply ucw_ret; [exact I | symmetry; exact E].
  Qed.

  (* [comment removed for export] *)
  Lemma ucw_loop : forall (k : nat) m1 x5 x6 x8 x15 x16 x17, uptrs -> UCINV m1 -> (1 <= k <= length a)%nat ->
    cmp_words a b = cmp_words (firstn k a) (firstn k b) ->
    evt bgusegs POST (ST 0xff5cc m1 x5 x6 x8 a0 a1 (Z_to_bv 64 (18446744073709551615 - ap)) (Z_to_bv 64 (Z.of_nat k))
                       (Z_to_bv 64 (18446744073709551615 - bp)) x15 x16 x17).
  Proof.
    induction k as [|k IH]; intros m1 x5 x6 x8 x15 x16 x17 P I Hk E; [exfalso; lia|]. unfold uptrs in P.
    pose proof I as (HA & HB & _).
    assert (Hka : (k < length a)%nat) by lia. assert (Hkb : (k < length b)%nat) by lia.
    destruct (nth_error a k) as [x|] eqn:Ex; [|apply nth_error_None in Ex; lia].
    destruct (nth_error b k) as [y|] eqn:Ey; [|apply nth_error_None in Ey; lia].
    pose proof (limbs_nth_error_lit a k x LA Ex) as Rx. pose proof (limbs_nth_error_lit b k y LB Ey) as Ry.
    zstep.
    rewrite (bn_swrap32_small (Z.of_nat (S k) + -1)) by (clear - Hk N31; lia).
    replace (Z.of_nat (S k) + -1)%Z with (Z.of_nat k) by (clear; lia).
    zstep.
    chk ltac:(fun C => rewrite Z.shiftl_mul_pow2 in C by lia; clear - C P Hka; lia).
    chk ltac:(fun C => rewrite Z.shiftl_mul_pow2 in C by lia; clear - C P Hka; lia).
    do 2 zstep.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bgusegs m1 ap a k x ad HA Ex ltac:(unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD); zstep; clear RD.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bgusegs m1 bp b k y ad HB Ey ltac:(unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD); zstep; clear RD.
    pose proof (cmp_words_top a b k x y (eq_sym LEN) Ex Ey) as T.
    zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      do 2 zstep.
      eapply ucw_differ; [exact I | exact Rx | exact Ry | exact K1 |].
      rewrite E, T. destruct (Z.eqb_spec x y) as [|_]; [contradiction | reflexivity].
    - assert (E' : cmp_words a b = cmp_words (firstn k a) (firstn k b)).
      { rewrite E, T. destruct (Z.eqb_spec x y) as [_|]; [reflexivity | contradiction]. }
      zstep. if_cases K2; zify_cond K2.
      + eapply IH; [exact P | exact I | clear - K0 Hk; lia | exact E'].
      + assert (k = 0%nat).
        { apply andb_false_iff in K2. destruct K2 as [K2|K2]; apply Z.ltb_ge in K2; clear - K2 Hk N31; lia. }
        subst k.
        eapply ucw_zero; [exact I | rewrite E'; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma bn_cmp_words_uspec :
    evt bgusegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xff514) fc None m (seg_rom bgusegs)).
  Proof.
    pose proof (munch_refl [(SP - 16, SP)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    assert (P0 : (0 < n)%Z -> uptrs).
    { intros Hn. unfold uptrs. pose proof (UBA Hn) as (H1 & H2). pose proof (UBB Hn) as (H3 & H4).
      pose proof (limbs_at_bound _ _ _ _ RA) as BA. pose proof (limbs_at_bound _ _ _ _ RB) as BB. rewrite LEN in BB.
      change (2 ^ 64)%Z with 18446744073709551616%Z in *. clear - H1 H2 H3 H4 BA BB. lia. }
    carve_frame 16%nat STK.
    do 4 zstep.
    assert (I : UCINV m1).
    { unfold UCINV. split; [|split].
      - eapply limbs_at_transport; [exact RA | exact MU | cbn [disjoint_from]; lia].
      - eapply limbs_at_transport; [exact RB | exact MU | cbn [disjoint_from]; rewrite LEN; lia].
      - split; [exact FR|]. split; [exact STK|]. split; [exact MI0|]. split; [exact MU | exact WM]. }
    clear RA RB FR STK MI0 MU WM.
    zstep. if_cases K; zify_cond K.
    { (* [comment removed for export] *)
      assert (E0 : cmp_words a b = 0%Z) by (clear - K A2; destruct a; [reflexivity | exfalso; cbn [length] in *; lia]).
      eapply ucw_zero; [exact I | exact E0]. }
    assert (Hn : (1 <= length a)%nat) by (clear - K A2; lia).
    set (k := (length a - 1)%nat).
    assert (Ek : (Z.of_nat k = n - 1)%Z) by (subst k; clear - Hn; lia).
    destruct (nth_error a k) as [x|] eqn:Ex; [|apply nth_error_None in Ex; subst k; lia].
    destruct (nth_error b k) as [y|] eqn:Ey; [|apply nth_error_None in Ey; subst k; lia].
    pose proof (limbs_nth_error_lit a k x LA Ex) as Rx. pose proof (limbs_nth_error_lit b k y LB Ey) as Ry.
    pose proof I as (HA & HB & _).
    assert (Ea2 : a2 = Z_to_bv 64 n) by (rewrite <- A2; symmetry; apply Z_to_bv_bv_unsigned).
    pose proof (P0 ltac:(clear - Hn; lia)) as P. clear P0. unfold uptrs in P.
    zstep. rewrite A2, (bn_swrap32_small (n + -1)) by (clear - Hn N31; lia).
    replace (n + -1)%Z with (Z.of_nat k) by (clear - Ek; lia).
    zstep. rewrite Ea2. rewrite lts_small by (clear - Ek N31; lia).
    if_cases C0; [exfalso; zify_cond C0; clear - C0 Ek; lia | clear C0].
    zstep. replace (Z.of_nat k ≪ 3)%Z with (8 * Z.of_nat k)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    do 3 zstep.
    setreg 16%Z (Z_to_bv 64 1) ltac:(replace (0 <? ap)%Z with true by (symmetry; apply Z.ltb_lt; clear - P; lia); reflexivity).
    setreg 17%Z (Z_to_bv 64 0) ltac:(replace (ap + 8 * Z.of_nat k <? 1)%Z with false by (symmetry; apply Z.ltb_ge; clear - P; lia); reflexivity).
    zstep. if_false.
    do 4 zstep.
    setreg 16%Z (Z_to_bv 64 0) ltac:(
      rewrite lxor_signbit' by (clear - Ek N31; lia);
      replace (Z.of_nat k + 9223372036854775808 <? 9223372036854775808)%Z with false by (symmetry; apply Z.ltb_ge; clear; lia); reflexivity).
    setreg 17%Z (Z_to_bv 64 1) ltac:(
      rewrite lxor_signbit' by (clear - Ek N31; lia);
      replace (Z.of_nat k + 9223372036854775808 <? 9223372036854775808)%Z with false by (symmetry; apply Z.ltb_ge; clear; lia);
      replace (ap + 8 * Z.of_nat k <? 8 * Z.of_nat k)%Z with false by (symmetry; apply Z.ltb_ge; clear - P; lia); reflexivity).
    zstep. if_false.
    chk ltac:(fun C => clear - C P; lia).
    zstep. rewrite land7 by (clear - P; Z.div_mod_to_equations; lia).
    zstep. if_false.
    do 3 zstep.
    setreg 5%Z (Z_to_bv 64 1) ltac:(replace (0 <? bp)%Z with true by (symmetry; apply Z.ltb_lt; clear - P; lia); reflexivity).
    setreg 6%Z (Z_to_bv 64 0) ltac:(replace (8 * Z.of_nat k + bp <? 1)%Z with false by (symmetry; apply Z.ltb_ge; clear - P; lia); reflexivity).
    zstep. if_false.
    do 3 zstep.
    setreg 15%Z (Z_to_bv 64 1) ltac:(
      replace (8 * Z.of_nat k + bp <? 8 * Z.of_nat k)%Z with false by (symmetry; apply Z.ltb_ge; clear - P; lia); reflexivity).
    zstep. if_false.
    chk ltac:(fun C => clear - C P; lia).
    zstep. rewrite land7 by (clear - P; Z.div_mod_to_equations; lia).
    zstep. if_false.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bgusegs m1 ap a k x ad HA Ex ltac:(unfold wa; f_equal; lia)) as RD); zstep; clear RD.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bgusegs m1 bp b k y ad HB Ey ltac:(unfold wa; f_equal; lia)) as RD); zstep; clear RD.
    pose proof (cmp_words_top a b k x y (eq_sym LEN) Ex Ey) as T.
    assert (EF : cmp_words a b = cmp_words (firstn (S k) a) (firstn (S k) b)).
    { replace (S k) with (length a) by (subst k; clear - Hn; lia). rewrite firstn_all. rewrite <- LEN, firstn_all. reflexivity. }
    zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      assert (E' : cmp_words a b = cmp_words (firstn k a) (firstn k b)).
      { rewrite EF, T. destruct (Z.eqb_spec x y) as [_|]; [reflexivity | contradiction]. }
      zstep. rewrite (bn_swrap32_small (n + -2)) by (clear - Hn N31; lia).
      zstep. rewrite lts_signed by (clear - Hn N31; lia).
      if_cases C0; [exfalso; zify_cond C0; clear - C0; lia | clear C0].
      zstep. rewrite lts_signed by (clear - Hn N31; lia).
      if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        assert (H0 : k = 0%nat) by (subst k; clear - K2 Hn; lia).
        eapply ucw_zero; [exact I | rewrite E', H0; reflexivity].
      + do 2 zstep. rewrite !lxor_ones64' by (clear - P Hn; lia).
        eapply evt_eq; [ | eapply (ucw_loop k m1); [exact P | exact I | subst k; clear - K2 Hn; lia | exact E'] ].
        reflexivity.
    - (* [comment removed for export] *)
      zstep.
      eapply ucw_differ; [exact I | exact Rx | exact Ry | exact K1 |].
      rewrite EF, T. destruct (Z.eqb_spec x y) as [|_]; [contradiction | reflexivity].

  Qed.
End Proofs.
