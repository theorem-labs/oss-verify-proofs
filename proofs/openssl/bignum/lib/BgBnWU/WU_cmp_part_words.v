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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnWU Require Import WU_cmp_words.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition bn_cmp_part_words_uentry := 0xff608%Z.

(* [comment removed for export] *)
Ltac weq :=
  apply Z_to_bv_eqm;
  rewrite ?Z_to_bv_unsigned, ?Z.shiftl_mul_pow2 by lia; change (2 ^ 1)%Z with 2%Z; change (2 ^ 3)%Z with 8%Z;
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus;
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z; change (2 ^ Z.of_N 32)%Z with 4294967296%Z;
  change (4294967296 `div` 2)%Z with 2147483648%Z; change (2 ^ 64)%Z with 18446744073709551616%Z;
  Z.div_mod_to_equations; lia.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b : list Z) (cl da db : nat) (lo : Z).
  Notation ap := (bv_unsigned a0).
  Notation bp := (bv_unsigned a1).
  Notation SP := (bv_unsigned sp).
  Hypothesis LA : limbs a.
  Hypothesis LB : limbs b.
  Hypothesis HLA : length a = (cl + da)%nat.
  Hypothesis HLB : length b = (cl + db)%nat.
  Hypothesis DAB : (da = 0 \/ db = 0)%nat.
  Hypothesis NA31 : (Z.of_nat (cl + da + db) < 2147483648)%Z.
  Hypothesis A2 : bv_unsigned a2 = Z.of_nat cl.
  Hypothesis A3 : a3 = Z_to_bv 64 (Z.of_nat da - Z.of_nat db).
  Hypothesis RA : limbs_at bgusegs m ap a.
  Hypothesis RB : limbs_at bgusegs m bp b.
  Hypothesis STK : stk bgusegs m lo SP.
  Hypothesis LO : (lo <= SP - 16)%Z.
  Hypothesis SEPA : (ap + 8 * Z.of_nat (length a) <= SP - 16 \/ SP <= ap)%Z.
  Hypothesis SEPB : (bp + 8 * Z.of_nat (length b) <= SP - 16 \/ SP <= bp)%Z.
  Hypothesis MI0 : mem_inv bgusegs m.
  Hypothesis UBA : ub_ptr_ok 1 ap.
  Hypothesis UBB : ub_ptr_ok 1 bp.

  Notation POST := (ro_post bgusegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 16%Z (cmp_part_words a b cl) lo m).

  (* [comment removed for export] *)
  Notation ST pc mm x5 x6 x8 x10 x13 x14 x15 x16 x17 :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 t2 x8 s1 x10 a1 a2 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgusegs)).

  Definition UCINV (m1 : word -> option byte) : Prop :=
    limbs_at bgusegs m1 ap a /\ limbs_at bgusegs m1 bp b /\
    rw_cells bgusegs m1 (SP + -16) [C8 s0; C8 ra] /\ stk bgusegs m1 lo (SP + -16) /\
    mem_inv bgusegs m1 /\ munch [(SP + -16, SP)]%Z m m1 /\ wmono bgusegs m m1.

  (* [comment removed for export] *)
  Definition uptrs : Prop := (0 < ap /\ ap mod 8 = 0 /\ ap + 8 * Z.of_nat (length a) <= 18446744073709551616 /\
                              0 < bp /\ bp mod 8 = 0 /\ bp + 8 * Z.of_nat (length b) <= 18446744073709551616)%Z.

  Lemma HBsk : length (skipn cl b) = db. Proof. rewrite length_skipn. lia. Qed.
  Lemma HAsk : length (skipn cl a) = da. Proof. rewrite length_skipn. lia. Qed.

  (* [comment removed for export] *)
  Lemma ucpw_ret : forall m1 res x5 x6 x8 x13 x14 x15 x16 x17, UCINV m1 -> res = cmp_part_words a b cl ->
    evt bgusegs POST (ST 0xff6f8 m1 x5 x6 x8 (Z_to_bv 64 res) x13 x14 x15 x16 x17).
  Proof.
    intros m1 res x5 x6 x8 x13 x14 x15 x16 x17 (HA & HB & FR & ST & MI & MU & WM) ->.
    do 4 zstep.
    release_frame FR ST (bv_unsigned sp).
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma ucpw_neg : forall m1 x5 x6 x8 x10 x13 x14 x15 x16 x17, UCINV m1 -> existsb nonzero (skipn cl b) = true ->
    evt bgusegs POST (ST 0xff6f4 m1 x5 x6 x8 x10 x13 x14 x15 x16 x17).
  Proof.
    intros m1 x5 x6 x8 x10 x13 x14 x15 x16 x17 I E.
    zstep. eapply ucpw_ret; [exact I|]. unfold cmp_part_words. rewrite E. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ucpw_pos : forall m1 x5 x6 x8 x10 x13 x14 x15 x16 x17, UCINV m1 ->
    existsb nonzero (skipn cl b) = false -> existsb nonzero (skipn cl a) = true ->
    evt bgusegs POST (ST 0xff6ec m1 x5 x6 x8 x10 x13 x14 x15 x16 x17).
  Proof.
    intros m1 x5 x6 x8 x10 x13 x14 x15 x16 x17 I Eb Ea.
    do 2 zstep. eapply ucpw_ret; [exact I|]. unfold cmp_part_words. rewrite Eb, Ea. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ucpw_tail : forall m1 x5 x6 x13 x14 x15 x16 x17, UCINV m1 ->
    existsb nonzero (skipn cl b) = false -> existsb nonzero (skipn cl a) = false ->
    evt bgusegs POST (ST 0xff6dc m1 x5 x6 sp a0 x13 x14 x15 x16 x17).
  Proof.
    intros m1 x5 x6 x13 x14 x15 x16 x17 (HA & HB & FR & ST & MI & MU & WM) Eb Ea.
    do 4 zstep.
    release_frame FR ST (bv_unsigned sp).
    eapply evt_mono.
    - assert (La : length (firstn cl a) = cl) by (rewrite length_firstn; lia).
      assert (Lb : length (firstn cl b) = cl) by (rewrite length_firstn; lia).
      eapply bn_cmp_words_uspec with (a := firstn cl a) (b := firstn cl b) (lo := lo).
      + apply limbs_firstn. exact LA.
      + apply limbs_firstn. exact LB.
      + rewrite La, Lb. reflexivity.
      + rewrite La. clear - NA31. lia.
      + rewrite La. exact A2.
      + rewrite <- (firstn_skipn cl a) in HA. apply limbs_at_app in HA. exact (proj1 HA).
      + rewrite <- (firstn_skipn cl b) in HB. apply limbs_at_app in HB. exact (proj1 HB).
      + exact ST.
      + exact LO.
      + rewrite La. clear - SEPA HLA. lia.
      + rewrite La. clear - SEPB HLB. lia.
      + exact MI.
      + intros _. apply UBA. lia.
      + intros _. apply UBB. lia.
    - intros ms' (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & E & MU' & WM' & MI' & ST').
      exists u0, u1, u2, v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, m'.
      split. { rewrite E. unfold cmp_part_words. rewrite Eb, Ea. reflexivity. }
      split. { eapply munch_trans; [ | exact MU']. replace (SP - 16)%Z with (SP + -16)%Z by lia. exact MU. }
      split. { eapply wmono_trans; [exact WM | exact WM']. }
      split; [exact MI' | exact ST'].
  Qed.

  (* [comment removed for export] *)
  Lemma ucpw_loopA : forall (j : nat) m1 x5 x6 x17, uptrs -> UCINV m1 -> db = 0%nat -> (1 <= j <= da)%nat -> zeros_above (skipn cl a) j ->
    evt bgusegs POST (ST 0xff688 m1 x5 x6 sp a0 (Z_to_bv 64 (Z.of_nat j)) (Z_to_bv 64 (Z.of_nat cl + -1)) (Z_to_bv 64 1) (Z_to_bv 64 2) x17).
  Proof.
    induction j as [|j IH]; intros m1 x5 x6 x17 P I Hdb Hj Z; [exfalso; lia|]. unfold uptrs in P.
    pose proof I as (HA & _).
    assert (Eb : existsb nonzero (skipn cl b) = false).
    { apply existsb_nonzero_zeros. intros i y _ E. exfalso. assert (nth_error (skipn cl b) i <> None) by congruence.
      apply nth_error_Some in H. rewrite HBsk in H. lia. }
    destruct (nth_error a (cl + j)) as [x|] eqn:Ex; [|apply nth_error_None in Ex; lia].
    pose proof (limbs_nth_error_lit a _ x LA Ex) as Rx.
    assert (Exs : nth_error (skipn cl a) j = Some x) by (rewrite nth_error_skipn; exact Ex).
    do 3 zstep.
    setreg 13%Z (Z_to_bv 64 (Z.of_nat (cl + j))) ltac:(clear - NA31 Hj; weq).
    setreg 5%Z (Z_to_bv 64 (Z.of_nat (cl + j))) ltac:(f_equal; clear; lia).
    chk ltac:(fun C => clear - C; lia).
    zstep. rewrite (bn_swrap32_small (Z.of_nat (cl + j) + 0)), Z.add_0_r by (clear - NA31 Hj; lia).
    zstep. replace (Z.of_nat (cl + j) ≪ 3)%Z with (8 * Z.of_nat (cl + j))%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    do 2 zstep.
    setreg 6%Z (Z_to_bv 64 0) ltac:(replace (ap + 8 * Z.of_nat (cl + j) <? 1)%Z with false by (symmetry; apply Z.ltb_ge; clear - P; lia); reflexivity).
    zstep. if_false.
    do 4 zstep.
    setreg 5%Z (Z_to_bv 64 1) ltac:(
      replace (ap + 8 * Z.of_nat (cl + j) <? ap)%Z with false by (symmetry; apply Z.ltb_ge; clear; lia);
      rewrite lxor_signbit' by (clear - NA31 Hj; lia);
      replace (Z.of_nat (cl + j) + 9223372036854775808 <? 9223372036854775808)%Z with false by (symmetry; apply Z.ltb_ge; clear; lia);
      reflexivity).
    zstep. if_false.
    chk ltac:(fun C => clear - C P; lia).
    zstep. rewrite land7 by (clear - P; Z.div_mod_to_equations; lia).
    zstep. if_false.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bgusegs m1 ap a (cl + j) x ad HA Ex ltac:(unfold wa; f_equal; lia)) as RD); zstep; clear RD.
    zstep. if_cases K; zify_cond K.
    - eapply ucpw_pos; [exact I | exact Eb | exact (existsb_nonzero_nth _ _ _ Exs K)].
    - subst x. pose proof (zeros_above_step _ _ Z Exs) as Z'.
      zstep. rewrite (bn_swrap32_small (Z.of_nat (S j) + -1)) by (clear - NA31 Hj; lia).
      setreg 13%Z (Z_to_bv 64 (Z.of_nat j)) ltac:(f_equal; clear; lia).
      zstep. rewrite lts_signed by (clear - Hj NA31; lia).
      if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        eapply IH; [exact P | exact I | exact Hdb | clear - K2 Hj; lia | exact Z'].
      + (* [comment removed for export] *)
        assert (j = 0%nat) by (clear - K2; lia). subst j.
        eapply ucpw_tail; [exact I | exact Eb | exact (existsb_nonzero_zeros _ Z')].
  Qed.

  (* [comment removed for export] *)
  Lemma ucpw_loopB : forall (j : nat) m1 x5 x6 x13 x17, uptrs -> UCINV m1 -> (1 <= j <= db)%nat -> zeros_above (skipn cl b) j ->
    (forall y5 y6 y16 y17, zeros_above (skipn cl b) 0 ->
       evt bgusegs POST (ST 0xff67c m1 y5 y6 sp a0 x13 (Z_to_bv 64 (Z.of_nat cl + -1)) (Z_to_bv 64 1) y16 y17)) ->
    evt bgusegs POST (ST 0xff62c m1 x5 x6 sp a0 x13 (Z_to_bv 64 (Z.of_nat cl + -1)) (Z_to_bv 64 1) (Z_to_bv 64 (- Z.of_nat j)) x17).
  Proof.
    induction j as [|j IH]; intros m1 x5 x6 x13 x17 P I Hj Z KMID; [exfalso; lia|]. unfold uptrs in P.
    pose proof I as (_ & HB & _).
    destruct (nth_error b (cl + j)) as [y|] eqn:Ey; [|apply nth_error_None in Ey; lia].
    pose proof (limbs_nth_error_lit b _ y LB Ey) as Ry.
    assert (Eys : nth_error (skipn cl b) j = Some y) by (rewrite nth_error_skipn; exact Ey).
    do 2 zstep.
    setreg 17%Z (Z_to_bv 64 (Z.of_nat (cl + j))) ltac:(clear - NA31 Hj; weq).
    setreg 5%Z (Z_to_bv 64 (Z.of_nat (cl + j))) ltac:(clear - NA31 Hj; weq).
    chk ltac:(fun C => clear - C; lia).
    zstep. rewrite (bn_swrap32_small (Z.of_nat (cl + j) + 0)), Z.add_0_r by (clear - NA31 Hj; lia).
    zstep. replace (Z.of_nat (cl + j) ≪ 3)%Z with (8 * Z.of_nat (cl + j))%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    do 2 zstep.
    setreg 6%Z (Z_to_bv 64 0) ltac:(replace (bp + 8 * Z.of_nat (cl + j) <? 1)%Z with false by (symmetry; apply Z.ltb_ge; clear - P; lia); reflexivity).
    zstep. if_false.
    do 4 zstep.
    setreg 5%Z (Z_to_bv 64 1) ltac:(
      replace (bp + 8 * Z.of_nat (cl + j) <? bp)%Z with false by (symmetry; apply Z.ltb_ge; clear; lia);
      rewrite lxor_signbit' by (clear - NA31 Hj; lia);
      replace (Z.of_nat (cl + j) + 9223372036854775808 <? 9223372036854775808)%Z with false by (symmetry; apply Z.ltb_ge; clear; lia);
      reflexivity).
    zstep. if_false.
    chk ltac:(fun C => clear - C P; lia).
    zstep. rewrite land7 by (clear - P; Z.div_mod_to_equations; lia).
    zstep. if_false.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bgusegs m1 bp b (cl + j) y ad HB Ey ltac:(unfold wa; f_equal; lia)) as RD); zstep; clear RD.
    zstep. if_cases K; zify_cond K.
    - eapply ucpw_neg; [exact I | exact (existsb_nonzero_nth _ _ _ Eys K)].
    - subst y. pose proof (zeros_above_step _ _ Z Eys) as Z'.
      zstep.
      setreg 16%Z (Z_to_bv 64 (- Z.of_nat j)) ltac:(clear - NA31 Hj; weq).
      zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        eapply IH; [exact P | exact I | | exact Z' | exact KMID].
        assert (j <> 0%nat) by (intros ->; apply K2; reflexivity). clear - H Hj. lia.
      + (* [comment removed for export] *)
        assert (j = 0%nat).
        { destruct j as [|j']; [reflexivity | exfalso]. clear - K2 Hj NA31.
          rewrite Z.mod_opp_l_nz in K2; rewrite ?Z.mod_small in * by lia; lia. }
        subst j. apply KMID. exact Z'.
  Qed.

  (* [comment removed for export] *)
  Lemma ucpw_mid : forall m1 x5 x6 x15 x16 x17, uptrs -> UCINV m1 -> zeros_above (skipn cl b) 0 ->
    evt bgusegs POST (ST 0xff67c m1 x5 x6 sp a0 (Z_to_bv 64 (Z.of_nat da - Z.of_nat db)) (Z_to_bv 64 (Z.of_nat cl + -1)) x15 x16 x17).
  Proof.
    intros m1 x5 x6 x15 x16 x17 P I Zb.
    pose proof (existsb_nonzero_zeros _ Zb) as Eb.
    zstep. rewrite lts_signed by (clear - NA31; lia).
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (da = 0%nat) by (clear - K DAB; lia).
      eapply ucpw_tail; [exact I | exact Eb |].
      apply existsb_nonzero_zeros. intros i y _ E. exfalso. assert (nth_error (skipn cl a) i <> None) by congruence.
      apply nth_error_Some in H0. rewrite HAsk in H0. lia.
    - assert (Hda : (1 <= da)%nat /\ db = 0%nat) by (clear - K DAB; lia). destruct Hda as (Hda & Hdb).
      do 2 zstep.
      setreg 15%Z (Z_to_bv 64 1) ltac:(replace (0 <? ap)%Z with true by (symmetry; apply Z.ltb_lt; clear - P; unfold uptrs in P; lia); reflexivity).
      setreg 13%Z (Z_to_bv 64 (Z.of_nat da)) ltac:(f_equal; clear - Hdb; lia).
      eapply ucpw_loopA; [exact P | exact I | exact Hdb | clear - Hda; lia |].
      pose proof (zeros_above_len (skipn cl a)) as ZL. rewrite HAsk in ZL. exact ZL.
  Qed.

  (* [comment removed for export] *)
  Lemma bn_cmp_part_words_uspec :
    evt bgusegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xff608) fc None m (seg_rom bgusegs)).
  Proof.
    pose proof (munch_refl [(SP - 16, SP)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    assert (P : uptrs).
    { unfold uptrs. pose proof (UBA ltac:(lia)) as (H1 & H2). pose proof (UBB ltac:(lia)) as (H3 & H4).
      pose proof (limbs_at_bound _ _ _ _ RA) as BA. pose proof (limbs_at_bound _ _ _ _ RB) as BB.
      change (2 ^ 64)%Z with 18446744073709551616%Z in *. clear - H1 H2 H3 H4 BA BB. lia. }
    carve_frame 16%nat STK.
    do 4 zstep.
    assert (I : UCINV m1).
    { unfold UCINV. split; [|split].
      - eapply limbs_at_transport; [exact RA | exact MU | cbn [disjoint_from]; lia].
      - eapply limbs_at_transport; [exact RB | exact MU | cbn [disjoint_from]; lia].
      - split; [exact FR|]. split; [exact STK|]. split; [exact MI0|]. split; [exact MU | exact WM]. }
    clear RA RB FR STK MI0 MU WM.
    assert (Ea2 : a2 = Z_to_bv 64 (Z.of_nat cl)) by (rewrite <- A2; symmetry; apply Z_to_bv_bv_unsigned).
    zstep. rewrite A2. rewrite (bn_swrap32_small (Z.of_nat cl + -1)) by (clear - NA31; lia).
    zstep.
    if_cases C0; [exfalso; rewrite Ea2 in C0; rewrite lts_signed in C0 by (clear - NA31; lia); zify_cond C0; clear - C0; lia | clear C0].
    rewrite A3.
    zstep. rewrite lts_signed by (clear - NA31; lia).
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (Hdb : db = 0%nat) by (clear - K DAB; lia).
      eapply ucpw_mid; [exact P | exact I|].
      intros i y _ E. exfalso. assert (nth_error (skipn cl b) i <> None) by congruence.
      apply nth_error_Some in H. rewrite HBsk in H. lia.
    - assert (Hdb : (1 <= db)%nat /\ da = 0%nat) by (clear - K DAB; lia). destruct Hdb as (Hdb & Hda).
      do 2 zstep.
      setreg 15%Z (Z_to_bv 64 1) ltac:(replace (0 <? bp)%Z with true by (symmetry; apply Z.ltb_lt; clear - P; unfold uptrs in P; lia); reflexivity).
      setreg 16%Z (Z_to_bv 64 (- Z.of_nat db)) ltac:(f_equal; clear - Hda; lia).
      eapply ucpw_loopB; [exact P | exact I | clear - Hdb; lia | |].
      + pose proof (zeros_above_len (skipn cl b)) as ZL. rewrite HBsk in ZL. exact ZL.
      + intros y5 y6 y16 y17 Zb.
        replace (- Z.of_nat db)%Z with (Z.of_nat da - Z.of_nat db)%Z by (clear - Hda; lia).
        eapply ucpw_mid; [exact P | exact I | exact Zb].

  Qed.

End Proofs.
