(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prog BnBase BnWords BnModel BnMInv.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnCmp.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW Require Import W_cmp_words.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnRep.
From OSSVerify.Proofs.openssl.bignum.lib.BnA Require Import BnAPure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition BN_UCMP : Z := 0xf6488.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo A B Da Db : Z) (ba bb : bignum bptr).
  Notation SP := (bv_unsigned sp).
  Notation la := (firstn (bn_top ba) (bn_buf ba)).
  Notation lb := (firstn (bn_top bb) (bn_buf bb)).
  Hypothesis SA : rw_cells bgpsegs m A (bn_cells Da ba).
  Hypothesis SB : rw_cells bgpsegs m B (bn_cells Db bb).
  Hypothesis RA : limbs_at bgpsegs m Da la.
  Hypothesis RB : limbs_at bgpsegs m Db lb.
  Hypothesis OKA : bn_okm ba.
  Hypothesis OKB : bn_okm bb.
  Hypothesis A0 : (0 < A)%Z.
  Hypothesis B0 : (0 < B)%Z.
  Hypothesis STK : stk bgpsegs m lo SP.
  Hypothesis LO : (lo <= SP - 32)%Z.
  Hypothesis SEPA : (A + 24 <= SP - 32 \/ SP <= A)%Z.
  Hypothesis SEPB : (B + 24 <= SP - 32 \/ SP <= B)%Z.
  Hypothesis SEPDA : (Da + 8 * Z.of_nat (bn_top ba) <= SP - 32 \/ SP <= Da)%Z.
  Hypothesis SEPDB : (Db + 8 * Z.of_nat (bn_top bb) <= SP - 32 \/ SP <= Db)%Z.
  Hypothesis MI0 : mem_inv bgpsegs m.
  Hypothesis EA0 : a0 = Z_to_bv 64 A.
  Hypothesis EA1 : a1 = Z_to_bv 64 B.

  Notation POST := (ro_post bgpsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 32%Z (ucmp_pure ba bb) lo m).

  Notation ST pc mm x8 x10 x11 x12 x13 x14 :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 x8 s1 x10 x11 x12 x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgpsegs)).

  Definition UINV (m1 : word -> option byte) : Prop :=
    limbs_at bgpsegs m1 Da la /\ limbs_at bgpsegs m1 Db lb /\
    (exists jb, rw_cells bgpsegs m1 (SP + -32) [CB 16 jb; C8 s0; C8 ra]) /\ stk bgpsegs m1 lo (SP + -32) /\
    mem_inv bgpsegs m1 /\ munch [(SP + -32, SP)]%Z m m1 /\ wmono bgpsegs m m1.

  Lemma uc_ret : forall m1 res x8 x11 x12 x13 x14, UINV m1 -> res = ucmp_pure ba bb ->
    evt bgpsegs POST (ST 0xf666c m1 x8 (Z_to_bv 64 res) x11 x12 x13 x14).
  Proof.
    intros m1 res x8 x11 x12 x13 x14 (HA & HB & (jb & FR) & ST & MI & MU & WM) ->.
    do 2 zstep.
    release_frame FR ST (bv_unsigned sp). zstep. zstep.
    finish.
  Qed.

  Lemma uc_zero : forall m1 x8 x10 x11 x12 x13 x14, UINV m1 -> ucmp_pure ba bb = 0%Z ->
    evt bgpsegs POST (ST 0xf667c m1 x8 x10 x11 x12 x13 x14).
  Proof.
    intros m1 x8 x10 x11 x12 x13 x14 I E.
    do 2 zstep.
    eapply uc_ret; [exact I | symmetry; exact E].
  Qed.

  Lemma uc_differ : forall m1 x y x8 x10 x12 x14, UINV m1 ->
    (0 <= x < 18446744073709551616)%Z -> (0 <= y < 18446744073709551616)%Z -> x <> y -> cmp1 x y = ucmp_pure ba bb ->
    evt bgpsegs POST (ST 0xf6500 m1 x8 x10 (Z_to_bv 64 x) x12 (Z_to_bv 64 y) x14).
  Proof.
    intros m1 x y x8 x10 x12 x14 I Rx Ry NE E.
    do 3 zstep.
    setreg 10%Z (Z_to_bv 64 (cmp1 x y))
      ltac:(unfold cmp1; destruct (Z.eqb_spec x y) as [|_]; [contradiction|]; destruct (y <? x)%Z; apply Z_to_bv_eqm; vm_compute; reflexivity).
    zstep.
    eapply uc_ret; [exact I | exact E].
  Qed.

  Lemma uc_loop : forall (k : nat) m1 x8 x11 x13, UINV m1 -> (k <= bn_top ba)%nat -> bn_top bb = bn_top ba ->
    ucmp_pure ba bb = cmp_words (firstn k la) (firstn k lb) ->
    evt bgpsegs POST (ST 0xf64e4 m1 x8 (Z_to_bv 64 (Z.of_nat k + 1)) x11 (Z_to_bv 64 (Db + 8 * Z.of_nat k + -8))
                       x13 (Z_to_bv 64 (Da + 8 * Z.of_nat k + -8))).
  Proof.
    induction k as [|k IH]; intros m1 x8 x11 x13 I Hk ET E.
    - zstep. zstep. if_cases K; zify_cond K.
      + eapply uc_zero; [exact I | rewrite E; reflexivity].
      + exfalso. clear - K. lia.
    - pose proof I as (HA & HB & _).
      pose proof OKA as (LMA & TDA & DMA & _). pose proof OKB as (LMB & TDB & DMB & _).
      assert (TA31 : (0 <= Z.of_nat (bn_top ba) < 8388608)%Z) by (clear - TDA DMA; unfold BN_WORDS_MAX, bn_dmax in *; lia).
      assert (LLA : length la = bn_top ba) by (rewrite firstn_length_le; [reflexivity | clear - TDA; unfold bn_dmax in *; lia]).
      assert (LLB : length lb = bn_top ba) by (rewrite firstn_length_le; [exact ET | clear - TDB ET; unfold bn_dmax in *; lia]).
      destruct (nth_error la k) as [x|] eqn:Ex; [|apply nth_error_None in Ex; exfalso; clear - Ex LLA Hk; lia].
      destruct (nth_error lb k) as [y|] eqn:Ey; [|apply nth_error_None in Ey; exfalso; clear - Ey LLB Hk; lia].
      pose proof (limbs_nth_error_lit la k x (limbs_firstn _ _ LMA) Ex) as Rx.
      pose proof (limbs_nth_error_lit lb k y (limbs_firstn _ _ LMB) Ey) as Ry.
      zstep.
      rewrite (bn_swrap32_small (Z.of_nat (S k) + 1 + -1)) by (clear - Hk TA31; lia).
      replace (Z.of_nat (S k) + 1 + -1)%Z with (Z.of_nat (S k)) by (clear; lia).
      zstep. if_cases K; zify_cond K;
        [exfalso; apply andb_false_iff in K; destruct K as [K|K]; apply Z.ltb_ge in K; clear - K Hk TA31; lia|].
      (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bgpsegs m1 Da la k x ad HA Ex ltac:(unfold wa; f_equal; clear; lia)) as RD); zstep; clear RD.
      (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bgpsegs m1 Db lb k y ad HB Ey ltac:(unfold wa; f_equal; clear; lia)) as RD); zstep; clear RD.
      zstep. zstep.
      pose proof (cmp_words_top la lb k x y ltac:(rewrite LLA, LLB; reflexivity) Ex Ey) as T.
      zstep. if_cases K2; zify_cond K2.
      +
        assert (E' : ucmp_pure ba bb = cmp_words (firstn k la) (firstn k lb)).
        { rewrite E, T. destruct (Z.eqb_spec x y) as [_|]; [reflexivity | contradiction]. }
        setreg 10%Z (Z_to_bv 64 (Z.of_nat k + 1)) ltac:(f_equal; clear; lia).
        setreg 12%Z (Z_to_bv 64 (Db + 8 * Z.of_nat k + -8)) ltac:(f_equal; clear; lia).
        setreg 14%Z (Z_to_bv 64 (Da + 8 * Z.of_nat k + -8)) ltac:(f_equal; clear; lia).
        eapply IH; [exact I | clear - Hk; lia | exact ET | exact E'].
      + eapply uc_differ; [exact I | exact Rx | exact Ry | exact K2 |].
        rewrite E, T. destruct (Z.eqb_spec x y) as [|_]; [contradiction | reflexivity].
  Qed.

  Lemma BN_ucmp_spec :
    evt bgpsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 BN_UCMP) fc None m (seg_rom bgpsegs)).
  Proof.
    unfold BN_UCMP. subst a0 a1.
    pose proof (munch_refl [(SP - 32, SP)]%Z m) as MU. pose proof (wmono_refl bgpsegs m) as WM.
    unfold bn_cells in SA, SB.
    pose proof OKA as (LMA & TDA & DMA & FLA). pose proof OKB as (LMB & TDB & DMB & FLB).
    assert (FRA : (0 <= bn_flags ba <= 1)%Z) by (clear - FLA; destruct FLA as [E|E]; rewrite E; lia).
    assert (FRB : (0 <= bn_flags bb <= 1)%Z) by (clear - FLB; destruct FLB as [E|E]; rewrite E; lia).
    assert (EL4A : Z.land (bn_flags ba) 4 = 0%Z) by (clear - FLA; destruct FLA as [E|E]; rewrite E; reflexivity).
    assert (EL4B : Z.land (bn_flags bb) 4 = 0%Z) by (clear - FLB; destruct FLB as [E|E]; rewrite E; reflexivity).
    assert (TA31 : (0 <= Z.of_nat (bn_top ba) < 8388608)%Z) by (clear - TDA DMA; unfold BN_WORDS_MAX, bn_dmax in *; lia).
    assert (TB31 : (0 <= Z.of_nat (bn_top bb) < 8388608)%Z) by (clear - TDB DMB; unfold BN_WORDS_MAX, bn_dmax in *; lia).
    assert (LLA : length la = bn_top ba) by (rewrite firstn_length_le; [reflexivity | clear - TDA; unfold bn_dmax in *; lia]).
    assert (LLB : length lb = bn_top bb) by (rewrite firstn_length_le; [reflexivity | clear - TDB; unfold bn_dmax in *; lia]).
    unfold wz in SA, SB.
    apply (flag_cell_split bgpsegs m A _ _ _ _ (bn_flags ba) FRA) in SA.
    apply (flag_cell_split bgpsegs m B _ _ _ _ (bn_flags bb) FRB) in SB.
    pose proof (rw_cells_bound _ _ _ _ SA) as BA_. pose proof (rw_cells_bound _ _ _ _ SB) as BB_. cbn [cells_size csize Nat.add] in BA_, BB_.
    carve_frame 32%nat STK.
    do 4 zstep.
    assert (I : UINV m1).
    { unfold UINV. split; [|split].
      - eapply limbs_at_transport; [exact RA | exact MU | cbn [disjoint_from]; rewrite LLA; clear - SEPDA; lia].
      - eapply limbs_at_transport; [exact RB | exact MU | cbn [disjoint_from]; rewrite LLB; clear - SEPDB; lia].
      - split; [eexists; exact FR|]. split; [exact STK|]. split; [exact MI0|]. split; [exact MU | exact WM]. }
    clear RA RB FR STK MU WM.
    zstep. if_cases K; zify_cond K; [exfalso; clear - K A0; lia|]. clear K.
    zstep. if_cases K; zify_cond K; [exfalso; clear - K B0; lia|]. clear K.
    zstep. cbv beta. rewrite (u8_lit (bn_flags ba)) by (clear - FRA; lia).
    do 3 zstep.
    rewrite EL4A. zstep. if_false.
    zstep. cbv beta. rewrite (u8_lit (bn_flags bb)) by (clear - FRB; lia).
    zstep. rewrite EL4B. zstep. if_false.
    zstep. rewrite (zx32_small (Z.of_nat (bn_top ba))) by (clear - TA31; lia).
    zstep. rewrite (sx32_small (Z.of_nat (bn_top bb))) by (clear - TB31; lia).
    zstep. rewrite (bn_swrap32_small (Z.of_nat (bn_top ba) - Z.of_nat (bn_top bb))) by (clear - TA31 TB31; lia).
    zstep. if_cases K; zify_cond K.
    -
      rewrite land64_zero_iff in K by (clear - TA31 TB31; lia).
      eapply uc_ret; [exact I|]. unfold ucmp_pure. cbv zeta.
      destruct (Z.eqb_spec (Z.of_nat (bn_top ba) - Z.of_nat (bn_top bb)) 0) as [E0|_]; [contradiction | reflexivity].
    - rewrite land64_zero_iff in K by (clear - TA31 TB31; lia).
      assert (ET : bn_top bb = bn_top ba) by (clear - K; lia).
      do 5 zstep.
      setreg 12%Z (Z_to_bv 64 (Db + 8 * Z.of_nat (bn_top ba) + -8)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
      setreg 14%Z (Z_to_bv 64 (Da + 8 * Z.of_nat (bn_top ba) + -8)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
      eapply uc_loop; [exact I | clear; lia | exact ET |].
      unfold ucmp_pure. cbv zeta. rewrite K. cbn [Z.eqb].
      rewrite ET, !firstn_firstn, Nat.min_id. reflexivity.
  Qed.

End Proofs.
