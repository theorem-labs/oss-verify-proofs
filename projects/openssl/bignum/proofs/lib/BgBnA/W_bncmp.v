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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition BN_CMP : Z := 0xf6694.

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
  Hypothesis LO : (lo <= SP - 16)%Z.
  Hypothesis SEPA : (A + 24 <= SP - 16 \/ SP <= A)%Z.
  Hypothesis SEPB : (B + 24 <= SP - 16 \/ SP <= B)%Z.
  Hypothesis SEPDA : (Da + 8 * Z.of_nat (bn_top ba) <= SP - 16 \/ SP <= Da)%Z.
  Hypothesis SEPDB : (Db + 8 * Z.of_nat (bn_top bb) <= SP - 16 \/ SP <= Db)%Z.
  Hypothesis MI0 : mem_inv bgpsegs m.
  Hypothesis EA0 : a0 = Z_to_bv 64 A.
  Hypothesis EA1 : a1 = Z_to_bv 64 B.

  Notation POST := (ro_post bgpsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 16%Z (cmp_pure ba bb) lo m).

  Definition gtv : Z := if bn_neg ba then -1 else 1.
  Definition ltv : Z := if bn_neg ba then 1 else -1.

  Notation ST pc mm x8 x10 x11 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 x8 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgpsegs)).

  Definition BINV (m1 : word -> option byte) : Prop :=
    limbs_at bgpsegs m1 Da la /\ limbs_at bgpsegs m1 Db lb /\
    rw_cells bgpsegs m1 A (bn_cells Da ba) /\ rw_cells bgpsegs m1 B (bn_cells Db bb) /\
    rw_cells bgpsegs m1 (SP + -16) [C8 s0; C8 ra] /\ stk bgpsegs m1 lo (SP + -16) /\
    mem_inv bgpsegs m1 /\ munch [(SP + -16, SP)]%Z m m1 /\ wmono bgpsegs m m1.

  Lemma bc_ret : forall m1 res x8 x11 x12 x13 x14 x15 x16 x17, BINV m1 -> res = cmp_pure ba bb ->
    evt bgpsegs POST (ST 0xf674c m1 x8 (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17).
  Proof.
    intros m1 res x8 x11 x12 x13 x14 x15 x16 x17 (HA & HB & _ & _ & FR & ST & MI & MU & WM) ->.
    do 2 zstep.
    release_frame FR ST (bv_unsigned sp). zstep. zstep.
    finish.
  Qed.

  Lemma bc_zero : forall m1 x8 x10 x11 x12 x13 x14 x15 x16 x17, BINV m1 -> cmp_pure ba bb = 0%Z ->
    evt bgpsegs POST (ST 0xf6748 m1 x8 x10 x11 x12 x13 x14 x15 x16 x17).
  Proof.
    intros m1 x8 x10 x11 x12 x13 x14 x15 x16 x17 I E.
    zstep.
    eapply bc_ret; [exact I | symmetry; exact E].
  Qed.

  Lemma cmp_pure_tops_eq : Bool.eqb (bn_neg ba) (bn_neg bb) = true -> bn_top bb = bn_top ba ->
    cmp_pure ba bb = (if cmp_words la lb =? 0 then 0 else if 0 <? cmp_words la lb then gtv else ltv)%Z.
  Proof.
    intros EN ET. unfold cmp_pure, gtv, ltv. rewrite EN. cbn [negb]. cbv zeta. rewrite ET, Nat.ltb_irrefl. reflexivity.
  Qed.

  Lemma bc_loop : forall (k : nat) m1 x8 x16 x17, BINV m1 -> (k <= bn_top ba)%nat ->
    Bool.eqb (bn_neg ba) (bn_neg bb) = true -> bn_top bb = bn_top ba ->
    cmp_words la lb = cmp_words (firstn k la) (firstn k lb) ->
    evt bgpsegs POST (ST 0xf6714 m1 x8 (Z_to_bv 64 gtv) (Z_to_bv 64 B) (Z_to_bv 64 A) (Z_to_bv 64 ltv)
                       (Z_to_bv 64 (Z.of_nat k + 1)) (Z_to_bv 64 (8 * Z.of_nat k + -8)) x16 x17).
  Proof.
    induction k as [|k IH]; intros m1 x8 x16 x17 I Hk EN ET E.
    - zstep. zstep. if_cases K; zify_cond K.
      + eapply bc_zero; [exact I|]. rewrite (cmp_pure_tops_eq EN ET), E. reflexivity.
      + exfalso. clear - K. lia.
    - pose proof I as (HA & HB & SA1 & SB1 & _).
      unfold bn_cells, wz in SA1, SB1.
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
      do 4 zstep.
      (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bgpsegs m1 Da la k x ad HA Ex ltac:(unfold wa; f_equal; clear; lia)) as RD); zstep; clear RD.
      (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bgpsegs m1 Db lb k y ad HB Ey ltac:(unfold wa; f_equal; clear; lia)) as RD); zstep; clear RD.
      pose proof (cmp_words_top la lb k x y ltac:(rewrite LLA, LLB; reflexivity) Ex Ey) as T.
      zstep. if_cases K2; zify_cond K2.
      {
        eapply bc_ret; [exact I|]. rewrite (cmp_pure_tops_eq EN ET), E, T. unfold cmp1.
        destruct (Z.eqb_spec x y) as [E0|_]; [exfalso; clear - E0 K2; lia|].
        replace (y <? x)%Z with true by (symmetry; apply Z.ltb_lt; exact K2). reflexivity. }
      zstep. zstep. if_cases K3; zify_cond K3.
      +
        assert (Exy : x = y) by (clear - K2 K3; lia).
        assert (E' : cmp_words la lb = cmp_words (firstn k la) (firstn k lb)).
        { rewrite E, T. destruct (Z.eqb_spec x y) as [_|]; [reflexivity | contradiction]. }
        setreg 14%Z (Z_to_bv 64 (Z.of_nat k + 1)) ltac:(f_equal; clear; lia).
        setreg 15%Z (Z_to_bv 64 (8 * Z.of_nat k + -8)) ltac:(f_equal; clear; lia).
        eapply IH; [exact I | clear - Hk; lia | exact EN | exact ET | exact E'].
      +
        zstep. zstep.
        eapply bc_ret; [exact I|]. rewrite (cmp_pure_tops_eq EN ET), E, T. unfold cmp1.
        destruct (Z.eqb_spec x y) as [E0|_]; [exfalso; clear - E0 K3; lia|].
        replace (y <? x)%Z with false by (symmetry; apply Z.ltb_ge; clear - K2; lia). reflexivity.
  Qed.

  Notation ST0 pc x10 x11 x12 x13 x14 x15 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 x15 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom bgpsegs)).

  Lemma bc_ret0 : forall res x11 x12 x13 x14 x15, res = cmp_pure ba bb ->
    evt bgpsegs POST (ST0 0xf66ec (Z_to_bv 64 res) x11 x12 x13 x14 x15).
  Proof.
    intros res x11 x12 x13 x14 x15 ->.
    pose proof (munch_refl [(SP - 16, SP)]%Z m) as MU. pose proof (wmono_refl bgpsegs m) as WM.
    zstep. finish.
  Qed.

  Lemma bc_ret1 : forall res x11 x12 x13 x14 x15, res = cmp_pure ba bb ->
    evt bgpsegs POST (ST0 0xf66d8 (Z_to_bv 64 res) x11 x12 x13 x14 x15).
  Proof.
    intros res x11 x12 x13 x14 x15 ->.
    pose proof (munch_refl [(SP - 16, SP)]%Z m) as MU. pose proof (wmono_refl bgpsegs m) as WM.
    zstep. finish.
  Qed.

  Lemma BN_cmp_spec :
    evt bgpsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 BN_CMP) fc None m (seg_rom bgpsegs)).
  Proof.
    unfold BN_CMP. subst a0 a1.
    pose proof (munch_refl [(SP - 16, SP)]%Z m) as MU. pose proof (wmono_refl bgpsegs m) as WM.
    pose proof SA as SA'. pose proof SB as SB'.
    unfold bn_cells in SA', SB'.
    pose proof OKA as (LMA & TDA & DMA & FLA). pose proof OKB as (LMB & TDB & DMB & FLB).
    assert (TA31 : (0 <= Z.of_nat (bn_top ba) < 8388608)%Z) by (clear - TDA DMA; unfold BN_WORDS_MAX, bn_dmax in *; lia).
    assert (TB31 : (0 <= Z.of_nat (bn_top bb) < 8388608)%Z) by (clear - TDB DMB; unfold BN_WORDS_MAX, bn_dmax in *; lia).
    assert (LLA : length la = bn_top ba) by (rewrite firstn_length_le; [reflexivity | clear - TDA; unfold bn_dmax in *; lia]).
    assert (LLB : length lb = bn_top bb) by (rewrite firstn_length_le; [reflexivity | clear - TDB; unfold bn_dmax in *; lia]).
    assert (NA : (0 <= Z.b2z (bn_neg ba) <= 1)%Z) by (destruct (bn_neg ba); cbn; lia).
    assert (NB : (0 <= Z.b2z (bn_neg bb) <= 1)%Z) by (destruct (bn_neg bb); cbn; lia).
    unfold wz in SA', SB'.
    pose proof (rw_cells_bound _ _ _ _ SA') as BA_. pose proof (rw_cells_bound _ _ _ _ SB') as BB_. cbn [cells_size csize Nat.add] in BA_, BB_.
    zstep.
    zstep. if_cases K; zify_cond K; [exfalso; clear - K A0; lia|]. clear K.
    zstep. if_cases K; zify_cond K; [exfalso; clear - K B0; lia|]. clear K.
    zstep. rewrite (sx32_small (Z.b2z (bn_neg ba))) by (clear - NA; lia).
    zstep. rewrite (sx32_small (Z.b2z (bn_neg bb))) by (clear - NB; lia).
    do 3 zstep.
    setreg 10%Z (Z_to_bv 64 gtv) ltac:(unfold gtv; destruct (bn_neg ba); apply Z_to_bv_eqm; vm_compute; reflexivity).
    zstep. if_cases K; zify_cond K.
    {
      eapply bc_ret0. unfold cmp_pure, gtv.
      replace (Bool.eqb (bn_neg ba) (bn_neg bb)) with false by (clear - K; destruct (bn_neg ba), (bn_neg bb); cbn in *; congruence).
      reflexivity. }
    assert (EN : Bool.eqb (bn_neg ba) (bn_neg bb) = true) by (clear - K; destruct (bn_neg ba), (bn_neg bb); cbn in *; congruence).
    zstep. rewrite (sx32_small (Z.of_nat (bn_top ba))) by (clear - TA31; lia).
    zstep. rewrite (sx32_small (Z.of_nat (bn_top bb))) by (clear - TB31; lia).
    zstep. rewrite lts_small by (clear - TA31 TB31; lia). if_cases K1; zify_cond K1.
    {
      eapply bc_ret0. unfold cmp_pure. rewrite EN. cbn [negb]. cbv zeta.
      replace (bn_top bb <? bn_top ba)%nat with true by (symmetry; apply Nat.ltb_lt; clear - K1; lia). reflexivity. }
    do 3 zstep.
    setreg 13%Z (Z_to_bv 64 ltv) ltac:(unfold ltv; destruct (bn_neg ba); apply Z_to_bv_eqm; vm_compute; reflexivity).
    zstep. rewrite lts_small by (clear - TA31 TB31; lia). if_cases K2; zify_cond K2.
    2:{
      zstep. eapply bc_ret1. unfold cmp_pure. rewrite EN. cbn [negb]. cbv zeta.
      replace (bn_top bb <? bn_top ba)%nat with false by (symmetry; apply Nat.ltb_ge; clear - K1; lia).
      replace (bn_top ba <? bn_top bb)%nat with true by (symmetry; apply Nat.ltb_lt; clear - K2; lia). reflexivity. }
    assert (ET : bn_top bb = bn_top ba) by (clear - K1 K2; lia).
    carve_frame 16%nat STK.
    do 4 zstep.
    assert (I : BINV m1).
    { unfold BINV. split; [|split].
      - eapply limbs_at_transport; [exact RA | exact MU | cbn [disjoint_from]; rewrite LLA; clear - SEPDA; lia].
      - eapply limbs_at_transport; [exact RB | exact MU | cbn [disjoint_from]; rewrite LLB; clear - SEPDB; lia].
      - split; [unfold bn_cells, wz; exact SA'|]. split; [unfold bn_cells, wz; exact SB'|]. split; [exact FR|]. split; [exact STK|]. split; [exact MI0|]. split; [exact MU | exact WM]. }
    clear RA RB FR STK MU WM.
    do 5 zstep.
    setreg 15%Z (Z_to_bv 64 (8 * Z.of_nat (bn_top ba) + -8))
      ltac:(f_equal; change 4294967295%Z with (Z.ones 32); rewrite Z.land_ones, Z.mod_small, Z.shiftl_mul_pow2 by (clear - TA31; lia); clear; lia).
    eapply bc_loop; [exact I | clear; lia | exact EN | exact ET |].
    rewrite ET, !firstn_firstn, Nat.min_id. reflexivity.
  Qed.
End Proofs.
