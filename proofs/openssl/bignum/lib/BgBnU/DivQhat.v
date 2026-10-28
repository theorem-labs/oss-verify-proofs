(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnModel.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnArith.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import DivQhatPure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Ltac weqm := apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; unfold subw, addw, mulw, BW; Z.div_mod_to_equations; lia.

Section Blocks.
  Variables (ra sp gp tp t0 t1 t2 s1 a6 a7 s4 s5 s7 s8 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variable POST : machine_state -> Prop.
  Variables d0 d1 : Z.
  Hypothesis Hd0 : (9223372036854775808 <= d0 < 18446744073709551616)%Z.
  Hypothesis Hd1 : (0 <= d1 < 18446744073709551616)%Z.
  (* [comment removed for export] *)
  Variable c0 : list byte.   (* [comment removed for export] *)
  Variables (c1 c2 c3 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 : word).
  Notation FRAME :=
    [CB 8 c0; C8 c1; C8 c2; C8 c3; C8 (Z_to_bv 64 (d1 mod 4294967296)); C8 (Z_to_bv 64 4294967295); C8 (Z_to_bv 64 (Z.shiftr d1 32)); C8 c7; C8 c8; C8 c9;
     C8 c10; C8 c11; C8 c12; C8 c13; C8 c14; C8 c15; C8 c16; C8 c17; C8 c18; C8 c19; C8 c20; C8 c21; C8 c22; C8 c23; C8 c24; C8 c25;
     C8 c26; C8 c27; C8 c28; C8 c29; C8 c30; C8 c31].

  (* [comment removed for export] *)
  Notation QST pc mm x10 x11 x12 x13 x14 x15 xq xn1 xn2 :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -256)) gp tp t0 t1 t2 sp s1 x10 x11 x12 x13 x14 x15 a6 a7 (Z_to_bv 64 d1) xq s4 s5 xn2 s7 s8 s9 (Z_to_bv 64 d0) xn1 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgusegs)).

  Notation KQ mm v n2 :=
    (forall x10 x11 x12 x13 x14 x15 x19, evt bgusegs POST (QST 0x109d14 mm x10 x11 x12 x13 x14 x15 (Z_to_bv 64 v) x19 (Z_to_bv 64 n2))).

  (* [comment removed for export] *)
  Lemma qh_loop : forall (fuel : nat) mm q rem t2l t2h n2 x13 x14 x15,
    rw_cells bgusegs mm (bv_unsigned sp + -256) FRAME ->
    (0 <= q < 18446744073709551616)%Z -> (0 <= rem < 18446744073709551616)%Z ->
    (0 <= t2l < 18446744073709551616)%Z -> (0 <= t2h < 18446744073709551616)%Z -> (0 <= n2 < 18446744073709551616)%Z ->
    (rem <= t2h)%Z -> (18446744073709551616 <= rem + Z.of_nat fuel * d0 - d0)%Z ->
    KQ mm (qhat_corr fuel q rem t2l t2h n2 d0 d1) n2 ->
    evt bgusegs POST (QST 0x109cdc mm (Z_to_bv 64 t2l) (Z_to_bv 64 rem) (Z_to_bv 64 t2h) x13 x14 x15 (Z_to_bv 64 q)
                        (Z_to_bv 64 (addw rem d0)) (Z_to_bv 64 n2)).
  Proof.
    induction fuel as [|f IH]; intros mm q rem t2l t2h n2 x13 x14 x15 FR Hq Hrem Ht2l Ht2h Hn2 HT HF K.
    { exfalso. clear - HF Hrem Hd0. lia. }
    pose proof (addw_lit rem d0) as R1.
    assert (B820 : (t2h <> rem \/ n2 < t2l)%Z ->
              evt bgusegs POST (QST 0x109ce8 mm (Z_to_bv 64 t2l) (Z_to_bv 64 rem) (Z_to_bv 64 t2h) (Z_to_bv 64 q) x14 x15 (Z_to_bv 64 q)
                                  (Z_to_bv 64 (addw rem d0)) (Z_to_bv 64 n2))).
    { intros HC.
      remember (addw rem d0) as rem1 eqn:Erem1.
      zstep. if_cases K3; zify_cond K3.
      - (* [comment removed for export] *)
        do 2 zstep.
        rewrite (qhat_corr_exit2 f q rem t2l t2h n2 d0 d1 HT HC) in K by (rewrite <- Erem1; exact K3).
        setreg 19%Z (Z_to_bv 64 (subw q 1)) ltac:(clear; weqm).
        apply K.
      - (* [comment removed for export] *)
        do 6 zstep.
        rewrite (qhat_corr_cont f q rem t2l t2h n2 d0 d1 HT HC) in K by (rewrite <- Erem1; exact K3).
        pose proof (subw_lit q 1) as Rq'. pose proof (subw_lit t2l d1) as Rl'. pose proof (t2h_step_lit t2l t2h d1 Ht2h) as Rh'.
        setreg 19%Z (Z_to_bv 64 (subw q 1)) ltac:(clear; weqm).
        setreg 10%Z (Z_to_bv 64 (subw t2l d1)) ltac:(clear; weqm).
        setreg 12%Z (Z_to_bv 64 (if (t2l <? d1)%Z then subw t2h 1 else t2h)) ltac:(clear; destruct (t2l <? d1)%Z; cbn [Z.b2z]; weqm).
        setreg 11%Z (Z_to_bv 64 rem1) ltac:(clear - Erem1; subst rem1; weqm).
        setreg 27%Z (Z_to_bv 64 (addw rem1 d0)) ltac:(clear; weqm).
        rewrite <- Erem1 in K.
        remember (subw q 1) as q' eqn:Eq'. remember (subw t2l d1) as t2l' eqn:Et2l'.
        remember (if (t2l <? d1)%Z then subw t2h 1 else t2h) as t2h' eqn:Et2h'.
        zstep. if_cases K4; zify_cond K4.
        + (* [comment removed for export] *)
          eapply IH; try eassumption.
          clear - HF K3 Erem1 Hrem Hd0 R1. unfold addw in Erem1. rewrite BW_lit in Erem1.
          assert (rem1 = rem + d0)%Z by (Z.div_mod_to_equations; lia). lia.
        + (* [comment removed for export] *)
          do 2 zstep.
          rewrite (qhat_corr_exit0 f q' rem1 t2l' t2h' n2 d0 d1) in K by (clear - K4; lia).
          setreg 19%Z (Z_to_bv 64 q') ltac:(clear - Eq'; subst q'; weqm).
          apply K. }
    zstep.
    zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      apply B820. left. clear - K1. lia.
    - zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        zstep.
        rewrite (qhat_corr_exit1 (S f) q rem t2l t2h n2 d0 d1) in K by (clear - K1 K2; lia).
        apply K.
      + apply B820. right. clear - K2. lia.
  Qed.

  Lemma qh_block : forall mm q n1 n2 x11 x12 x13 x14 x15 x18,
    rw_cells bgusegs mm (bv_unsigned sp + -256) FRAME ->
    (0 <= q < 18446744073709551616)%Z -> (0 <= n1 < 18446744073709551616)%Z -> (0 <= n2 < 18446744073709551616)%Z ->
    (forall x10 x11 x12 x13 x14 x15 x19,
       evt bgusegs POST (QST 0x109d14 mm x10 x11 x12 x13 x14 x15
                           (Z_to_bv 64 (qhat_corr QHAT_FUEL q (subw n1 (mulw q d0)) ((d1 * q) mod BW) ((d1 * q) / BW) n2 d0 d1)) x19 (Z_to_bv 64 n2))) ->
    evt bgusegs POST (QST 0x109c74 mm (Z_to_bv 64 q) x11 x12 x13 x14 x15 x18 (Z_to_bv 64 n1) (Z_to_bv 64 n2)).
  Proof.
    intros mm q n1 n2 x11 x12 x13 x14 x15 x18 FR Hq Hn1 Hn2 K.
    do 2 zstep.
    zstep.
    do 4 zstep. zstep. zstep. zstep. do 11 zstep.
    pose proof (subw_lit n1 (mulw q d0)) as Rrem. pose proof (mod_BW_lit (d1 * q)) as Rl.
    pose proof (mul_hi_lit d1 q Hd1 Hq) as Rh.
    setreg 11%Z (Z_to_bv 64 (subw n1 (mulw q d0))) ltac:(clear; weqm).
    setreg 10%Z (Z_to_bv 64 ((d1 * q) mod BW)) ltac:(clear; weqm).
    setreg 12%Z (Z_to_bv 64 ((d1 * q) / BW)) ltac:(f_equal; rewrite (qh_t2h q d1 Hq Hd1); rewrite (Z.mul_comm d1 q); reflexivity).
    remember (subw n1 (mulw q d0)) as rem eqn:Erem. remember ((d1 * q) mod BW)%Z as t2l eqn:Et2l. remember ((d1 * q) / BW)%Z as t2h eqn:Et2h.
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      rewrite (qhat_corr_exit0 QHAT_FUEL q rem t2l t2h n2 d0 d1) in K by (clear - K0; lia).
      apply K.
    - do 4 zstep.
      setreg 27%Z (Z_to_bv 64 (addw rem d0)) ltac:(clear - Erem; subst rem; weqm).
      eapply (qh_loop QHAT_FUEL); try eassumption.
      clear - Hd0 Rrem. unfold QHAT_FUEL. lia.
  Qed.
End Blocks.
