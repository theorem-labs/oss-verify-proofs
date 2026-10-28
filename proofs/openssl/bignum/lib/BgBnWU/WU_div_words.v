(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnDivWords.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnArith BnNumBits BnDivW.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnW Require Import W_div_words.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnWU Require Import WU_num_bits_word.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition bn_div_words_uentry := 0x1032c8%Z.

Section Blocks.
  Variables (sp gp tp a0 a2 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variable POST : machine_state -> Prop.
  Variables dh dl : Z.
  Notation d := (bv_unsigned a2).
  Hypothesis Hd : (d = dh * 4294967296 + dl)%Z.
  Hypothesis Hdh : (2147483648 <= dh < 4294967296)%Z.
  Hypothesis Hdl : (0 <= dl < 4294967296)%Z.

  (* [comment removed for export] *)
  Notation DST pc mm x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 :=
    (MS (mkR (Z_to_bv 64 1061628) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 sp a2 x10 x11 x12 x13 x14 x15 x16 x17 x18 a0
             s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgusegs)).
  (* [comment removed for export] *)
  Notation RST pc mm hr lr ret flag x5 x6 x7 x16 x17 x28 x29 x30 x31 :=
    (DST pc mm x5 x6 x7 (Z_to_bv 64 hr) (Z_to_bv 64 dh) (Z_to_bv 64 ret) (Z_to_bv 64 dl) (Z_to_bv 64 4294967295) (Z_to_bv 64 flag)
         x16 x17 (Z_to_bv 64 lr) x28 x29 x30 x31).
  (* [comment removed for export] *)
  Notation KCE0 mm hr lr ret flag x31 :=
    (forall x6 x7 x28 x29 x30,
       evt bgusegs POST (RST 0x1033d4 mm hr lr ret flag (Z_to_bv 64 (dwQ hr lr d * dl)) x6 x7 (Z_to_bv 64 (dwQ hr lr d))
                           (Z_to_bv 64 (dwQ hr lr d * dh)) x28 x29 x30 x31)).

  Lemma dw_loop : forall (n : nat) q mm hr lr ret flag x29 x30 x31,
    (0 <= hr < d)%Z -> (0 <= lr < 18446744073709551616)%Z ->
    (q - dwQ hr lr d <= Z.of_nat n)%Z -> (dwQ hr lr d <= q - 1)%Z -> (q < 4294967296)%Z ->
    (0 <= q * dh <= hr)%Z -> (0 <= q * dl < 18446744073709551616)%Z -> (dh <= q * dh)%Z -> (dl <= q * dl)%Z ->
    KCE0 mm hr lr ret flag x31 ->
    evt bgusegs POST (RST 0x1033a8 mm hr lr ret flag (Z_to_bv 64 (q * dl)) (Z_to_bv 64 (Z.shiftr lr 32)) (Z_to_bv 64 (hr - (q - 1) * dh))
                        (Z_to_bv 64 q) (Z_to_bv 64 (q * dh)) (Z_to_bv 64 ((q - 1) * dl)) x29 x30 x31).
  Proof using All.
    induction n as [|n IH]; intros q mm hr lr ret flag x29 x30 x31 Hh Hl Hn HQ Hq Hqh Hql Hdh1 Hdl1 K.
    { exfalso. clear - Hn HQ. lia. }
    pose proof (zr_word a2) as RD. unfold inr64 in RD. change (2 ^ 64)%Z with 18446744073709551616%Z in RD.
    assert (P1 : (0 <= (q - 1) * dh <= hr)%Z) by (clear - Hqh Hdh1 Hdh; lia).
    assert (P2 : (0 <= (q - 1) * dl < 18446744073709551616)%Z) by (clear - Hql Hdl1 Hdl; lia).
    do 5 zstep.
    setreg 16%Z (Z_to_bv 64 (q - 1)) ltac:(f_equal; clear; lia).
    setreg 17%Z (Z_to_bv 64 ((q - 1) * dh)) ltac:(f_equal; clear; lia).
    setreg 5%Z (Z_to_bv 64 ((q - 1) * dl)) ltac:(f_equal; clear; lia).
    assert (HQ1 : (dwQ hr lr d <= q - 1 < 4294967296)%Z) by (clear - HQ Hq; lia).
    zstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *)
      rewrite (dwm_exit_hi hr lr d dh dl Hd Hdh Hdl Hh Hl (q - 1) HQ1 P1 K1). apply K. }
    do 4 zstep.
    zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      destruct (dwm_cont hr lr d dh dl Hd Hdh Hdl Hh Hl (q - 1) HQ1 P1 K1 K2) as (C1 & C2 & C3 & C4).
      setreg 7%Z (Z_to_bv 64 (hr - (q - 1 - 1) * dh)) ltac:(f_equal; clear; lia).
      setreg 28%Z (Z_to_bv 64 ((q - 1 - 1) * dl)) ltac:(f_equal; clear; lia).
      apply IH; [exact Hh | exact Hl | clear - Hn; lia | exact C1 | clear - Hq; lia | exact P1 | exact P2 | exact C3 | exact C4 | exact K].
    - (* [comment removed for export] *)
      rewrite (dwm_exit_lo hr lr d dh dl Hd Hdh Hdl Hh Hl (q - 1) HQ1 P1 K2). apply K.
  Qed.

  Lemma dw_first : forall q mm hr lr ret flag x5 x6 x7 x17 x28 x29 x30 x31,
    (0 <= hr < d)%Z -> (0 <= lr < 18446744073709551616)%Z ->
    (dwQ hr lr d <= q < 4294967296)%Z -> (0 <= q * dh <= hr)%Z -> (0 <= q * dl < 18446744073709551616)%Z ->
    KCE0 mm hr lr ret flag x31 ->
    evt bgusegs POST (RST 0x103374 mm hr lr ret flag x5 x6 x7 (Z_to_bv 64 q) x17 x28 x29 x30 x31).
  Proof using All.
    intros q mm hr lr ret flag x5 x6 x7 x17 x28 x29 x30 x31 Hh Hl HQ Hqh Hql K.
    pose proof (zr_word a2) as RD. unfold inr64 in RD. change (2 ^ 64)%Z with 18446744073709551616%Z in RD.
    do 4 zstep.
    zstep. if_cases K1; zify_cond K1.
    { rewrite (dwm_exit_hi hr lr d dh dl Hd Hdh Hdl Hh Hl q HQ Hqh K1). apply K. }
    do 3 zstep.
    zstep. if_cases K2; zify_cond K2.
    { rewrite (dwm_exit_lo hr lr d dh dl Hd Hdh Hdl Hh Hl q HQ Hqh K2). apply K. }
    destruct (dwm_cont hr lr d dh dl Hd Hdh Hdl Hh Hl q HQ Hqh K1 K2) as (C1 & C2 & C3 & C4).
    do 4 zstep.
    setreg 7%Z (Z_to_bv 64 (hr - (q - 1) * dh)) ltac:(f_equal; clear; lia).
    setreg 28%Z (Z_to_bv 64 ((q - 1) * dl)) ltac:(f_equal; clear; lia).
    apply (dw_loop (Z.to_nat (q - dwQ hr lr d))); [exact Hh | exact Hl | clear - C1; lia | exact C1 | clear - HQ; lia | exact Hqh | exact Hql | exact C3 | exact C4 | exact K].
  Qed.

  (* [comment removed for export] *)
  Lemma dw_round : forall mm hr lr ret flag x5 x6 x7 x16 x17 x28 x29 x30 x31,
    (0 <= hr < d)%Z -> (0 <= lr < 18446744073709551616)%Z ->
    KCE0 mm hr lr ret flag x31 ->
    evt bgusegs POST (RST 0x103360 mm hr lr ret flag x5 x6 x7 x16 x17 x28 x29 x30 x31).
  Proof using All.
    intros mm hr lr ret flag x5 x6 x7 x16 x17 x28 x29 x30 x31 Hh Hl K.
    pose proof (zr_word a2) as RD. unfold inr64 in RD. change (2 ^ 64)%Z with 18446744073709551616%Z in RD.
    do 2 zstep.
    zstep. if_cases K0; zify_cond K0.
    - destruct (dwm_q0 hr lr d dh dl Hd Hdh Hdl Hh Hl 4294967295%Z ltac:(intros _; reflexivity) ltac:(intros X; contradiction)) as (Q1 & Q2 & Q3).
      apply dw_first; [exact Hh | exact Hl | exact Q1 | exact Q2 | exact Q3 | exact K].
    - zstep. if_cases KZ; zify_cond KZ. { exfalso. clear - KZ Hdh. lia. }   (* [comment removed for export] *)
      zstep. rewrite divu64 by (clear - Hh RD Hdh; lia).
      destruct (dwm_q0 hr lr d dh dl Hd Hdh Hdl Hh Hl (hr / dh)%Z ltac:(intros X; contradiction) ltac:(intros _; reflexivity)) as (Q1 & Q2 & Q3).
      apply dw_first; [exact Hh | exact Hl | exact Q1 | exact Q2 | exact Q3 | exact K].
  Qed.

  (* [comment removed for export] *)
  Lemma dw_tail1 : forall mm hr lr ret x6 x7 x28 x29 x30 x31,
    (0 <= hr < d)%Z -> (0 <= lr < 18446744073709551616)%Z ->
    (forall x5 x6 x7 x16 x17,
       evt bgusegs POST (RST 0x103360 mm (dwH2 hr lr d) (dwL2 hr lr d) (Z.shiftl (dwQ hr lr d) 32) 1 x5 x6 x7 x16 x17 x28 x29 x30 x31)) ->
    evt bgusegs POST (RST 0x1033d4 mm hr lr ret 0 (Z_to_bv 64 (dwQ hr lr d * dl)) x6 x7 (Z_to_bv 64 (dwQ hr lr d))
                        (Z_to_bv 64 (dwQ hr lr d * dh)) x28 x29 x30 x31).
  Proof using All.
    intros mm hr lr ret x6 x7 x28 x29 x30 x31 Hh Hl K.
    pose proof (zr_word a2) as RD. unfold inr64 in RD. change (2 ^ 64)%Z with 18446744073709551616%Z in RD.
    destruct (dwm_Q_range hr lr d dh dl Hd Hdh Hdl Hh Hl) as (RQ & RQh & RQl).
    pose proof (dwm_tail hr lr d dh dl Hd Hdh Hdl Hh Hl) as T. cbv zeta in T. destruct T as (T1 & T2 & T3 & T4).
    pose proof (dwm_next hr lr d dh dl Hd Hdh Hdl Hh Hl) as N. cbv zeta in N. destruct N as (N1 & N2 & N3 & N4).
    set (Q := dwQ hr lr d) in *.
    do 6 zstep.
    rewrite (proj2 (Z.ltb_ge hr _) (proj2 T1)). change (Z.b2z false) with 0%Z.
    do 2 zstep.
    setreg 15%Z (Z_to_bv 64 Q) ltac:(f_equal; clear; lia).
    zstep. if_false.
    do 12 zstep.
    rewrite N1.
    setreg 18%Z (Z_to_bv 64 (dwL2 hr lr d)) ltac:(rewrite <- N2; apply Z_to_bv_mod64).
    apply K.
  Qed.

  (* [comment removed for export] *)
  Lemma dw_tail2 : forall mm hr lr ret x6 x7 x28 x29 x30 x31,
    (0 <= hr < d)%Z -> (0 <= lr < 18446744073709551616)%Z ->
    (forall x5 x6 x7 x17,
       evt bgusegs POST (RST 0x103428 mm hr lr ret (dwQ hr lr d) x5 x6 x7 (Z_to_bv 64 (dwQ hr lr d)) x17 x28 x29 x30 x31)) ->
    evt bgusegs POST (RST 0x1033d4 mm hr lr ret 1 (Z_to_bv 64 (dwQ hr lr d * dl)) x6 x7 (Z_to_bv 64 (dwQ hr lr d))
                        (Z_to_bv 64 (dwQ hr lr d * dh)) x28 x29 x30 x31).
  Proof using All.
    intros mm hr lr ret x6 x7 x28 x29 x30 x31 Hh Hl K.
    pose proof (zr_word a2) as RD. unfold inr64 in RD. change (2 ^ 64)%Z with 18446744073709551616%Z in RD.
    destruct (dwm_Q_range hr lr d dh dl Hd Hdh Hdl Hh Hl) as (RQ & RQh & RQl).
    pose proof (dwm_tail hr lr d dh dl Hd Hdh Hdl Hh Hl) as T. cbv zeta in T. destruct T as (T1 & _).
    set (Q := dwQ hr lr d) in *.
    do 6 zstep.
    rewrite (proj2 (Z.ltb_ge hr _) (proj2 T1)). change (Z.b2z false) with 0%Z.
    do 2 zstep.
    setreg 15%Z (Z_to_bv 64 Q) ltac:(f_equal; clear; lia).
    zstep. if_true.
    apply K.
  Qed.

  (* [comment removed for export] *)
  Lemma dw_rounds : forall mm h l x5 x6 x7 x16 x17 x28 x29 x30 x31,
    (0 <= h < d)%Z -> (0 <= l < 18446744073709551616)%Z ->
    (forall x5 x6 x7 x16 x17 x28 x29 x30,
       evt bgusegs POST (RST 0x103428 mm (dwH2 h l d) (dwL2 h l d) (Z.shiftl (dwQ h l d) 32) (dwQ (dwH2 h l d) (dwL2 h l d) d)
                           x5 x6 x7 x16 x17 x28 x29 x30 x31)) ->
    evt bgusegs POST (RST 0x103360 mm h l 0 0 x5 x6 x7 x16 x17 x28 x29 x30 x31).
  Proof using All.
    intros mm h l x5 x6 x7 x16 x17 x28 x29 x30 x31 Hh Hl K.
    pose proof (dwm_next h l d dh dl Hd Hdh Hdl Hh Hl) as N. cbv zeta in N. destruct N as (_ & _ & N3 & N4).
    apply dw_round; [exact Hh | exact Hl |]. intros y6 y7 y28 y29 y30.
    apply dw_tail1; [exact Hh | exact Hl |]. intros z5 z6 z7 z16 z17.
    apply dw_round; [exact N3 | exact N4 |]. intros u6 u7 u28 u29 u30.
    apply dw_tail2; [exact N3 | exact N4 |]. intros v5 v6 v7 v17.
    apply K.
  Qed.
End Blocks.

Definition dvw_upost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h l d : Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3' a4' a5' a6' a7' t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (div_words h l d)) a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bgusegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono bgusegs m m' /\ mem_inv bgusegs m'
    /\ stk bgusegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Lemma bn_div_words_uspec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  (9223372036854775808 <= bv_unsigned a2)%Z -> (bv_unsigned a0 < bv_unsigned a2)%Z ->
  stk bgusegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64)%Z -> mem_inv bgusegs m ->
  evt bgusegs (dvw_upost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1032c8) fc None m (seg_rom bgusegs)).
Proof.
  intros until lo. intros HD HH ST LO MI.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
  pose proof (zr_word a2) as RD. unfold inr64 in RD. change (2 ^ 64)%Z with 18446744073709551616%Z in RD.
  pose proof (zr_word a0) as RH. unfold inr64 in RH. change (2 ^ 64)%Z with 18446744073709551616%Z in RH.
  pose proof (zr_word a1) as RL. unfold inr64 in RL. change (2 ^ 64)%Z with 18446744073709551616%Z in RL.
  pose proof (zr_word sp) as RSP. unfold inr64 in RSP. change (2 ^ 64)%Z with 18446744073709551616%Z in RSP.
  pose proof (proj1 ST) as LO0.
  carve_frame 48%nat ST.
  do 7 zstep.
  zstep. if_cases K; zify_cond K. { exfalso. clear - K HD. lia. }
  do 5 zstep.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = (bv_unsigned sp + -48)%Z)
    by (apply inr64_unsigned_lit; unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; clear - LO LO0 RSP; lia).
  call BN_num_bits_word_uspec.
  { rewrite ESP. exact ST. }
  { rewrite ESP. clear - LO. lia. }
  { exact MI. }
  rewrite ESP in *.
  rewrite (num_bits_word_norm (bv_unsigned a2)) by (unfold BW; clear - HD RD; lia).
  do 3 zstep.
  zstep. if_false.   (* [comment removed for export] *)
  do 5 zstep.
  (* [comment removed for export] *)
  rewrite (proj2 (Z.ltb_lt _ _) HH). change (Z.b2z true + -1)%Z with 0%Z. change (0 mod 18446744073709551616)%Z with 0%Z.
  rewrite Z.land_0_l, Z.sub_0_r.
  (* [comment removed for export] *)
  zstep. if_true.
  do 7 zstep.
  destruct (dw_split (bv_unsigned a2) ltac:(clear - HD RD; lia)) as (Hd & Hdh & Hdl).
  eapply evt_eq;
    [ | eapply (dw_rounds sp gp tp a0 a2 s4 s5 s6 s7 s8 s9 s10 s11 F fc _ _ _ Hd Hdh Hdl x13 (bv_unsigned a0) (bv_unsigned a1)
                          x x0 x1 x7 x8 x9 x10 x11 x12); [ clear - RH HH; lia | exact RL | ] ].
  { rewrite !Z_to_bv_bv_unsigned. reflexivity. }
  intros y5 y6 y7 y16 y17 y28 y29 y30.
  assert (HH' : (0 <= bv_unsigned a0 < bv_unsigned a2)%Z) by (clear - RH HH; lia).
  pose proof (dwm_next _ _ _ _ _ Hd Hdh Hdl HH' RL) as N. cbv zeta in N. destruct N as (_ & _ & N3 & N4).
  destruct (dwm_Q_range _ _ _ _ _ Hd Hdh Hdl N3 N4) as (RQ2 & _ & _).
  zstep.
  rewrite <- (div_words_rounds (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2)) by (clear - HD RD HH' RL; lia).
  do 8 zstep.
  release_frame FR POST (bv_unsigned sp).
  finish.
Qed.

