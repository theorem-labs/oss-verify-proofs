(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import F_f128_mul_core1 F_sf_helpers F_f128_mul.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import F_multf3_core.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import ImageA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= step_fast.
Local Ltac zsimp ::= zsimp_fast.

Definition multf3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (R : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' (bv_unsigned sp - 80) (bv_unsigned sp).

Definition saved9 (s8 s7 s6 s5 s4 s3 s2 s1 s0 : word) (j : list byte) : list cell :=
  [CB 8 j; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0].

Lemma land_M32_small : forall x, 0 <= x < 4294967296 -> Z.land x 4294967295 = x.
Proof. intros. rewrite landM32_mod. apply Z.mod_small. lia. Qed.
Lemma land_ones_r : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros. rewrite land_W64. apply Z.mod_small. lia. Qed.
Lemma land_ones_l : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 x = x.
Proof. intros. rewrite Z.land_comm. apply land_ones_r. assumption. Qed.

Lemma sra63_neg : forall x, -2^63 <= x < 0 -> Z.shiftr (bv_signed (Z_to_bv 64 x)) 63 = -1.
Proof.
  intros x Hx. rewrite Z_to_bv_signed, bv_swrap_small.
  2:{ unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64 `div` 2) with (2^63). lia. }
  rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia.
Qed.
Lemma sra63_negw : forall x, 2^63 <= x < 2^64 -> Z.shiftr (bv_signed (Z_to_bv 64 x)) 63 = -1.
Proof.
  intros x Hx. replace (Z_to_bv 64 x) with (Z_to_bv 64 (x - 2^64)) by (apply Z_to_bv_eqm; Z.div_mod_to_equations; lia).
  apply sra63_neg. lia.
Qed.
Lemma sra63_pos : forall x, 0 <= x < 2^63 -> Z.shiftr (bv_signed (Z_to_bv 64 x)) 63 = 0.
Proof.
  intros x Hx. rewrite Z_to_bv_signed, bv_swrap_small.
  2:{ unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64 `div` 2) with (2^63). lia. }
  rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia.
Qed.
Lemma lxor_b2z_1 : forall b, Z.lxor (Z.b2z b) 1 = Z.b2z (negb b).
Proof. intros [|]; reflexivity. Qed.

Ltac zzr := zsimp; rewrite ?Z.add_0_r;
  try rewrite !land_sub_neg by alia;
  try rewrite !land_M32_small by alia;
  try rewrite !sra63_neg by alia; try rewrite !sra63_pos by alia;
  try rewrite !land_ones_l by (first [zrange | alia]);
  rewrite ?Z.land_0_l.
Ltac zrstep := step; zzr.

Lemma mfr_normal : forall s pe hh hl lh ll,
  0 < pe <= 131072 -> 0 <= hl < 2^64 ->
  mul_finish s pe hh hl lh ll =
  mul_round s (Z.lor (Z.land (pe ≪ 48) 18446744073709551615) (Z.land hh 281474976710655)) (Z.land hl 18446744073709551615) lh ll.
Proof.
  intros * Hpe Hhl. rewrite (land_ones_r hl) by lia. apply mf_normal. lia.
Qed.

Lemma mfr_caseA : forall s pe hh hl lh ll,
  -126 <= pe < -63 -> 0 <= hh < 2^64 -> 0 <= hl < 2^64 -> 0 <= lh < 2^64 -> 0 <= ll < 2^64 ->
  mul_finish s pe hh hl lh ll =
  mul_round s 0 (hh ≫ Z.land (1 - pe) 63)
    (Z.lor (Z.lor (Z.land (hh ≪ Z.land (pe + 127) 63) 18446744073709551615)
                  (Z.land ((hl ≫ 1) ≫ Z.land (Z.lxor (pe + 127) 18446744073709551615) 63) 18446744073709551615)) 0)
    (Z.lor (Z.lor (Z.land (hl ≪ Z.land (pe + 127) 63) 18446744073709551615) (Z.land (lh ≫ Z.land (1 - pe) 63) 18446744073709551615))
           (Z.b2z (0 <? Z.lor (Z.land (ll ≪ Z.land (pe + 127) 63) 18446744073709551615)
                               (Z.lor (Z.land (lh ≪ Z.land (pe + 127) 63) 18446744073709551615)
                                      (Z.land ((ll ≫ 1) ≫ Z.land (Z.lxor (pe + 127) 18446744073709551615) 63) 18446744073709551615))))).
Proof. intros * Hpe Hhh Hhl Hlh Hll. mf_pure. Qed.

Lemma mfr_caseB : forall s pe hh hl lh ll,
  pe = -63 -> 0 <= hh < 2^64 -> 0 <= hl < 2^64 -> 0 <= lh < 2^64 -> 0 <= ll < 2^64 ->
  mul_finish s pe hh hl lh ll =
  mul_round s 0 (hh ≫ Z.land (1 - pe) 63)
    (Z.lor (Z.land (hl ≪ Z.land (pe + 127) 63) 18446744073709551615) 0)
    (Z.lor (Z.lor 0 (Z.land (lh ≫ Z.land (1 - pe) 63) 18446744073709551615))
           (Z.b2z (0 <? Z.lor 0 (Z.land (ll ≪ Z.land (pe + 127) 63) 18446744073709551615)))).
Proof. intros * Hpe Hhh Hhl Hlh Hll. mf_pure. Qed.

Lemma mfr_caseC : forall s pe hh hl lh ll,
  -63 < pe <= 0 -> 0 <= hh < 2^64 -> 0 <= hl < 2^64 -> 0 <= lh < 2^64 -> 0 <= ll < 2^64 ->
  mul_finish s pe hh hl lh ll =
  mul_round s (Z.land (hh ≫ Z.land (1 - pe) 63) 18446744073709551615)
    (Z.lor (Z.land (hl ≫ Z.land (1 - pe) 63) 18446744073709551615)
           (Z.land (Z.land (hh ≪ 1) 18446744073709551615 ≪ Z.land (Z.lxor (1 - pe) 18446744073709551615) 63) 18446744073709551615))
    (Z.lor (Z.land (hl ≪ Z.land (pe + 127) 63) 18446744073709551615) (Z.land (lh ≫ Z.land (1 - pe) 63) 18446744073709551615))
    (Z.lor (Z.lor 0 (Z.lor (Z.land (ll ≫ Z.land (1 - pe) 63) 18446744073709551615)
                           (Z.land (Z.land (lh ≪ 1) 18446744073709551615 ≪ Z.land (Z.lxor (1 - pe) 18446744073709551615) 63) 18446744073709551615)))
           (Z.b2z (0 <? Z.lor 0 (Z.land (ll ≪ Z.land (pe + 127) 63) 18446744073709551615)))).
Proof. intros * Hpe Hhh Hhl Hlh Hll. mf_pure. Qed.

Section Walk.
  Variables (sp : word).
  Notation spw := (Z_to_bv 64 (bv_unsigned sp + -80)).

  Ltac hyp :=
    match goal with
    | H : mem_inv _ ?m |- mem_inv _ ?m => exact H
    | H : munch ?W ?m ?m' |- munch ?W ?m ?m' => exact H
    | H : wmono _ ?m ?m' |- wmono _ ?m ?m' => exact H
    | H : stk _ ?m ?lo ?hi |- stk _ ?m ?lo ?hi => exact H
    | H : rw_cells _ ?m ?A _ |- rw_cells _ ?m ?A _ => exact H
    | H : (?a <= ?b)%Z |- (?a <= ?b)%Z => exact H
    | H : bv_unsigned ?w = _ |- bv_unsigned ?w = _ => exact H
    | H : ?x = ?y |- ?x = ?y => exact H
    | H : ?x <> ?y |- ?x <> ?y => exact H
    | |- (0 <= _ < _)%Z => zrange2
    end.
  Ltac join L := eapply L; try hyp.

  Ltac model_in H := sf_model_in H.

  Ltac eblia := rewrite ?Z.shiftl_mul_pow2 in * by lia; blia.
  Ltac decide_in_cond H c :=
    match c with
    | context [Z.eqb ?x ?y] =>
        first [ rewrite (proj2 (Z.eqb_eq x y)) in H by (clear H; eblia) | rewrite (proj2 (Z.eqb_neq x y)) in H by (clear H; eblia) ]
    | context [Z.ltb ?x ?y] =>
        first [ rewrite (proj2 (Z.ltb_lt x y)) in H by (clear H; eblia) | rewrite (proj2 (Z.ltb_ge x y)) in H by (clear H; eblia) ]
    | context [Z.leb ?x ?y] =>
        first [ rewrite (proj2 (Z.leb_le x y)) in H by (clear H; eblia) | rewrite (proj2 (Z.leb_gt x y)) in H by (clear H; eblia) ]
    end.
  Ltac decide_head H :=
    cbn_bool_in H;
    lazymatch type of H with
    | _ = ?t => match t with context [if ?c then _ else _] => decide_in_cond H c end
    end;
    cbn_bool_in H.

  Lemma Lepi : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w0 w1
      y5 y6 y7 y8 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv bsegs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono bsegs m m1 ->
    stk bsegs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells bsegs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    Z_to_bv 64 (lo64 R) = w0 -> Z_to_bv 64 (hi64 R) = w1 ->
    evt bsegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp y5 y6 y7 y8 y9 w0 w1 y12 y13 y14 y15 y16 y17
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0x154170) fc None m1 (seg_rom bsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO H0 H1. unfold saved9 in FR.
    pose_word_ranges.
    do 11 zstep.
    release_frame FR ST (bv_unsigned sp).
    rewrite <- H0, <- H1. finish.
  Qed.

  Ltac res_words :=
    rewrite ?lo64_mk128, ?hi64_mk128 by zrange; weq.

  Lemma Linf : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (sgn : Z)
      y5 y6 y7 y8 y9 y10 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv bsegs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono bsegs m m1 ->
    stk bsegs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells bsegs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= sgn < 2^64)%Z ->
    R = mk128 (Z.lor sgn 9223090561878065152) 0 ->
    evt bsegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp y5 y6 y7 y8 y9 y10 (Z_to_bv 64 sgn) y12 y13 y14 y15 y16 y17
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0x153e90) fc None m1 (seg_rom bsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO Rs HR. subst R.
    do 5 zstep. join Lepi; res_words.
  Qed.

  Lemma Lup : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (rl rh1 : Z)
      y5 y6 y7 y8 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv bsegs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono bsegs m m1 ->
    stk bsegs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells bsegs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= rl < 2^64)%Z -> (0 <= rh1 < 2^64)%Z ->
    R = mk128 (Z.land (rh1 + Z.b2z (Z.land (rl + 1) 18446744073709551615 =? 0)) 18446744073709551615) (Z.land (rl + 1) 18446744073709551615) ->
    evt bsegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 rl) (Z_to_bv 64 rh1) y12 y13 y14 y15 y16 y17
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0x154164) fc None m1 (seg_rom bsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO R0 R1 HR. subst R.
    do 3 zstep. join Lepi; res_words.
  Qed.

  Lemma Ltie : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (rl rh1 lh2 ll2 : Z)
      y5 y6 y7 y8 y9 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv bsegs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono bsegs m m1 ->
    stk bsegs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells bsegs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= rl < 2^64)%Z -> (0 <= rh1 < 2^64)%Z -> (0 <= lh2 < 2^64)%Z -> (0 <= ll2 < 2^64)%Z ->
    R = (if Z.lor ll2 (Z.lxor lh2 9223372036854775808) =? 0
         then mk128 (Z.land (rh1 + Z.b2z (Z.land (rl + Z.land rl 1) 18446744073709551615 <? rl)) 18446744073709551615)
                    (Z.land (rl + Z.land rl 1) 18446744073709551615)
         else mk128 rh1 rl) ->
    evt bsegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 rl) (Z_to_bv 64 rh1) (Z_to_bv 64 ll2) (Z_to_bv 64 lh2) y14 y15 y16 y17
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0x153ed4) fc None m1 (seg_rom bsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO R0 R1 R2 R3 HR.
    do 4 zstep. zstep. if_cases K; zify_cond K.
    -   decide_head HR. subst R. join Lepi; res_words.
    - decide_head HR. subst R. do 7 zstep. join Lepi; res_words.
  Qed.

  Lemma Lrnd2 : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (rl rh lh2 ll2 sgn : Z)
      y5 y6 y7 y8 y9 y16 y17 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv bsegs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono bsegs m m1 ->
    stk bsegs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells bsegs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= rl < 2^64)%Z -> (0 <= rh < 2^64)%Z -> (0 <= lh2 < 2^64)%Z -> (0 <= ll2 < 2^64)%Z -> (0 <= sgn < 2^64)%Z ->
    lh2 <> 9223372036854775808 ->
    R = mul_round sgn rh rl lh2 ll2 ->
    evt bsegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 rl) (Z_to_bv 64 sgn) (Z_to_bv 64 ll2) (Z_to_bv 64 lh2) (Z_to_bv 64 rh)
               (Z_to_bv 64 9223372036854775808) y16 y17
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0x153ec4) fc None m1 (seg_rom bsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO R0 R1 R2 R3 R4 Kh HR.
    unfold mul_round in HR. model_in HR. decide_head HR.
    do 2 zstep. rewrite lxor_b2z_1. zstep.
    zstep. if_cases K; zify_cond K; rewrite zb_lxor_sign in K by lia.
    -   decide_head HR. join Lup.
    - decide_head HR. join Ltie.
  Qed.

  Lemma Lhalf : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (rl rh lh2 ll2 sgn : Z)
      y5 y6 y7 y8 y9 y16 y17 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv bsegs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono bsegs m m1 ->
    stk bsegs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells bsegs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= rl < 2^64)%Z -> (0 <= rh < 2^64)%Z -> (0 <= lh2 < 2^64)%Z -> (0 <= ll2 < 2^64)%Z -> (0 <= sgn < 2^64)%Z ->
    lh2 = 9223372036854775808 ->
    R = mul_round sgn rh rl lh2 ll2 ->
    evt bsegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 rl) (Z_to_bv 64 sgn) (Z_to_bv 64 ll2) (Z_to_bv 64 lh2) (Z_to_bv 64 rh)
               (Z_to_bv 64 9223372036854775808) y16 y17
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0x154158) fc None m1 (seg_rom bsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO R0 R1 R2 R3 R4 Kh HR.
    unfold mul_round in HR. model_in HR. decide_head HR.
    do 2 zstep.
    zstep. if_cases K; zify_cond K.
    -   decide_head HR. join Ltie.
    - decide_head HR. join Lup.
  Qed.

  Lemma Lfin : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (pe hh hl lh ll sgn : Z)
      y6 y8 y9 y10 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv bsegs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono bsegs m m1 ->
    stk bsegs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells bsegs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (-131072 <= pe < 32767)%Z -> (0 <= hh < 2^64)%Z -> (0 <= hl < 2^64)%Z -> (0 <= lh < 2^64)%Z -> (0 <= ll < 2^64)%Z ->
    (0 <= sgn < 2^64)%Z ->
    R = mul_finish sgn pe hh hl lh ll ->
    evt bsegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp (Z_to_bv 64 pe) y6 (Z_to_bv 64 (-16383)) y8 y9
               y10 (Z_to_bv 64 sgn) (Z_to_bv 64 ll) (Z_to_bv 64 lh) (Z_to_bv 64 hh)
               (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 281474976710655) (Z_to_bv 64 hl)
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0x153ea4) fc None m1 (seg_rom bsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO Rpe Rhh Rhl Rlh Rll Rsg HR.
    pose_word_ranges.
    destruct (Z.lt_ge_cases 0 pe) as [C1|C1].
    -
      rewrite mfr_normal in HR by lia.
      zrstep; if_decide. do 4 zrstep. do 2 zrstep. zrstep; if_cases K; zify_cond K.
      + join Lhalf.
      + join Lrnd2.
    - destruct (Z.lt_ge_cases pe (-126)) as [C2|C2].
      +
        rewrite mf_tiny in HR by lia. subst R.
        zrstep; if_decide. do 3 zrstep. zrstep; if_decide. do 2 zrstep. join Lepi; res_words.
      + zrstep; if_decide. do 3 zrstep. zrstep; if_decide. do 5 zrstep.
        destruct (Z.lt_total pe (-63)) as [C3|[C3|C3]].
        *
          rewrite mfr_caseA in HR by lia.
          zrstep; if_decide. do 7 zrstep. zrstep; if_decide. do 5 zrstep.
          do 7 zrstep. zrstep; if_decide. do 6 zrstep. zrstep; if_decide. do 7 zrstep.
          zrstep; if_cases K; zify_cond K.
          -- join Lrnd2.
          -- join Lhalf.
        *
          rewrite mfr_caseB in HR by lia.
          zrstep; if_decide. do 4 zrstep. zrstep; if_decide. do 8 zrstep. zrstep; if_decide.
          do 6 zrstep. zrstep; if_decide. do 7 zrstep.
          zrstep; if_cases K; zify_cond K.
          -- join Lrnd2.
          -- join Lhalf.
        *
          rewrite mfr_caseC in HR by lia.
          zrstep; if_decide. do 4 zrstep. zrstep; if_decide. do 8 zrstep. zrstep; if_decide.
          do 9 zrstep. zrstep; if_decide. do 5 zrstep. do 6 zrstep.
          zrstep; if_cases K; zify_cond K.
          -- join Lrnd2.
          -- join Lhalf.
  Qed.

  Lemma Ltail : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (es hh hl lh ll scale sgn : Z)
      y6 y8 y9 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv bsegs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono bsegs m m1 ->
    stk bsegs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells bsegs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= es < 65536)%Z -> (0 <= hh < 2^64)%Z -> (0 <= hl < 2^64)%Z -> (0 <= lh < 2^64)%Z -> (0 <= ll < 2^64)%Z ->
    (-1024 <= scale <= 1024)%Z -> (0 <= sgn < 2^64)%Z ->
    R = MC_tail sgn es hh hl lh ll scale ->
    evt bsegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp (Z_to_bv 64 es) y6 (Z_to_bv 64 (-16383)) y8 y9
               (Z_to_bv 64 scale) (Z_to_bv 64 sgn) (Z_to_bv 64 ll) (Z_to_bv 64 lh) (Z_to_bv 64 hh)
               (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 281474976710655) (Z_to_bv 64 hl)
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0x153de0) fc None m1 (seg_rom bsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO Res Rhh Rhl Rlh Rll Rsc Rsg HR.
    pose_word_ranges.
    unfold MC_tail in HR. model_in HR.
    do 3 zstep. replace (scale + -16383) with (scale - 16383) by lia.
    zstep. if_cases K1; zify_cond K1; decide_head HR.
    -
      do 3 zstep. zstep. if_cases K2; zify_cond K2; signed_lits_in K2; decide_head HR.
      + join Lfin. all: first [lia | exact HR].
      + join Linf.
    - do 12 zstep. zstep. if_cases K2; zify_cond K2; signed_lits_in K2; decide_head HR.
      + join Linf.
      + zstep. rewrite <- (Z_to_bv_land64 (Z.shiftl ll 1)). join Lfin. all: first [lia | exact HR].
  Qed.
End Walk.

Lemma multf3_core : forall ra sp gp tp w1 w2 s0 s1 (scale sgn ea eb : Z) w4 a3 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 t5 t6
    y8 y9 y18 y19 y20 y21 y22 y23 y24 y28
    (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
  y28 = Z_to_bv 64 (Z.shiftr (bv_unsigned w1) 32) ->
  mem_inv bsegs m1 ->
  munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono bsegs m m1 ->
  stk bsegs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
  rw_cells bsegs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
  (4096 <= bv_unsigned sp)%Z ->
  (0 <= ea < 32768)%Z -> (0 <= eb < 32768)%Z -> (-1024 <= scale <= 1024)%Z -> (0 <= sgn < 2^64)%Z ->
  R = mul_core sgn ea eb (bv_unsigned w1) (bv_unsigned w3) (bv_unsigned w2) (bv_unsigned w4) scale ->
  evt bsegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp (Z_to_bv 64 eb) w1 w2 y8 y9 (Z_to_bv 64 scale) (Z_to_bv 64 sgn) w4 a3 a4
             (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 281474976710655) (Z_to_bv 64 ea)
             y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 w3 t5 t6)
        F (Z_to_bv 64 0x153c54) fc None m1 (seg_rom bsegs)).
Proof.
  intros until R. intros Hy28 MI MU WM ST FR SPLO Ra Rb Rsc Rsg HR. subst y28 R.
  eapply evt_cut. { eapply multf3_core1; eauto. }
  intros ms' P.
  destruct P as (es & hh & hl & lh & ll & y5' & t1 & t2' & x8 & x9 & a5' & a6' & s2' & s3' & s4' & s5' & s6' & s7' & s8' & t3 & t4 & t5' & t6'
                  & EQ & Res & Rhh & Rhl & Rlh & Rll & E5 & Ea5 & Ea6 & Et2 & E).
  subst ms' y5' a5' a6' t2'. rewrite EQ.
  eapply Ltail; eauto.
Qed.
