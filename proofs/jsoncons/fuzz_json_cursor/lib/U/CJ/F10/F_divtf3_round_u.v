(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import SFModel.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.FA Require Import F_f128_mul_core1.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.FA Require Import F_f128_mul.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.FA Require Import F_sf_helpers3.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.FA Require Import F_f128_div_wide.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.FA Require Import F_f128_div_core1.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.FA Require Import F_f128_div_core2.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_multf3_core_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_multf3_tail_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_divtf3_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_divtf3_core_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_divtf3_wide_u.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= step_fast.
Local Ltac zsimp ::= zsimp_fast.

Definition saved12 (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) (j : list byte) : list cell :=
  [CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition DRr (signHi absHi absLo r3Hi r3Lo bHi bLo gt1 : Z) : Z :=
  let abs1Lo := add64 absLo gt1 in
  let b2Hi := shl64 bHi 1 in
  let ca := b2z (Z.ltb abs1Lo absLo) in
  let b3Hi0 := mulhu bLo 3 in
  let abs1Hi := add64 absHi ca in
  let b3Hi1 := add64 b3Hi0 bHi in
  let b3Hi := add64 b3Hi1 b2Hi in
  let ltInf1 := b2z (Z.ltb abs1Hi INF_HI) in
  let gt3 := b2z (if Z.eqb r3Hi b3Hi then Z.ltb (add64 (shl64 bLo 1) bLo) r3Lo else Z.ltb b3Hi r3Hi) in
  let inc2 := Z.land ltInf1 gt3 in
  let b5Hi0 := mulhu bLo 5 in
  let b5Hi1 := add64 b5Hi0 bHi in
  let b4Hi := shl64 bHi 2 in
  let abs2Lo := add64 abs1Lo inc2 in
  let cb := b2z (Z.ltb abs2Lo abs1Lo) in
  let abs2Hi := add64 abs1Hi cb in
  let b5Hi := add64 b5Hi1 b4Hi in
  let ltInf2 := b2z (Z.ltb abs2Hi INF_HI) in
  let gt5 := b2z (if Z.eqb r3Hi b5Hi then Z.ltb (add64 (shl64 bLo 2) bLo) r3Lo else Z.ltb b5Hi r3Hi) in
  let inc3 := Z.land ltInf2 gt5 in
  let resLo := add64 abs2Lo inc3 in
  let cc := b2z (Z.ltb resLo abs2Lo) in
  let resHi := Z.lor (add64 abs2Hi cc) signHi in
  mk128 resHi resLo.

Lemma div_round_DRr : forall s aH aL rH rL bH bL,
  div_round s aH aL rH rL bH bL =
  let odd := Z.land aL 1 in
  let r3Lo := add64 odd rL in
  let rc := b2z (Z.ltb r3Lo odd) in
  let r3Hi := add64 rH rc in
  DRr s aH aL r3Hi r3Lo bH bL (b2z (if Z.eqb r3Hi bH then Z.ltb bL r3Lo else Z.ltb bH r3Hi)).
Proof. reflexivity. Qed.

Lemma subw_amt : forall wE, -2^30 < wE < 2^30 ->
  bv_swrap 32 (1 - Z.land wE 18446744073709551615) = 1 - wE.
Proof.
  intros. rewrite land_W64. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2^32). change (2 ^ 32 `div` 2) with (2^31).
  Z.div_mod_to_equations. lia.
Qed.

Section IfLemmas.
  Context {T : Type}.
  Lemma if_ltb_t x y (A B : T) : x < y -> (if x <? y then A else B) = A.   Proof. intro; now rewrite (proj2 (Z.ltb_lt x y)). Qed.
  Lemma if_ltb_f x y (A B : T) : y <= x -> (if x <? y then A else B) = B.  Proof. intro; now rewrite (proj2 (Z.ltb_ge x y)). Qed.
  Lemma if_leb_t x y (A B : T) : x <= y -> (if x <=? y then A else B) = A. Proof. intro; now rewrite (proj2 (Z.leb_le x y)). Qed.
  Lemma if_leb_f x y (A B : T) : y < x -> (if x <=? y then A else B) = B.  Proof. intro; now rewrite (proj2 (Z.leb_gt x y)). Qed.
  Lemma if_eqb_t x y (A B : T) : x = y -> (if x =? y then A else B) = A.   Proof. intro; now rewrite (proj2 (Z.eqb_eq x y)). Qed.
  Lemma if_eqb_f x y (A B : T) : x <> y -> (if x =? y then A else B) = B.  Proof. intro; now rewrite (proj2 (Z.eqb_neq x y)). Qed.
  Lemma if_nltb_t x y (A B : T) : x < y -> (if negb (x <? y) then A else B) = B.   Proof. intro; now rewrite (proj2 (Z.ltb_lt x y)). Qed.
  Lemma if_nltb_f x y (A B : T) : y <= x -> (if negb (x <? y) then A else B) = A.  Proof. intro; now rewrite (proj2 (Z.ltb_ge x y)). Qed.
  Lemma if_nleb_t x y (A B : T) : x <= y -> (if negb (x <=? y) then A else B) = B. Proof. intro; now rewrite (proj2 (Z.leb_le x y)). Qed.
  Lemma if_nleb_f x y (A B : T) : y < x -> (if negb (x <=? y) then A else B) = A.  Proof. intro; now rewrite (proj2 (Z.leb_gt x y)). Qed.
  Lemma if_neqb_t x y (A B : T) : x = y -> (if negb (x =? y) then A else B) = B.   Proof. intro; now rewrite (proj2 (Z.eqb_eq x y)). Qed.
  Lemma if_neqb_f x y (A B : T) : x <> y -> (if negb (x =? y) then A else B) = A.  Proof. intro; now rewrite (proj2 (Z.eqb_neq x y)). Qed.
End IfLemmas.
Ltac decide_ifs ::=
  repeat (match goal with
  | |- context [if (?x <? ?y) then ?A else ?B] => first [rewrite (if_ltb_t x y A B) by lia | rewrite (if_ltb_f x y A B) by lia]
  | |- context [if negb (?x <? ?y) then ?A else ?B] => first [rewrite (if_nltb_t x y A B) by lia | rewrite (if_nltb_f x y A B) by lia]
  | |- context [if (?x <=? ?y) then ?A else ?B] => first [rewrite (if_leb_t x y A B) by lia | rewrite (if_leb_f x y A B) by lia]
  | |- context [if negb (?x <=? ?y) then ?A else ?B] => first [rewrite (if_nleb_t x y A B) by lia | rewrite (if_nleb_f x y A B) by lia]
  | |- context [if (?x =? ?y) then ?A else ?B] => first [rewrite (if_eqb_t x y A B) by lia | rewrite (if_eqb_f x y A B) by lia]
  | |- context [if negb (?x =? ?y) then ?A else ?B] => first [rewrite (if_neqb_t x y A B) by lia | rewrite (if_neqb_f x y A B) by lia]
  end).

Section Walk.
  Variables (sp sgw w6 : word).
  Notation spw := (Z_to_bv 64 (bv_unsigned sp + -112)).
  Notation sgn := (bv_unsigned sgw).
  Notation bLo := (bv_unsigned w6).

  Ltac hyp :=
    match goal with
    | H : mem_inv _ ?m |- mem_inv _ ?m => exact H
    | H : munch ?W ?m ?m' |- munch ?W ?m ?m' => exact H
    | H : wmono _ ?m ?m' |- wmono _ ?m ?m' => exact H
    | H : stk _ ?m ?lo ?hi |- stk _ ?m ?lo ?hi => exact H
    | H : rw_cells _ ?m ?A _ |- rw_cells _ ?m ?A _ => exact H
    | H : (?a <= ?b)%Z |- (?a <= ?b)%Z => exact H
    | H : (?a <= ?x < ?b)%Z |- (?a <= ?x < ?b)%Z => exact H
    | |- (_ <= _ <= _)%Z => lia
    | |- (0 <= _ < _)%Z => first [zrange2 | lia]
    end.
  Ltac join L := eapply L; try hyp.
  Ltac exact_HR :=
    lazymatch goal with |- ?g =>
      match goal with
      | HR : ?t |- _ => constr_eq t g; exact HR
      | HR : @eq Z ?r ?t |- _ => fail 0 "exact_HR: goal" g "but HR:" r "=" t
      end
    end.

  Lemma Lepi : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w0 w1
      y1 y5 y6 y7 y8 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv rsegs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells rsegs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    Z_to_bv 64 (lo64 R) = w0 -> Z_to_bv 64 (hi64 R) = w1 ->
    evt rsegs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp y5 y6 y7 y8 y9 w0 w1 y12 y13 y14 y15 y16 y17
               y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0xb1690) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO H0 H1. unfold saved12 in FR.
    pose_word_ranges.
    do 15 zstep.
    release_frame FR ST (bv_unsigned sp).
    rewrite <- H0, <- H1. finish.
  Qed.

  Lemma Lzero : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w1
      y1 y5 y6 y7 y8 y9 y10 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv rsegs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells rsegs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    R = mk128 (bv_unsigned w1) 0 ->
    evt rsegs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp y5 y6 y7 y8 y9 y10 w1 y12 y13 y14 y15 y16 y17
               y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0xb1458) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO HR.
    pose_word_ranges.
    do 2 zstep. join Lepi; subst R; rewrite ?lo64_mk128, ?hi64_mk128 by zrange; [reflexivity | apply Z_to_bv_bv_unsigned].
  Qed.

  Lemma Linf : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      y1 y5 y6 y7 y8 y9 y10 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv rsegs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells rsegs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    R = mk128 (Z.lor sgn INF_HI) 0 ->
    evt rsegs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp y5 y6 y7 y8 y9 y10 sgw y12 y13 y14 y15 y16 y17
               y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0xb1398) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO HR.
    pose_word_ranges.
    do 5 zstep. join Lepi; subst R; unfold INF_HI; rewrite ?lo64_mk128, ?hi64_mk128 by zrange; reflexivity.
  Qed.

  Ltac flag_join n G body K :=
    set (G := body);
    let w := getreg n in
    lazymatch w with Z_to_bv 64 ?e =>
      replace (Z_to_bv 64 e) with (Z_to_bv 64 G)
        by (subst G; first [ rewrite (proj2 (Z.eqb_eq _ _) K) | rewrite (proj2 (Z.eqb_neq _ _) K) ]; first [ reflexivity | f_equal; zeq ])
    end;
    let RG := fresh "R" G in assert (RG : 0 <= G < 18446744073709551616) by (subst G; apply zr_b2z).

  Lemma Lround : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (absHi absLo r3Hi r3Lo bHi : Z) (g1 : bool)
      y1 y5 y6 y7 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv rsegs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells rsegs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= absHi < 2^64)%Z -> (0 <= absLo < 2^64)%Z -> (0 <= r3Hi < 2^64)%Z -> (0 <= r3Lo < 2^64)%Z -> (0 <= bHi < 2^64)%Z ->
    R = DRr sgn absHi absLo r3Hi r3Lo bHi bLo (Z.b2z g1) ->
    evt rsegs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 absLo) sgw w6 (Z_to_bv 64 bHi) (Z_to_bv 64 r3Lo) (Z_to_bv 64 absHi) (Z_to_bv 64 r3Hi) (Z_to_bv 64 (Z.b2z g1))
               y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0xb15f8) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO R1 R2 R3 R4 R5 HR.
    pose_word_ranges.
    name_as gt1 (Z.b2z g1).
    zstep. model_reg 17 abs1Lo (Z.land (absLo + gt1) 18446744073709551615).
    do 3 zstep. model_reg 7 b2Hi (Z.land (Z.shiftl bHi 1) 18446744073709551615).
    zstep. model_reg 28 ca (Z.b2z (abs1Lo <? absLo)).
    zstep. zstep. model_reg 5 b3Hi0 (Z.shiftr (bLo * 3) 64). mulhu_rng b3Hi0.
    zstep. model_reg 15 abs1Hi (Z.land (absHi + ca) 18446744073709551615).
    zstep. model_reg 5 b3Hi1 (Z.land (b3Hi0 + bHi) 18446744073709551615).
    zstep. model_reg 6 b3Hi (Z.land (b3Hi1 + b2Hi) 18446744073709551615).
    zstep. model_reg 5 ltInf1 (Z.b2z (abs1Hi <? 9223090561878065152)).
    zstep. if_cases K2; zify_cond K2; [ do 3 zstep | do 2 zstep ];
      flag_join 6%Z gt3 (Z.b2z (if r3Hi =? b3Hi then Z.land (Z.land (Z.shiftl bLo 1) 18446744073709551615 + bLo) 18446744073709551615 <? r3Lo else b3Hi <? r3Hi)) K2;
      ( zstep; model_reg 5 inc2 (Z.land ltInf1 gt3);
        do 2 zstep; model_reg 6 b5Hi0 (Z.shiftr (bLo * 5) 64); mulhu_rng b5Hi0;
        zstep; model_reg 6 b5Hi1 (Z.land (b5Hi0 + bHi) 18446744073709551615);
        zstep; model_reg 7 b4Hi (Z.land (Z.shiftl bHi 2) 18446744073709551615);
        zstep; model_reg 13 abs2Lo (Z.land (abs1Lo + inc2) 18446744073709551615);
        zstep; model_reg 17 cb (Z.b2z (abs2Lo <? abs1Lo));
        zstep; model_reg 15 abs2Hi (Z.land (abs1Hi + cb) 18446744073709551615);
        zstep; model_reg 17 b5Hi (Z.land (b5Hi1 + b4Hi) 18446744073709551615);
        zstep; model_reg 10 ltInf2 (Z.b2z (abs2Hi <? 9223090561878065152));
        zstep; if_cases K3; zify_cond K3; [ do 3 zstep | do 2 zstep ] );
      flag_join 12%Z gt5 (Z.b2z (if r3Hi =? b5Hi then Z.land (Z.land (Z.shiftl bLo 2) 18446744073709551615 + bLo) 18446744073709551615 <? r3Lo else b5Hi <? r3Hi)) K3;
      ( zstep; model_reg 10 inc3 (Z.land ltInf2 gt5);
        zstep; model_reg 10 resLo (Z.land (abs2Lo + inc3) 18446744073709551615);
        zstep; model_reg 12 cc (Z.b2z (resLo <? abs2Lo));
        do 2 zstep; model_reg 11 resHi (Z.lor (Z.land (abs2Hi + cc) 18446744073709551615) sgn);
        assert (E : R = mk128 resHi resLo);
        [ rewrite HR; change (Z.b2z g1) with gt1; cbv beta delta [DRr]; sf_vocab;
          fold_model_lets2;
          repeat (first [ progress fold_model_lets2
                        | match goal with |- (let x := ?b in _) = _ =>
                            first [ change b with gt3 | change b with gt5 ] end ]);
          reflexivity
        | join Lepi; rewrite E; rewrite ?lo64_mk128, ?hi64_mk128 by zrange; reflexivity ] ).
  Time Qed.

End Walk.
