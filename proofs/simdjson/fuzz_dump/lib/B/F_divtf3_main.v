(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import F_f128_mul_core1 F_sf_helpers F_sf_helpers2 F_f128_mul F_f128_mul_top F_sf_helpers3 F_f128_div_wide F_f128_div_core1 F_f128_div_core2 F_f128_div_top.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import F_multf3_core F_multf3_tail F_multf3_norm F_divtf3 F_divtf3_core F_divtf3_wide F_divtf3_round F_divtf3_tail F_divtf3_norm.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import ImageA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= step_fast.
Local Ltac zsimp ::= zsimp_fast.

Section Walk.
  Variables (sp a0 a1 a2 a3 : word).
  Notation a_lo := (bv_unsigned a0). Notation a_hi := (bv_unsigned a1).
  Notation b_lo := (bv_unsigned a2). Notation b_hi := (bv_unsigned a3).
  Notation spw := (Z_to_bv 64 (bv_unsigned sp + -112)).
  Notation E_sgn := (Z.land (Z.shiftl (Z.shiftr (Z.lxor b_hi a_hi) 63) 63) 18446744073709551615).
  Notation E_aExp := (Z.shiftr (Z.land (Z.shiftl a_hi 1) 18446744073709551615) 49).
  Notation E_bExp := (Z.shiftr (Z.land (Z.shiftl b_hi 1) 18446744073709551615) 49).
  Notation E_aSig := (Z.land a_hi 281474976710655).
  Notation E_bSig := (Z.land b_hi 281474976710655).
  Notation E_aAbs := (Z.land a_hi 9223372036854775807).
  Notation E_bAbs := (Z.land b_hi 9223372036854775807).
  Notation MONE := (Z_to_bv 64 (-1)).
  Notation M48 := (Z_to_bv 64 281474976710655).
  Notation EXPK := (Z_to_bv 64 (-32767)).

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
    | H : (?a <= ?x < ?b)%Z |- (?a <= ?x < ?b)%Z => exact H
    | |- (_ <= _ <= _)%Z => lia
    | |- (0 <= _ < _)%Z => first [zrange2 | lia]
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
  Ltac res_words := rewrite ?lo64_mk128, ?hi64_mk128 by zrange; first [ apply Z_to_bv_lit_self | weq ].
  Ltac exact_HR0 :=
    lazymatch goal with |- ?g =>
      match goal with
      | HR : ?t |- _ => constr_eq t g; exact HR
      | HR : @eq Z ?r ?t |- _ => fail 0 "exact_HR: goal" g "but HR:" r "=" t
      end
    end.
  Ltac exact_HR := rewrite ?unsigned_lit by zrange; cbv delta [INF_HI QNAN_HI QUIET_HI]; exact_HR0.

  Lemma Lbchk : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (sc1 : Z) w3 w4
      y1 y8 y9 y13 y28' y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    y28' = Z_to_bv 64 sc1 ->
    mem_inv bsegs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono bsegs m m1 ->
    stk bsegs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells bsegs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (-600 <= sc1 <= 16)%Z ->
    R = FD_p2b a_hi b_lo b_hi (bv_unsigned w3) (bv_unsigned w4) sc1 ->
    evt bsegs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp (Z_to_bv 64 E_bSig) (Z_to_bv 64 E_aExp) (Z_to_bv 64 E_bExp) y8 y9
               w4 (Z_to_bv 64 E_sgn) a2 y13 (Z_to_bv 64 E_bAbs) MONE M48 w3
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28' y29 y30 y31)
          F (Z_to_bv 64 0x15508c) fc None m1 (seg_rom bsegs)).
  Proof.
    intros until R. intros -> MI MU WM ST FR SPLO Rsc HR.
    pose_word_ranges.
    assert (Ra : 0 <= E_aExp < 32768).
    { rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. zb_masks. Z.div_mod_to_equations. lia. }
    assert (Rb : 0 <= E_bExp < 32768).
    { rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. zb_masks. Z.div_mod_to_equations. lia. }
    unfold FD_p2b in HR. model_in HR.
    zstep. zstep. if_cases K; zify_cond K; decide_head HR.
    -
      join divtf3_core; exact_HR.
    - rewrite norm_denormal_eta in HR. cbn_bool_in HR.
      eapply LnormB; [zrange | lia |]. intros.
      pose proof (nd_clz_range E_bSig b_lo).
      pose proof (nd_hi_range E_bSig b_lo ltac:(zrange)). pose proof (nd_lo_range E_bSig b_lo).
      join divtf3_core; rewrite ?unsigned_lit by first [assumption | zrange]; exact_HR.
  Qed.

  Lemma Lp2r : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      y1 y8 y9 y13 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv bsegs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono bsegs m m1 ->
    stk bsegs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells bsegs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    R = FD_p2 a_lo a_hi b_lo b_hi ->
    evt bsegs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp (Z_to_bv 64 E_bSig) (Z_to_bv 64 E_aExp) (Z_to_bv 64 E_bExp) y8 y9
               a0 (Z_to_bv 64 E_sgn) a2 y13 (Z_to_bv 64 E_bAbs) MONE M48 (Z_to_bv 64 E_aSig)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 E_aAbs) y29 y30 y31)
          F (Z_to_bv 64 0x154dec) fc None m1 (seg_rom bsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO HR.
    pose_word_ranges.
    unfold FD_p2 in HR. model_in HR.
    zstep. zstep. if_cases K; zify_cond K; decide_head HR.
    -
      do 2 zstep. join Lbchk; [reflexivity | lia | exact_HR].
    - rewrite norm_denormal_eta in HR. cbn_bool_in HR.
      eapply LnormA; [zrange |]. intros.
      pose proof (nd_clz_range E_aSig a_lo).
      pose proof (nd_hi_range E_aSig a_lo ltac:(zrange)). pose proof (nd_lo_range E_aSig a_lo).
      join Lbchk; [reflexivity | lia | rewrite ?unsigned_lit by first [assumption | zrange]; exact_HR].
  Qed.

  Lemma Linfr : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      y1 y8 y9 y13 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv bsegs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono bsegs m m1 ->
    stk bsegs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells bsegs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    R = FD_inf a_lo a_hi b_lo b_hi ->
    evt bsegs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp (Z_to_bv 64 E_bSig) (Z_to_bv 64 E_aExp) (Z_to_bv 64 E_bExp) y8 y9
               a0 (Z_to_bv 64 E_sgn) a2 y13 (Z_to_bv 64 E_bAbs) MONE M48 (Z_to_bv 64 E_aSig)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 E_aAbs) y29 y30 y31)
          F (Z_to_bv 64 0x154c94) fc None m1 (seg_rom bsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO HR.
    pose_word_ranges.
    unfold FD_inf in HR. model_in HR.
    do 4 zstep. zstep. if_cases K7; zify_cond K7; decide_head HR.
    -
      do 2 zstep. zstep. if_cases K9; zify_cond K9; decide_head HR.
      +
        zstep. zstep. if_cases K11; zify_cond K11; decide_head HR.
        *   zstep. zstep. if_cases K12; zify_cond K12; decide_head HR.
          -- join Lzero; exact_HR.
          -- do 3 zstep. join Lzero. all: zsimp; exact_HR.
        * zstep. zstep. if_cases K12; zify_cond K12; decide_head HR.
          --   join Linf; exact_HR.
          -- join Lp2r; exact_HR.
      +   join Lzero; exact_HR.
    -
      do 2 zstep. zstep. if_cases K8; zify_cond K8; decide_head HR.
      + join Linf; exact_HR.
      + subst R. do 4 zstep. join Lepi; res_words.
  Qed.

  Lemma Lbr : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      y1 y8 y9 y14 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv bsegs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono bsegs m m1 ->
    stk bsegs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells bsegs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    R = FD_b a_lo a_hi b_lo b_hi ->
    evt bsegs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp (Z_to_bv 64 E_bSig) (Z_to_bv 64 E_aExp) (Z_to_bv 64 E_bExp) y8 y9
               a0 (Z_to_bv 64 E_sgn) a2 a3 y14 MONE M48 (Z_to_bv 64 E_aSig)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 E_aAbs) (Z_to_bv 64 9223372036854775807) y30 y31)
          F (Z_to_bv 64 0x154c7c) fc None m1 (seg_rom bsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO HR.
    pose_word_ranges.
    unfold FD_b in HR. model_in HR.
    do 3 zstep. zstep. if_cases K5; zify_cond K5; decide_head HR.
    -
      zstep. zstep. if_cases K6; zify_cond K6; decide_head HR.
      +   join Linfr; exact_HR.
      + subst R. do 5 zstep. join Lepi; res_words.
    - zstep. zstep. if_cases K6; zify_cond K6; decide_head HR.
      +   subst R. do 5 zstep. join Lepi; res_words.
      + join Linfr; exact_HR.
  Qed.

  Lemma Lspec : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      y1 y8 y9 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv bsegs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono bsegs m m1 ->
    stk bsegs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells bsegs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    R = FD_a a_lo a_hi b_lo b_hi ->
    evt bsegs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp (Z_to_bv 64 E_bSig) (Z_to_bv 64 E_aExp) (Z_to_bv 64 E_bExp) y8 y9
               a0 (Z_to_bv 64 E_sgn) a2 a3 a1 MONE M48 (Z_to_bv 64 E_aSig)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0x154c60) fc None m1 (seg_rom bsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO HR.
    pose_word_ranges.
    unfold FD_a in HR. model_in HR.
    do 4 zstep. zstep. if_cases K3; zify_cond K3; decide_head HR.
    -
      zstep. zstep. if_cases K4; zify_cond K4; decide_head HR.
      + join Lbr; exact_HR.
      + subst R. do 4 zstep. join Lepi; res_words.
    - zstep. zstep. if_cases K4; zify_cond K4; decide_head HR.
      + subst R. do 4 zstep. join Lepi; res_words.
      + join Lbr; exact_HR.
  Qed.

  Lemma divtf3_walk : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte),
    stk bsegs m (bv_unsigned sp - 112) (bv_unsigned sp) ->
    mem_inv bsegs m ->
    (4096 <= bv_unsigned sp)%Z ->
    evt bsegs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                 (f128_div_w a_lo a_hi b_lo b_hi) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x154894) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros ST MI SPLO.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose_word_ranges.
    carve_frame 112%nat ST.
    remember (f128_div_w a_lo a_hi b_lo b_hi) as R eqn:HR.
    unfold f128_div_w in HR. model_in HR.
    do 14 zstep. do 16 zstep.
    rewrite <- (Z_to_bv_land64 (Z.shiftl (Z.shiftr (Z.lxor b_hi a_hi) 63) 63)).
    assert (Ra : 0 <= E_aExp < 32768).
    { rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. zb_masks. Z.div_mod_to_equations. lia. }
    assert (Rb : 0 <= E_bExp < 32768).
    { rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. zb_masks. Z.div_mod_to_equations. lia. }

    zstep. if_cases K1; zify_cond K1; decide_head HR.
    -   join Lspec; exact_HR.
    - unfold FD_0b in HR. model_in HR.
      zstep. zstep. if_cases K2; zify_cond K2; decide_head HR.
      + join Lspec; exact_HR.
      + zstep. join divtf3_core; exact_HR.
  Qed.
End Walk.

Theorem divtf3_spec : divtf3_stmt.
Proof.
  unfold divtf3_stmt. intros.
  rewrite f128_div_words by (pose_word_ranges; assumption).
  apply divtf3_walk; assumption.
Qed.
