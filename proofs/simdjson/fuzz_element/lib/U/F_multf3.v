(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_f128_mul_core1 F_sf_helpers F_sf_helpers2 F_f128_mul F_f128_mul_top.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_multf3_core F_multf3_tail F_multf3_norm.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Image.
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
  Notation spw := (Z_to_bv 64 (bv_unsigned sp + -80)).
  Notation E_sgn := (Z.land (Z.shiftl (Z.shiftr (Z.lxor b_hi a_hi) 63) 63) 18446744073709551615).
  Notation E_aExp := (Z.shiftr (Z.land (Z.shiftl a_hi 1) 18446744073709551615) 49).
  Notation E_bExp := (Z.shiftr (Z.land (Z.shiftl b_hi 1) 18446744073709551615) 49).
  Notation E_aSig := (Z.land a_hi 281474976710655).
  Notation E_bSig := (Z.land b_hi 281474976710655).
  Notation E_aAbs := (Z.land a_hi 9223372036854775807).
  Notation E_bAbs := (Z.land b_hi 9223372036854775807).
  Notation ONES := (Z_to_bv 64 18446744073709551615).
  Notation M48 := (Z_to_bv 64 281474976710655).

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

  Lemma Lbchk : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (h1 sc1 : Z) w3
      y8 y9 y13 y18 y19 y20 y21 y22 y23 y24 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv usegs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono usegs m m1 ->
    stk usegs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells usegs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= h1 < 2^64)%Z -> (-600 <= sc1 <= 16)%Z ->
    R = FM_p2b a_hi b_lo b_hi h1 (bv_unsigned w3) sc1 ->
    evt usegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp (Z_to_bv 64 E_bExp) (Z_to_bv 64 h1) (Z_to_bv 64 E_bSig) y8 y9
               (Z_to_bv 64 sc1) (Z_to_bv 64 E_sgn) a2 y13 (Z_to_bv 64 E_bAbs) ONES M48 (Z_to_bv 64 E_aExp)
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 (Z_to_bv 64 (Z.shiftr h1 32)) w3 y30 y31)
          F (Z_to_bv 64 0xc9080) fc None m1 (seg_rom usegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO Rh1 Rsc HR.
    pose_word_ranges.
    assert (Ra : 0 <= E_aExp < 32768).
    { rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. zb_masks. Z.div_mod_to_equations. lia. }
    assert (Rb : 0 <= E_bExp < 32768).
    { rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. zb_masks. Z.div_mod_to_equations. lia. }
    unfold FM_p2b in HR. model_in HR.
    zstep. zstep. if_cases K; zify_cond K; decide_head HR.
    -
      join multf3_core. { rewrite unsigned_lit by lia. reflexivity. }
      rewrite !unsigned_lit by zrange. exact HR.
    - rewrite norm_denormal_eta in HR. cbn_bool_in HR.
      eapply LnormB; [zrange | lia |]. intros.
      pose proof (nd_clz_range E_bSig b_lo).
      pose proof (nd_hi_range E_bSig b_lo ltac:(zrange)). pose proof (nd_lo_range E_bSig b_lo).
      join multf3_core. { rewrite unsigned_lit by lia. reflexivity. }
      rewrite !unsigned_lit by assumption. exact HR.
  Qed.

  Lemma Lp2r : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      y8 y9 y13 y18 y19 y20 y21 y22 y23 y24 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv usegs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono usegs m m1 ->
    stk usegs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells usegs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    R = FM_p2 a_lo a_hi b_lo b_hi ->
    evt usegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp (Z_to_bv 64 E_bExp) (Z_to_bv 64 E_aSig) (Z_to_bv 64 E_bSig) y8 y9
               a0 (Z_to_bv 64 E_sgn) a2 y13 (Z_to_bv 64 E_bAbs) ONES M48 (Z_to_bv 64 E_aExp)
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 (Z_to_bv 64 (Z.shiftr E_aSig 32)) a0 (Z_to_bv 64 E_aAbs) y31)
          F (Z_to_bv 64 0xc8e68) fc None m1 (seg_rom usegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO HR.
    pose_word_ranges.
    unfold FM_p2 in HR. model_in HR.
    zstep. zstep. if_cases K; zify_cond K; decide_head HR.
    -
      do 2 zstep. join Lbchk. all: rewrite ?unsigned_lit by zrange; exact HR.
    - rewrite norm_denormal_eta in HR. cbn_bool_in HR.
      eapply LnormA; [zrange |]. intros.
      pose proof (nd_clz_range E_aSig a_lo).
      pose proof (nd_hi_range E_aSig a_lo ltac:(zrange)). pose proof (nd_lo_range E_aSig a_lo).
      join Lbchk. all: rewrite ?unsigned_lit by assumption; exact HR.
  Qed.

  Lemma Linfr : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      y8 y9 y13 y18 y19 y20 y21 y22 y23 y24 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv usegs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono usegs m m1 ->
    stk usegs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells usegs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    R = FM_inf a_lo a_hi b_lo b_hi ->
    evt usegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp (Z_to_bv 64 E_bExp) (Z_to_bv 64 E_aSig) (Z_to_bv 64 E_bSig) y8 y9
               a0 (Z_to_bv 64 E_sgn) a2 y13 (Z_to_bv 64 E_bAbs) ONES M48 (Z_to_bv 64 E_aExp)
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 (Z_to_bv 64 (Z.shiftr E_aSig 32)) a0 (Z_to_bv 64 E_aAbs) y31)
          F (Z_to_bv 64 0xc8d14) fc None m1 (seg_rom usegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO HR.
    pose_word_ranges.
    unfold FM_inf in HR. model_in HR.
    do 4 zstep. zstep. if_cases K7; zify_cond K7; decide_head HR.
    -
      do 2 zstep. zstep. if_cases K9; zify_cond K9; decide_head HR.
      +
        zstep. zstep. if_cases K11; zify_cond K11; decide_head HR.
        *   subst R. do 2 zstep. join Lepi; res_words.
        * zstep. zstep. if_cases K12; zify_cond K12; decide_head HR.
          -- subst R. do 2 zstep. join Lepi; res_words.
          -- join Lp2r.
      +
        zstep. zstep. if_cases K10; zify_cond K10; decide_head HR.
        * join Linf.
        * subst R. do 3 zstep. join Lepi; res_words.
    -
      zstep. zstep. if_cases K8; zify_cond K8; decide_head HR.
      + join Linf.
      + subst R. do 2 zstep. do 3 zstep. join Lepi; res_words.
  Qed.

  Lemma Lbr : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      y8 y9 y14 y18 y19 y20 y21 y22 y23 y24
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv usegs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono usegs m m1 ->
    stk usegs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells usegs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    R = FM_b a_lo a_hi b_lo b_hi ->
    evt usegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp (Z_to_bv 64 E_bExp) (Z_to_bv 64 E_aSig) (Z_to_bv 64 E_bSig) y8 y9
               a0 (Z_to_bv 64 E_sgn) a2 a3 y14 ONES M48 (Z_to_bv 64 E_aExp)
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 (Z_to_bv 64 (Z.shiftr E_aSig 32)) a0 (Z_to_bv 64 E_aAbs)
               (Z_to_bv 64 9223372036854775807))
          F (Z_to_bv 64 0xc8cfc) fc None m1 (seg_rom usegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO HR.
    pose_word_ranges.
    unfold FM_b in HR. model_in HR.
    do 3 zstep. zstep. if_cases K5; zify_cond K5; decide_head HR.
    -
      zstep. zstep. if_cases K6; zify_cond K6; decide_head HR.
      +   join Linfr.
      + subst R. do 5 zstep. join Lepi; res_words.
    - zstep. zstep. if_cases K6; zify_cond K6; decide_head HR.
      +   subst R. do 5 zstep. join Lepi; res_words.
      + join Linfr.
  Qed.

  Lemma Lspec : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      y8 y9 y18 y19 y20 y21 y22 y23 y24 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv usegs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono usegs m m1 ->
    stk usegs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells usegs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    R = FM_a a_lo a_hi b_lo b_hi ->
    evt usegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp (Z_to_bv 64 E_bExp) (Z_to_bv 64 E_aSig) (Z_to_bv 64 E_bSig) y8 y9
               a0 (Z_to_bv 64 E_sgn) a2 a3 a1 ONES M48 (Z_to_bv 64 E_aExp)
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 (Z_to_bv 64 (Z.shiftr E_aSig 32)) a0 y30 y31)
          F (Z_to_bv 64 0xc8ce0) fc None m1 (seg_rom usegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO HR.
    pose_word_ranges.
    unfold FM_a in HR. model_in HR.
    do 4 zstep. zstep. if_cases K3; zify_cond K3; decide_head HR.
    -
      zstep. zstep. if_cases K4; zify_cond K4; decide_head HR.
      + join Lbr.
      + subst R. do 4 zstep. join Lepi; res_words.
    - zstep. zstep. if_cases K4; zify_cond K4; decide_head HR.
      + subst R. do 4 zstep. join Lepi; res_words.
      + join Lbr.
  Qed.

  Lemma multf3_walk : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte),
    stk usegs m (bv_unsigned sp - 80) (bv_unsigned sp) ->
    mem_inv usegs m ->
    (4096 <= bv_unsigned sp)%Z ->
    evt usegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                 (f128_mul_w a_lo a_hi b_lo b_hi) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xc8a8c) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros ST MI SPLO.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose_word_ranges.
    carve_frame 80%nat ST.
    remember (f128_mul_w a_lo a_hi b_lo b_hi) as R eqn:HR.
    unfold f128_mul_w in HR. model_in HR.
    do 10 zstep. do 18 zstep.

    replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
    rewrite <- (Z_to_bv_land64 (Z.shiftl (Z.shiftr (Z.lxor b_hi a_hi) 63) 63)).
    assert (Ra : 0 <= E_aExp < 32768).
    { rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. zb_masks. Z.div_mod_to_equations. lia. }
    assert (Rb : 0 <= E_bExp < 32768).
    { rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. zb_masks. Z.div_mod_to_equations. lia. }
    zstep. if_cases K1; zify_cond K1; decide_head HR.
    -   join Lspec.
    - zstep. zstep. if_cases K2; zify_cond K2; decide_head HR.
      + join Lspec.
      + zstep. join multf3_core. { rewrite unsigned_lit by zrange. reflexivity. }
        all: rewrite ?unsigned_lit by zrange; exact HR.
  Qed.
End Walk.

Definition multf3_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte),
    stk usegs m (bv_unsigned sp - 80) (bv_unsigned sp) ->
    mem_inv usegs m ->
    (4096 <= bv_unsigned sp)%Z ->
    evt usegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                 (f128_mul (mk128 (bv_unsigned a1) (bv_unsigned a0)) (mk128 (bv_unsigned a3) (bv_unsigned a2))) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xc8a8c) fc None m (seg_rom usegs)).

Theorem multf3_spec : multf3_stmt.
Proof.
  unfold multf3_stmt. intros.
  rewrite f128_mul_words by (pose_word_ranges; assumption).
  apply multf3_walk; assumption.
Qed.
