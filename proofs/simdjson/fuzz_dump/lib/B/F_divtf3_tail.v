(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import F_f128_mul_core1 F_f128_mul F_sf_helpers3 F_f128_div_wide F_f128_div_core1 F_f128_div_core2.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import F_multf3_core F_multf3_tail F_divtf3 F_divtf3_core F_divtf3_wide F_divtf3_round.
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

  Ltac flag_join n G body K :=
    set (G := body);
    let w := getreg n in
    lazymatch w with Z_to_bv 64 ?e =>
      replace (Z_to_bv 64 e) with (Z_to_bv 64 G)
        by (subst G; first [ rewrite (proj2 (Z.eqb_eq _ _) K) | rewrite (proj2 (Z.eqb_neq _ _) K) ]; first [ reflexivity | f_equal; zeq ])
    end;
    let RG := fresh "R" G in assert (RG : 0 <= G < 18446744073709551616) by (subst G; apply zr_b2z).

  Lemma L6r : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wE q1Hi q1Lo resHi resLo aDHi aDLo bHi : Z)
      y1 y5 y8 y9 y10 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv bsegs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono bsegs m m1 ->
    stk bsegs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells bsegs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= q1Hi < 2^64)%Z -> (0 <= q1Lo < 2^64)%Z -> (0 <= resHi < 2^64)%Z -> (0 <= resLo < 2^64)%Z ->
    (0 <= aDHi < 2^64)%Z -> (0 <= aDLo < 2^64)%Z -> (0 <= bHi < 2^64)%Z ->
    (-100000 <= wE <= 32766)%Z ->
    R = DC6 sgn wE q1Hi q1Lo resHi resLo aDHi aDLo bHi bLo ->
    evt bsegs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp y5 (Z_to_bv 64 resLo) (Z_to_bv 64 resHi) y8 y9 y10 sgw w6 (Z_to_bv 64 bHi) (Z_to_bv 64 aDLo)
               (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 aDHi)
               y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 (Z_to_bv 64 q1Hi) (Z_to_bv 64 wE) (Z_to_bv 64 q1Lo) y31)
          F (Z_to_bv 64 0x154d28) fc None m1 (seg_rom bsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO R1 R2 R3 R4 R5 R6 R7 RwE HR.
    pose_word_ranges.
    zstep. if_cases K; zify_cond K; sgn_cond K.
    -
      do 2 zstep. if_cases K2; zify_cond K2; signed_lits_in K2.
      + join Lzero. rewrite HR. apply DC6_tiny. lia.
      + do 6 zstep. rewrite !subw_amt by lia. unland. rewrite !landM32_id by lia.
        zstep. if_cases K3; zify_cond K3; sgn_cond K3.
        *
          do 5 zstep. unland.
          model_reg 10 absLo (Z.lor (Z.shiftr q1Lo (Z.land (1 - wE) 63))
                                   (Z.land (Z.shiftl (Z.land (Z.shiftl q1Hi 1) 18446744073709551615) (Z.land (Z.lxor (1 - wE) 18446744073709551615) 63)) 18446744073709551615)).
          rng absLo.
          zstep. unland. model_reg 15 absHi0 (Z.shiftr q1Hi (Z.land (1 - wE) 63)). rng absHi0.
          zstep. rewrite !signed_of_Z by lia. do 3 zstep. rewrite !landM32_id by lia.
          zstep. rewrite (srai63_mask (1 - wE + -64)) by lia. decide_ifs. rewrite land_ones_l by zrange2.
          zstep. if_cases K4; zify_cond K4; sgn_cond K4.
          --
             do 5 zstep. unland. model_reg 17 aSHi (Z.lor (Z.land (Z.shiftl aDHi (Z.land (wE + 112) 63)) 18446744073709551615)
                                   (Z.shiftr (Z.shiftr aDLo 1) (Z.land (Z.lxor (wE + 112) 18446744073709551615) 63))). rng aSHi.
              zstep. model_reg 14 aSLo0 (Z.land (Z.shiftl aDLo (Z.land (wE + 112) 63)) 18446744073709551615).
              zstep.
              zstep. model_reg 5 pb1 (Z.land (bLo * absHi0) 18446744073709551615).
              zstep. model_reg 6 pb2 (Z.shiftr (bLo * absLo) 64). mulhu_rng pb2.
              zstep. model_reg 7 pb3 (Z.land (bHi * absLo) 18446744073709551615).
              zstep. rewrite !signed_of_Z by lia. rewrite (srai63_mask (wE + 48)) by lia. decide_ifs. rewrite land_ones_l by zrange2. model_reg 14 aSLo aSLo0.
              zstep. model_reg 16 qbLo (Z.land (bLo * absLo) 18446744073709551615).
              zstep. model_reg 6 qh1 (Z.land (pb2 + pb3) 18446744073709551615).
              zstep. model_reg 7 qb2Lo (Z.land (Z.shiftl qbLo 1) 18446744073709551615).
              zstep. model_reg 5 qbHi (Z.land (qh1 + pb1) 18446744073709551615).
              zstep. model_reg 6 bor (Z.b2z (aSLo <? qb2Lo)).
              zstep. model_reg 17 d1 (Z.land (aSHi - bor) 18446744073709551615).
              do 3 zstep. model_reg 16 qb2Hi (Z.lor (Z.land (Z.shiftl qbHi 1) 18446744073709551615) (Z.shiftr qbLo 63)).
              zstep. model_reg 16 r2Hi (Z.land (d1 - qb2Hi) 18446744073709551615).
              zstep. model_reg 14 r2Lo (Z.land (aSLo - qb2Lo) 18446744073709551615).
              zstep. model_reg 17 odd (Z.land absLo 1).
              zstep. model_reg 14 r3Lo (Z.land (odd + r2Lo) 18446744073709551615).
              zstep. model_reg 17 rc (Z.b2z (r3Lo <? odd)).
              zstep. model_reg 16 r3Hi (Z.land (r2Hi + rc) 18446744073709551615).
              zstep. if_cases K1; zify_cond K1; [ do 2 zstep | zstep ].
              all: flag_join 17%Z gt1 (Z.b2z (if r3Hi =? bHi then bLo <? r3Lo else bHi <? r3Hi)) K1.
              all: join Lround.
              all: rewrite HR, DC6_denorm by lia; cbv beta delta [DC6d]; sf_vocab; fold_dc6;
                   rewrite div_round_DRr; sf_vocab; fold_model_lets2; first [ reflexivity | decide_ifs; reflexivity ].
          --
             do 2 zstep. unland. model_reg 17 aSHi (Z.land (Z.shiftl aDLo (Z.land (wE + 112) 63)) 18446744073709551615). rng aSHi.
              zstep. change (Z.land (Z.shiftl aDLo (Z.land (wE + 112) 63)) 18446744073709551615) with aSHi.
              zstep.
              zstep. model_reg 5 pb1 (Z.land (bLo * absHi0) 18446744073709551615).
              zstep. model_reg 6 pb2 (Z.shiftr (bLo * absLo) 64). mulhu_rng pb2.
              zstep. model_reg 7 pb3 (Z.land (bHi * absLo) 18446744073709551615).
              zstep. rewrite !signed_of_Z by lia. rewrite (shr63_nonneg (wE + 48)), ?Z.land_0_l by lia.
              zstep. model_reg 16 qbLo (Z.land (bLo * absLo) 18446744073709551615).
              zstep. model_reg 6 qh1 (Z.land (pb2 + pb3) 18446744073709551615).
              zstep. model_reg 7 qb2Lo (Z.land (Z.shiftl qbLo 1) 18446744073709551615).
              zstep. model_reg 5 qbHi (Z.land (qh1 + pb1) 18446744073709551615).
              zstep. model_reg 6 bor (Z.b2z (0 <? qb2Lo)).
              zstep. model_reg 17 d1 (Z.land (aSHi - bor) 18446744073709551615).
              do 3 zstep. model_reg 16 qb2Hi (Z.lor (Z.land (Z.shiftl qbHi 1) 18446744073709551615) (Z.shiftr qbLo 63)).
              zstep. model_reg 16 r2Hi (Z.land (d1 - qb2Hi) 18446744073709551615).
              zstep. model_reg 14 r2Lo (Z.land (0 - qb2Lo) 18446744073709551615).
              zstep. model_reg 17 odd (Z.land absLo 1).
              zstep. model_reg 14 r3Lo (Z.land (odd + r2Lo) 18446744073709551615).
              zstep. model_reg 17 rc (Z.b2z (r3Lo <? odd)).
              zstep. model_reg 16 r3Hi (Z.land (r2Hi + rc) 18446744073709551615).
              zstep. if_cases K1; zify_cond K1; [ do 2 zstep | zstep ].
              all: flag_join 17%Z gt1 (Z.b2z (if r3Hi =? bHi then bLo <? r3Lo else bHi <? r3Hi)) K1.
              all: join Lround.
              all: rewrite HR, DC6_denorm by lia; cbv beta delta [DC6d]; sf_vocab; fold_dc6;
                   rewrite div_round_DRr; sf_vocab; fold_model_lets2; first [ reflexivity | decide_ifs; reflexivity ].
        *
          do 2 zstep. unland. model_reg 10 absLo (Z.shiftr q1Hi (Z.land (1 - wE) 63)). rng absLo.
          zstep. unland.
          zstep. rewrite !signed_of_Z by lia. do 3 zstep. rewrite !landM32_id by lia.
          zstep. rewrite (shr63_nonneg (1 - wE + -64)), ?Z.land_0_l by lia.
          zstep. if_cases K4; zify_cond K4; sgn_cond K4; [ | exfalso; lia ].
          do 5 zstep. unland. model_reg 17 aSHi (Z.lor (Z.land (Z.shiftl aDHi (Z.land (wE + 112) 63)) 18446744073709551615)
                                   (Z.shiftr (Z.shiftr aDLo 1) (Z.land (Z.lxor (wE + 112) 18446744073709551615) 63))). rng aSHi.
           zstep. model_reg 14 aSLo0 (Z.land (Z.shiftl aDLo (Z.land (wE + 112) 63)) 18446744073709551615).
           zstep.
           zstep. model_reg 5 pb1 (Z.land (bLo * 0) 18446744073709551615).
           zstep. model_reg 6 pb2 (Z.shiftr (bLo * absLo) 64). mulhu_rng pb2.
           zstep. model_reg 7 pb3 (Z.land (bHi * absLo) 18446744073709551615).
           zstep. rewrite !signed_of_Z by lia. rewrite (srai63_mask (wE + 48)) by lia. decide_ifs. rewrite land_ones_l by zrange2. model_reg 14 aSLo aSLo0.
           zstep. model_reg 16 qbLo (Z.land (bLo * absLo) 18446744073709551615).
           zstep. model_reg 6 qh1 (Z.land (pb2 + pb3) 18446744073709551615).
           zstep. model_reg 7 qb2Lo (Z.land (Z.shiftl qbLo 1) 18446744073709551615).
           zstep. model_reg 5 qbHi (Z.land (qh1 + pb1) 18446744073709551615).
           zstep. model_reg 6 bor (Z.b2z (aSLo <? qb2Lo)).
           zstep. model_reg 17 d1 (Z.land (aSHi - bor) 18446744073709551615).
           do 3 zstep. model_reg 16 qb2Hi (Z.lor (Z.land (Z.shiftl qbHi 1) 18446744073709551615) (Z.shiftr qbLo 63)).
           zstep. model_reg 16 r2Hi (Z.land (d1 - qb2Hi) 18446744073709551615).
           zstep. model_reg 14 r2Lo (Z.land (aSLo - qb2Lo) 18446744073709551615).
           zstep. model_reg 17 odd (Z.land absLo 1).
           zstep. model_reg 14 r3Lo (Z.land (odd + r2Lo) 18446744073709551615).
           zstep. model_reg 17 rc (Z.b2z (r3Lo <? odd)).
           zstep. model_reg 16 r3Hi (Z.land (r2Hi + rc) 18446744073709551615).
           zstep. if_cases K1; zify_cond K1; [ do 2 zstep | zstep ].
           all: flag_join 17%Z gt1 (Z.b2z (if r3Hi =? bHi then bLo <? r3Lo else bHi <? r3Hi)) K1.
           all: join Lround.
           all: rewrite HR, DC6_denorm by lia; cbv beta delta [DC6d]; sf_vocab; fold_dc6;
                rewrite div_round_DRr; sf_vocab; fold_model_lets2; first [ reflexivity | decide_ifs; reflexivity ].
    -
      assert (K' : 0 < wE) by (rewrite land_W64 in K0, K1; Z.div_mod_to_equations; lia). clear K0 K1.
      do 2 zstep. unland.
      model_reg 14 fracHi (Z.land q1Hi 281474976710655).
      do 4 zstep. unland. model_reg 15 absHi (Z.lor (Z.land (Z.shiftl wE 48) 18446744073709551615) fracHi). rng absHi.
      zstep. model_reg 16 r2Hi (Z.lor (Z.land (Z.shiftl resHi 1) 18446744073709551615) (Z.shiftr resLo 63)). rng r2Hi.
      zstep. model_reg 14 r2Lo (Z.land (Z.shiftl resLo 1) 18446744073709551615).
      zstep. model_reg 17 odd (Z.land q1Lo 1).
      zstep. model_reg 14 r3Lo (Z.land (odd + r2Lo) 18446744073709551615).
      zstep. model_reg 17 rc (Z.b2z (r3Lo <? odd)).
      zstep. model_reg 16 r3Hi (Z.land (r2Hi + rc) 18446744073709551615).
      zstep. if_cases K1; zify_cond K1; [ zstep | do 2 zstep ];
        flag_join 17%Z gt1 (Z.b2z (if r3Hi =? bHi then bLo <? r3Lo else bHi <? r3Hi)) K1;
        (join Lround;
         rewrite HR, DC6_normal, div_round_DRr by lia; unland;
         change (Z.land q1Hi 281474976710655) with fracHi;
         change (Z.lor (Z.land (Z.shiftl wE 48) 18446744073709551615) fracHi) with absHi;
         change (Z.lor (Z.land (Z.shiftl resHi 1) 18446744073709551615) (Z.shiftr resLo 63)) with r2Hi;
         change (Z.land (Z.shiftl resLo 1) 18446744073709551615) with r2Lo;
         fold_model_lets2; reflexivity).
  Time Qed.

  Lemma L5r : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (w4 : word) (expM1 q_hi q_lo aSigHiI bSigHiI aHi2 aLoTop a2Lo : Z)
      y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv bsegs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono bsegs m m1 ->
    stk bsegs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells bsegs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= q_hi < 2^64)%Z -> (0 <= q_lo < 2^64)%Z -> (0 <= aSigHiI < 2^64)%Z -> (0 <= bSigHiI < 2^64)%Z ->
    (0 <= aHi2 < 2^64)%Z -> (0 <= aLoTop < 2^64)%Z -> (0 <= a2Lo < 2^64)%Z ->
    (-20000 <= expM1 <= 60000)%Z ->
    R = divc_tail sgn expM1 q_hi q_lo (bv_unsigned w4) aSigHiI bSigHiI bLo aHi2 aLoTop a2Lo ->
    evt bsegs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp (Z_to_bv 64 expM1) (Z_to_bv 64 aLoTop) (Z_to_bv 64 aHi2) y8 y9 w4 sgw w6
               (Z_to_bv 64 bSigHiI) (Z_to_bv 64 a2Lo) (Z_to_bv 64 (Z.shiftr q_hi 49)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 aSigHiI)
               y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 (Z_to_bv 64 q_hi) (Z_to_bv 64 (expM1 + 1)) (Z_to_bv 64 q_lo) y31)
          F (Z_to_bv 64 0x154bec) fc None m1 (seg_rom bsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO R1 R2 R3 R4 R5 R6 R7 Rexp HR.
    pose_word_ranges.
    zstep. if_cases K; zify_cond K.
    -
      do 3 zstep. model_reg 28 q1Hi (Z.shiftr q_hi 1). rng q1Hi.
      zstep. model_reg 5 aTop (Z.land (Z.shiftl (bv_unsigned w4) 48) 18446744073709551615).
      zstep. model_reg 30 q1Lo (Z.lor (Z.shiftr q_lo 1) (Z.land (Z.shiftl q_hi 63) 18446744073709551615)). rng q1Lo.
      zstep. model_reg 14 pq1 (Z.land (q1Hi * bLo) 18446744073709551615).
      zstep. model_reg 15 pq2 (Z.land (q1Lo * bSigHiI) 18446744073709551615).
      zstep. model_reg 6 pq3 (Z.shiftr (q1Lo * bLo) 64). mulhu_rng pq3.
      zstep. model_reg 14 d1 (Z.land (aTop - pq1) 18446744073709551615).
      zstep. model_reg 5 qbLo (Z.land (q1Lo * bLo) 18446744073709551615).
      zstep. model_reg 15 sh (Z.land (pq3 + pq2) 18446744073709551615).
      zstep. model_reg 6 bor (Z.b2z (negb (qbLo =? 0))).
      zstep. model_reg 14 d2 (Z.land (d1 - sh) 18446744073709551615).
      zstep. model_reg 7 resHi (Z.land (d2 - bor) 18446744073709551615).
      zstep. model_reg 6 resLo (Z.land (0 - qbLo) 18446744073709551615).
      do 4 zstep. zstep. if_cases Kov; zify_cond Kov; signed_lits_in Kov.
      + rewrite <- (Z_to_bv_bv_unsigned w4). join L6r. all: try lia.
        rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. reflexivity.
      + join Linf. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. reflexivity.
    -
      assert (Rbit : 0 <= Z.shiftr q_hi 48 <= 1).
      { rewrite !Z.shiftr_div_pow2 in * by lia. Z.div_mod_to_equations. lia. }
      zstep. name_as bit112 (Z.shiftr q_hi 48).
      zstep. zstep. rewrite (ltb1_eqb0 bit112) by lia. model_reg 31 sh (Z.b2z (bit112 =? 0)).
      assert (Rsh' : 0 <= sh <= 1) by (cbv delta [sh]; destruct (bit112 =? 0); cbn; lia).
      zstep. rewrite (land63_id sh) by lia.
      zstep. zstep.
      assert (Hamt : Z.land (Z.lxor sh 63) 63 = Z.lxor sh 63) by (cbv delta [sh]; destruct (bit112 =? 0); reflexivity).
      rewrite Hamt.
      zstep. unland. model_reg 28 q1Hi (Z.lor (Z.land (Z.shiftl q_hi sh) 18446744073709551615) (Z.shiftr (Z.shiftr q_lo 1) (Z.lxor sh 63))). rng q1Hi.
      zstep. rewrite (land63_id sh) by lia. model_reg 30 q1Lo (Z.land (Z.shiftl q_lo sh) 18446744073709551615).
      zstep. if_cases Kb; zify_cond Kb.
      *
        zstep. model_reg 17 aDHi (Z.lor aHi2 aLoTop). rng aDHi.
        zstep. model_reg 10 aTop (Z.land (Z.shiftl (bv_unsigned w4) 49) 18446744073709551615).
        zstep. model_reg 15 pq2 (Z.land (q1Lo * bSigHiI) 18446744073709551615).
        zstep. model_reg 6 pq3 (Z.shiftr (q1Lo * bLo) 64). mulhu_rng pq3.
        zstep. model_reg 7 pq1 (Z.land (q1Hi * bLo) 18446744073709551615).
        zstep. model_reg 15 sh2 (Z.land (pq3 + pq2) 18446744073709551615).
        zstep. model_reg 6 qbLo (Z.land (q1Lo * bLo) 18446744073709551615).
        zstep. model_reg 10 d1 (Z.land (aTop - sh2) 18446744073709551615).
        zstep. model_reg 15 bor (Z.b2z (negb (qbLo =? 0))).
        zstep. model_reg 6 resLo (Z.land (0 - qbLo) 18446744073709551615).
        zstep. model_reg 10 d2 (Z.land (d1 - pq1) 18446744073709551615).
        zstep. model_reg 7 resHi (Z.land (d2 - bor) 18446744073709551615).
        do 4 zstep. zstep. if_cases Kov; zify_cond Kov; signed_lits_in Kov.
        +   join Linf. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. reflexivity.
        + zstep. join L6r. all: try lia. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. f_equal; lia.
      *
        zstep.
        zstep. model_reg 17 aDHi (Z.lor aHi2 aLoTop). rng aDHi.
        zstep. model_reg 10 aTop (Z.land (Z.shiftl (bv_unsigned w4) 49) 18446744073709551615).
        zstep. model_reg 15 pq2 (Z.land (q1Lo * bSigHiI) 18446744073709551615).
        zstep. model_reg 6 pq3 (Z.shiftr (q1Lo * bLo) 64). mulhu_rng pq3.
        zstep. model_reg 7 pq1 (Z.land (q1Hi * bLo) 18446744073709551615).
        zstep. model_reg 15 sh2 (Z.land (pq3 + pq2) 18446744073709551615).
        zstep. model_reg 6 qbLo (Z.land (q1Lo * bLo) 18446744073709551615).
        zstep. model_reg 10 d1 (Z.land (aTop - sh2) 18446744073709551615).
        zstep. model_reg 15 bor (Z.b2z (negb (qbLo =? 0))).
        zstep. model_reg 6 resLo (Z.land (0 - qbLo) 18446744073709551615).
        zstep. model_reg 10 d2 (Z.land (d1 - pq1) 18446744073709551615).
        zstep. model_reg 7 resHi (Z.land (d2 - bor) 18446744073709551615).
        do 4 zstep. zstep. if_cases Kov; zify_cond Kov; signed_lits_in Kov.
        +   join Linf. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. reflexivity.
        + zstep. join L6r. all: try lia. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. f_equal; lia.
  Time Qed.

  Lemma divtf3_core : forall ra gp tp (w3 w4 w5 : word) (scale ea eb : Z) s0 s1 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 y1
      y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv bsegs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono bsegs m m1 ->
    stk bsegs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
    rw_cells bsegs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= ea < 32768)%Z -> (0 <= eb < 32768)%Z -> (-1024 <= scale <= 1024)%Z ->
    R = div_core sgn ea eb (bv_unsigned w3) (bv_unsigned w4) (bv_unsigned w5) bLo scale ->
    evt bsegs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR y1 spw gp tp w5 (Z_to_bv 64 ea) (Z_to_bv 64 eb) y8 y9 w4 sgw w6 a3 a4 a5 (Z_to_bv 64 281474976710655) w3
               y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 (Z_to_bv 64 scale) t4 t5 t6)
          F (Z_to_bv 64 0x15491c) fc None m1 (seg_rom bsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO Ra Rb Rsc HR.
    pose_word_ranges.
    eapply evt_cut. { eapply (divtf3_core12 w3 w4 w5 w6 ea eb scale); eauto. }
    intros ms' P.
    destruct P as (q_hi & q_lo & z1 & z8 & z9 & z18 & z19 & z20 & z21 & z22 & z23 & z24 & z25 & z26 & z27 & z31 & EQ & Rqh & Rql & ->).
    rewrite EQ in HR.
    eapply L5r; try eassumption; try exact HR.
    all: try (cbv beta delta [E_aSigHiI E_bSigHiI E_aHi2 E_aLoTop E_a2Lo]; zrange).
    cbv beta delta [E_expM1]. lia.
  Qed.
End Walk.
