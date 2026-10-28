(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_f128_mul_core1 F_sf_helpers F_sf_helpers2 F_f128_mul F_f128_mul_top.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_multf3_core F_multf3_tail F_multf3_norm F_divtf3.
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

Section Norm.
  Variables (sp : word).
  Notation spw := (Z_to_bv 64 (bv_unsigned sp + -112)).
  Notation M48 := (Z_to_bv 64 281474976710655).

  Ltac norm_tailA HQ E clz sh n32 hi lo :=
    let K2 := fresh "K2" in let E1 := fresh "E" in let E2 := fresh "E" in
    zstep; if_cases K2; zify_cond K2;
    [ do 5 zstep; do 5 zstep; rewrite (sra63_K_neg _ K2); zb_fold_lits; subst n32 sh;
      destruct (ndr_lt64 hi lo clz ltac:(zrange) ltac:(zrange) ltac:(assumption) E K2) as [E1 E2];
      rewrite <- E1, <- E2
    | do 2 zstep; do 5 zstep; rewrite (sra63_K_pos _ K2); zb_fold_lits; subst n32 sh;
      destruct (ndr_ge64 hi lo clz ltac:(zrange) ltac:(zrange) ltac:(assumption) E K2) as [E1 E2];
      match type of E1 with _ = Z.land ?v _ => rewrite <- (Z_to_bv_land64 v) end;
      rewrite <- E1, <- E2 ];
    rewrite <- nd_clz_eq in E; rewrite <- E; eapply HQ.

  Lemma LnormA : forall (Q : machine_state -> Prop) ra gp tp t0 t1 t2 (h : Z) s0 s1 wlo a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m1 : word -> option byte),
    (0 <= h < 2^64)%Z ->
    (forall y8 y13 y29 y30 y31,
      evt usegs Q
        (MS (mkR ra spw gp tp t0 t1 t2 y8 s1 (Z_to_bv 64 (nd_lo h (bv_unsigned wlo))) a1 a2 y13 a4 a5 a6 (Z_to_bv 64 (nd_hi h (bv_unsigned wlo)))
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (16 - nd_clz h (bv_unsigned wlo))) y29 y30 y31)
            F (Z_to_bv 64 0xca564) fc None m1 (seg_rom usegs))) ->
    evt usegs Q
      (MS (mkR ra spw gp tp t0 t1 t2 s0 s1 wlo a1 a2 a3 a4 a5 a6 (Z_to_bv 64 h) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xca2cc) fc None m1 (seg_rom usegs)).
  Proof.
    intros until m1. intros Rh HQ.
    pose_word_ranges.
    do 2 zstep. zstep. if_cases K; zify_cond K.
    -
      set (x := bv_unsigned wlo).
  do 5 zstep. model_reg 28 x1 (Z.lor x (Z.shiftr x 1)).
  do 5 zstep. model_reg 28 x2 (Z.lor x1 (Z.shiftr x1 2)).
  do 8 zstep. model_reg 28 x3 (Z.lor x2 (Z.shiftr x2 4)).
  do 2 zstep. model_reg 28 x4 (Z.lor x3 (Z.shiftr x3 8)).
  do 2 zstep. model_reg 28 x5 (Z.lor x4 (Z.shiftr x4 16)).
  do 2 zstep. model_reg 28 x6 (Z.lor x5 (Z.shiftr x5 32)).
  do 1 zstep. model_reg 28 y (Z.lxor x6 18446744073709551615).
  do 4 zstep. model_reg 28 c1 (Z.land (y - (Z.land (Z.shiftr y 1) 6148914691236517205)) 18446744073709551615).
  do 6 zstep. model_reg 28 c2 (Z.land ((Z.land c1 3689348814741910323) + (Z.land (Z.shiftr c1 2) 3689348814741910323)) 18446744073709551615).
  do 4 zstep. model_reg 28 c3 (Z.land (Z.land (c2 + (Z.shiftr c2 4)) 18446744073709551615) 1085102592571150095).
  do 3 zstep. model_reg 28 c4 (Z.shiftr (Z.land (c3 * 72340172838076673) 18446744073709551615) 56).
      assert (Ec4 : c4 = clz64_mirror x). { symmetry. cbv delta [clz64_mirror]. sf_vocab. fold_model_lets. reflexivity. }
      zstep. decide_tests_b. change (Z.b2z true) with 1. zb_fold_lits.
      model_reg 13 clz (Z.lor (clz64_mirror x) 64).
      pose proof (clz128_hi_z h x K) as E. fold clz in E.
      zstep. model_reg 28 sh (Z.land (clz - 15) 18446744073709551615).
      do 2 zstep. model_reg 30 n32 (Z.land sh 4294967295).
      zstep. subst x. norm_tailA HQ E clz sh n32 h (bv_unsigned wlo).
    - zstep.
  do 5 zstep. model_reg 28 x1 (Z.lor h (Z.shiftr h 1)).
  do 5 zstep. model_reg 28 x2 (Z.lor x1 (Z.shiftr x1 2)).
  do 8 zstep. model_reg 28 x3 (Z.lor x2 (Z.shiftr x2 4)).
  do 2 zstep. model_reg 28 x4 (Z.lor x3 (Z.shiftr x3 8)).
  do 2 zstep. model_reg 28 x5 (Z.lor x4 (Z.shiftr x4 16)).
  do 2 zstep. model_reg 28 x6 (Z.lor x5 (Z.shiftr x5 32)).
  do 1 zstep. model_reg 28 y (Z.lxor x6 18446744073709551615).
  do 4 zstep. model_reg 28 c1 (Z.land (y - (Z.land (Z.shiftr y 1) 6148914691236517205)) 18446744073709551615).
  do 6 zstep. model_reg 28 c2 (Z.land ((Z.land c1 3689348814741910323) + (Z.land (Z.shiftr c1 2) 3689348814741910323)) 18446744073709551615).
  do 4 zstep. model_reg 28 c3 (Z.land (Z.land (c2 + (Z.shiftr c2 4)) 18446744073709551615) 1085102592571150095).
  do 3 zstep. model_reg 28 c4 (Z.shiftr (Z.land (c3 * 72340172838076673) 18446744073709551615) 56).
      assert (Ec4 : c4 = clz64_mirror h). { symmetry. cbv delta [clz64_mirror]. sf_vocab. fold_model_lets. reflexivity. }
      zstep. decide_tests_b. change (Z.b2z false) with 0. zb_fold_lits. rewrite Z.lor_0_r.
      model_reg 13 clz (clz64_mirror h).
      pose proof (clz128_hi_nz h (bv_unsigned wlo) K) as E. fold clz in E.
      zstep. model_reg 28 sh (Z.land (clz - 15) 18446744073709551615).
      do 2 zstep. model_reg 30 n32 (Z.land sh 4294967295).
      zstep. norm_tailA HQ E clz sh n32 h (bv_unsigned wlo).
  Qed.

  Ltac norm_tailB2 HQ E clz sh n32 hi lo sc1 :=
    let K2 := fresh "K2" in let E1 := fresh "E" in let E2 := fresh "E" in
    zstep; if_cases K2; zify_cond K2;
    [ do 5 zstep; do 6 zstep; rewrite (sra63_K_neg _ K2); zb_fold_lits; subst n32 sh;
      destruct (ndr_lt64 hi lo clz ltac:(zrange) ltac:(zrange) ltac:(assumption) E K2) as [E1 E2];
      rewrite <- E1, <- E2
    | do 2 zstep; do 6 zstep; rewrite (sra63_K_pos _ K2); zb_fold_lits; subst n32 sh;
      destruct (ndr_ge64 hi lo clz ltac:(zrange) ltac:(zrange) ltac:(assumption) E K2) as [E1 E2];
      match type of E1 with _ = Z.land ?v _ => rewrite <- (Z_to_bv_land64 v) end;
      rewrite <- E1, <- E2 ];
    replace (Z_to_bv 64 (clz + sc1 + -16)) with (Z_to_bv 64 (sc1 + clz - 16)) by (f_equal; lia);
    rewrite <- nd_clz_eq in E; rewrite <- E; eapply HQ.

  Lemma LnormB : forall (Q : machine_state -> Prop) ra gp tp (h : Z) t1 t2 (sc1 : Z) s0 s1 a0 a1 wlo a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6
      (F : bvmap 5 word) fc (m1 : word -> option byte),
    (0 <= h < 2^64)%Z -> (-1024 <= sc1 <= 1024)%Z ->
    (forall y8 y13 y14 y29 y30 y31,
      evt usegs Q
        (MS (mkR ra spw gp tp (Z_to_bv 64 (nd_hi h (bv_unsigned wlo))) t1 t2 y8 s1 a0 a1 (Z_to_bv 64 (nd_lo h (bv_unsigned wlo))) y13 y14 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (sc1 + nd_clz h (bv_unsigned wlo) - 16)) y29 y30 y31)
            F (Z_to_bv 64 0xc9df4) fc None m1 (seg_rom usegs))) ->
    evt usegs Q
      (MS (mkR ra spw gp tp (Z_to_bv 64 h) t1 t2 s0 s1 a0 a1 wlo a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 sc1) t4 t5 t6)
          F (Z_to_bv 64 0xca56c) fc None m1 (seg_rom usegs)).
  Proof.
    intros until m1. intros Rh Rsc HQ.
    pose_word_ranges.
    do 2 zstep. zstep. if_cases K; zify_cond K.
    -
      set (x := bv_unsigned wlo).
  do 5 zstep. model_reg 14 x1 (Z.lor x (Z.shiftr x 1)).
  do 5 zstep. model_reg 14 x2 (Z.lor x1 (Z.shiftr x1 2)).
  do 8 zstep. model_reg 14 x3 (Z.lor x2 (Z.shiftr x2 4)).
  do 2 zstep. model_reg 14 x4 (Z.lor x3 (Z.shiftr x3 8)).
  do 2 zstep. model_reg 14 x5 (Z.lor x4 (Z.shiftr x4 16)).
  do 2 zstep. model_reg 14 x6 (Z.lor x5 (Z.shiftr x5 32)).
  do 1 zstep. model_reg 14 y (Z.lxor x6 18446744073709551615).
  do 4 zstep. model_reg 14 c1 (Z.land (y - (Z.land (Z.shiftr y 1) 6148914691236517205)) 18446744073709551615).
  do 6 zstep. model_reg 14 c2 (Z.land ((Z.land c1 3689348814741910323) + (Z.land (Z.shiftr c1 2) 3689348814741910323)) 18446744073709551615).
  do 4 zstep. model_reg 14 c3 (Z.land (Z.land (c2 + (Z.shiftr c2 4)) 18446744073709551615) 1085102592571150095).
  do 3 zstep. model_reg 14 c4 (Z.shiftr (Z.land (c3 * 72340172838076673) 18446744073709551615) 56).
      assert (Ec4 : c4 = clz64_mirror x). { symmetry. cbv delta [clz64_mirror]. sf_vocab. fold_model_lets. reflexivity. }
      zstep. decide_tests_b. change (Z.b2z true) with 1. zb_fold_lits.
      model_reg 13 clz (Z.lor (clz64_mirror x) 64).
      pose proof (clz128_hi_z h x K) as E. fold clz in E.
      zstep. model_reg 14 sh (Z.land (clz - 15) 18446744073709551615).
      do 2 zstep. model_reg 30 n32 (Z.land sh 4294967295).
      zstep. subst x. norm_tailB2 HQ E clz sh n32 h (bv_unsigned wlo) sc1.
    - zstep.
  do 5 zstep. model_reg 14 x1 (Z.lor h (Z.shiftr h 1)).
  do 5 zstep. model_reg 14 x2 (Z.lor x1 (Z.shiftr x1 2)).
  do 8 zstep. model_reg 14 x3 (Z.lor x2 (Z.shiftr x2 4)).
  do 2 zstep. model_reg 14 x4 (Z.lor x3 (Z.shiftr x3 8)).
  do 2 zstep. model_reg 14 x5 (Z.lor x4 (Z.shiftr x4 16)).
  do 2 zstep. model_reg 14 x6 (Z.lor x5 (Z.shiftr x5 32)).
  do 1 zstep. model_reg 14 y (Z.lxor x6 18446744073709551615).
  do 4 zstep. model_reg 14 c1 (Z.land (y - (Z.land (Z.shiftr y 1) 6148914691236517205)) 18446744073709551615).
  do 6 zstep. model_reg 14 c2 (Z.land ((Z.land c1 3689348814741910323) + (Z.land (Z.shiftr c1 2) 3689348814741910323)) 18446744073709551615).
  do 4 zstep. model_reg 14 c3 (Z.land (Z.land (c2 + (Z.shiftr c2 4)) 18446744073709551615) 1085102592571150095).
  do 3 zstep. model_reg 14 c4 (Z.shiftr (Z.land (c3 * 72340172838076673) 18446744073709551615) 56).
      assert (Ec4 : c4 = clz64_mirror h). { symmetry. cbv delta [clz64_mirror]. sf_vocab. fold_model_lets. reflexivity. }
      zstep. decide_tests_b. change (Z.b2z false) with 0. zb_fold_lits. rewrite Z.lor_0_r.
      model_reg 13 clz (clz64_mirror h).
      pose proof (clz128_hi_nz h (bv_unsigned wlo) K) as E. fold clz in E.
      zstep. model_reg 14 sh (Z.land (clz - 15) 18446744073709551615).
      do 2 zstep. model_reg 30 n32 (Z.land sh 4294967295).
      zstep. norm_tailB2 HQ E clz sh n32 h (bv_unsigned wlo) sc1.
  Qed.
End Norm.
