(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import ImageA.
Import ListNotations.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import SF_buildtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= step_fast.
Local Ltac zsimp ::= zsimp_fast.

Definition floatsitf_entry := 0x15042c%Z.

Definition floatsitf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (R : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'.

Local Ltac sitf_tail nM64 clz :=
  zstep; zstep; rewrite (srai63_word nM64) by lia; decide_tests_b;
  do 7 zstep; rewrite Z_to_bv_swrap32; rewrite (sext32_land64 (16414 - clz));
  name_as_by expW (sext32 (16414 - clz)) (apply sext32_range);
  zstep;
  match goal with |- context [Z_to_bv 64 (Z.shiftl ?x 48)] =>
    model_reg 15%Z expSh (Z.land (Z.shiftl x 48) W64) end;
  do 3 zstep.

Lemma floatsitf_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (i : Z),
  mem_inv asegs m ->
  bv_unsigned a0 = sext32 i ->
  evt asegs (floatsitf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_i32 i) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15042c) fc None m (seg_rom asegs)).
Proof.
  intros until i. intros MI U.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (Ra0 : (0 <= bv_unsigned a0 < 2^64)%Z) by apply (zr_word a0).
  unfold f128_of_i32. rewrite <- U.
  cbv beta delta [add64 sub64 shl64 not64 is_neg64 sra63 lo64 hi64 wrap64 b2z ONES64 IMPLICIT_HI]. zb_fold_lits.
  zstep. if_cases K0; zify_cond K0; decide_tests_b.
  -   zstep. zstep. sf_finish.
  -
    zstep. rewrite (sraiw31_word (bv_unsigned a0)) by lia.
    model_reg 11%Z s (Z.land (0 - Z.land (Z.shiftr (bv_unsigned a0) 31) 1) W64).
    do 7 zstep. rewrite Z_to_bv_swrap32. rewrite (sext32_land64 (Z.lxor (bv_unsigned a0) s - s)).
    name_as_by absW (sext32 (Z.lxor (bv_unsigned a0) s - s)) (apply sext32_range).

    wstep. model_reg_w 10%Z half (srliw absW 1).
    wstep. model_reg 11%Z x1 (Z.lor absW half).
    do 2 wstep. model_reg_w 11%Z x2 (Z.lor x1 (srliw x1 2)).
    do 2 wstep. model_reg_w 11%Z x3 (Z.lor x2 (srliw x2 4)).
    do 2 wstep. model_reg_w 11%Z x4 (Z.lor x3 (srliw x3 8)).
    do 2 wstep. model_reg_w 11%Z x5 (Z.lor x4 (srliw x4 16)).
    wstep. model_reg 11%Z y (Z.lxor x5 W64).
    do 5 wstep. model_reg 11%Z c1 (Z.land (y - Z.land (Z.shiftr y 1) 1431655765) W64).
    do 5 wstep. model_reg 11%Z c2 (Z.land (Z.land c1 858993459 + Z.land (Z.shiftr c1 2) 858993459) W64).
    do 7 wstep. model_reg 12%Z c3 (Z.land (Z.land (c2 + Z.shiftr c2 4) W64) 252645135).
    do 2 wstep. model_reg_w 12%Z c4 (srliw (Z.land (c3 * 16843009) W64) 24).
    replace (Z_to_bv 64 c4) with (Z_to_bv 64 (clz32_mirror absW)) by (f_equal; model_eval; reflexivity).
    name_as_by clz (clz32_mirror absW) (apply clz32_mirror_range).

    zstep. model_reg 13%Z e (Z.lxor clz 31).
    zstep. rewrite Z_to_bv_swrap32. rewrite (sext32_land64 (112 - e)).
    name_as_by shW (sext32 (112 - e)) (apply sext32_range).
    do 3 zstep. replace (Z_to_bv 64 (Z.land shW 4294967295)) with (Z_to_bv 64 (zext32 shW)) by reflexivity.
    name_as_by n (zext32 shW) (rewrite zext32_eq; pose proof (Z.mod_pos_bound shW 4294967296 ltac:(lia)); lia).
    zstep. model_reg 15%Z nM64 (Z.land (n - 64) W64).
    zstep. replace (Z_to_bv 64 (Z.land absW 4294967295)) with (Z_to_bv 64 (zext32 absW)) by reflexivity.
    name_as_by aZ (zext32 absW) (rewrite zext32_eq; pose proof (Z.mod_pos_bound absW 4294967296 ltac:(lia)); lia).
    zstep. if_cases K1; zify_cond K1; decide_tests_b.
    +
      zstep. zstep.
      name_as_by hi0 (Z.shiftr half (Z.land (Z.lxor n W64) 63))
        (change (inr64 (Z.shiftr half (Z.land (Z.lxor n W64) 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
      sitf_tail nM64 clz. sf_finish.
    +
      zstep. zstep.
      sitf_tail nM64 clz. sf_finish.
Qed.
