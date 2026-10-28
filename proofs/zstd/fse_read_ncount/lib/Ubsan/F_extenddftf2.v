(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
Import ListNotations.
Open Scope bv_scope.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SF_buildtac.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.
Local Ltac step ::= step_fast.
Local Ltac zsimp ::= zsimp_fast.
Definition extenddftf2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [] m m' /\ wmono usegs m m' /\ mem_inv usegs m'.
Local Ltac extend_tail shM64 :=
zstep; zstep; rewrite (srai63_word shM64) by lia; decide_tests_b;
do 11 zstep.
Lemma extenddftf2_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
mem_inv usegs m ->
evt usegs (extenddftf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
(f128_of_d (bv_unsigned (reg_get F 10))) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1a1b4) fc None m (seg_rom usegs)).
Proof.
intros until m. intros MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
unfold f128_of_d.
cbv beta delta [add64 sub64 shl64 not64 is_neg64 sra63 lo64 hi64 wrap64 b2z ONES64 IMPLICIT_HI INF_HI]. zb_fold_lits.
Local Ltac2 Set LiaHints.tbl := fun () => "00N0>10336720952.3711447729963.6713168393118.4017114530413.4817122713556.3718032496357.6419620497060.4824040356596.4632969465626.7933392159193.5335027953801.8835027953801.9235027953802.5635497698861.4636024693271.7237654378318.7737658974283.8143713689867.8843713689867.9245859665771.7746286549312.8546286549312.8951521005083.6255888456068.4859552398415.7562231074346.5662231074346.8762231074346.9163357301334.487345754199.74 00000100I00N00O00P00Q00R00S00T00U00V00W00X00Y00Z00b00j00k00l00m00n00o01001101201301401501:01;FS5RaExp2K01H2H02H42H52H9S3RdwSSFFFSFFFFSFS6RshM64S6RshM64FFFFFFFFFFFS3RdwF".
zstep. remember (reg_get F 10) as dw eqn:Edw.
assert (Rdw : (0 <= bv_unsigned dw < 2^64)%Z) by apply (zr_word dw).
rewrite (land_W64_small (bv_unsigned dw)) by lia.
do 4 zstep. name_reg 12%Z aExp. name_reg 10%Z aSig.
zstep. if_cases K0; zify_cond K0; decide_tests_b.
-
zstep. if_cases K2; zify_cond K2; decide_tests_b.
+ do 6 zstep. sf_finish.
+
zstep. model_reg 12%Z half (Z.shiftr aSig 1).
do 5 zstep. model_reg 17%Z x1 (Z.lor aSig half).
do 6 zstep. model_reg 17%Z x2 (Z.lor x1 (Z.shiftr x1 2)).
do 10 zstep. model_reg 17%Z x3 (Z.lor x2 (Z.shiftr x2 4)).
do 2 zstep. model_reg 17%Z x4 (Z.lor x3 (Z.shiftr x3 8)).
do 2 zstep. model_reg 17%Z x5 (Z.lor x4 (Z.shiftr x4 16)).
do 2 zstep. model_reg 17%Z x6 (Z.lor x5 (Z.shiftr x5 32)).
zstep. model_reg 17%Z y (Z.lxor x6 W64).
do 3 zstep. model_reg 13%Z c1 (Z.land (y - Z.land (Z.shiftr y 1) 6148914691236517205) W64).
do 4 zstep. model_reg 13%Z c2 (Z.land (Z.land c1 3689348814741910323 + Z.land (Z.shiftr c1 2) 3689348814741910323) W64).
do 4 zstep. model_reg 13%Z c3 (Z.land (Z.land (c2 + Z.shiftr c2 4) W64) 1085102592571150095).
do 2 zstep. model_reg 13%Z c4 (Z.shiftr (Z.land (c3 * 72340172838076673) W64) 56).
replace (Z_to_bv 64 c4) with (Z_to_bv 64 (clz64_mirror aSig)) by (f_equal; model_eval; reflexivity).
name_as_by clz (clz64_mirror aSig) (apply clz64_mirror_range).
zstep. zstep. model_reg 16%Z shM64 (Z.land (clz - 15) W64).
zstep. model_reg 15%Z sh (Z.land (clz + 49) W64).
zstep. if_cases K3; zify_cond K3; decide_tests_b.
*
zstep. zstep. rewrite Z_to_bv_swrap32. rewrite (sext32_land64 (14 - clz)).
name_as_by t14 (sext32 (14 - clz)) (apply sext32_range).
zstep. name_as_by hi0 (Z.shiftr half (Z.land t14 63))
(change (inr64 (Z.shiftr half (Z.land t14 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
extend_tail shM64. sf_finish.
*
zstep. zstep.
extend_tail shM64. sf_finish.
-
zstep. zstep. if_cases K1; zify_cond K1; decide_tests_b.
+ do 11 zstep. sf_finish.
+ do 10 zstep. sf_finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
