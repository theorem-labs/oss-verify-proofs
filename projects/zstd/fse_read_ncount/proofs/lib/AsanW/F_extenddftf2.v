(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFW1_lemmas.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SF_buildtac.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.
Local Ltac zsimp ::= zsimp_fast.
Local Ltac sf_finish ::=
apply evtF_done;
lazymatch goal with |- ?P ?ms => try unfold P end; hnf;
rewrite ?lo64_mk128, ?hi64_mk128 by zrange;
repeat (lazymatch goal with |- ex _ => eexists end);
split; [ ms_eq | repeat match goal with |- _ /\ _ => split end; try assumption ].
Section CANSEC1. Context {rc : runConstT}.
Definition extenddftf2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'.
End CANSEC1.
Local Ltac extend_tail shM64 :=
zstep; zstep; rewrite (srai63_word shM64) by lia; decide_tests_b;
do 11 zstep.
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma extenddftf2_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
mem_inv asegs m ->
evtF asegs RNG (extenddftf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
(f128_of_d (bv_unsigned (reg_get F 10))) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x82874) fc None m (seg_rom asegs)).
Proof.
intros until m. intros MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold f128_of_d.
cbv beta delta [add64 sub64 shl64 not64 is_neg64 sra63 lo64 hi64 wrap64 b2z ONES64 IMPLICIT_HI INF_HI]. zb_fold_lits.
Local Ltac2 Set LiaHints.tbl := fun () => "00N0>10336720952.3911447729963.6913168393118.4217114530413.5017122713556.3918032496357.6619620497060.5024040356596.4832969465626.8133392159193.5535027953801.9035027953801.9435027953802.5835497698861.4836024693271.7437654378318.7937658974283.8343713689867.9043713689867.9445859665771.7946286549312.8746286549312.9151521005083.6455888456068.5059552398415.7762231074346.5862231074346.8962231074346.9363357301334.507345754199.76 00000100I00N00O00P00Q00R00S00T00U00V00W00X00Y00Z00b00j00k00l00m00n00o01001101201301401501:01;FS5RaExp2K01H2H02H42H52H9S3RdwSSFFFSFFFFSFS6RshM64S6RshM64FFFFFFFFFFFS3RdwF".
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
End CANSEC2.
