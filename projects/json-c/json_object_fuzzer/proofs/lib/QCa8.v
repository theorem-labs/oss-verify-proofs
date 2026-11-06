(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1 Q2qa QVbl QQLG Q91D Q8QT QZAa Lib.CodeAt Lib.StepGen Lib.StepGenSF Lib.GwCallee.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QnDM_c1 Q2qa.
Import QVbl.Mq0.
Import QQLG.Mq0.
Import Q91D.Mq0.
Import Q8QT.Mq0.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.

Import QZAa.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenSF OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base addtf3_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 1996.

Hypothesis fe_getround_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq0.fe_getround_spec segs (base + 1996)%Z 0%Z 0%Z) 3%nat in let T := gw_fold_pcs T base (1996)%Z [0; 48]%Z in exact T).
Hypothesis fe_raise_inexact_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq0.fe_raise_inexact_spec segs (base + 1996)%Z 0%Z 0%Z) 3%nat in let T := gw_fold_pcs T base (1996)%Z [0; 48]%Z in exact T).

Ltac unfold_sfw := cbv beta delta [add64 sub64 shl64 not64 is_neg64 sra63 lt_s64 eqz64 nez64 zext32 lo64 hi64 wrap64
ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI IMPL3_HI SPEC_K].

Definition addtf3_post := Eval cbv beta delta [Q8QT.Mq0.addtf3_post] in (Q8QT.Mq0.addtf3_post segs).
Definition add_LM4 := Q8QT.Mq0.add_LM4 segs base CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= g_step_fast.
Local Ltac zsimp ::= zsimp_fast.

Ltac finL := first [ eassumption | reflexivity | zrange | lia | (decide_tests_b; reflexivity) | fail 1 "finL: unsolved premise" ].

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte).
Hypothesis FRM : frm0 fc.
Hypothesis MI : mem_inv segs m1.
Hypothesis FR : rw_cells segs m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Hypothesis STK : stk segs m1 (bv_unsigned sp + -48) (bv_unsigned sp + -48).
Hypothesis MU : munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1.
Hypothesis WM : wmono segs m m1.
Hypothesis SPLO : (48 <= bv_unsigned sp)%Z.

Notation POST r := (addtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F r m).
Notation SP := (Z_to_bv 64 (bv_unsigned sp + -48)).

Notation ST pc fcx x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 :=
(MS (mkR x1 SP gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 pc) fcx None m1 (seg_rom segs)).

Lemma add_L3ac : forall x1 x9 x18 x19 x20 x29 x30 x31 (aHi bHi xHi aSigHi aSigLo aExp bSigLo clz sh d mask nhi r : Z),
(0 <= aHi < 2^64)%Z -> (0 <= bHi < 2^64)%Z -> (0 <= xHi < 2^64)%Z -> (0 <= aSigHi < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
(0 <= bSigLo < 2^64)%Z -> (0 <= clz < 2^64)%Z -> (0 <= sh < 2^64)%Z -> (0 <= d < 2^64)%Z -> (0 <= nhi < 2^64)%Z ->
(if 9223372036854775808 <=? d then 18446744073709551615 else 0)%Z = mask ->
r = normB3 aHi bHi xHi aSigHi aSigLo aExp bSigLo clz sh mask nhi ->
evt segs (POST r) (ST (base + 0x394) fc x1 (Z_to_bv 64 clz) (Z_to_bv 64 nhi) (Z_to_bv 64 sh) (Z_to_bv 64 bHi) x9
(Z_to_bv 64 aSigLo) (Z_to_bv 64 aHi) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 bSigLo) (Z_to_bv 64 aSigHi)
x18 x19 x20 (Z_to_bv 64 d) x29 x30 x31).
Proof using CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec FR FRM MI MU STK WM.
intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 Hm HR. subst r. unfold normB3, shl128_lo. unfold_sfw.
assert (Rm : (0 <= mask < 2^64)%Z) by (rewrite <- Hm; destruct (Z.leb _ _); lia).
zstep. zstep. rewrite (srai63_word d), Hm by lia.
zstep. zstep. name_reg 16%Z nlo.
zstep. model_reg 5%Z bExp2 (Z.land (16 - clz) W64).
eapply add_LM4; finL.
Qed.

Lemma add_L2d0 : forall x1 x9 x18 x19 x20 x28 x29 x30 x31 (aHi bHi xHi aSigHi aSigLo aExp bSigHi bSigLo word hz r : Z),
(0 <= aHi < 2^64)%Z -> (0 <= bHi < 2^64)%Z -> (0 <= xHi < 2^64)%Z -> (0 <= aSigHi < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
(0 <= bSigHi < 2^64)%Z -> (0 <= bSigLo < 2^64)%Z -> (0 <= word < 2^64)%Z -> (0 <= hz <= 1)%Z ->
r = (let '(h, l, e) := norm_w2 bSigHi bSigLo word hz in add_M4 aHi bHi xHi aSigHi aSigLo aExp h l e) ->
evt segs (POST r) (ST (base + 0x2b8) fc x1 (Z_to_bv 64 hz) (Z_to_bv 64 bSigHi) (Z_to_bv 64 word) (Z_to_bv 64 bHi) x9
(Z_to_bv 64 aSigLo) (Z_to_bv 64 aHi) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 bSigLo) (Z_to_bv 64 aSigHi)
x18 x19 x20 x28 x29 x30 x31).
Proof using CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec FR FRM MI MU STK WM.
intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 HR. subst r. unfold norm_w2, clz128_w. unfold shl128_mirror. unfold_sfw.

do 5 zstep. model_reg 7%Z x1_ (Z.lor word (Z.shiftr word 1)).
do 5 zstep. model_reg 7%Z x2_ (Z.lor x1_ (Z.shiftr x1_ 2)).
do 8 zstep. model_reg 7%Z x3_ (Z.lor x2_ (Z.shiftr x2_ 4)).
do 2 zstep. model_reg 7%Z x4_ (Z.lor x3_ (Z.shiftr x3_ 8)).
do 2 zstep. model_reg 7%Z x5_ (Z.lor x4_ (Z.shiftr x4_ 16)).
do 2 zstep. model_reg 7%Z x6_ (Z.lor x5_ (Z.shiftr x5_ 32)).
zstep. model_reg 7%Z y_ (Z.lxor x6_ W64).
do 4 zstep. model_reg 7%Z c1_ (Z.land (y_ - Z.land (Z.shiftr y_ 1) 6148914691236517205) W64).
do 6 zstep. model_reg 7%Z c2_ (Z.land (Z.land c1_ 3689348814741910323 + Z.land (Z.shiftr c1_ 2) 3689348814741910323) W64).
do 4 zstep. model_reg 7%Z c3_ (Z.land (Z.land (c2_ + Z.shiftr c2_ 4) W64) 1085102592571150095).
do 3 zstep. model_reg 7%Z c4_ (Z.shiftr (Z.land (c3_ * 72340172838076673) W64) 56).
replace (Z_to_bv 64 c4_) with (Z_to_bv 64 (clz64_mirror word)) by (f_equal; model_eval; reflexivity).
name_as_by clz64v (clz64_mirror word) (apply clz64_mirror_range).
zstep. rewrite (land_W64_small (Z.shiftl hz 6)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
name_as_by clz (Z.lor clz64v (Z.shiftl hz 6))
(change (inr64 (Z.lor clz64v (Z.shiftl hz 6))); apply zr_lor; [zrange | apply zr_lit; rewrite Z.shiftl_mul_pow2 by lia; lia]).
zstep. model_reg 7%Z sh (Z.land (clz - 15) W64).
zstep. zstep. name_reg 29%Z n. zstep. model_reg 28%Z d (Z.land (n - 64) W64).
zstep. if_cases Kd; zify_cond Kd; decide_tests_b.
-
zstep. zstep. zstep. zstep. name_as_by sr0 (Z.shiftr (Z.shiftr bSigLo 1) (Z.land (Z.lxor n W64) 63))
(change (inr64 (Z.shiftr (Z.shiftr bSigLo 1) (Z.land (Z.lxor n W64) 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
zstep. name_reg 6%Z nhi.
eapply add_L3ac with (mask := 18446744073709551615%Z); finL.
- zstep. model_reg 6%Z nhi (Z.land (Z.shiftl bSigLo (Z.land n 63)) W64). zstep.
eapply add_L3ac with (mask := 0%Z); finL.
Qed.

Lemma add_L2c0 : forall x1 x5 x7 x9 x18 x19 x20 x28 x29 x30 x31 (aHi bHi xHi aSigHi aSigLo aExp bSigHi bSigLo r : Z),
(0 <= aHi < 2^64)%Z -> (0 <= bHi < 2^64)%Z -> (0 <= xHi < 2^64)%Z -> (0 <= aSigHi < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
(0 <= bSigHi < 2^64)%Z -> (0 <= bSigLo < 2^64)%Z ->
r = (let '(h, l, e) := normalize_mirror bSigHi bSigLo in add_M4 aHi bHi xHi aSigHi aSigLo aExp h l e) ->
evt segs (POST r) (ST (base + 0x2a8) fc x1 x5 (Z_to_bv 64 bSigHi) x7 (Z_to_bv 64 bHi) x9
(Z_to_bv 64 aSigLo) (Z_to_bv 64 aHi) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 bSigLo) (Z_to_bv 64 aSigHi)
x18 x19 x20 x28 x29 x30 x31).
Proof using CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec FR FRM MI MU STK WM.
intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 HR. subst r. rewrite normalize_mirror_w. rewrite ?b2z_Zb2z.
zstep. rewrite (ltb1_eqb0 bSigHi) by lia. zstep. zstep. if_cases Kw; zify_cond Kw; decide_tests_b.
-  change (Z.b2z true) with 1%Z. eapply add_L2d0; finL.
- change (Z.b2z false) with 0%Z. zstep. eapply add_L2d0; finL.
Qed.

Lemma add_L2a4 : forall x1 x9 x18 x19 x20 x29 x30 x31 (aHi bHi xHi aSigLo yHi yLo bExp clz sh d mask nhi r : Z),
(0 <= aHi < 2^64)%Z -> (0 <= bHi < 2^64)%Z -> (0 <= xHi < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z -> (0 <= yHi < 2^64)%Z -> (0 <= yLo < 2^64)%Z ->
(0 <= bExp < 2^64)%Z -> (0 <= clz < 2^64)%Z -> (0 <= sh < 2^64)%Z -> (0 <= d < 2^64)%Z -> (0 <= nhi < 2^64)%Z ->
(if 9223372036854775808 <=? d then 18446744073709551615 else 0)%Z = mask ->
r = normA3 aHi bHi xHi aSigLo yHi yLo bExp clz sh mask nhi ->
evt segs (POST r) (ST (base + 0x28c) fc x1 (Z_to_bv 64 bExp) (Z_to_bv 64 yHi) (Z_to_bv 64 sh) (Z_to_bv 64 bHi) x9
(Z_to_bv 64 aSigLo) (Z_to_bv 64 aHi) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 clz) (Z_to_bv 64 yLo) (Z_to_bv 64 nhi)
x18 x19 x20 (Z_to_bv 64 d) x29 x30 x31).
Proof using CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec FR FRM MI MU STK WM.
intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 Hm HR. subst r. unfold normA3, shl128_lo.
assert (Rm : (0 <= mask < 2^64)%Z) by (rewrite <- Hm; destruct (Z.leb _ _); lia).
unfold add_M3b. unfold_sfw.
zstep. zstep. rewrite (srai63_word d), Hm by lia.
zstep. zstep. name_reg 10%Z nlo.
zstep. model_reg 15%Z aExp2 (Z.land (16 - clz) W64).
zstep. name_reg 6%Z bSigHi.
zstep. if_cases Kb; zify_cond Kb; decide_tests_b.
-  eapply add_LM4; finL.
-  eapply add_L2c0; finL.
Qed.

Lemma add_L194 : forall x1 x9 x18 x19 x20 x28 x29 x30 x31 (aHi bHi xHi aSigHi aSigLo yHi yLo bExp word hz r : Z),
(0 <= aHi < 2^64)%Z -> (0 <= bHi < 2^64)%Z -> (0 <= xHi < 2^64)%Z -> (0 <= aSigHi < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z ->
(0 <= yHi < 2^64)%Z -> (0 <= yLo < 2^64)%Z -> (0 <= bExp < 2^64)%Z -> (0 <= word < 2^64)%Z -> (0 <= hz <= 1)%Z ->
r = (let '(h, l, e) := norm_w2 aSigHi aSigLo word hz in add_M3b aHi bHi xHi h l e (Z.land yHi MASK48) yLo bExp) ->
evt segs (POST r) (ST (base + 0x17c) fc x1 (Z_to_bv 64 bExp) (Z_to_bv 64 yHi) (Z_to_bv 64 word) (Z_to_bv 64 bHi) x9
(Z_to_bv 64 aSigLo) (Z_to_bv 64 aHi) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 hz) (Z_to_bv 64 yLo) (Z_to_bv 64 aSigHi)
x18 x19 x20 x28 x29 x30 x31).
Proof using CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec FR FRM MI MU STK WM.
intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 HR. subst r. unfold norm_w2, clz128_w. unfold shl128_mirror. unfold_sfw.

do 5 zstep. model_reg 7%Z x1_ (Z.lor word (Z.shiftr word 1)).
do 5 zstep. model_reg 7%Z x2_ (Z.lor x1_ (Z.shiftr x1_ 2)).
do 8 zstep. model_reg 7%Z x3_ (Z.lor x2_ (Z.shiftr x2_ 4)).
do 2 zstep. model_reg 7%Z x4_ (Z.lor x3_ (Z.shiftr x3_ 8)).
do 2 zstep. model_reg 7%Z x5_ (Z.lor x4_ (Z.shiftr x4_ 16)).
do 2 zstep. model_reg 7%Z x6_ (Z.lor x5_ (Z.shiftr x5_ 32)).
zstep. model_reg 7%Z y_ (Z.lxor x6_ W64).
do 4 zstep. model_reg 7%Z c1_ (Z.land (y_ - Z.land (Z.shiftr y_ 1) 6148914691236517205) W64).
do 6 zstep. model_reg 7%Z c2_ (Z.land (Z.land c1_ 3689348814741910323 + Z.land (Z.shiftr c1_ 2) 3689348814741910323) W64).
do 4 zstep. model_reg 7%Z c3_ (Z.land (Z.land (c2_ + Z.shiftr c2_ 4) W64) 1085102592571150095).
do 3 zstep. model_reg 7%Z c4_ (Z.shiftr (Z.land (c3_ * 72340172838076673) W64) 56).
replace (Z_to_bv 64 c4_) with (Z_to_bv 64 (clz64_mirror word)) by (f_equal; model_eval; reflexivity).
name_as_by clz64v (clz64_mirror word) (apply clz64_mirror_range).
zstep. rewrite (land_W64_small (Z.shiftl hz 6)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
name_as_by clz (Z.lor clz64v (Z.shiftl hz 6))
(change (inr64 (Z.lor clz64v (Z.shiftl hz 6))); apply zr_lor; [zrange | apply zr_lit; rewrite Z.shiftl_mul_pow2 by lia; lia]).
zstep. model_reg 7%Z sh (Z.land (clz - 15) W64).
zstep. zstep. name_reg 29%Z n. zstep. model_reg 28%Z d (Z.land (n - 64) W64).
zstep. if_cases Kd; zify_cond Kd; decide_tests_b.
-
zstep. zstep. zstep. zstep. name_as_by sr0 (Z.shiftr (Z.shiftr aSigLo 1) (Z.land (Z.lxor n W64) 63))
(change (inr64 (Z.shiftr (Z.shiftr aSigLo 1) (Z.land (Z.lxor n W64) 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
zstep. name_reg 17%Z nhi.
eapply add_L2a4 with (mask := 18446744073709551615%Z); finL.
- zstep. model_reg 17%Z nhi (Z.land (Z.shiftl aSigLo (Z.land n 63)) W64). zstep.
eapply add_L2a4 with (mask := 0%Z); finL.
Qed.

Lemma add_L184 : forall x1 x7 x9 x15 x18 x19 x20 x28 x29 x30 x31 (aHi bHi xHi aSigHi aSigLo yHi yLo bExp r : Z),
(0 <= aHi < 2^64)%Z -> (0 <= bHi < 2^64)%Z -> (0 <= xHi < 2^64)%Z -> (0 <= aSigHi < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z ->
(0 <= yHi < 2^64)%Z -> (0 <= yLo < 2^64)%Z -> (0 <= bExp < 2^64)%Z ->
r = (let '(h, l, e) := normalize_mirror aSigHi aSigLo in add_M3b aHi bHi xHi h l e (Z.land yHi MASK48) yLo bExp) ->
evt segs (POST r) (ST (base + 0x16c) fc x1 (Z_to_bv 64 bExp) (Z_to_bv 64 yHi) x7 (Z_to_bv 64 bHi) x9
(Z_to_bv 64 aSigLo) (Z_to_bv 64 aHi) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) x15 (Z_to_bv 64 yLo) (Z_to_bv 64 aSigHi)
x18 x19 x20 x28 x29 x30 x31).
Proof using CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec FR FRM MI MU STK WM.
intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 HR. subst r. rewrite normalize_mirror_w. rewrite ?b2z_Zb2z.
zstep. rewrite (ltb1_eqb0 aSigHi) by lia. zstep. zstep. if_cases Kw; zify_cond Kw; decide_tests_b.
- change (Z.b2z true) with 1%Z. eapply add_L194; finL.
- change (Z.b2z false) with 0%Z. zstep. eapply add_L194; finL.
Qed.

Lemma add_L0d4 : forall x1 x7 x9 x18 x19 x20 x28 x29 x30 x31 (aHi bHi xHi aSigHi aSigLo aExp yHi yLo bExp r : Z),
(0 <= aHi < 2^64)%Z -> (0 <= bHi < 2^64)%Z -> (0 <= xHi < 2^64)%Z -> (0 <= aSigHi < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
(0 <= yHi < 2^64)%Z -> (0 <= yLo < 2^64)%Z -> (0 <= bExp < 2^64)%Z ->
r = add_M3b aHi bHi xHi aSigHi aSigLo aExp (Z.land yHi MASK48) yLo bExp ->
evt segs (POST r) (ST (base + 0xbc) fc x1 (Z_to_bv 64 bExp) (Z_to_bv 64 yHi) x7 (Z_to_bv 64 bHi) x9
(Z_to_bv 64 aSigLo) (Z_to_bv 64 aHi) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 yLo) (Z_to_bv 64 aSigHi)
x18 x19 x20 x28 x29 x30 x31).
Proof using CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec FR FRM MI MU STK WM.
intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 R9 HR. subst r. unfold add_M3b. unfold_sfw.
zstep. name_reg 6%Z bSigHi.
zstep. if_cases Kb; zify_cond Kb; decide_tests_b.
- eapply add_LM4; finL.
- zstep. eapply add_L2c0; finL.
Qed.
End Proofs.

End G.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Qy5Y Q4J3 QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1.
Import Q2qa.Mq0 Qy5Y.Mq3 Q4J3 QPjm.
Import QQLG.
Import QVbl.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4.
Local Open Scope Z_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenSF OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base divtf3_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 2308.

Hypothesis mulhu_shl32 : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.mulhu_shl32 segs (base + -4832)%Z) 3%nat in let T := gw_fold_pcs T base (-4832)%Z [0; 128; 524]%Z in exact T).

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= g_step_fast.
Local Ltac zsimp ::= zsimp_fast.

Definition divtf3_core_pc := (base + 0x88)%Z.
Definition divtf3_mid1_pc := (base + 0x218)%Z.

#[using="CODE BASE4 BASER mulhu_shl32"] Lemma shl_shr_32 : forall x, 0 <= x -> Z.shiftr (Z.land (Z.shiftl x 32) 18446744073709551615) 32 = Z.land x 4294967295.
Proof. intros. rewrite zb_shl_shr_land by lia. reflexivity. Qed.

Definition E_aSigHiI (aSigHi : Z) := Z.lor aSigHi 281474976710656.
Definition E_bSigHiI (bSigHi : Z) := Z.lor bSigHi 281474976710656.
Definition E_aLoTop (aLo : Z) := Z.shiftr aLo 63.
Definition E_a2Lo (aLo : Z) := Z.land (Z.shiftl aLo 1) 18446744073709551615.
Definition E_aHi2n (aSigHi : Z) := Z.land (Z.shiftl aSigHi 1) 18446744073709551615.
Definition E_aHi2 (aSigHi : Z) := Z.land (Z.shiftl (E_aSigHiI aSigHi) 1) 18446744073709551615.
Definition E_A1 (aSigHi : Z) := Z.shiftr (E_aHi2 aSigHi) 32.
Definition E_A2 (aSigHi aLo : Z) := Z.land (Z.lor (E_aLoTop aLo) (E_aHi2n aSigHi)) 4294967295.
Definition E_A2sh (aSigHi aLo : Z) := Z.shiftl (Z.lor (E_aLoTop aLo) (E_aHi2n aSigHi)) 32.
Definition E_A3 (aLo : Z) := Z.shiftr (E_a2Lo aLo) 32.
Definition E_A4 (aLo : Z) := Z.land (E_a2Lo aLo) 4294967294.
Definition E_X3 (x_lo : Z) := Z.shiftr x_lo 32.
Definition E_X4sh (x_lo : Z) := Z.land (Z.shiftl x_lo 32) 18446744073709551615.
Definition E_X4 (x_lo : Z) := Z.shiftr (E_X4sh x_lo) 32.
Definition E_p3 (x_lo A : Z) := Z.land (E_X3 x_lo * A) 18446744073709551615.
Definition E_p42 (x_lo aSigHi aLo : Z) := Z.land (E_X4 x_lo * E_A2 aSigHi aLo) 18446744073709551615.
Definition E_expM1 (scale ea eb : Z) := scale + 16382 + (ea - eb).
Definition E_blo (bLo : Z) := Z.land (Z.shiftl bLo 15) 18446744073709551615.
Definition E_bhw (bSigHi bLo : Z) := Z.lor (Z.shiftr bLo 49) (Z.land (Z.shiftl (E_bSigHiI bSigHi) 15) 18446744073709551615).
Definition E_x0 (bSigHi bLo : Z) := Z.land (8432131802713292800 - E_bhw bSigHi bLo) 18446744073709551615.

Definition DCW (sgn ea eb aSigHi aLo bSigHi bLo scale x_hi x_lo : Z) : Z :=
let '(q_hi, q_lo) := divc_wide x_hi x_lo (E_A1 aSigHi) (E_A2 aSigHi aLo) (E_A3 aLo) (E_A4 aLo) in
divc_tail sgn (E_expM1 scale ea eb) q_hi q_lo aLo (E_aSigHiI aSigHi) (E_bSigHiI bSigHi) bLo (E_aHi2 aSigHi) (E_aLoTop aLo) (E_a2Lo aLo).

Ltac half_block b_hw xp xn h corr lo hi r :=
zstep; model_reg 22 h (Z.shiftr (xp * b_hw) 64); mulhu_rng h;
zstep; model_reg 22 corr (Z.land (0 - h) 18446744073709551615);
zstep; model_reg 23 lo (Z.land (corr * xp) 18446744073709551615);
zstep; model_reg 21 hi (Z.shiftr (corr * xp) 64); mulhu_rng hi;
do 3 zstep; model_reg 21 r (Z.lor (Z.shiftr lo 63) (Z.land (Z.shiftl hi 1) 18446744073709551615));
replace (Z_to_bv 64 r) with (Z_to_bv 64 (half_iter xp b_hw)) by (f_equal; subst r hi lo corr h; reflexivity);
name_as xn (half_iter xp b_hw); hi_rng xn.

Definition divtf3_mid1 (ra sp gp tp w4 sgw w6 a5 a6 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(ea eb aSigHi bSigHi scale : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists x_hi x_lo y21 y22,
(forall sgn, div_core sgn ea eb aSigHi (bv_unsigned w4) bSigHi (bv_unsigned w6) scale
= DCW sgn ea eb aSigHi (bv_unsigned w4) bSigHi (bv_unsigned w6) scale x_hi x_lo)
/\ (0 <= x_hi < 2^64)%Z /\ (0 <= x_lo < 2^64)%Z
/\ ms' = MS (mkR ra sp gp tp (Z_to_bv 64 (E_expM1 scale ea eb)) (Z_to_bv 64 (E_aLoTop (bv_unsigned w4))) (Z_to_bv 64 (E_aHi2 aSigHi))
(Z_to_bv 64 (E_A1 aSigHi)) (Z_to_bv 64 (E_A2sh aSigHi (bv_unsigned w4)))
w4 sgw w6 (Z_to_bv 64 (E_bSigHiI bSigHi)) (Z_to_bv 64 (E_a2Lo (bv_unsigned w4))) a5 a6 (Z_to_bv 64 (E_aSigHiI aSigHi))
(Z_to_bv 64 (E_A2 aSigHi (bv_unsigned w4))) (Z_to_bv 64 (E_p42 x_lo aSigHi (bv_unsigned w4))) (Z_to_bv 64 (E_X4 x_lo)) y21 y22
(Z_to_bv 64 (E_p3 x_lo (E_A3 (bv_unsigned w4)))) (Z_to_bv 64 (E_p3 x_lo (E_A4 (bv_unsigned w4)))) (Z_to_bv 64 x_hi) s10 s11
(Z_to_bv 64 (E_A4 (bv_unsigned w4))) (Z_to_bv 64 (E_p3 x_lo (E_A1 aSigHi))) (Z_to_bv 64 (E_p3 x_lo (E_A2 aSigHi (bv_unsigned w4)))) (Z_to_bv 64 (E_A3 (bv_unsigned w4))))
F (Z_to_bv 64 (base + 0x218)) fc None m (seg_rom segs).

Section Core1.
Variables (w3 w4 w5 w6 : word) (ea eb scale : Z).
Notation aSigHi := (bv_unsigned w3). Notation aLo := (bv_unsigned w4).
Notation bSigHi := (bv_unsigned w5). Notation bLo := (bv_unsigned w6).

#[using="CODE BASE4 BASER mulhu_shl32"] Lemma divtf3_core1 : forall (ra sp gp tp s0 s1 sgw a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
(F : bvmap 5 word) fc (m : word -> option byte),
mem_inv segs m ->
(0 <= ea < 32768)%Z -> (0 <= eb < 32768)%Z -> (-1024 <= scale <= 1024)%Z ->
evt segs (divtf3_mid1 ra sp gp tp w4 sgw w6 a5 a6 s10 s11 F fc ea eb aSigHi bSigHi scale m)
(MS (mkR ra sp gp tp w5 (Z_to_bv 64 ea) (Z_to_bv 64 eb) s0 s1 w4 sgw w6 a3 a4 a5 a6 w3
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 scale) t4 t5 t6)
F (Z_to_bv 64 (base + 0x88)) fc None m (seg_rom segs)).
Proof.
intros until m. intros MI Ra Rb Rsc.
pose_word_ranges.
set (aExp := ea) in *. set (bExp := eb) in *.

do 3 zstep. model_reg 7 expDiff (aExp - bExp).
do 1 zstep. model_reg 30 blo (Z.land (Z.shiftl bLo 15) 18446744073709551615).
do 4 zstep. model_reg 6 aLoTop (Z.shiftr aLo 63).
do 1 zstep. model_reg 14 a2Lo (Z.land (Z.shiftl aLo 1) 18446744073709551615).
do 1 zstep. model_reg 18 aHi2n (Z.land (Z.shiftl aSigHi 1) 18446744073709551615).
do 7 zstep. model_reg 31 A3 (Z.shiftr a2Lo 32).
do 2 zstep. model_reg 17 aSigHiI (Z.lor aSigHi 281474976710656).
do 1 zstep. model_reg 13 bSigHiI (Z.lor bSigHi 281474976710656).
do 5 zstep. model_reg 5 expM1 ((scale + 16382) + expDiff).
do 2 zstep. model_reg 7 aHi2 (Z.land (Z.shiftl aSigHiI 1) 18446744073709551615).
do 1 zstep. model_reg 18 A2 (Z.land (Z.lor aLoTop aHi2n) 4294967295).
do 1 zstep. model_reg 28 A4 (Z.land a2Lo 4294967294).
do 1 zstep. model_reg 20 b_hw (Z.lor (Z.shiftr bLo 49) (Z.land (Z.shiftl bSigHiI 15) 18446744073709551615)).
do 1 zstep. model_reg 8 A1 (Z.shiftr aHi2 32).
do 1 zstep. model_reg 21 x0 (Z.land (8432131802713292800 - b_hw) 18446744073709551615).

half_block b_hw x0 hx1 h1 k1 lo1 hi1 r1.
half_block b_hw hx1 hx2 h2 k2 lo2 hi2 r2.
half_block b_hw hx2 hx3 h3 k3 lo3 hi3 r3.
half_block b_hw hx3 hx4 h4 k4 lo4 hi4 r4.
do 1 zstep. model_reg 21 xh (Z.land (hx4 - 1) 18446744073709551615).
do 1 zstep. model_reg 22 pHhi (Z.shiftr (b_hw * xh) 64). mulhu_rng pHhi.
do 1 zstep. model_reg 20 pHlo (Z.land (b_hw * xh) 18446744073709551615).
do 1 zstep. model_reg 30 pLhi (Z.shiftr (blo * xh) 64). mulhu_rng pLhi.
do 1 zstep. model_reg 30 sumlo (Z.land (pHlo + pLhi) 18446744073709551615).
do 1 zstep. model_reg 20 c0 (Z.b2z (sumlo <? pHlo)).
do 1 zstep. model_reg 23 lt2 (Z.b2z (sumlo <? 2)).
do 1 zstep. model_reg 29 lo_corr (Z.land (1 - sumlo) 18446744073709551615).
do 1 zstep. model_reg 20 hiP (Z.land (pHhi + c0) 18446744073709551615).
do 1 zstep. model_reg 30 ge2 (Z.lxor lt2 1).
do 1 zstep. model_reg 22 m1lo (Z.land (lo_corr * xh) 18446744073709551615).
do 1 zstep. model_reg 29 m1hi (Z.shiftr (lo_corr * xh) 64). mulhu_rng m1hi.
do 1 zstep. model_reg 30 negHi (Z.land (hiP + ge2) 18446744073709551615).
do 3 zstep. model_reg 29 Bhi (Z.shiftr m1hi 63).
do 1 zstep. model_reg 30 hi_corr (Z.land (0 - negHi) 18446744073709551615).
do 1 zstep. model_reg 20 Blo (Z.lor (Z.shiftr m1lo 63) (Z.land (Z.shiftl m1hi 1) 18446744073709551615)).
do 1 zstep. model_reg 22 m2lo (Z.land (xh * hi_corr) 18446744073709551615).
do 1 zstep. model_reg 30 m2hi (Z.shiftr (xh * hi_corr) 64). mulhu_rng m2hi.
do 3 zstep. model_reg 22 Alo (Z.land (Z.shiftl m2lo 1) 18446744073709551615).
do 1 zstep. model_reg 30 Ahi (Z.lor (Z.land (Z.shiftl m2hi 1) 18446744073709551615) (Z.shiftr m2lo 63)).
do 1 zstep. model_reg 20 sLo (Z.land (Alo + Blo) 18446744073709551615).
do 1 zstep. model_reg 29 sHi (Z.land (Ahi + Bhi) 18446744073709551615).
do 1 zstep. model_reg 30 cs1 (Z.b2z (sLo <? Alo)).
do 1 zstep. model_reg 19 x_lo (Z.land (sLo + 18446744073709537689) 18446744073709551615).
do 1 zstep. model_reg 29 sHi1 (Z.land (sHi + cs1) 18446744073709551615).
do 1 zstep. model_reg 30 cs2 (Z.b2z (x_lo <? sLo)).
do 1 zstep. model_reg 20 X3 (Z.shiftr x_lo 32).
do 1 zstep. model_reg 19 X4sh (Z.land (Z.shiftl x_lo 32) 18446744073709551615).
do 1 zstep. model_reg 21 sHi2 (Z.land (sHi1 + cs2) 18446744073709551615).
do 1 zstep. model_reg 29 p31 (Z.land (X3 * A1) 18446744073709551615).
do 1 zstep. model_reg 30 p32 (Z.land (X3 * A2) 18446744073709551615).
do 1 zstep. model_reg 23 p33 (Z.land (X3 * A3) 18446744073709551615).
do 1 zstep. model_reg 24 p34 (Z.land (X3 * A4) 18446744073709551615).
do 1 zstep. model_reg 20 X4 (Z.shiftr X4sh 32).
do 1 zstep. cbv delta [X4sh]. rewrite mulhu_shl32 by zrange_nonneg. replace (Z.land x_lo 4294967295) with X4 by (cbv delta [X4 X4sh]; apply shl_shr_32; zrange_nonneg). change (Z.land (Z.lor aLoTop aHi2n) 4294967295) with A2. change (Z.land (Z.shiftl x_lo 32) 18446744073709551615) with X4sh.
do 0 zstep. model_reg 19 p42 (Z.land (X4 * A2) 18446744073709551615).
do 1 zstep. model_reg 25 x_hi (Z.land (sHi2 - 1) 18446744073709551615).

apply evt_done. unfold divtf3_mid1.
exists x_hi, x_lo. eexists. eexists.
split.
{ intros sg. cbv beta delta [DCW].
change (E_A1 aSigHi) with A1. change (E_A2 aSigHi aLo) with A2. change (E_A3 aLo) with A3. change (E_A4 aLo) with A4.
change (E_expM1 scale aExp bExp) with expM1. change (E_aSigHiI aSigHi) with aSigHiI. change (E_bSigHiI bSigHi) with bSigHiI.
change (E_aHi2 aSigHi) with aHi2. change (E_aLoTop aLo) with aLoTop. change (E_a2Lo aLo) with a2Lo.
cbv beta delta [div_core].
change (divc_setup aExp bExp aSigHi aLo bSigHi bLo scale) with (expM1, blo, b_hw, A1, A2, A3, A4, aSigHiI, bSigHiI, aHi2, aLoTop, a2Lo, x0).
cbv beta iota.
assert (HN : divc_newton x0 b_hw = xh).
{ cbv delta [divc_newton]. sf_vocab. fold_model_lets. folded_check. reflexivity. }
rewrite HN. cbv beta iota zeta.
assert (HF : divc_full xh b_hw blo = (x_hi, x_lo)).
{ cbv delta [divc_full]. sf_vocab. fold_model_lets. folded_check. reflexivity. }
rewrite HF. cbv beta iota. reflexivity. }
split. { exact Rx_hi. } split. { exact Rx_lo. }
reflexivity.
Time Qed.
End Core1.

End G.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1.
Import Q2qa.Mq0 Q2qa.Mq2 Qy5Y.Mq2 Qy5Y.Mq0 Q4J3.Mq0.
Import QQLG.
Import Q91D.
Import Q8QT.
Import QVbl.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Local Open Scope Z_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenSF OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base divtf3_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 2308.

Hypothesis sra63_K_neg : gw_hyp ltac:(let T := gw_callee_type0 (Q8QT.sra63_K_neg segs (base + -4832)%Z) 3%nat in let T := gw_fold_pcs T base (-4832)%Z [0; 128; 996; 1524; 1532]%Z in exact T).
Hypothesis sra63_K_pos : gw_hyp ltac:(let T := gw_callee_type0 (Q8QT.sra63_K_pos segs (base + -4832)%Z) 3%nat in let T := gw_fold_pcs T base (-4832)%Z [0; 128; 996; 1524; 1532]%Z in exact T).
Hypothesis ndr_lt64 : gw_hyp ltac:(let T := gw_callee_type0 (Q8QT.ndr_lt64 segs (base + -4832)%Z) 3%nat in let T := gw_fold_pcs T base (-4832)%Z [0; 128; 996; 1524; 1532]%Z in exact T).
Hypothesis ndr_ge64 : gw_hyp ltac:(let T := gw_callee_type0 (Q8QT.ndr_ge64 segs (base + -4832)%Z) 3%nat in let T := gw_fold_pcs T base (-4832)%Z [0; 128; 996; 1524; 1532]%Z in exact T).

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= g_step_fast.
Local Ltac zsimp ::= zsimp_fast.

Section Norm.
Variables (sp : word).
Notation spw := (Z_to_bv 64 (bv_unsigned sp + -112)).

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

#[using="CODE BASE4 BASER sra63_K_neg sra63_K_pos ndr_lt64 ndr_ge64"] Lemma LnormA : forall (Q : machine_state -> Prop) ra gp tp t0 t1 t2 (h : Z) s0 s1 wlo a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m1 : word -> option byte),
(0 <= h < 2^64)%Z ->
(forall y8 y13 y29 y30 y31,
evt segs Q
(MS (mkR ra spw gp tp t0 t1 t2 y8 s1 (Z_to_bv 64 (nd_lo h (bv_unsigned wlo))) a1 a2 y13 a4 a5 a6 (Z_to_bv 64 (nd_hi h (bv_unsigned wlo)))
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (16 - nd_clz h (bv_unsigned wlo))) y29 y30 y31)
F (Z_to_bv 64 (base + 0x7f8)) fc None m1 (seg_rom segs))) ->
evt segs Q
(MS (mkR ra spw gp tp t0 t1 t2 s0 s1 wlo a1 a2 a3 a4 a5 a6 (Z_to_bv 64 h) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x560)) fc None m1 (seg_rom segs)).
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

#[using="CODE BASE4 BASER sra63_K_neg sra63_K_pos ndr_lt64 ndr_ge64"] Lemma LnormB : forall (Q : machine_state -> Prop) ra gp tp (h : Z) t1 t2 (sc1 : Z) s0 s1 a0 a1 wlo a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6
(F : bvmap 5 word) fc (m1 : word -> option byte),
(0 <= h < 2^64)%Z -> (-1024 <= sc1 <= 1024)%Z ->
(forall y8 y13 y14 y29 y30 y31,
evt segs Q
(MS (mkR ra spw gp tp (Z_to_bv 64 (nd_hi h (bv_unsigned wlo))) t1 t2 y8 s1 a0 a1 (Z_to_bv 64 (nd_lo h (bv_unsigned wlo))) y13 y14 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (sc1 + nd_clz h (bv_unsigned wlo) - 16)) y29 y30 y31)
F (Z_to_bv 64 (base + 0x88)) fc None m1 (seg_rom segs))) ->
evt segs Q
(MS (mkR ra spw gp tp (Z_to_bv 64 h) t1 t2 s0 s1 a0 a1 wlo a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 sc1) t4 t5 t6)
F (Z_to_bv 64 (base + 0x800)) fc None m1 (seg_rom segs)).
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

End G.
End Mq2.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Lib.GwApply Qfw3_c1 QZAi QUZl Q7S0 Q6q3 Lib.StepGenX Lib.StepGenX2 Lib.GwFold G.GwFamMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1.

Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1.
Import Q8QT.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope bv_scope.
Open Scope Z_scope.

Definition enframe_code (w_10 w_12 : Z) : list Z :=
[0x02053703; 0x00c75793; 0x00078e63; 0x01f77793; 0x00079a63; 0xfffff7b7; 0x00f77733; 0xff070713; 0x0200006f; 0x00575713; w_10; 0x07e77713; w_12; 0x00e78733; 0x00075703; 0x00471713; 0x01053803; 0x02b707b3; 0x00f807b3; 0x00d7c883; 0x40c702b3; 0xffc28293; 0x01078793; 0x00088663; 0xffe7d683; 0x00168693; 0xffc7c383; 0x0042d313; 0x0ff6f893; 0x00038463; 0x00000023; 0x03137e63; 0x0052d693; 0x00d366b3; 0x0026d293; 0x00d2e6b3; 0x0046d293; 0x00d2e6b3; 0x00d8f6b3; 0x00d338b3; 0xfff34293; 0x411008bb; 0x0058f8b3; 0x00d888bb; 0x01137463; 0x00000023; 0x00078693; 0x02088063; 0xfe000813; 0x0048969b; 0x00d786b3; 0xff078ea3; 0xff179f23; 0xfe068e23; 0x01053803; 0x00e78733; 0x410687bb; 0x00d60633; 0xffc70513; 0xff078793; 0x0047d793; 0x40c5083b; 0xfeb68ea3; 0xfef69f23; 0x02080463; 0x40c505bb; 0x40b0063b; 0x00c50633; 0x00500513; 0x00060023; 0x00a5cc63; 0xfe070ba3; 0xfeb72c23; 0x0100006f; 0x00000513; 0x0080006f; 0x00058513; 0xffd6c583; 0x01f5f593; 0x00551513; 0x00b56533; 0xfea68ea3; 0x00068513; 0x00008067]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (w_10 w_12 : Z).
Variables (hi_10 : bv 20).
Variables (lo_12 : bv 12).
Hypothesis CODE : code_at segs base (enframe_code w_10 w_12).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 336.
Hypothesis D_10 : decode_any (Z_to_bv 32 w_10) = Some (Auipc 15 hi_10, 4%Z).
Hypothesis E_10 : is_ecall (Z_to_bv 32 w_10) = false.
Hypothesis D_12 : decode_any (Z_to_bv 32 w_12) = Some (OpImm ALU_ADD 15 15 lo_12, 4%Z).
Hypothesis E_12 : is_ecall (Z_to_bv 32 w_12) = false.
Hypothesis ANCH_12 : gw_anch (Z.shiftl (bv_signed hi_10) 12 + (base + 40) + bv_signed lo_12)%Z (RDEBRUIJN + 32).
Hypothesis RNG_RATP : gw_br RATP 1896.
Hypothesis LAY_lo_RATP : gw_le (gw_RDATA2_LO + 164) RATP.
Hypothesis LAY_hi_RATP : gw_le ((RATP + 132896)) RIMG_HI.
Hypothesis AL_RATP : gw_al RATP 8.
Hypothesis RNG_RDEBRUIJN : gw_br RDEBRUIJN 159.
Hypothesis LAY_lo_RDEBRUIJN : gw_le (0x10000 + 0) RDEBRUIJN.
Hypothesis LAY_hi_RDEBRUIJN : gw_le ((RDEBRUIJN + 159)) gw_RTEXT_LO.
Hypothesis AL_RDEBRUIJN : gw_al RDEBRUIJN 8.
Hypothesis RNG_RGOT_SSP : gw_br RGOT_SSP 8.
Hypothesis LAY_lo_RGOT_SSP : gw_le (RDATA_LO + 0) RGOT_SSP.
Hypothesis LAY_hi_RGOT_SSP : gw_le ((RGOT_SSP + 8)) gw_RDATA2_LO.
Hypothesis AL_RGOT_SSP : gw_al RGOT_SSP 8.
Hypothesis LAY_win_0 : gw_win (0x10000 + 1) gw_RTEXT_LO.
Hypothesis LAY_win_1 : gw_win (gw_RTEXT_LO + 1) RDATA_LO.
Hypothesis LAY_win_2 : gw_win (RDATA_LO + 1) gw_RDATA2_LO.
Hypothesis LAY_win_3 : gw_win (gw_RDATA2_LO + 1) RIMG_HI.
Hypothesis LAY_win_4 : gw_win RIMG_HI 0x1000000.
Hypothesis AL_win_RIMG_HI : gw_winal RIMG_HI 4096.
Hypothesis AL_win_RDATA_LO : gw_winal RDATA_LO 4096.
Hypothesis AL_win_gw_RTEXT_LO : gw_winal gw_RTEXT_LO 4096.
Hypothesis AL_win_gw_RDATA2_LO : gw_winal gw_RDATA2_LO 4096.
Hypothesis ROM_RSIZE_CLASSES : QZDE.ro_bytes segs (RDEBRUIJN + 32) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSIZE_CLASSES.
Hypothesis ROM_RDEBRUIJN : QZDE.ro_bytes segs RDEBRUIJN OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RDEBRUIJN.
Hypothesis ROM_RSMALL_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 128) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSMALL_CNT.
Hypothesis ROM_RMED_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 155) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RMED_CNT.
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rsize_classes_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rsize_classes_read) constr:(gw_tbl_0)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rsize_classes_read)).

#[using="RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_10 E_10 D_12 E_12 ANCH_12 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

Definition renframe_tail_mem (m : word -> option byte) (P E n k q : Z) : word -> option byte :=
let m1 := write_to_mem m (wa (P - 3)) [b8 k] in
let m2 := write_to_mem m1 (wa (P - 2)) (le2 (wz q)) in
let r := E - P - n in
let m3 := if r =? 0 then m2 else write_to_mem m2 (wa (E - r)) [b8 0] in
let '(m4, r') := if 5 <=? r then (write_to_mem (write_to_mem m3 (wa (E - 5)) [b8 0]) (wa (E - 4)) (le4 (wz r)), 5) else (m3, r) in
write_to_mem m4 (wa (P - 3)) [b8 (Z.land k 31 + Z.shiftl r' 5)].

Definition ren3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 pw : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (P E n k q : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 pw a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ m' = renframe_tail_mem m P E n k q
/\ mem_inv segs m'.

#[using="Type"] Lemma lor_shl5 r k : 0 <= k < 32 -> 0 <= r -> Z.lor (r * 2 ^ 5) k = Z.land k 31 + Z.shiftl r 5.
Proof. clear - r k.
intros Hk Hr. replace (Z.land k 31) with k by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
rewrite Z.shiftl_mul_pow2 by lia.
assert (D : Z.land (r * 2 ^ 5) k = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i 5).
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit k i) with false; [apply andb_false_r|]. symmetry.
destruct (Z.eq_dec k 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
apply (Z.lt_le_trans _ 5); [|lia]. apply Z.log2_lt_pow2; lia. }
rewrite <- Z.lxor_lor by gw_exact D. rewrite <- (Z.add_nocarry_lxor _ _ D). lia.
Qed.
End RC__1.

Ltac read_k := lazymatch goal with BKc : bytes_at segs ?mc (?P - 3) [b8 ?k] |- _ =>
pose proof (bytes_at_read segs mc (P - 3) [b8 k] 0 1 BKc ltac:(lia) ltac:(cbn; lia)) as RK;
cbv [take drop Z.to_nat] in RK; replace (P - 3 + 0) with (P + -3) in RK by lia;
change (wa (P + -3)) with (Z_to_bv 64 (P + -3)) in RK end.

Ltac sok off len addr := lazymatch goal with W : wr_at segs ?mc (?P - 3) _ |- _ =>
let H := fresh "SO" in
pose proof (wr_at_store_ok segs mc _ _ off len W ltac:(lia) ltac:(lia)) as H;
replace (P - 3 + off) with addr in H by lia; change (wa addr) with (Z_to_bv 64 addr) in H end.
Section RC__2.

#[using="w_10 w_12 CODE"] Lemma renframe_tail_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 gw a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 p0w nw : word) F fc m
(P0 P E B n k stride : Z),
bv_unsigned p0w = P0 -> bv_unsigned nw = n -> E = P0 + stride - 4 ->
mem_inv segs m ->
wr_at segs m (P - 3) (E - P + 3) ->
E + 1 <= 2^64 -> B + 16 <= P -> P0 <= P -> P + n <= E -> E - P - n < 2^31 -> P - B < 2^31 -> 16 <= P0 -> 0 <= B -> 0 <= n -> 0 <= k < 32 ->
0 <= stride ->
evt segs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 P) F fc m P E n k ((P - B - 16) / 16))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1
gw (wz k) nw (Z_to_bv 64 P) (Z_to_bv 64 stride) p0w (wz B) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xdc)) fc None m (seg_rom segs)).
Proof. clear - w_10 w_12 CODE segs base.
intros until stride. intros HP0 HN HE MI WR ETOP BP P0P PNE EP PB P16 B0 N0 HK S0.
pose proof (bv_unsigned_in_range _ p0w) as PWR. change (bv_modulus 64) with (2^64) in PWR.
set (r := E - P - n).
assert (K31 : Z.land k 31 = k) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; apply Z.mod_small; lia).

step.

step. rewrite (unsigned_lit P), (wz_unsigned B), (swrap32_small (P - B)) by lia.

step. rewrite HN.

step. rewrite HP0. replace (P0 + stride + -4) with E by lia.

step. step. rewrite (unsigned_lit (P - B + -16)), Z.shiftr_div_pow2 by lia.
change (2 ^ 4) with 16. replace (P - B + -16) with (P - B - 16) by lia.

step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
replace (E - (n + P)) with r by lia.

sok 0 1%nat (P + -3).
step. rewrite (le1_wz k) by lia. sdk.
lazymatch goal with E2 : ?mc = write_to_mem ?mp (wa ?a) [b8 k] |- _ =>
pose proof (bytes_at_write_same segs mp a [b8 k] ltac:(lia) ltac:(cbn; lia)) as BK; rewrite <- E2 in BK;
replace a with (P - 3) in BK by lia end.

sok 1 2%nat (P + -2).
step. change (le2 (Z_to_bv 64 ((P - B - 16) / 16))) with (le2 (wz ((P - B - 16) / 16))). sdk.

step. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit r) in KR by lia.
-
step. step.

read_k. step. clear RK. rewrite ?zxb_b8 by lia.
step. rewrite ?(wz_unsigned k), ?K31 by lia. step. step. rewrite ?(unsigned_lit 0), ?(unsigned_lit k) by lia.
rewrite Z.lor_0_l.
sok 0 1%nat (P + -3).
step. change (le1 (Z_to_bv 64 k)) with (le1 (wz k)). rewrite (le1_wz k) by lia. sdk.
step. step.
apply evt_done. unfold ren3_post. do 15 eexists. split; [reflexivity|].
split; [|assumption].
unfold renframe_tail_mem. fold r. rewrite KR. change (0 =? 0) with true. change (5 <=? 0) with false. cbv beta iota zeta.
rewrite K31. change (Z.shiftl 0 5) with 0. rewrite Z.add_0_r.
repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
repeat (f_equal; try (unfold wa; f_equal; lia)).
-
step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
replace (E - (n + P)) with r by lia.
step. rewrite (unsigned_lit r), (swrap32_small (0 - r)) by lia.
step. replace (E + (0 - r)) with (E - r + 0) by lia.
step.
sok (n + 3) 1%nat (E - r + 0).
step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.

step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small in K5 by lia.
+
step.
read_k. step. clear RK. rewrite ?zxb_b8 by lia.
step. rewrite ?(wz_unsigned k), ?K31 by lia.
step. rewrite (unsigned_lit r), (Z.shiftl_mul_pow2 r) by lia.
step. rewrite (unsigned_lit (r * 2 ^ 5)), (unsigned_lit k) by lia. rewrite (lor_shl5 r k) by lia.
sok 0 1%nat (P + -3).
step. rewrite (le1_wz (Z.land k 31 + Z.shiftl r 5)) by (rewrite K31, Z.shiftl_mul_pow2 by lia; lia). sdk.
step. step.
apply evt_done. unfold ren3_post. do 15 eexists. split; [reflexivity|].
split; [|assumption].
unfold renframe_tail_mem. fold r.
replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta.
repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
repeat (f_equal; try (unfold wa; f_equal; lia)).
+
sok (E - P - 2) 1%nat (P0 + stride + -9).
step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
sok (E - P - 1) 4%nat (P0 + stride + -8).
step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
step.
read_k. step. clear RK. rewrite ?zxb_b8 by lia.
step. rewrite ?(wz_unsigned k), ?K31 by lia.
step. step. rewrite ?(unsigned_lit 5), (unsigned_lit k) by lia. change (5 ≪ 5) with (5 * 2 ^ 5). rewrite (lor_shl5 5 k) by lia.
sok 0 1%nat (P + -3).
step. rewrite (le1_wz (Z.land k 31 + Z.shiftl 5 5)) by (rewrite K31; change (Z.shiftl 5 5) with 160; lia). sdk.
step. step.
apply evt_done. unfold ren3_post. do 15 eexists. split; [reflexivity|].
split; [|assumption].
unfold renframe_tail_mem. fold r.
replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). cbv beta iota zeta.
repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
repeat (f_equal; try (unfold wa; f_equal; lia)).
Qed.

Definition renframe_off_mem (m : word -> option byte) (P0 off : Z) : word -> option byte :=
if off =? 0 then m
else write_to_mem (write_to_mem (write_to_mem m (wa (P0 - 3)) [b8 224]) (wa (P0 - 2)) (le2 (wz off)))
(wa (P0 + 16 * off - 4)) [b8 0].

#[using="w_10 w_12 CODE"] Lemma renframe_off_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 gw a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 p0w nw prev next : word) F fc m
(P0 B stride n k off avail freed mword : Z),
bv_unsigned p0w = P0 -> bv_unsigned nw = n ->
mem_inv segs m ->
rw_cells segs m (bv_unsigned gw) [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
wr_at segs m (P0 - 4) stride ->
P0 + stride <= 2^64 -> (P0 + stride <= bv_unsigned gw \/ bv_unsigned gw + 40 <= P0 - 4) ->
B + 16 <= P0 -> 0 <= B -> 0 <= n -> n + 4 <= stride -> stride - 4 - n < 2^31 -> P0 + 16 * off - B < 2^31 -> 16 <= P0 -> 0 <= k < 32 ->
0 <= off -> 16 * off <= stride - 4 - n ->
evt segs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (P0 + 16 * off)) F fc
(renframe_off_mem m P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1
gw (wz k) nw a3 (Z_to_bv 64 stride) p0w (wz B) (Z_to_bv 64 off) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xb8)) fc None m (seg_rom segs)).
Proof. clear - w_10 w_12 CODE segs base.
intros until mword. intros HP HN MI MM WR PTOP SEPG BP B0 N0 NS SS PBS P16 HK OFF0 OFFS.
pose proof (bv_unsigned_in_range _ gw) as GWR. change (bv_modulus 64) with (2^64) in GWR.

step. step. if_cases KO; zify_cond KO; rewrite ?(unsigned_lit off) in KO by lia.
-
subst off. unfold renframe_off_mem. rewrite Z.eqb_refl.
replace (P0 + 16 * 0) with P0 by lia.
replace p0w with (Z_to_bv 64 P0) by (rewrite <- HP; apply Z_to_bv_bv_unsigned).
eapply renframe_tail_walk with (P0 := P0) (E := P0 + stride - 4); try eassumption; try lia.
+ apply unsigned_lit. lia.
+ eapply wr_at_sub; [gw_exact WR | lia | lia].
-
step.
step. rewrite (unsigned_lit off), (Z.shiftl_mul_pow2 off), (swrap32_small (off * 2 ^ 4)) by lia.
step. rewrite HP.
pose proof (wr_at_store_ok segs m _ _ 1 1 WR ltac:(lia) ltac:(lia)) as SO1.
replace (P0 - 4 + 1) with (bv_unsigned p0w + -3) in SO1 by lia.
change (wa (bv_unsigned p0w + -3)) with (Z_to_bv 64 (bv_unsigned p0w + -3)) in SO1.
step. rewrite le1_neg32. sdk.
lazymatch goal with W : wr_at segs ?mc (P0 - 4) _ |- _ =>
pose proof (wr_at_store_ok segs mc _ _ 2 2 W ltac:(lia) ltac:(lia)) as SO2;
replace (P0 - 4 + 2) with (bv_unsigned p0w + -2) in SO2 by lia;
change (wa (bv_unsigned p0w + -2)) with (Z_to_bv 64 (bv_unsigned p0w + -2)) in SO2 end.
step. change (le2 (Z_to_bv 64 off)) with (le2 (wz off)). sdk.
lazymatch goal with W : wr_at segs ?mc (P0 - 4) _ |- _ =>
pose proof (wr_at_store_ok segs mc _ _ (16 * off) 1 W ltac:(lia) ltac:(lia)) as SO3;
replace (P0 - 4 + 16 * off) with (P0 + off * 2 ^ 4 + -4) in SO3 by lia;
change (wa (P0 + off * 2 ^ 4 + -4)) with (Z_to_bv 64 (P0 + off * 2 ^ 4 + -4)) in SO3 end.
step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
step.
replace (P0 + off * 2 ^ 4) with (P0 + 16 * off) by lia.
unfold renframe_off_mem. replace (off =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
replace (write_to_mem (write_to_mem (write_to_mem m (wa (P0 - 3)) [b8 224]) (wa (P0 - 2)) (le2 (wz off))) (wa (P0 + 16 * off - 4)) [b8 0])
with mc end.
2:{ repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
repeat (f_equal; try (unfold wa; f_equal; lia)). }
eapply renframe_tail_walk with (P0 := P0) (E := P0 + stride - 4); try eassumption; try lia.
eapply wr_at_sub; [gw_exact WR | lia | lia].
Qed.

#[using="Type"] Lemma swrap32_add_2p64 d : -2^31 <= d < 2^31 -> bv_swrap 32 (18446744073709551616 + d) = d.
Proof. clear - d.
intros Hd. unfold bv_swrap, bv_wrap.
change (bv_modulus 32) with 4294967296. change (bv_half_modulus 32) with 2147483648.
replace (18446744073709551616 + d + 2147483648) with ((d + 2147483648) + 4294967296 * 4294967296) by lia.
rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
Qed.

#[using="w_10 w_12 CODE"] Lemma renframe_fold_walk : forall (ra sp gp tp t2 s0 s1 gw a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 p0w nw prev next : word) F fc m
(P0 B stride n k off0 avail freed mword T0 : Z),
let slack := (stride - 4 - n) / 16 in
let off := fold_off off0 slack in
bv_unsigned p0w = P0 -> bv_unsigned nw = n -> T0 = stride - 4 - n ->
mem_inv segs m ->
rw_cells segs m (bv_unsigned gw) [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
wr_at segs m (P0 - 4) stride ->
P0 + stride <= 2^64 -> (P0 + stride <= bv_unsigned gw \/ bv_unsigned gw + 40 <= P0 - 4) ->
B + 16 <= P0 -> 0 <= B -> 0 <= n -> n + 4 <= stride -> stride - 4 - n < 2^31 ->
(forall off', 0 <= off' -> 16 * off' + n + 4 <= stride -> P0 + 16 * off' - B < 2^31) -> 16 <= P0 -> 0 <= k < 32 ->
0 <= off0 < 256 ->
evt segs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (P0 + 16 * off)) F fc
(renframe_off_mem m P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
(MS (mkR ra sp gp tp (Z_to_bv 64 T0) (Z_to_bv 64 slack) t2 s0 s1
gw (wz k) nw a3 (Z_to_bv 64 stride) p0w (wz B) (Z_to_bv 64 off0) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x7c)) fc None m (seg_rom segs)).
Proof. clear - w_10 w_12 CODE segs base.
intros until T0. intros slack off HP HN HT0 MI MM WR PTOP SEPG BP B0 N0 NS SS PBS P16 HK OF.
assert (SL : 0 <= slack <= stride) by (subst slack; Z.div_mod_to_equations; lia).
pose proof (fold_off_le_slack off0 slack OF ltac:(lia)) as FO. fold off in FO.
assert (S16 : 16 * slack <= stride - 4 - n) by (subst slack; Z.div_mod_to_equations; lia).

step. if_cases K1; zify_cond K1; rewrite ?(unsigned_lit slack), ?(unsigned_lit off0) in K1 by lia.
-
assert (EO : off = off0) by (subst off; rewrite fold_off_eq; replace (slack <? off0) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
rewrite EO. eapply renframe_off_walk; try eassumption; try lia; try (apply PBS; lia).
-
step. rewrite (unsigned_lit T0), HT0 by lia.
replace ((stride - 4 - n) ≫ 5) with (slack ≫ 1) by (subst slack; rewrite <- (Z.shiftr_div_pow2 _ 4), Z.shiftr_shiftr by lia; reflexivity).
pose proof (Z_shiftr_range slack 1 ltac:(lia) ltac:(lia)) as R1.

step. rewrite (unsigned_lit (slack ≫ 1)), (unsigned_lit slack) by lia.
set (m1 := Z.lor slack (slack ≫ 1)).
pose proof (Z_lor_range slack (slack ≫ 1) ltac:(lia) R1) as RM1. fold m1 in RM1.

step. rewrite (unsigned_lit m1) by lia. pose proof (Z_shiftr_range m1 2 RM1 ltac:(lia)) as R2.
step. rewrite (unsigned_lit m1), (unsigned_lit (m1 ≫ 2)) by lia. rewrite (Z.lor_comm (m1 ≫ 2) m1).
set (m2 := Z.lor m1 (m1 ≫ 2)). pose proof (Z_lor_range m1 (m1 ≫ 2) RM1 R2) as RM2. fold m2 in RM2.

step. rewrite (unsigned_lit m2) by lia. pose proof (Z_shiftr_range m2 4 RM2 ltac:(lia)) as R3.
step. rewrite (unsigned_lit m2), (unsigned_lit (m2 ≫ 4)) by lia. rewrite (Z.lor_comm (m2 ≫ 4) m2).
set (m3 := Z.lor m2 (m2 ≫ 4)). pose proof (Z_lor_range m2 (m2 ≫ 4) RM2 R3) as RM3. fold m3 in RM3.
assert (SM : m3 = smear slack) by first [reflexivity | (cbn; lia)].

step. rewrite (unsigned_lit off0), (unsigned_lit m3) by lia.
set (x := Z.land off0 m3).
assert (RX : 0 <= x <= off0) by (subst x; split; [apply Z.land_nonneg; lia | apply land_le_l; lia]).

step. rewrite v_sltu_b2z, (unsigned_lit slack), (unsigned_lit x) by lia.

step. rewrite (unsigned_lit slack) by lia.
destruct (Z.ltb_spec slack x) as [LT|GE]; cbn [Z.b2z].
+ pose proof (fold_assert_ok off0 slack OF ltac:(lia) ltac:(rewrite <- SM; gw_exact LT)) as FA. rewrite <- SM in FA. fold x in FA.
step. step. rewrite (zb_lxor_ones slack) by lia. rewrite (unsigned_lit (18446744073709551615 - slack)) by lia.
change 18446744073709551615 with (Z.ones 64) at 1. rewrite (Z.land_comm (Z.ones 64)), Z.land_ones by lia.
rewrite (Z.mod_small (18446744073709551615 - slack)) by lia.
step. rewrite (unsigned_lit (18446744073709551615 - slack)), (unsigned_lit x) by lia.
replace (18446744073709551615 - slack + x) with (18446744073709551616 + (x - (slack + 1))) by lia.
rewrite swrap32_add_2p64 by lia.

step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit slack), ?(unsigned_lit (x - (slack + 1))) in K2 by lia; [|exfalso; lia].
assert (EO : off = x - (slack + 1)).
{ subst off. rewrite fold_off_eq. replace (slack <? off0) with true by (symmetry; apply Z.ltb_lt; lia). cbv zeta.
rewrite <- SM. fold x. replace (slack <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
rewrite EO. eapply renframe_off_walk; try eassumption; try lia; try (apply PBS; lia).
+ step. step. change (Z.land 0 _) with 0.
step. rewrite (unsigned_lit x), Z.add_0_l, (swrap32_small x) by lia.
step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit slack), ?(unsigned_lit x) in K2 by lia; [|exfalso; lia].
assert (EO : off = x).
{ subst off. rewrite fold_off_eq. replace (slack <? off0) with true by (symmetry; apply Z.ltb_lt; lia). cbv zeta.
rewrite <- SM. fold x. replace (slack <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
rewrite EO. eapply renframe_off_walk; try eassumption; try lia; try (apply PBS; lia).
Qed.

#[using="Type"] Lemma land_m4096 a : 0 <= a < 2^64 -> Z.land a 18446744073709547520 = a - a mod 4096.
Proof. clear - a.
intros Ha.
replace (a - a mod 4096) with (Z.shiftl (Z.shiftr a 12) 12) by (rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia; change (2^12) with 4096; Z.div_mod_to_equations; lia).
change 18446744073709547520 with (Z.ldiff (Z.ones 64) (Z.ones 12)).
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, !Z.testbit_ones by lia.
destruct (Z.lt_ge_cases i 12).
- rewrite Z.shiftl_spec_low by lia. replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia).
replace (i <? 12) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb negb]. rewrite !andb_false_r. reflexivity.
- rewrite Z.shiftl_spec_high, Z.shiftr_spec by lia. replace (i - 12 + 12) with i by lia.
replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia).
replace (i <? 12) with false by (symmetry; apply Z.ltb_ge; lia).
destruct (Z.lt_ge_cases i 64).
+ replace (i <? 64) with true by (symmetry; apply Z.ltb_lt; lia). cbn. rewrite andb_true_r. reflexivity.
+ replace (Z.testbit a i) with false; [reflexivity|]. symmetry.
destruct (Z.eq_dec a 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia|lia].
Qed.

#[using="RDEBRUIJN w_10 w_12 hi_10 lo_12 CODE D_10 E_10 D_12 E_12 ANCH_12 RNG_RDEBRUIJN ROM_RSIZE_CLASSES"] Lemma renframe_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gw nw prev next : word) F fc m
(B stride n k ctr avail freed last_idx freeable sc maplen vb3 v16 : Z),
let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
let P0 := B + 16 + stride * k in
let slack := (stride - 4 - n) / 16 in
let off0 := (if vb3 =? 0 then Z.land ctr 255 else Z.land (v16 + 1) 255) in
let off := fold_off off0 slack in
bv_unsigned nw = n ->
stride = (if (last_idx =? 0) && negb (maplen =? 0) then maplen * 4096 - 16 else 16 * size_class sc) ->
((last_idx =? 0) && negb (maplen =? 0) = false -> sc < 48) ->
mem_inv segs m ->
rw_cells segs m (bv_unsigned gw) [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
wr_at segs m (P0 - 4) stride ->
ov_read_bytes segs m (wa (P0 - 3)) 1 = Some [b8 vb3] ->
ov_read_bytes segs m (wa (P0 - 2)) 2 = Some (le2 (wz v16)) ->
ov_read_bytes segs m (wa (P0 - 4)) 1 = Some [b8 0] ->
P0 + stride <= 2^64 -> (P0 + stride <= bv_unsigned gw \/ bv_unsigned gw + 40 <= P0 - 4) ->
0 <= B -> 0 <= n -> n + 4 <= stride -> stride - 4 - n < 2^31 ->
(forall off', 0 <= off' -> 16 * off' + n + 4 <= stride -> P0 + 16 * off' - B < 2^31) -> 0 <= k < 32 ->
0 <= ctr < 2^32 -> 0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
0 <= vb3 < 256 -> 0 <= v16 < 65536 ->
evt segs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (P0 + 16 * off)) F fc
(renframe_off_mem m P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1
gw (wz k) nw (wz (sxv ctr)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof. clear - RDEBRUIJN w_10 w_12 hi_10 lo_12 CODE D_10 E_10 D_12 E_12 ANCH_12 RNG_RDEBRUIJN ROM_RSIZE_CLASSES segs base. gw_expose_fam RDEBRUIJN.
intros until v16. intros mword P0 slack off0 off HN HS SC48 MI MM WR R3 R2 R4 PTOP SEPG B0 N0 NS SS PBS HK CT LI FB SC ML VB V16.
pose proof (bv_unsigned_in_range _ gw) as GWR. change (bv_modulus 64) with (2^64) in GWR.
assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
assert (MW1 : Z.land mword 31 = last_idx).
{ change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (MW5 : Z.land (Z.shiftr mword 5) 126 = 2 * sc) by (subst mword; apply mword_sc; lia).
assert (MW12 : Z.land mword 18446744073709547520 = 4096 * maplen).
{ rewrite land_m4096 by lia. subst mword. Z.div_mod_to_equations. lia. }
assert (MZ : Z.shiftr mword 12 = maplen).
{ rewrite Z.shiftr_div_pow2 by lia. subst mword. change (2^12) with 4096. Z.div_mod_to_equations. lia. }
assert (L255 : Z.land (sxv ctr) 255 = Z.land ctr 255).
{ change 255 with (Z.ones 8). rewrite !Z.land_ones by lia.
rewrite <- (mod_mod_pow2 (sxv ctr) 8 32), sxv_mod32, (mod_mod_pow2 ctr 8 32) by lia. reflexivity. }
assert (OF0 : 0 <= off0 < 256).
{ subst off0. destruct (vb3 =? 0); (split; [apply Z.land_nonneg; lia|]);
change 255 with (Z.ones 8); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia. }
assert (SK0 : 0 <= stride * k) by (apply Z.mul_nonneg_nonneg; lia).
assert (ST16 : 16 <= stride /\ B + 16 <= P0).
{ split; [| subst P0; lia]. rewrite HS. destruct ((last_idx =? 0) && negb (maplen =? 0)) eqn:E.
- apply andb_prop in E. destruct E as [_ E2]. destruct (Z.eqb_spec maplen 0); [discriminate|]. lia.
- pose proof (size_class_range sc ltac:(specialize (SC48 eq_refl); lia)). lia. }
destruct ST16 as [ST16 BP0].

step. step. rewrite (wz_unsigned mword), MZ by lia.

assert (JOIN : forall a5',
evt segs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (P0 + 16 * off)) F fc
(renframe_off_mem m P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1
gw (wz k) nw (wz (sxv ctr)) (Z_to_bv 64 stride) a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x40)) fc None m (seg_rom segs))).
{ intros a5'.
pose proof (sxv_range ctr) as RC.
assert (Eoff0 : off0 = (if vb3 =? 0 then Z.land ctr 255 else Z.land (v16 + 1) 255)) by first [reflexivity | (cbn; lia)].
assert (EP0 : P0 = B + 16 + stride * k) by first [reflexivity | (cbn; lia)].
assert (Eoff : off = fold_off off0 slack) by first [reflexivity | (cbn; lia)].
assert (Esl : slack = (stride - 4 - n) / 16) by first [reflexivity | (cbn; lia)].
clearbody off slack off0 P0 mword. clear MW1 MW5 MW12 MZ HS SC48.

step. step. step. rewrite ?(wz_unsigned k), ?(wz_unsigned B), ?(unsigned_lit stride) by lia.

replace (wa (P0 - 3)) with (Z_to_bv 64 (B + stride * k + 13)) in R3 by (unfold wa; f_equal; lia).
lazymatch type of R2 with ?T => change T with (frozen T) in R2 end.
lazymatch type of R4 with ?T => change T with (frozen T) in R4 end.
step. rewrite ?zxb_b8 by lia. clear R3.

step. rewrite HN. step. step. replace (B + stride * k + 16) with P0 by lia.
set (p0w := Z_to_bv 64 P0). assert (HP0 : bv_unsigned p0w = P0) by (subst p0w; apply unsigned_lit; lia). clearbody p0w.
replace (wa (P0 - 2)) with (Z_to_bv 64 (bv_unsigned p0w + -2)) in R2 by (unfold wa; f_equal; lia).
replace (wa (P0 - 4)) with (Z_to_bv 64 (bv_unsigned p0w + -4)) in R4 by (unfold wa; f_equal; lia).

step. if_cases KB; zify_cond KB; rewrite ?(wz_unsigned vb3), ?(unsigned_lit vb3) in KB by lia.
-
clear R2. unfold frozen in R4. step. rewrite ?zxb_b8 by lia. clear R4.
step. rewrite (unsigned_lit (stride + - n + -4)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
replace ((stride + - n + -4) / 16) with ((stride - 4 - n) / 16) by (f_equal; lia).
step. rewrite ?(wz_unsigned (sxv ctr)), ?L255 by lia.
step. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?(wz_unsigned 0), ?(unsigned_lit 0) in K4 by lia. lia. }
replace (Z.land ctr 255) with off0 by (rewrite Eoff0, KB; reflexivity).
rewrite Eoff, Esl. eapply renframe_fold_walk.
all: lazymatch goal with
| |- rw_cells _ _ _ [_; _; _; _; _; _] => gw_exact MM
| |- mem_inv _ _ => gw_exact MI
| |- wr_at _ _ _ _ => gw_exact WR
| |- _ => idtac end.
all: first [lia | gw_exact PBS].
-
unfold frozen in R2.
step. rewrite ?zx16_wz by lia. clear R2. step. rewrite (wz_unsigned v16) by lia.
unfold frozen in R4. step. rewrite ?zxb_b8 by lia. clear R4.
step. rewrite (unsigned_lit (stride + - n + -4)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
replace ((stride + - n + -4) / 16) with ((stride - 4 - n) / 16) by (f_equal; lia).
step. rewrite ?(unsigned_lit (v16 + 1)) by lia.
step. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?(wz_unsigned 0), ?(unsigned_lit 0) in K4 by lia. lia. }
replace (Z.land (v16 + 1) 255) with off0 by (rewrite Eoff0; replace (vb3 =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
rewrite Eoff, Esl. eapply renframe_fold_walk.
all: lazymatch goal with
| |- rw_cells _ _ _ [_; _; _; _; _; _] => gw_exact MM
| |- mem_inv _ _ => gw_exact MI
| |- wr_at _ _ _ _ => gw_exact WR
| |- _ => idtac end.
all: first [lia | gw_exact PBS]. }

assert (JOIN2 : forall a5', stride = 16 * size_class sc -> sc < 48 ->
evt segs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (P0 + 16 * off)) F fc
(renframe_off_mem m P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1
gw (wz k) nw (wz (sxv ctr)) (wz mword) a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x24)) fc None m (seg_rom segs))).
{ intros a5' HS16 SC'.
lazymatch type of R2 with ?T => change T with (frozen T) in R2 end.
lazymatch type of R3 with ?T => change T with (frozen T) in R3 end.
lazymatch type of R4 with ?T => change T with (frozen T) in R4 end.
pose proof (Z_shiftr_range mword 5 MWR ltac:(lia)) as R5.
pose proof (size_class_range sc ltac:(lia)) as SZ.

step. rewrite (wz_unsigned mword) by lia. step. step. rewrite (unsigned_lit (mword ≫ 5)), MW5 by lia.
step. step. rewrite ?(unsigned_lit (2 * sc)) by lia.
pose proof (rsize_classes_read m sc MI ltac:(lia)) as RS. gw_expose_fam RDEBRUIJN.

step. rewrite ?zx16_wz by lia.
step. rewrite (wz_unsigned (size_class sc)), (Z.shiftl_mul_pow2 (size_class sc)) by lia.
replace (size_class sc * 2 ^ 4) with stride by lia.
apply JOIN. }

step. if_cases KM; zify_cond KM; rewrite ?(unsigned_lit maplen) in KM by lia.
-
apply JOIN2; [| apply SC48]; rewrite ?HS; replace (maplen =? 0) with true by (symmetry; apply Z.eqb_eq; lia); rewrite ?andb_false_r; cbn [negb andb]; try reflexivity.
all: destruct (last_idx =? 0); reflexivity.
-
step. rewrite (wz_unsigned mword), MW1 by lia.
step. if_cases KL; zify_cond KL; rewrite ?(unsigned_lit last_idx) in KL by lia.
+
apply JOIN2; [| apply SC48]; rewrite ?HS; replace (last_idx =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity.
+
step. step. rewrite (wz_unsigned mword) by lia. rewrite MW12.
step. replace (4096 * maplen + -16) with stride.
2:{ rewrite HS. replace (last_idx =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
replace (maplen =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn. lia. }
step. apply JOIN.
Qed.

End RC__2.

End G.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1.

Import Q2qa.Mq1 Qy5Y.Mq1.
Import Q8QT.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope bv_scope.
Open Scope Z_scope.

Definition get_meta_code (w_36 w_39 w_47 w_48 : Z) : list Z :=
[0x00f57593; 0x00058463; 0x00000023; 0xffc54603; 0xffd54683; 0xffe55583; 0x00060e63; 0x00058463; 0x00000023; 0xff856583; 0x0105d613; 0x00061463; 0x00000023; 0x00459613; 0x40c50633; 0xff063503; 0x01053703; 0xff060613; 0x01f6f693; 0x00c70463; 0x00000023; 0x02053603; 0x01f67713; 0x00d77463; 0x00000023; 0x01852783; 0x00100713; 0x00d7173b; 0x00e7f7b3; 0x00078463; 0x00000023; 0x01c52783; 0x00e7f733; 0x00070463; 0x00000023; 0xfffff737; w_36; 0x00e57733; 0x00073703; w_39; 0x00f70463; 0x00000023; 0x03461713; 0x03a75713; 0x02f00793; 0x02e7ea63; 0x00171713; w_47; w_48; 0x00e78733; 0x00075703; 0x02d707b3; 0x00f5f463; 0x00000023; 0x00168693; 0x02e686b3; 0x00d5f863; 0x0100006f; 0x03f00693; 0x00d70463; 0x00000023; 0x00c65613; 0x00060a63; 0x00861613; 0xfff60613; 0x00b67463; 0x00000023; 0x00008067]%Z.

Definition unlock_code : list Z :=
[0x00052583; 0x0005c463; 0x00008067; 0x80000637; 0xfff60613; 0x00052583; 0x00c586bb; 0x1605272f; 0x00b71663; 0x1ed527af; 0xfe079ae3; 0x0007071b; 0xfeb712e3; 0x80000637; 0x0016061b; 0xfcc586e3; 0x06200893; 0x08100593; 0x00100613; 0xfda00713; 0x00050693; 0x00000073; 0xfae518e3; 0x06200893; 0x00100593; 0x00100613; 0x00068513; 0x00000073; 0x00008067]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (runlock_entry : Z).
Variables (w_36 w_39 w_47 w_48 : Z).
Variables (hi_36 hi_47 : bv 20).
Variables (lo_39 lo_48 : bv 12).
Hypothesis CODE : code_at segs base (get_meta_code w_36 w_39 w_47 w_48).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 272.
Let rget_meta_entry := (base + 0)%Z.
Hypothesis D_36 : decode_any (Z_to_bv 32 w_36) = Some (Auipc 15 hi_36, 4%Z).
Hypothesis E_36 : is_ecall (Z_to_bv 32 w_36) = false.
Hypothesis D_39 : decode_any (Z_to_bv 32 w_39) = Some (Load SZ8 true 15 15 lo_39, 4%Z).
Hypothesis E_39 : is_ecall (Z_to_bv 32 w_39) = false.
Hypothesis D_47 : decode_any (Z_to_bv 32 w_47) = Some (Auipc 15 hi_47, 4%Z).
Hypothesis E_47 : is_ecall (Z_to_bv 32 w_47) = false.
Hypothesis D_48 : decode_any (Z_to_bv 32 w_48) = Some (OpImm ALU_ADD 15 15 lo_48, 4%Z).
Hypothesis E_48 : is_ecall (Z_to_bv 32 w_48) = false.
Hypothesis ANCH_39 : gw_anch (Z.shiftl (bv_signed hi_36) 12 + (base + 144) + bv_signed lo_39)%Z (RATP + 131968).
Hypothesis ANCH_48 : gw_anch (Z.shiftl (bv_signed hi_47) 12 + (base + 188) + bv_signed lo_48)%Z (RDEBRUIJN + 32).
Hypothesis CODE_runlock_entry : code_at segs runlock_entry unlock_code.
Hypothesis AL_runlock_entry_b4 : gw_b4 runlock_entry.
Hypothesis RNG_runlock_entry_code : gw_br runlock_entry 116.
Hypothesis RNG_RATP : gw_br RATP 1896.
Hypothesis LAY_lo_RATP : gw_le (gw_RDATA2_LO + 164) RATP.
Hypothesis LAY_hi_RATP : gw_le ((RATP + 132896)) RIMG_HI.
Hypothesis AL_RATP : gw_al RATP 8.
Hypothesis RNG_RDEBRUIJN : gw_br RDEBRUIJN 159.
Hypothesis LAY_lo_RDEBRUIJN : gw_le (0x10000 + 0) RDEBRUIJN.
Hypothesis LAY_hi_RDEBRUIJN : gw_le ((RDEBRUIJN + 159)) gw_RTEXT_LO.
Hypothesis AL_RDEBRUIJN : gw_al RDEBRUIJN 8.
Hypothesis RNG_RGOT_SSP : gw_br RGOT_SSP 8.
Hypothesis LAY_lo_RGOT_SSP : gw_le (RDATA_LO + 0) RGOT_SSP.
Hypothesis LAY_hi_RGOT_SSP : gw_le ((RGOT_SSP + 8)) gw_RDATA2_LO.
Hypothesis AL_RGOT_SSP : gw_al RGOT_SSP 8.
Hypothesis LAY_win_0 : gw_win (0x10000 + 1) gw_RTEXT_LO.
Hypothesis LAY_win_1 : gw_win (gw_RTEXT_LO + 1) RDATA_LO.
Hypothesis LAY_win_2 : gw_win (RDATA_LO + 1) gw_RDATA2_LO.
Hypothesis LAY_win_3 : gw_win (gw_RDATA2_LO + 1) RIMG_HI.
Hypothesis LAY_win_4 : gw_win RIMG_HI 0x1000000.
Hypothesis AL_win_RIMG_HI : gw_winal RIMG_HI 4096.
Hypothesis AL_win_RDATA_LO : gw_winal RDATA_LO 4096.
Hypothesis AL_win_gw_RTEXT_LO : gw_winal gw_RTEXT_LO 4096.
Hypothesis AL_win_gw_RDATA2_LO : gw_winal gw_RDATA2_LO 4096.
Hypothesis ROM_RSIZE_CLASSES : QZDE.ro_bytes segs (RDEBRUIJN + 32) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSIZE_CLASSES.
Hypothesis ROM_RDEBRUIJN : QZDE.ro_bytes segs RDEBRUIJN OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RDEBRUIJN.
Hypothesis ROM_RSMALL_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 128) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSMALL_CNT.
Hypothesis ROM_RMED_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 155) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RMED_CNT.
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis AL_runlock_entry : gw_al runlock_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_0).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_1).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_2).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_3).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_4).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_5).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_6).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_7).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_8).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_9).

Definition rmrep_shadow_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_shadow_read) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_shadow_read)).
Definition rmrep_shadow_read2 : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_shadow_read2) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_shadow_read2)).
Definition rsize_classes_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rsize_classes_read) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rsize_classes_read)).
Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).
Definition rmrep_group_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_group_read) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_group_read)).
Definition rmrep_area_check_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_area_check_read) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_area_check_read)).
Definition rmrep_ctx_secret_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_ctx_secret_read) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_ctx_secret_read)).

#[using="runlock_entry RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_36 E_36 D_39 E_39 D_47 E_47 D_48 E_48 ANCH_39 ANCH_48 CODE_runlock_entry AL_runlock_entry_b4 RNG_runlock_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_runlock_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rget_meta_entry"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

#[using="base rget_meta_entry"] Lemma land_pow2_testbit a i : 0 <= a -> 0 <= i -> Z.land a (2 ^ i) = 0 <-> Z.testbit a i = false.
Proof. clear - base rget_meta_entry a i.
intros Ha Hi. split.
- intros H. destruct (Z.testbit a i) eqn:E; [|reflexivity]. exfalso.
assert (T : Z.testbit (Z.land a (2 ^ i)) i = true) by (rewrite Z.land_spec, E, Z.pow2_bits_true by lia; reflexivity).
rewrite H, Z.bits_0 in T. discriminate.
- intros H. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z.eq_dec n i) as [->|NE]; [rewrite H; reflexivity|].
rewrite (Z.pow2_bits_false i n) by lia. apply andb_false_r.
Qed.

#[using="base rget_meta_entry"] Lemma sllw1_word' i : 0 <= i < 32 -> Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (i mod 32))) = wz (sxv (2 ^ i)).
Proof. clear - base rget_meta_entry i. intros Hi. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity. Qed.

Definition rget_meta_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 a7 gw : word) (off16 : Z)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a2 a3 a4 a5,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 gw (wz off16) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom segs).

#[using="w_36 w_39 w_47 w_48 CODE rget_meta_entry"] Lemma rget_meta_tail : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gw : word) F fc m
(off16 mword maplen : Z),
0 <= off16 < 65536 -> 0 <= mword < 2^64 -> 0 <= maplen < 2^40 -> Z.shiftr mword 12 = maplen ->
(maplen <> 0 -> off16 <= maplen * 256 - 1) ->
evt segs (rget_meta_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 a7 gw off16 F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 gw (wz off16) (wz mword) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0xf4)) fc None m (seg_rom segs)).
Proof. clear - w_36 w_39 w_47 w_48 CODE rget_meta_entry segs base.
intros until maplen. intros O16 MW ML MW4 Hml.
st1. rewrite MW4. st1. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia.
- st1. unfold rget_meta_post. finish.
- st1. st1. st1. if_cases K2; zify_cond K2.
+ st1. unfold rget_meta_post. finish.
+ exfalso. rewrite Z.shiftl_mul_pow2 in K2 by lia. change (2^8) with 256 in K2. change 18446744073709551615 with (Z.ones 64) in K2.
rewrite Z.land_ones, wz_unsigned in K2 by lia. rewrite Z.mod_small in K2 by lia. lia.
Qed.

#[using="w_36 w_39 w_47 w_48 hi_36 hi_47 lo_39 lo_48 CODE D_36 E_36 D_39 E_39 D_47 E_47 D_48 E_48 ANCH_39 ANCH_48 rget_meta_entry"] Lemma rget_meta_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(P G B A : Z) (b3 off16 avail freed last_idx freeable sc maplen secret: Z) (prev next : word),
let idx := Z.land b3 31 in
let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
bv_unsigned a0 = P -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= 2^64 ->
B = P - 16 * off16 - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
ov_read_bytes segs m (wa (P - 4)) 1 = Some [b8 0] ->
ov_read_bytes segs m (wa (P - 3)) 1 = Some [b8 b3] ->
ov_read_bytes segs m (wa (P - 2)) 2 = Some (le2 (wz off16)) ->
ov_read_bytes segs m (wa B) 8 = Some (le8 (wz G)) ->
rw_cells segs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
ov_read_bytes segs m (wa A) 8 = Some (le8 (wz secret)) ->
ov_read_bytes segs m (wa (RATP + 131968)) 8 = Some (le8 (wz secret)) ->
(sc < 48 -> ov_read_bytes segs m (wa ((RDEBRUIJN + 32) + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
(sc < 48 -> size_class sc * idx <= off16 < size_class sc * (idx + 1)) ->
(48 <= sc -> sc = 63) ->
(maplen <> 0 -> off16 <= maplen * 256 - 1) ->
evt segs (rget_meta_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 a7 (wz G) off16 F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof. clear - w_36 w_39 w_47 w_48 hi_36 hi_47 lo_39 lo_48 CODE D_36 E_36 D_39 E_39 D_47 E_47 D_48 E_48 ANCH_39 ANCH_48 rget_meta_entry segs base RATP RDEBRUIJN. gw_expose_fam RATP; gw_expose_fam RDEBRUIJN.
intros until next. intros idx mword HP AL PLO PHI HB HA GLO GHI R4 R3 R2 RG MM RA RC RS B3 O16 AV FR SE LI FB SC ML
Hidx Hav Hfr Hsc Hsc63 Hml.
assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. }
st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
st1.

assert (RG' : ov_read_bytes segs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
{ replace (P - off16 * 16 + -16) with B by lia. gw_exact RG. }
st1.
set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. clearbody gw.
assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
st1. st1. st1. fold idx. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite wz_unsigned in K3 by lia. lia. }

assert (MW1 : Z.land mword 31 = last_idx).
{ change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
st1. st1. rewrite MW1. st1. if_cases K4; zify_cond K4. 2:{ exfalso. lia. }

st1. rewrite sx32_wz_sxv by lia. st1. st1.
rewrite sllw1_word' by lia.
assert (P2 : 0 <= 2 ^ idx < 2^32) by (split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
pose proof (sxv_range avail) as SXA. pose proof (sxv_range (2 ^ idx)) as SXI.
assert (LA : Z.land avail (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit avail idx ltac:(lia) ltac:(lia))); gw_exact Hav).
assert (LF : Z.land freed (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit freed idx ltac:(lia) ltac:(lia))); gw_exact Hfr).
st1. rewrite sxv_land, LA, (sxv_small 0) by lia. st1. if_cases K5; zify_cond K5. 2:{ exfalso. apply K5. reflexivity. }

pose proof (sxv_range freed) as SXF.
st1. rewrite sx32_wz_sxv by lia. st1. rewrite sxv_land, LF, (sxv_small 0) by lia. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }

st1. st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. gw_expose_fam RATP. st1. st1.
if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }

assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
{ rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
st1. st1. rewrite MW2. st1. st1. if_cases K8; zify_cond K8.
-  specialize (Hsc63 ltac:(rewrite ?wz_unsigned in K8 by lia; lia)).
st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned in K9 by lia. lia. }
rewrite GW. eapply rget_meta_tail; eauto.
subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
rewrite Z.div_add, Z.div_small by lia. lia.
- specialize (RS ltac:(rewrite ?wz_unsigned in K8 by lia; lia)). specialize (Hsc ltac:(rewrite ?wz_unsigned in K8 by lia; lia)).
st1. st1. st1. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2.
assert (RS' : ov_read_bytes segs m (Z_to_bv 64 ((RDEBRUIJN + 32) + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
{ replace (Z_to_bv 64 ((RDEBRUIJN + 32) + sc * 2)) with (wa ((RDEBRUIJN + 32) + 2 * sc)) by ((gw_expose_fam RDEBRUIJN; unfold wa); f_equal; lia). gw_exact RS. }
clear RS. pose proof (size_class_range sc ltac:(lia)) as SZ. st1.
try rewrite (Z.mod_small (size_class sc)) by lia. fold idx.
st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
st1. st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
st1. rewrite GW. eapply rget_meta_tail; eauto.
subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
rewrite Z.div_add, Z.div_small by lia. lia.
Qed.

#[using="RDEBRUIJN w_36 w_39 w_47 w_48 hi_36 hi_47 lo_39 lo_48 CODE D_36 E_36 D_39 E_39 D_47 E_47 D_48 E_48 ANCH_39 ANCH_48 RNG_RDEBRUIJN ROM_RSIZE_CLASSES rget_meta_entry"] Lemma rget_meta_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
st (p : aptr) r g gh ar (b3 lo hi : Z),
let sh := get_shadow st (fst p) in
let po := snd p in
let off16 := lo + 256 * hi in
let idx := Z.land b3 31 in
let base_ := aadd p (- (UNIT * off16) - UNIT) in
let mr := get_meta_rec st g in
rmrep st m -> mem_inv segs m ->
(s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
bv_unsigned a0 = r_base r + po -> po mod 16 = 0 ->
16 <= po -> 16 * off16 + 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
cell_read sh (po - 4) = Known 0 -> cell_read sh (po - 3) = Known b3 ->
cell_read sh (po - 2) = Known lo -> cell_read sh (po - 1) = Known hi ->
(s_groups st) !! base_ = Some gh -> g_meta gh = Some g -> meta_slot st g -> 0 <= snd g ->
m_mem mr = Some base_ ->
(s_areas st) !! (area_of g) = Some ar -> a_check ar = c_secret (ctx st) ->
0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 -> 0 <= c_secret (ctx st) < 2^64 ->
0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
idx <= m_last_idx mr -> Z.testbit (m_avail mr) idx = false -> Z.testbit (m_freed mr) idx = false ->
(m_sizeclass mr < 48 -> size_class (m_sizeclass mr) * idx <= off16 < size_class (m_sizeclass mr) * (idx + 1)) ->
(48 <= m_sizeclass mr -> m_sizeclass mr = 63) ->
(m_maplen mr <> 0 -> off16 <= m_maplen mr * 256 - 1) ->
evt segs (rget_meta_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 a7 (wz (conc st g)) off16 F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rget_meta_entry) fc None m (seg_rom segs)).
Proof. clear - RDEBRUIJN w_36 w_39 w_47 w_48 hi_36 hi_47 lo_39 lo_48 CODE D_36 E_36 D_39 E_39 D_47 E_47 D_48 E_48 ANCH_39 ANCH_48 RNG_RDEBRUIJN ROM_RSIZE_CLASSES rget_meta_entry segs.
intros until hi. intros sh po off16 idx base_ mr MR MI Hr Hk HP AL P16 PLO PHI C4 C3 C2 C1 Hgh Hg MS G0 Hmem Har Hchk
AV FR SE LI FB SC ML Hidx Hav Hfr Hsc Hsc63 Hml.
pose proof MR as (WF & CX & GL & AR & GR & SH).
destruct WF as (Hres & WR & DISJ & WA & WG).
destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & _). unfold alloc_ceiling in BC.

destruct (rmrep_shadow_read st m (fst p) r (po - 4) 0 MR Hr Hk ltac:(lia) C4) as [R4 _].
destruct (rmrep_shadow_read st m (fst p) r (po - 3) b3 MR Hr Hk ltac:(lia) C3) as [R3 B3].
destruct (rmrep_shadow_read2 st m (fst p) r (po - 2) lo hi MR Hr Hk ltac:(lia) ltac:(lia) C2 ltac:(replace (po - 2 + 1) with (po - 1) by lia; gw_exact C1)) as (R2 & LO & HI).
rewrite <- le2_lohi in R2 by lia.

destruct (rmrep_group_read st m base_ gh MR Hgh) as [RG _]. rewrite Hg in RG. cbn [pw oconc] in RG.

pose proof (rmrep_meta_chunk st m g MR MS) as MM. fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.

pose proof (rmrep_area_check_read st m (area_of g) ar MR Har) as RA. rewrite Hchk in RA.
pose proof (rmrep_ctx_secret_read st m MR) as RC.

destruct (WG base_ gh Hgh) as (rb & Hrb & _ & Bb0 & _). cbn [base_ aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb.
assert (HB : conc st base_ = (r_base r + po) - 16 * off16 - 16).
{ unfold base_. rewrite conc_aadd by (rewrite Hr; eauto). rewrite (conc_region' st p r Hr). unfold po, UNIT. lia. }
destruct MS as (a & ara & k & Ha & Hkk & Eg).
destruct (WA a ara Ha) as (rg & Hrg & A0 & A1 & AAL & ANG & _).
assert (HG : conc st g = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
{ rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
destruct (WR (fst a) rg Hrg) as (RB0 & RBAL & RL0 & RBC & _). unfold alloc_ceiling in RBC.
assert (Hm : (r_base rg + snd a + (AREA_HDR + META_SIZE * k)) mod 4096 = AREA_HDR + META_SIZE * k).
{ unfold AREA_HDR, META_SIZE, NSLOTS in *.
replace (r_base rg + snd a + (24 + 40 * k)) with ((24 + 40 * k) + (snd a / 4096 + r_base rg / 4096) * 4096) by (Z.div_mod_to_equations; nia).
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (HA : conc st (area_of g) = conc st g - conc st g mod 4096).
{ rewrite HG, Hm. unfold area_of. rewrite Eg. unfold aadd. cbn [fst snd]. rewrite (conc_region st (fst a) _ rg Hrg).
replace ((snd a + (AREA_HDR + META_SIZE * k)) mod 4096) with (AREA_HDR + META_SIZE * k); [lia|].
unfold AREA_HDR, META_SIZE, NSLOTS in *.
replace (snd a + (24 + 40 * k)) with ((24 + 40 * k) + (snd a / 4096) * 4096) by (Z.div_mod_to_equations; nia).
rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
unfold rget_meta_entry.
eapply (rget_meta_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(r_base r + po) (conc st g) (conc st base_) (conc st (area_of g)) b3 off16 (m_avail mr) (m_freed mr)
(m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (c_secret (ctx st))
(pw st (m_prev mr)) (pw st (m_next mr))); try eassumption; try lia.
- replace (r_base r + po - 4) with (r_base r + (po - 4)) by lia. gw_exact R4.
- replace (r_base r + po - 3) with (r_base r + (po - 3)) by lia. gw_exact R3.
- replace (r_base r + po - 2) with (r_base r + (po - 2)) by lia. gw_exact R2.
- intros Hlt. apply rsize_classes_read; [gw_exact MI | lia].
Qed.

Definition runlock_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom segs).

#[using="base CODE_runlock_entry rget_meta_entry"] Lemma runlock_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m,
bv_unsigned a0 = (RATP + 131960) ->
rw_cells segs m (bv_unsigned a0) [C4 (wz 0)] ->
evt segs (runlock_post ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (runlock_entry + 0)) fc None m (seg_rom segs)).
Proof. clear - base CODE_runlock_entry rget_meta_entry segs RATP runlock_entry. gw_expose_fam RATP.
intros until m. intros HA LK. idtac.
step. rewrite sx32_wz by lia. step. if_cases K; zify_cond K.
{ exfalso. rewrite wz_unsigned in K by lia. lia. }
step. apply evt_done. reflexivity.
Qed.

End RC__1.

End G.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1 Q5Rg QytA Ql2m QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Export QytA.
Export Q8QT.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (ralloc_meta_entry : Z).
Hypothesis RNG_RATP : gw_br RATP 1896.
Hypothesis LAY_lo_RATP : gw_le (gw_RDATA2_LO + 164) RATP.
Hypothesis LAY_hi_RATP : gw_le ((RATP + 132896)) RIMG_HI.
Hypothesis AL_RATP : gw_al RATP 8.
Hypothesis RNG_RDEBRUIJN : gw_br RDEBRUIJN 159.
Hypothesis LAY_lo_RDEBRUIJN : gw_le (0x10000 + 0) RDEBRUIJN.
Hypothesis LAY_hi_RDEBRUIJN : gw_le ((RDEBRUIJN + 159)) gw_RTEXT_LO.
Hypothesis AL_RDEBRUIJN : gw_al RDEBRUIJN 8.
Hypothesis RNG_RGOT_SSP : gw_br RGOT_SSP 8.
Hypothesis LAY_lo_RGOT_SSP : gw_le (RDATA_LO + 0) RGOT_SSP.
Hypothesis LAY_hi_RGOT_SSP : gw_le ((RGOT_SSP + 8)) gw_RDATA2_LO.
Hypothesis AL_RGOT_SSP : gw_al RGOT_SSP 8.
Hypothesis LAY_win_0 : gw_win (0x10000 + 1) gw_RTEXT_LO.
Hypothesis LAY_win_1 : gw_win (gw_RTEXT_LO + 1) RDATA_LO.
Hypothesis LAY_win_2 : gw_win (RDATA_LO + 1) gw_RDATA2_LO.
Hypothesis LAY_win_3 : gw_win (gw_RDATA2_LO + 1) RIMG_HI.
Hypothesis LAY_win_4 : gw_win RIMG_HI 0x1000000.
Hypothesis AL_win_RIMG_HI : gw_winal RIMG_HI 4096.
Hypothesis AL_win_RDATA_LO : gw_winal RDATA_LO 4096.
Hypothesis AL_win_gw_RTEXT_LO : gw_winal gw_RTEXT_LO 4096.
Hypothesis AL_win_gw_RDATA2_LO : gw_winal gw_RDATA2_LO 4096.
Hypothesis ROM_RSIZE_CLASSES : QZDE.ro_bytes segs (RDEBRUIJN + 32) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSIZE_CLASSES.
Hypothesis ROM_RDEBRUIJN : QZDE.ro_bytes segs RDEBRUIJN OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RDEBRUIJN.
Hypothesis ROM_RSMALL_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 128) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSMALL_CNT.
Hypothesis ROM_RMED_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 155) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RMED_CNT.
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis AL_ralloc_meta_entry : gw_al ralloc_meta_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_0).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_1).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_2).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_3).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_4).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_5).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_6).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_7).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_8).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)).

#[using="RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved ralloc_meta_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_ralloc_meta_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Section RC__1.

Definition rimplT {R} (o : mem) (t : QUZl.M R) (s : PState)
(Q : R -> PState -> machine_state -> Prop) (ms : machine_state) : Prop :=
implM segs (membed (mrun o t)) s (fun r s' ms' => Q (snd r) s' ms') ms.

#[using="Type"] Lemma rimplT_ret {R} o (r : R) s Q ms : evt segs (Q r s) ms -> rimplT o (SRet r) s Q ms.
Proof. clear - segs R o r s Q ms. intros H. unfold rimplT. rewrite mrun_ret. cbn [membed]. apply implM_ret. gw_exact H. Qed.

#[using="Type"] Lemma rimplT_peek {R} o p c h (k : Z -> QUZl.M R) s Q ms :
rimplT o (k (pans_mem o p c h)) s Q ms -> rimplT o (SVis (EPeek p c h) k) s Q ms.
Proof. clear - R o p c h k s Q ms. intros H. unfold rimplT. rewrite mrun_peek. gw_exact H. Qed.

#[using="Type"] Lemma rimplT_undef {R} o w (k : Z -> QUZl.M R) s Q ms : rimplT o (SVis (EUndef w) k) s Q ms.
Proof. clear - R o w k s Q ms segs.
unfold rimplT. rewrite mrun_vis by exact I. cbn [membed ev_step].
eapply (implM_bind segs _ _ _ (fun _ _ _ => False)); [apply implM_unr|]. intros ? ? ? [].
Qed.

#[using="Type"] Lemma rimplT_vis {R} o e (k : Z -> QUZl.M R) s Q1 Q ms :
match e with EPeek _ _ _ => False | EUndef _ => False | _ => True end ->
implM segs (ev_step e) s Q1 ms ->
(forall z s' ms', Q1 z s' ms' -> rimplT o (k z) s' Q ms') ->
rimplT o (SVis e k) s Q ms.
Proof. clear - segs R o e k s Q1 Q ms.
intros He H K. unfold rimplT. rewrite mrun_vis by (destruct e; auto). cbn [membed].
eapply implM_bind; [gw_exact H|]. intros z s' ms' H1. apply (K z s' ms' H1).
Qed.

#[using="Type"] Lemma rimplT_mono {R} o (t : QUZl.M R) s Q Q' ms :
rimplT o t s Q ms -> (forall r s' ms', Q r s' ms' -> Q' r s' ms') -> rimplT o t s Q' ms.
Proof. clear - R o t s Q Q' ms. intros H HQ. unfold rimplT in *. eapply implM_mono; [gw_exact H|]. intros [o' r] s' ms'; cbn; auto. Qed.

#[using="Type"] Lemma rimplT_evt {R} o (t : QUZl.M R) s Q P ms :
evt segs P ms -> (forall ms', P ms' -> rimplT o t s Q ms') -> rimplT o t s Q ms.
Proof. clear - segs R o t s Q P ms. intros H K. unfold rimplT in *. eapply implM_evt; eauto. Qed.

#[using="Type"] Lemma rimpl_vis_unfold {R} n (k : resp -> itree node R) Q ms :
impl segs (at_node segs) (Vis n k) Q ms = evt segs (fun ms1 => at_node segs n ms1 /\ forall rsp, impl segs (at_node segs) (k rsp) Q (nret ms1 rsp)) ms.
Proof. clear - segs R n k Q ms. reflexivity. Qed.

#[using="Type"] Lemma rimpl_bind_mono {A B C} (t : itree node A) (f1 : A -> itree node B) (f2 : A -> itree node C) Q1 Q2 ms :
impl segs (at_node segs) (QlEo_c1.Mq0.bind _ t f1) Q1 ms ->
(forall r ms', impl segs (at_node segs) (f1 r) Q1 ms' -> impl segs (at_node segs) (f2 r) Q2 ms') ->
impl segs (at_node segs) (QlEo_c1.Mq0.bind _ t f2) Q2 ms.
Proof. clear - segs A B C t f1 f2 Q1 Q2 ms.
revert ms. induction t as [r|n k IH]; intros ms H K; cbn [QlEo_c1.Mq0.bind] in *.
- apply K. gw_exact H.
- rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold. eapply evt_mono; [gw_exact H|].
intros ms1 [Hat Hk]. split; [gw_exact Hat|]. intros rsp. eapply IH; eauto.
Qed.

#[using="Type"] Lemma rmembed_strel {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : QUZl.M R1) (t2 : QUZl.M R2) :
strel RR t1 t2 ->
forall s (Q1 : R1 -> PState -> machine_state -> Prop) (Q2 : R2 -> PState -> machine_state -> Prop) ms,
implM segs (membed t1) s Q1 ms ->
(forall r1 r2 s' ms', RR r1 r2 -> Q1 r1 s' ms' -> Q2 r2 s' ms') ->
implM segs (membed t2) s Q2 ms.
Proof. clear - segs R1 R2 RR t1 t2.
induction 1 as [r1 r2 Hr | e k1 k2 Hk IH]; intros s Q1 Q2 ms H HQ.
- cbn [membed] in *. unfold implM, mret in *. cbn in *. eapply evt_mono; [gw_exact H|]. intros ms' H1. eapply HQ; eauto.
- cbn [membed] in *. unfold implM, mbind in *. unfold ebind in *.
eapply rimpl_bind_mono; [gw_exact H|]. intros [|[z s']] ms' H1; cbn in *.
+ gw_exact H1.
+ eapply IH; [gw_exact H1| gw_exact HQ].
Qed.

#[using="Type"] Lemma rimplT_strel {R1 R2} (RR : mem * R1 -> R2 -> Prop) o (t1 : QUZl.M R1) (t2 : QUZl.M R2) s Q1 Q2 ms :
strel RR (mrun o t1) t2 ->
rimplT o t1 s Q1 ms ->
(forall o1 r1 r2 s' ms', RR (o1, r1) r2 -> Q1 r1 s' ms' -> Q2 r2 s' ms') ->
implM segs (membed t2) s Q2 ms.
Proof. clear - segs R1 R2 RR o t1 t2 s Q1 Q2 ms.
intros Hs H HQ. unfold rimplT in H. eapply (rmembed_strel _ _ _ Hs); [gw_exact H|]. intros [o1 r1] r2 s' ms'; cbn; eauto.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved ROM_reservedZ LAY_ref_reserved"] Lemma rimplM_membed_steq {R} (t1 t2 : QUZl.M R) s Q ms :
steq t1 t2 -> implM segs (membed t1) s Q ms -> implM segs (membed t2) s Q ms.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved ROM_reservedZ LAY_ref_reserved segs R t1 t2 s Q ms.
intros Hs H. apply strel_eq_steq in Hs. eapply (rmembed_strel eq t1 t2 Hs); [gw_exact H|]. intros; subst; auto.
Qed.

#[using="Type"] Lemma rimplM_membed_sbind {R S} (T : QUZl.M R) (F : R -> QUZl.M S) s Q1 Q ms :
implM segs (membed T) s Q1 ms ->
(forall x s' ms', Q1 x s' ms' -> implM segs (membed (F x)) s' Q ms') ->
implM segs (membed (sbind T F)) s Q ms.
Proof. clear - segs R S T F s Q1 Q ms.
revert s ms. induction T as [x|e k IH]; intros s ms H K.
- cbn [sbind membed] in *. unfold implM, mret in H. cbn in H. eapply implM_evt; [gw_exact H|]. intros ms' H1. exact (K x s ms' H1).
- cbn [sbind membed] in *. unfold implM, mbind, ebind in *.
eapply rimpl_bind_mono; [gw_exact H|]. intros [|[z s']] ms' H1; cbn in *.
+ gw_exact H1.
+ eapply IH; [gw_exact H1|gw_exact K].
Qed.

#[using="Type"] Lemma rimplT_bind {R S} o (t : QUZl.M R) (f : R -> QUZl.M S) s Q1 Q ms :
rimplT o t s Q1 ms ->
(forall r s' ms', Q1 r s' ms' -> rimplT o (f r) s' Q ms') ->
rimplT o (sbind t f) s Q ms.
Proof. clear - R S o t f s Q1 Q ms.
unfold rimplT, mrun, prun. revert s ms. induction t as [r|e k IH]; intros s ms H K.
- cbn [sbind]. cbn [eruns membed] in H. unfold implM, mret in H. cbn in H.
eapply implM_evt; [gw_exact H|]. intros ms' H1. exact (K r s ms' H1).
- cbn [sbind eruns]. cbn [eruns] in H. unfold pupd_mem in *. destruct (psel pans_mem o e) as [a|].
+ eapply IH; [gw_exact H|gw_exact K].
+ cbn [membed]. cbn [membed] in H. unfold implM, mbind, ebind in H |- *.
eapply rimpl_bind_mono; [gw_exact H|]. intros [|[z s']] ms' H1; cbn in *.
* gw_exact H1.
* eapply IH; [gw_exact H1|gw_exact K].
Qed.

#[using="Type"] Lemma rimplT_from_evt {R} o (t : QUZl.M R) s Q ms :
evt segs (fun ms' => rimplT o t s Q ms') ms -> rimplT o t s Q ms.
Proof. clear - segs R o t s Q ms. intros H. eapply rimplT_evt; [gw_exact H|]. intros ms' H'; gw_exact H'. Qed.
End RC__1.
Section RC__2.

#[using="Type"] Lemma rimplM_msys_ret {A B} n (dec : resp -> option A) (f : A -> B) (P : A -> machine_state -> Prop)
(s : PState) (Q : B -> PState -> machine_state -> Prop) ms :
impl segs (at_node segs) (enode n dec) (epost P) ms ->
(forall a ms', P a ms' -> evt segs (Q (f a) s) ms') ->
implM segs (mbind (msys n dec) (fun a => mret (f a))) s Q ms.
Proof. clear - segs A B n dec f P s Q ms.
intros H K. unfold implM, mbind, msys, mret, ebind, enode in *.
cbn [QlEo_c1.Mq0.bind]. rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold.
eapply evt_mono; [gw_exact H|]. intros ms1 [Hat Hk]. split; [gw_exact Hat|]. intros rsp. specialize (Hk rsp).
destruct (dec rsp) as [a|]; cbn in *.
- eapply evt_cut; [gw_exact Hk|]. intros ms' HP. cbn in HP. apply K. gw_exact HP.
- gw_exact Hk.
Qed.

#[using="Type"] Lemma rimplT_mmap_rw {R} o len (k : Z -> QUZl.M R) s (P : mmap_ans -> machine_state -> Prop) Q ms :
impl segs (at_node segs) (enode (NMmap 0 len 3 34) (dec_mmap len [])) (epost P) ms ->
(forall a ms', P a ms' -> rimplT o (k (mmap_val a)) s Q ms') ->
rimplT o (SVis (EMmap 0 len PROT_RW (MAP_PRIVATE + MAP_ANON)) k) s Q ms.
Proof. clear - segs R o len k s P Q ms.
intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = mmap_val a /\ P a ms')); [exact I| |].
- cbn [ev_step PROT_RW MAP_PRIVATE MAP_ANON Z.add negb Z.eqb Z.land MAP_FIXED_Z Pos.land].
eapply rimplM_msys_ret; [gw_exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
- intros z s' ms' (-> & a & -> & HP). exact (K a ms' HP).
Qed.

#[using="Type"] Lemma rimplT_mmap_none {R} o len (k : Z -> QUZl.M R) s (P : mmap_ans -> machine_state -> Prop) Q ms :
impl segs (at_node segs) (enode (NMmap 0 len 0 34) (dec_mmap_none len [])) (epost P) ms ->
(forall a ms', P a ms' -> rimplT o (k (mmap_val a)) s Q ms') ->
rimplT o (SVis (EMmap 0 len PROT_NONE (MAP_PRIVATE + MAP_ANON)) k) s Q ms.
Proof. clear - segs R o len k s P Q ms.
intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = mmap_val a /\ P a ms')); [exact I| |].
- cbn [ev_step PROT_NONE MAP_PRIVATE MAP_ANON Z.add negb Z.eqb Z.land MAP_FIXED_Z Pos.land].
eapply rimplM_msys_ret; [gw_exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
- intros z s' ms' (-> & a & -> & HP). exact (K a ms' HP).
Qed.

#[using="Type"] Lemma rimplT_mmap_fixed {R} o addr len (k : Z -> QUZl.M R) s (P : fixed_ans -> machine_state -> Prop) Q ms :
impl segs (at_node segs) (enode (NMmap addr len 0 50) (dec_mmap_fixed addr len)) (epost P) ms ->
(forall a ms', P a ms' -> rimplT o (k (fixed_val addr a)) s Q ms') ->
rimplT o (SVis (EMmap addr len PROT_NONE (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) k) s Q ms.
Proof. clear - segs R o addr len k s P Q ms.
intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = fixed_val addr a /\ P a ms')); [exact I| |].
- cbn [ev_step PROT_NONE MAP_PRIVATE MAP_ANON MAP_FIXED Z.add negb Z.eqb Z.land MAP_FIXED_Z Pos.land].
eapply rimplM_msys_ret; [gw_exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
- intros z s' ms' (-> & a & -> & HP). exact (K a ms' HP).
Qed.

#[using="Type"] Lemma rimplT_munmap {R} o addr len (k : Z -> QUZl.M R) s (P : range_ans -> machine_state -> Prop) Q ms :
impl segs (at_node segs) (enode (NMunmap addr len) (dec_munmap addr len)) (epost P) ms ->
(forall a ms', P a ms' -> rimplT o (k (range_val a)) s Q ms') ->
rimplT o (SVis (EMunmap addr len) k) s Q ms.
Proof. clear - segs R o addr len k s P Q ms.
intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = range_val a /\ P a ms')); [exact I| |].
- cbn [ev_step]. eapply rimplM_msys_ret; [gw_exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
- intros z s' ms' (-> & a & -> & HP). exact (K a ms' HP).
Qed.

#[using="Type"] Lemma rimplT_mprotect {R} o addr len prot (k : Z -> QUZl.M R) s (P : range_ans -> machine_state -> Prop) Q ms :
impl segs (at_node segs) (enode (NMprotect addr len prot) (dec_mprotect_rw addr len)) (epost P) ms ->
(forall a ms', P a ms' -> rimplT o (k (range_val a)) s Q ms') ->
rimplT o (SVis (EMprotect addr len prot) k) s Q ms.
Proof. clear - segs R o addr len prot k s P Q ms.
intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = range_val a /\ P a ms')); [exact I| |].
- cbn [ev_step]. eapply rimplM_msys_ret; [gw_exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
- intros z s' ms' (-> & a & -> & HP). exact (K a ms' HP).
Qed.

#[using="Type"] Lemma rimplT_brk0 {R} o (k : Z -> QUZl.M R) s (P : Z -> machine_state -> Prop) Q ms :
impl segs (at_node segs) (enode (NBrk 0) dec_brk0) (epost P) ms ->
(forall r ms', P r ms' -> rimplT o (k r) (set_brk_ps r s) Q ms') ->
rimplT o (SVis (EBrk 0) k) s Q ms.
Proof. clear - segs R o k s P Q ms.
intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = set_brk_ps z s /\ P z ms')); [exact I| |].
- cbn [ev_step Z.eqb]. unfold implM, mbind, msys, mupd, mret, ebind, enode in *.
cbn [QlEo_c1.Mq0.bind]. rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold.
eapply evt_mono; [gw_exact H|]. intros ms1 [Hat Hk]. split; [gw_exact Hat|]. intros rsp. specialize (Hk rsp).
destruct (dec_brk0 rsp) as [a|]; cbn in *; [|gw_exact Hk].
eapply evt_mono; [gw_exact Hk|]. intros ms' HP. cbn in HP |- *. auto.
- intros z s' ms' (-> & HP). exact (K z ms' HP).
Qed.

#[using="Type"] Lemma rimplT_brk {R} o req (k : Z -> QUZl.M R) s (P : brk_ans -> machine_state -> Prop) Q ms :
req <> 0 ->
impl segs (at_node segs) (enode (NBrk req) (dec_brk (ps_brk s) req)) (epost P) ms ->
(forall a ms', P a ms' ->
rimplT o (k (match a with BrkGrown => req | BrkSame => ps_brk s end))
(match a with BrkGrown => set_brk_ps req s | BrkSame => s end) Q ms') ->
rimplT o (SVis (EBrk req) k) s Q ms.
Proof. clear - segs R o req k s P Q ms.
intros Hr H K.
eapply (rimplT_vis o _ k s (fun z s' ms' => exists a, P a ms' /\
z = match a with BrkGrown => req | BrkSame => ps_brk s end /\
s' = match a with BrkGrown => set_brk_ps req s | BrkSame => s end)); [exact I| |].
- cbn [ev_step]. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; gw_exact Hr).
unfold implM, mbind, msys, mget, mupd, mret, ebind, enode in *.
cbn [QlEo_c1.Mq0.bind fst snd]. rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold.
eapply evt_mono; [gw_exact H|]. intros ms1 [Hat Hk]. split; [gw_exact Hat|]. intros rsp. specialize (Hk rsp).
destruct (dec_brk (ps_brk s) req rsp) as [a|]; cbn in *; [|gw_exact Hk].
destruct a; cbn in *; (eapply evt_mono; [gw_exact Hk|]); intros ms' HP; cbn in HP |- *; eexists; eauto.
- intros z s' ms' (a & HP & -> & ->). exact (K a ms' HP).
Qed.

#[using="Type"] Lemma rimplT_reach {R} o (t : QUZl.M R) : forall s Q ms,
rimplT o t s Q ms -> rimplT o t s (fun r s' ms' => Q r s' ms' /\ leaf_of o t r) ms.
Proof. clear - R o t.
induction t as [r|e k IH]; intros s Q ms H.
- unfold rimplT, implM in *. rewrite mrun_ret in *. cbn [membed] in *. unfold mret in *. cbn in *.
eapply evt_mono; [gw_exact H|]. intros ms' HQ. split; [gw_exact HQ| apply leaf_of_ret].
- destruct e as [addr|addr len prot flags|addr len|addr len prot|p c h|w|ra ol nl fl].
5:{ apply rimplT_peek. eapply rimplT_mono; [apply IH; unfold rimplT in H |- *; rewrite mrun_peek in H; gw_exact H|].
cbn. intros r s' ms' [HQ HL]. split; [gw_exact HQ|]. apply leaf_of_peek. gw_exact HL. }
5:{ apply rimplT_undef. }
all: unfold rimplT in H |- *; rewrite mrun_vis in H |- * by exact I; cbn [membed] in H |- *;
unfold implM, mbind, ebind in H |- *;
eapply rimpl_bind_mono; [gw_exact H|]; intros [|[z s']] ms' H1; cbn in H1 |- *; [gw_exact H1|];
pose proof (IH z s' Q ms') as IH1; unfold rimplT, implM in IH1;
eapply impl_epost_mono; [apply IH1; gw_exact H1|];
intros [[o1 r] s2] ms2; cbn; intros [HQ HL]; split; [gw_exact HQ| apply (leaf_of_vis o _ k z); [exact I| gw_exact HL]].
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved ROM_reservedZ LAY_ref_reserved"] Lemma rraw_malloc_bridge : forall st s n (o : mem) Q1 Q ms,
strip st = ps_m s ->
rimplT o (malloc st n) s Q1 ms ->
(forall st' (p : optr) s' ms' (r : option bptr),
Q1 (st', p) s' ms' -> ptr_rel p r ->
(forall b, r = Some b -> snd b = fresh_off (strip st') (fst b) n) ->
Q r (set_m (strip st') s') ms') ->
implM segs (raw_malloc n) s Q ms.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved ROM_reservedZ LAY_ref_reserved segs.
intros st s n o Q1 Q ms Hst H HQ. unfold raw_malloc.
eapply (implM_bind segs _ _ _ (fun a s1 ms1 => a = s /\ s1 = s /\ ms1 = ms)).
{ apply implM_get. apply evt_done. repeat split; reflexivity. }
intros s0 s1 ms1 (-> & -> & ->). cbv beta.
eapply (implM_bind segs _ _ _ (fun r s' ms' => exists st' p, Q1 (st', p) s' ms' /\ MREL (o, (st', p)) r)).
{ rewrite <- Hst. eapply (rimplT_strel MREL o (malloc st n) (cmalloc (strip st) n) s Q1).
- unfold mrun. apply malloc_control. apply pans_mem_range.
- gw_exact H.
- intros o1 [st' p] [cs c] s' ms' HR H1. exists st', p. split; [gw_exact H1|].
unfold MREL in *. cbn in *. gw_exact HR. }
intros [cs c] s' ms' (st' & p & H1 & HR). cbv beta iota.
eapply (implM_bind segs _ _ _ (fun _ s2 ms2 => s2 = set_m cs s' /\ ms2 = ms')).
{ apply implM_upd. apply evt_done. split; reflexivity. }
intros [] s2 ms2 [-> ->]. apply implM_ret. apply evt_done.
unfold MREL in HR. cbn in HR. destruct HR as [Hs Hp]. subst cs.
eapply HQ; [gw_exact H1| |].
- destruct p as [pf|], c as [c|]; cbn in Hp |- *; try gw_exact Hp.
- intros b Hb. destruct c as [c|]; [|discriminate]. inversion Hb; subst. reflexivity.
Qed.

Definition rauxv_list (x3 x4 x5 x16 x6 x11 x12 x23 rnd : Z) : list word :=
map wz [3; x3; 4; x4; 5; x5; 16; x16; 6; x6; 11; x11; 12; x12; 23; x23; 25; rnd; 0; 0].

Definition rauxv_ok (m : mem) (B : Z) : Prop :=
exists av x3 x4 x5 x16 x6 x11 x12 x23 rnd,
rw_cells segs m (RATP + 131736) [C8 (wz av)]
/\ bytes_at segs m av (u64s (rauxv_list x3 x4 x5 x16 x6 x11 x12 x23 rnd))
/\ bytes_at segs m (rnd + 8) (le8 (wz rc_secret))
/\ alloc_ceiling <= B /\ B <= av /\ av + 160 <= 2^64 /\ B <= rnd + 8 /\ rnd + 16 <= 2^64
/\ 0 <= x3 < 2^64 /\ 0 <= x4 < 2^64 /\ 0 <= x5 < 2^64 /\ 0 <= x16 < 2^64 /\ 0 <= x6 < 2^64
/\ 0 <= x11 < 2^64 /\ 0 <= x12 < 2^64 /\ 0 <= x23 < 2^64 /\ 0 <= rnd < 2^64
/\ av mod 8 = 0.

#[using="RNG_RATP"] Lemma rauxv_ok_weaken : forall m B B', rauxv_ok m B -> alloc_ceiling <= B' <= B -> rauxv_ok m B'.
Proof. clear - RNG_RATP RATP. gw_expose_fam RATP.
intros m B B' (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & H) HB.
exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. repeat (split; [tauto|]). lia.
Qed.

#[using="Type"] Lemma rauxv_ok_frame : forall m m' B W,
rauxv_ok m B -> munch W m m' -> wmono segs m m' ->
Forall (fun iv : Z * Z => snd iv <= B /\ (snd iv <= (RATP + 131736) \/ (RATP + 131736) + 8 <= fst iv)) W ->
rauxv_ok m' B.
Proof. clear - segs RATP. gw_expose_fam RATP.
intros m m' B W (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & C & A1 & A2 & H) MU WM FW.
exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. split; [|split; [|split; [|gw_exact H]]].
- eapply rw_cells_transport; eauto. eapply Forall_disjoint_from; [gw_exact FW|]. cbn. intros lo hi [_ ?]. lia.
- eapply bytes_at_transport; eauto. eapply Forall_disjoint_from; [gw_exact FW|]. cbn. intros lo hi [? _]. lia.
- eapply bytes_at_transport; eauto. eapply Forall_disjoint_from; [gw_exact FW|]. cbn. intros lo hi [? _]. lia.
Qed.

#[using="Type"] Lemma rraw_free_bridge : forall st s (p : bptr) (pf : aptr) (o : mem) Q1 Q ms,
strip st = ps_m s ->
hdr_ok pans_mem pupd_mem st pf (fst p) ->
rimplT o (free st (Some pf)) s Q1 ms ->
(forall st' s' ms', Q1 st' s' ms' -> Q tt (set_m (strip st') s') ms') ->
implM segs (raw_free p) s Q ms.
Proof. clear - segs.
intros st s p pf o Q1 Q ms Hst Hh H HQ. unfold raw_free.
eapply (implM_bind segs _ _ _ (fun a s1 ms1 => a = s /\ s1 = s /\ ms1 = ms)).
{ apply implM_get. apply evt_done. repeat split; reflexivity. }
intros s0 s1 ms1 (-> & -> & ->). cbv beta.
eapply (implM_bind segs _ _ _ (fun cs s' ms' => exists st', Q1 st' s' ms' /\ strip st' = cs)).
{ rewrite <- Hst. eapply (rimplT_strel FREL o (free st (Some pf)) (cfree (strip st) (Some (fst p))) s Q1).
- unfold mrun. apply free_control. gw_exact Hh.
- gw_exact H.
- intros o1 st' cs s' ms' HR H1. exists st'. split; [gw_exact H1|]. unfold FREL in HR. gw_exact HR. }
intros cs s' ms' (st' & H1 & <-). cbv beta.
apply implM_upd. apply evt_done. eapply HQ. gw_exact H1.
Qed.

Definition rpres_except (C : Z -> Prop) (m m' : mem) : Prop :=
forall a, 0 <= a < 2^64 -> ~ C a ->
m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

#[using="Type"] Lemma rpres_except_refl C m : rpres_except C m m.
Proof. clear - C m. intros a _ _; auto. Qed.
#[using="Type"] Lemma rpres_except_trans C m1 m2 m3 : rpres_except C m1 m2 -> rpres_except C m2 m3 -> rpres_except C m1 m3.
Proof. clear - C m1 m2 m3. intros H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2]. split; [congruence|auto]. Qed.
#[using="Type"] Lemma rpres_except_mono (C C' : Z -> Prop) m m' : rpres_except C m m' -> (forall a, C a -> C' a) -> rpres_except C' m m'.
Proof. clear - C C' m m'. intros H HC a Ha Hc. apply H; [gw_exact Ha|]. intros Hc'. apply Hc, HC, Hc'. Qed.

#[using="Type"] Lemma rpres_except_of_munch C W m m' :
munch W m m' -> wmono segs m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> rpres_except C m m'.
Proof. clear - segs C W m m'.
intros MU WM HW a Ha Hc. split.
- apply MU. rewrite wa_unsigned by lia. apply HW; assumption.
- apply WM.
Qed.

#[using="Type"] Lemma rpres_except_bytes_at C m m' A bs :
rpres_except C m m' -> bytes_at segs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> ~ C a) ->
bytes_at segs m' A bs.
Proof. clear - segs C m m' A bs.
intros HP (H0 & H1 & HB) HR. split; [gw_exact H0|]. split; [gw_exact H1|].
intros i Hi. rewrite <- (HB i Hi). unfold mrd.
destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _]. rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma rpres_except_wr_at C m m' A n :
rpres_except C m m' -> wr_at segs m A n -> (forall a, A <= a < A + n -> ~ C a) -> wr_at segs m' A n.
Proof. clear - segs C m m' A n.
intros HP (H0 & H1 & HW) HR. split; [gw_exact H0|]. split; [gw_exact H1|].
intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W, HW, Hi.
Qed.

#[using="Type"] Lemma rpres_except_rw_cells C m m' A cs :
rpres_except C m m' -> rw_cells segs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ~ C a) ->
rw_cells segs m' A cs.
Proof. clear - segs C m m' A cs.
intros HP [[Hwf HB] HW] HR. split; [split; [gw_exact Hwf|]|].
- eapply rpres_except_bytes_at; eauto. rewrite cells_bytes_length by assumption. gw_exact HR.
- eapply rpres_except_wr_at; eauto.
Qed.

#[using="Type"] Lemma rpres_except_stk C m m' lo hi :
rpres_except C m m' -> stk segs m lo hi -> (forall a, lo <= a < hi -> ~ C a) -> stk segs m' lo hi.
Proof. clear - segs C m m' lo hi.
intros HP (H0 & H1 & HW) HR. split; [gw_exact H0|]. split; [gw_exact H1|].
intros i Hi. destruct (HP i ltac:(lia) ltac:(apply HR; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. gw_exact Hb.
Qed.

Definition ralloc_fp (K : rkind -> Prop) (st1 : mstate) (lo sp : Z) (a : Z) : Prop :=
lo <= a < sp
\/ errno_addr (Z_to_bv 64 RATP) <= a < errno_addr (Z_to_bv 64 RATP) + 4
\/ (RATP + 131968) <= a < (RATP + 132896)
\/ exists rid r, (s_regions st1) !! rid = Some r /\ K (r_kind r) /\ lr_lo r <= a < r_base r + round_up_pg (r_len r).

Definition RAM_STACK : Z := 144.

#[using="RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_ref_reserved"] Lemma rfresh_image st a : fresh_addr st a -> s_reserved st = ref_reserved -> a < 0x10000 \/ RIMG_HI <= a.
Proof. clear - RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_ref_reserved RIMG_HI ref_reserved st a. gw_expose_win.
intros [_ FR] RS. unfold live_ranges in FR. rewrite RS, LAY_ref_reserved in FR. rewrite ?LAY_ref_reserved in FR.
pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; right; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; right; right; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; right; right; right; left; reflexivity)). lia.
Qed.

Definition ram_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(st : mstate) (s : PState) (lo : Z) (m : mem)
(st1 : mstate) (mo : optr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (pw st1 mo) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
/\ rw_cells segs m' (errno_addr tp) [C4 errv']
/\ rauxv_ok m' (bv_unsigned sp)
/\ rpres_except (fun a => ralloc_fp (fun k => k <> RKGroup) st1 lo (bv_unsigned sp) a \/ fresh_addr st a) m m'
/\ rmrep st1 m' /\ ticks_ok st1
/\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ am_rel st st1 mo
/\ (mo = None -> errv' = Z_to_bv 64 12).

Definition ralloc_meta_stmt (am_pre : mstate -> Prop) : Prop :=
forall (R : Type) (k : mstate -> optr -> QUZl.M R) (bail : QUZl.M R) (o : mem)
(s : PState) (Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word),
am_pre st -> rmrep st m -> ticks_ok st -> brk_link_ps st s ->
rauxv_ok m (bv_unsigned sp) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAM_STACK ->
rw_cells segs m (errno_addr tp) [C4 errv] -> mem_inv segs m ->
tp = Z_to_bv 64 RATP ->
(forall st1 mo s' ms',
ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
brk_link_ps st1 s' ->
rimplT o (k st1 mo) s' Q ms') ->
rimplT o (alloc_meta st k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom segs)).

End RC__2.

End G.
End Mq5.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQLG.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q91D.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q91D.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8QT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8QT.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Local Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenSF GwCallee.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base multf3_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 1792.

Definition multf3_post := Eval cbv beta delta [Q91D.multf3_post] in (Q91D.multf3_post segs).
Definition land_M32_small := Q91D.land_M32_small segs base CODE BASE4 BASER.
Definition land_ones_l := Q91D.land_ones_l segs base CODE BASE4 BASER.
Definition sra63_neg := Q91D.sra63_neg segs base CODE BASE4 BASER.
Definition sra63_pos := Q91D.sra63_pos segs base CODE BASE4 BASER.
Definition Lepi := Q91D.Lepi segs base CODE BASE4 BASER.
Definition Linf := Q91D.Linf segs base CODE BASE4 BASER.
Definition multf3_core := Q91D.multf3_core segs base CODE BASE4 BASER.

Definition LnormA := Q8QT.LnormA segs base CODE BASE4 BASER.
Definition LnormB := Q8QT.LnormB segs base CODE BASE4 BASER.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= g_step_fast.
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

#[using="CODE BASE4 BASER"] Lemma Lbchk : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (h1 sc1 : Z) w3
y8 y9 y13 y18 y19 y20 y21 y22 y23 y24 y30 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv segs m1 ->
munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stk segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
rw_cells segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
(4096 <= bv_unsigned sp)%Z ->
(0 <= h1 < 2^64)%Z -> (-600 <= sc1 <= 16)%Z ->
R = FM_p2b a_hi b_lo b_hi h1 (bv_unsigned w3) sc1 ->
evt segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR ra spw gp tp (Z_to_bv 64 E_bExp) (Z_to_bv 64 h1) (Z_to_bv 64 E_bSig) y8 y9
(Z_to_bv 64 sc1) (Z_to_bv 64 E_sgn) a2 y13 (Z_to_bv 64 E_bAbs) ONES M48 (Z_to_bv 64 E_aExp)
y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 (Z_to_bv 64 (Z.shiftr h1 32)) w3 y30 y31)
F (Z_to_bv 64 (base + 0x5f4)) fc None m1 (seg_rom segs)).
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

#[using="CODE BASE4 BASER"] Lemma Lp2r : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
y8 y9 y13 y18 y19 y20 y21 y22 y23 y24 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv segs m1 ->
munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stk segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
rw_cells segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
(4096 <= bv_unsigned sp)%Z ->
R = FM_p2 a_lo a_hi b_lo b_hi ->
evt segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR ra spw gp tp (Z_to_bv 64 E_bExp) (Z_to_bv 64 E_aSig) (Z_to_bv 64 E_bSig) y8 y9
a0 (Z_to_bv 64 E_sgn) a2 y13 (Z_to_bv 64 E_bAbs) ONES M48 (Z_to_bv 64 E_aExp)
y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 (Z_to_bv 64 (Z.shiftr E_aSig 32)) a0 (Z_to_bv 64 E_aAbs) y31)
F (Z_to_bv 64 (base + 0x3dc)) fc None m1 (seg_rom segs)).
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

#[using="CODE BASE4 BASER"] Lemma Linfr : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
y8 y9 y13 y18 y19 y20 y21 y22 y23 y24 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv segs m1 ->
munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stk segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
rw_cells segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
(4096 <= bv_unsigned sp)%Z ->
R = FM_inf a_lo a_hi b_lo b_hi ->
evt segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR ra spw gp tp (Z_to_bv 64 E_bExp) (Z_to_bv 64 E_aSig) (Z_to_bv 64 E_bSig) y8 y9
a0 (Z_to_bv 64 E_sgn) a2 y13 (Z_to_bv 64 E_bAbs) ONES M48 (Z_to_bv 64 E_aExp)
y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 (Z_to_bv 64 (Z.shiftr E_aSig 32)) a0 (Z_to_bv 64 E_aAbs) y31)
F (Z_to_bv 64 (base + 0x288)) fc None m1 (seg_rom segs)).
Proof.
intros until R. intros MI MU WM ST FR SPLO HR.
pose_word_ranges.
unfold FM_inf in HR. model_in HR.
do 4 zstep. zstep. if_cases K7; zify_cond K7; decide_head HR.
-
do 2 zstep. zstep. if_cases K9; zify_cond K9; decide_head HR.
+
zstep. zstep. if_cases K11; zify_cond K11; decide_head HR.
*  subst R. do 2 zstep. join Lepi; res_words.
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

#[using="CODE BASE4 BASER"] Lemma Lbr : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
y8 y9 y14 y18 y19 y20 y21 y22 y23 y24
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv segs m1 ->
munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stk segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
rw_cells segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
(4096 <= bv_unsigned sp)%Z ->
R = FM_b a_lo a_hi b_lo b_hi ->
evt segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR ra spw gp tp (Z_to_bv 64 E_bExp) (Z_to_bv 64 E_aSig) (Z_to_bv 64 E_bSig) y8 y9
a0 (Z_to_bv 64 E_sgn) a2 a3 y14 ONES M48 (Z_to_bv 64 E_aExp)
y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 (Z_to_bv 64 (Z.shiftr E_aSig 32)) a0 (Z_to_bv 64 E_aAbs)
(Z_to_bv 64 9223372036854775807))
F (Z_to_bv 64 (base + 0x270)) fc None m1 (seg_rom segs)).
Proof.
intros until R. intros MI MU WM ST FR SPLO HR.
pose_word_ranges.
unfold FM_b in HR. model_in HR.
do 3 zstep. zstep. if_cases K5; zify_cond K5; decide_head HR.
-
zstep. zstep. if_cases K6; zify_cond K6; decide_head HR.
+  join Linfr.
+ subst R. do 5 zstep. join Lepi; res_words.
- zstep. zstep. if_cases K6; zify_cond K6; decide_head HR.
+  subst R. do 5 zstep. join Lepi; res_words.
+ join Linfr.
Qed.

#[using="CODE BASE4 BASER"] Lemma Lspec : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
y8 y9 y18 y19 y20 y21 y22 y23 y24 y30 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv segs m1 ->
munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stk segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
rw_cells segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
(4096 <= bv_unsigned sp)%Z ->
R = FM_a a_lo a_hi b_lo b_hi ->
evt segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR ra spw gp tp (Z_to_bv 64 E_bExp) (Z_to_bv 64 E_aSig) (Z_to_bv 64 E_bSig) y8 y9
a0 (Z_to_bv 64 E_sgn) a2 a3 a1 ONES M48 (Z_to_bv 64 E_aExp)
y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 (Z_to_bv 64 (Z.shiftr E_aSig 32)) a0 y30 y31)
F (Z_to_bv 64 (base + 0x254)) fc None m1 (seg_rom segs)).
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

#[using="CODE BASE4 BASER"] Lemma multf3_walk : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
stk segs m (bv_unsigned sp - 80) (bv_unsigned sp) ->
mem_inv segs m ->
(4096 <= bv_unsigned sp)%Z ->
evt segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
(f128_mul_w a_lo a_hi b_lo b_hi) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof.
intros until m. intros ST MI SPLO.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl segs m) as WM.
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
-  join Lspec.
- zstep. zstep. if_cases K2; zify_cond K2; decide_head HR.
+ join Lspec.
+ zstep. join multf3_core. { rewrite unsigned_lit by zrange. reflexivity. }
all: rewrite ?unsigned_lit by zrange; exact HR.
Qed.
End Walk.

Definition multf3_stmt : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
stk segs m (bv_unsigned sp - 80) (bv_unsigned sp) ->
mem_inv segs m ->
(4096 <= bv_unsigned sp)%Z ->
evt segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
(f128_mul (mk128 (bv_unsigned a1) (bv_unsigned a0)) (mk128 (bv_unsigned a3) (bv_unsigned a2))) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).

#[using="CODE BASE4 BASER"] Theorem multf3_spec : multf3_stmt.
Proof.
unfold multf3_stmt. intros.
rewrite f128_mul_words by (pose_word_ranges; assumption).
apply multf3_walk; assumption.
Qed.

End G.
