(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1 Q2qa QVbl QQLG QZAa Lib.CodeAt Lib.StepGen Lib.StepGenSF Lib.GwCallee.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QnDM_c1 Q2qa.
Import QVbl.Mq0.
Import QQLG.Mq0.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4.
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

Definition addtf3_post := Eval cbv beta delta [QQLG.Mq0.addtf3_post] in (QQLG.Mq0.addtf3_post segs).
Definition add_Lret := QQLG.Mq0.add_Lret segs base CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec.
Definition add_LM8 := QQLG.Mq0.add_LM8 segs base CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec.
Definition add_LM7 := QQLG.Mq0.add_LM7 segs base CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec.
Ltac unfold_sfw := cbv beta delta [add64 sub64 shl64 not64 is_neg64 sra63 lt_s64 eqz64 nez64 zext32 lo64 hi64 wrap64
ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI IMPL3_HI SPEC_K].

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

Lemma add_L658 : forall x1 x5 x6 x7 x8 x9 x18 x19 x20 x28 x29 x30 x31 (xHi SLo aExp shiftS d mask nhi r : Z),
(0 <= xHi < 2^64)%Z -> (0 <= SLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z -> (0 <= shiftS < 2^64)%Z ->
(0 <= d < 2^64)%Z -> (0 <= nhi < 2^64)%Z ->
(if 9223372036854775808 <=? d then 18446744073709551615 else 0)%Z = mask ->
r = subR3 xHi SLo aExp shiftS mask nhi ->
evt segs (POST r) (ST (base + 0x640) fc x1 x5 x6 x7 x8 x9 (Z_to_bv 64 nhi) (Z_to_bv 64 SLo) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 shiftS) (Z_to_bv 64 d) x18 x19 x20 x28 x29 x30 x31).
Proof using CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec FR FRM MI MU STK WM.
intros until r. intros R1 R2 R3 R4 R5 R6 Hm HR. subst r. unfold subR3, shl128_lo, add_M7. unfold_sfw.
assert (Rm : (0 <= mask < 2^64)%Z) by (rewrite <- Hm; destruct (Z.leb _ _); lia).
zstep. zstep. rewrite (srai63_word d), Hm by lia.
zstep. name_reg 11%Z nlo.
zstep. model_reg 15%Z aExp2 (Z.land (aExp - shiftS) W64).
do 3 zstep. zstep. model_reg 18%Z signHi (Z.land (Z.shiftl (Z.shiftr xHi 63) 63) W64).
zstep. if_cases K; rewrite ?bv_lts_lxor in K; zify_cond K; decide_tests_b.
-
do 5 zstep. eapply add_Lret; finL.
- eapply add_LM8; finL.
Qed.

Lemma add_L488 : forall x1 x5 x6 x7 x8 x9 x18 x19 x20 x28 x29 x30 x31 (xHi SHi SLo aExp word hz r : Z),
(0 <= xHi < 2^64)%Z -> (0 <= SHi < 2^64)%Z -> (0 <= SLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
(0 <= word < 2^64)%Z -> (0 <= hz <= 1)%Z ->
r = subR2 xHi SHi SLo aExp word hz ->
evt segs (POST r) (ST (base + 0x470) fc x1 x5 x6 x7 x8 x9 (Z_to_bv 64 SHi) (Z_to_bv 64 SLo) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 hz) (Z_to_bv 64 word) x18 x19 x20 x28 x29 x30 x31).
Proof using CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec FR FRM MI MU STK WM.
intros until r. intros R1 R2 R3 R4 R5 R6 HR. subst r. unfold subR2, clz128_w. unfold shl128_mirror. unfold_sfw.

do 5 zstep. model_reg 17%Z x1_ (Z.lor word (Z.shiftr word 1)).
do 5 zstep. model_reg 17%Z x2_ (Z.lor x1_ (Z.shiftr x1_ 2)).
do 8 zstep. model_reg 17%Z x3_ (Z.lor x2_ (Z.shiftr x2_ 4)).
do 2 zstep. model_reg 17%Z x4_ (Z.lor x3_ (Z.shiftr x3_ 8)).
do 2 zstep. model_reg 17%Z x5_ (Z.lor x4_ (Z.shiftr x4_ 16)).
do 2 zstep. model_reg 17%Z x6_ (Z.lor x5_ (Z.shiftr x5_ 32)).
zstep. model_reg 17%Z y_ (Z.lxor x6_ W64).
do 4 zstep. model_reg 17%Z c1_ (Z.land (y_ - Z.land (Z.shiftr y_ 1) 6148914691236517205) W64).
do 6 zstep. model_reg 17%Z c2_ (Z.land (Z.land c1_ 3689348814741910323 + Z.land (Z.shiftr c1_ 2) 3689348814741910323) W64).
do 4 zstep. model_reg 17%Z c3_ (Z.land (Z.land (c2_ + Z.shiftr c2_ 4) W64) 1085102592571150095).
do 3 zstep. model_reg 17%Z c4_ (Z.shiftr (Z.land (c3_ * 72340172838076673) W64) 56).
replace (Z_to_bv 64 c4_) with (Z_to_bv 64 (clz64_mirror word)) by (f_equal; model_eval; reflexivity).
name_as_by clz64v (clz64_mirror word) (apply clz64_mirror_range).
zstep. rewrite (land_W64_small (Z.shiftl hz 6)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
name_reg 16%Z clzS.
zstep. model_reg 16%Z shiftS (Z.land (clzS - 12) W64).
zstep. zstep. name_reg 5%Z n. zstep. model_reg 17%Z d (Z.land (n - 64) W64).
zstep. if_cases Kd; zify_cond Kd; decide_tests_b.
-
zstep. zstep. zstep. zstep. name_as_by sr0 (Z.shiftr (Z.shiftr SLo 1) (Z.land (Z.lxor n W64) 63))
(change (inr64 (Z.shiftr (Z.shiftr SLo 1) (Z.land (Z.lxor n W64) 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
zstep. name_reg 10%Z nhi.
eapply add_L658 with (mask := 18446744073709551615%Z); finL.
-
zstep. model_reg 10%Z nhi (Z.land (Z.shiftl SLo (Z.land n 63)) W64). zstep.
eapply add_L658 with (mask := 0%Z); finL.
Qed.

Lemma add_Lsub : forall x1 x6 x8 x9 x11 x17 x18 x19 x20 x28 x29 x30 x31 (xHi AHi ALo BHi BLo aExp r : Z),
(0 <= xHi < 2^64)%Z -> (0 <= AHi < 2^64)%Z -> (0 <= ALo < 2^64)%Z -> (0 <= BHi < 2^64)%Z -> (0 <= BLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
r = add_M6s xHi AHi ALo BHi BLo aExp ->
evt segs (POST r) (ST (base + 0x42c) fc x1 (Z_to_bv 64 ALo) x6 (Z_to_bv 64 BLo) x8 x9 (Z_to_bv 64 AHi) x11 (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 BHi) x17 x18 x19 x20 x28 x29 x30 x31).
Proof using CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec FR FRM MI MU STK WM.
intros until r. intros R1 R2 R3 R4 R5 R6 HR. subst r. unfold add_M6s, addsub_sub. unfold_sfw. rewrite ?b2z_Zb2z.
do 4 zstep. if_cases Kz; zify_cond Kz; decide_tests_b.
-
zstep. name_reg 11%Z borrow.
zstep. zstep. model_reg 10%Z SHi (Z.land (Z.land (AHi - BHi) W64 - borrow) W64).
zstep. zstep. model_reg 11%Z SLo (Z.land (ALo - BLo) W64).
zstep. if_cases Kr; zify_cond Kr; decide_tests_b.
+  eapply add_LM7; finL.
+
rewrite clz128_mirror_w. rewrite ?b2z_Zb2z.
zstep. rewrite (ltb1_eqb0 SHi) by lia. zstep. zstep. if_cases Kw; zify_cond Kw; decide_tests_b.
*  change (Z.b2z true) with 1%Z. eapply add_L488; finL.
* change (Z.b2z false) with 0%Z. zstep. eapply add_L488; finL.
-
do 3 zstep. eapply add_Lret; finL.
Qed.

Lemma add_Ladd : forall x1 x6 x8 x9 x11 x17 x18 x19 x20 x28 x29 x30 x31 (xHi AHi ALo BHi BLo aExp r : Z),
(0 <= xHi < 2^64)%Z -> (0 <= AHi < 2^64)%Z -> (0 <= ALo < 2^64)%Z -> (0 <= BHi < 2^64)%Z -> (0 <= BLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
r = add_M6a xHi AHi ALo BHi BLo aExp ->
evt segs (POST r) (ST (base + 0x5a8) fc x1 (Z_to_bv 64 ALo) x6 (Z_to_bv 64 BLo) x8 x9 (Z_to_bv 64 AHi) x11 (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 BHi) x17 x18 x19 x20 x28 x29 x30 x31).
Proof using CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec FR FRM MI MU STK WM.
intros until r. intros R1 R2 R3 R4 R5 R6 HR. subst r. unfold add_M6a, addsub_add. unfold_sfw. rewrite ?b2z_Zb2z.
zstep. model_reg 11%Z SLo (Z.land (BLo + ALo) W64).
zstep. name_reg 17%Z carry.
zstep. zstep.
replace (Z_to_bv 64 (BHi + AHi + carry)) with (Z_to_bv 64 (Z.land (Z.land (BHi + AHi) W64 + carry) W64))
by (apply Z_to_bv_eqm; rewrite !land_W64; Z.div_mod_to_equations; lia).
name_as SHi (Z.land (Z.land (BHi + AHi) W64 + carry) W64).
zstep. zstep. if_cases Kc; zify_cond Kc; decide_tests_b.
-  eapply add_LM7; finL.
-
zstep. name_reg 16%Z st.
do 5 zstep. name_reg 11%Z SLo2.
zstep. model_reg 15%Z aExp2 (Z.land (aExp + 1) W64).
eapply add_LM7; finL.
Qed.
End Proofs.

End G.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.SepCache QWxq_c1 QgoP Q3CA Lib.StepGenX Lib.StepGenX2 Lib.GwApply Lib.GwFold.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0.

Import QgoP.
Import Q3CA.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope bv_scope.

Definition intscan_code (w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 : Z) : list Z :=
[0xfb010113; 0x04113423; 0x04813023; 0x02913c23; 0x03213823; 0x03313423; 0x03413023; 0x01513c23; 0x01613823; 0x01713423; 0x01813023; 0x00058913; 0x02400593; 0x1325ee63; 0x00050493; 0x00100513; 0x12a90863; 0x00068413; 0x00060993; 0x00500a13; 0x02000a93; 0x0140006f; 0x00048513; w_23; 0xff750593; 0x0345f263; 0x0084b503; 0x0b84b583; 0xfeb504e3; 0x00150593; 0x00b4b423; 0x00054503; 0xff750593; 0xff45e2e3; 0xff5500e3; 0x02d00593; 0x00b50663; 0x02b00593; 0x02b51a63; 0x0084b583; 0x0b84b603; 0xfd350513; 0x00a03a33; 0xfffa0a1b; 0x02c58663; 0x00158513; 0x00a4b423; 0x0005c503; 0xfef97593; 0x02058463; 0x06c0006f; 0x00000a13; 0xfef97593; 0x00058c63; 0x05c0006f; 0x00048513; w_56; 0xfef97593; 0x04059663; 0x03000593; 0x04b51263; 0x0084b503; 0x0b84b583; 0x08b50463; 0x00150593; 0x00b4b423; 0x00054503; 0xfdf57593; 0x05800613; 0x08c59263; 0x0084b503; 0x0b84b583; 0x14b50e63; 0x00150593; 0x00b4b423; 0x00054503; 0x1540006f; 0x00091463; 0x00a00913; w_79; w_80; 0x00a585b3; 0x0015c583; 0x0525e863; 0x0c04b503; 0x00054863; 0x0084b503; 0xfff50513; 0x00a4b423; 0x00048513; 0x00000593; w_91; w_92; 0x00000413; 0x01600593; 0x00b52023; 0x4240006f; 0x00048513; w_98; 0xfdf57593; 0x05800613; 0xf8c582e3; 0x12090663; 0x00a00593; 0x12b91463; 0xfd050a9b; 0x00000993; 0x00900913; 0x07596063; 0x00a00b13; 0x1999a537; 0x99950b9b; 0x0200006f; 0x00048513; w_114; 0x036985b3; 0x015589bb; 0xfd050a9b; 0x03596863; 0x0379f663; 0x0084b503; 0x0b84b583; 0xfcb50ee3; 0x00150593; 0x00b4b423; 0x00054503; 0x036985b3; 0x015589bb; 0xfd050a9b; 0xfd597ce3; 0x02099993; 0x0209d993; 0x2d596463; w_133; w_134; 0x00a00513; 0x02a98c33; 0x00900b93; 0x0084b503; 0x0b84b583; 0x02b50063; 0x00150593; 0x00b4b423; 0x00054503; 0x015c09b3; 0xfd050a9b; 0x015bfe63; 0x26c0006f; 0x00048513; w_149; 0x015c09b3; 0xfd050a9b; 0x255bec63; 0x2569fa63; 0x00a00913; 0x03298c33; 0xfffac593; 0xfb85fae3; 0x24c0006f; 0x00048513; w_160; w_161; w_162; 0x00a585b3; 0x0015c583; 0x01000913; 0x0325e863; 0x0c04b503; 0x2e054863; 0x0084b503; 0xfff50593; 0x00b4b423; 0x2e098263; 0x00000413; 0xffe50513; 0x00a4b423; 0x2e40006f; 0x00800913; 0xfff9059b; 0x00b975b3; 0x0e059e63; 0x01700593; w_182; w_183; 0x02b905b3; w_185; w_186; 0x03859593; 0x03d5d593; 0x00b605b3; 0x00aa8633; 0x00164b83; 0x0005cb03; 0x00000993; 0x072bf063; 0x0280006f; 0x00048513; w_197; 0x016995bb; 0x00aa8633; 0x00bbe9b3; 0x00164b83; 0x032bfc63; 0x01b5d59b; 0x02059863; 0x0084b503; 0x0b84b583; 0xfcb50ae3; 0x00150593; 0x00b4b423; 0x00054503; 0x016995bb; 0x00aa8633; 0x00bbe9b3; 0x00164b83; 0xfd2be8e3; 0x02099993; 0x0209d993; 0x152bfe63; 0xfff00593; 0x0165dc33; 0x033c7463; 0x14c0006f; 0x00048513; w_224; 0x016995b3; 0x0175e9b3; 0x00aa85b3; 0x0015cb83; 0x132bf863; 0x133c6663; 0x0084b503; 0x0b84b583; 0xfcb50ce3; 0x00150593; 0x00b4b423; 0x00054503; 0x016995b3; 0x0175e9b3; 0x00aa85b3; 0x0015cb83; 0xfd2beae3; 0x0fc0006f; w_243; w_244; 0x00aa85b3; 0x0015cb03; 0x072b7863; 0x00000993; 0x071c7537; 0x1c750b9b; 0x0240006f; 0x00048513; w_253; 0x032985b3; 0x00bb09bb; 0x00aa85b3; 0x0015cb03; 0x032b7a63; 0x0379f863; 0x0084b503; 0x0b84b583; 0xfcb50ce3; 0x00150593; 0x00b4b423; 0x00054503; 0x032985b3; 0x00bb09bb; 0x00aa85b3; 0x0015cb03; 0xfd2b6ae3; 0x02099993; 0x0209d993; 0x012b6863; 0x07c0006f; 0x00000993; 0x072b7a63; 0x02091593; 0x0205db93; 0x0240006f; 0x00048513; w_281; 0x016c09b3; 0x00aa85b3; 0x0015cb03; 0x052b7863; 0x033bb5b3; 0x04059463; 0x03798c33; 0xfffb4593; 0x0385ee63; 0x0084b503; 0x0b84b583; 0xfcb506e3; 0x00150593; 0x00b4b423; 0x00054503; 0x016c09b3; 0x00aa85b3; 0x0015cb03; 0xfd2b64e3; 0x0100006f; 0x00900593; 0x0155ee63; 0x00a00913; w_305; w_306; 0x00aa8533; 0x00154503; 0x03256e63; 0x0c04b503; 0x00054863; 0x0084b503; 0xfff50513; 0x00a4b423; 0x0689f863; 0x0149c533; 0x41450433; 0x0ac0006f; 0x00048513; w_320; 0x00aa8533; 0x00154503; 0x03257463; 0x0084b503; 0x0b84b583; 0xfeb502e3; 0x00150593; 0x00b4b423; 0x00054503; 0x00aa8533; 0x00154503; 0xff2560e3; w_333; 0x02200593; 0x00b52023; 0x00147513; 0xfff5051b; 0x01457a33; 0x00040993; 0x0c04b503; 0xf80556e3; 0xf95ff06f; 0x00147513; 0x00051e63; 0x000a1c63; w_346; 0x02200593; 0x00b52023; 0xfff40413; 0x02c0006f; 0xf7347ae3; w_352; 0x02200593; 0x00b52023; 0x0180006f; 0x00099863; 0x00048513; 0x00000593; w_359; 0x00000413; 0x00040513; 0x04813083; 0x04013403; 0x03813483; 0x03013903; 0x02813983; 0x02013a03; 0x01813a83; 0x01013b03; 0x00813b83; 0x00013c03; 0x05010113; 0x00008067]%Z.

Definition errno_loc_code : list Z :=
[0x00020513; 0xf5c50513; 0x00008067]%Z.

Definition shlim_code : list Z :=
[0x00853683; 0x01053603; 0x05853703; 0x00b037b3; 0x40d60833; 0x0105a833; 0x0107f7b3; 0x40d70733; 0x0cb53023; 0x0ce53423; 0x00078463; 0x00b68633; 0x0ac53c23; 0x00008067]%Z.

Definition M64m1 : Z := 18446744073709551615.

Definition intscan_table_Z : list Z := [255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 255; 255; 255; 255; 255; 255; 255; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 255; 255; 255; 255; 255; 255; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255]%Z.
Definition intscan_table : list byte := map (Z_to_bv 8) intscan_table_Z.
Definition itab (c : Z) : Z :=
(if (48 <=? c) && (c <=? 57) then c - 48
else if (65 <=? c) && (c <=? 90) then c - 55
else if (97 <=? c) && (c <=? 122) then c - 87 else 255)%Z%bool.

Lemma itab_range : forall c, (0 <= itab c < 256)%Z.
Proof.
intros c. unfold itab.
destruct (Z.leb_spec0 48 c); destruct (Z.leb_spec0 c 57); cbn [andb]; try klia.
all: destruct (Z.leb_spec0 65 c); destruct (Z.leb_spec0 c 90); cbn [andb]; try klia.
all: destruct (Z.leb_spec0 97 c); destruct (Z.leb_spec0 c 122); cbn [andb]; klia.
Qed.

Lemma intscan_table_nth : forall c, (0 <= c < 256)%Z ->
nth_error intscan_table (Z.to_nat (c + 1)) = Some (Z_to_bv 8 (itab c)).
Proof.
intros c Hc.
pose proof (brute256_ok (fun c => match nth_error intscan_table (Z.to_nat (c + 1)) with
| Some b => (bv_unsigned b =? itab c)%Z | None => false end)
ltac:(vm_compute; reflexivity) c Hc) as H.
cbn beta in H. destruct (nth_error intscan_table (Z.to_nat (c + 1))) as [b|]; [|discriminate].
f_equal. apply bv_eq. apply Z.eqb_eq in H. rewrite Z_to_bv_unsigned, bv_wrap_small; [exact H|].
pose proof (itab_range c). unfold bv_modulus. cbn. klia.
Qed.

Lemma itab_lt10 : forall c, (0 <= c < 256)%Z -> (itab c < 10 <-> 48 <= c <= 57)%Z.
Proof.
intros c Hc. unfold itab. destruct (Z.leb_spec0 48 c); destruct (Z.leb_spec0 c 57); cbn [andb]; try klia.
all: destruct (Z.leb_spec0 65 c); destruct (Z.leb_spec0 c 90); cbn [andb]; try klia.
all: destruct (Z.leb_spec0 97 c); destruct (Z.leb_spec0 c 122); cbn [andb]; klia.
Qed.

Lemma swrap32_byte_off : forall c k, (0 <= c < 256)%Z -> (-256 <= k <= 0)%Z -> bv_swrap 32 (c + k) = (c + k)%Z.
Proof. intros c k Hc Hk. rewrite bv_swrap32_eq. rewrite Z.mod_small; klia. Qed.

Lemma digit_test : forall c, (0 <= c < 256)%Z ->
(((c + -48) mod 18446744073709551616 <= 9)%Z <-> (48 <= c <= 57)%Z).
Proof. intros c Hc. split; intros H; Z.div_mod_to_equations; klia. Qed.

Lemma itab_unsigned : forall c, bv_unsigned (Z_to_bv 8 (itab c)) = itab c.
Proof. intros c. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|]. pose proof (itab_range c). unfold bv_modulus; cbn; klia. Qed.

Definition file_cells (j0 j1 j2 j3 : list byte) (rp A shcnt : Z) : list cell :=
[CB 8 j0; C8 (Z_to_bv 64 rp); C8 (Z_to_bv 64 M64m1); CB 64 j1; C8 (Z_to_bv 64 A); CB 88 j2;
C8 (Z_to_bv 64 M64m1); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 shcnt); CB 24 j3].

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 : Z).
Variables (hi_79 hi_133 hi_305 : bv 20).
Variables (lo_80 lo_134 lo_306 : bv 12).
Variables (joff_91 joff_92 joff_333 joff_346 joff_352 : bv 21).
Variables (G_10760 ISTAB RATP RGLOBALS_TOP : Z).
Variables (e_errno_loc e_shlim : Z).
Hypothesis CODE : code_at segs base (intscan_code w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 1496.
Hypothesis D_79 : decode_any (Z_to_bv 32 w_79) = Some (Auipc 11 hi_79, 4%Z).
Hypothesis E_79 : is_ecall (Z_to_bv 32 w_79) = false.
Hypothesis D_80 : decode_any (Z_to_bv 32 w_80) = Some (OpImm ALU_ADD 11 11 lo_80, 4%Z).
Hypothesis E_80 : is_ecall (Z_to_bv 32 w_80) = false.
Hypothesis D_91 : decode_any (Z_to_bv 32 w_91) = Some (Jal 1 joff_91, 4%Z).
Hypothesis E_91 : is_ecall (Z_to_bv 32 w_91) = false.
Hypothesis D_92 : decode_any (Z_to_bv 32 w_92) = Some (Jal 1 joff_92, 4%Z).
Hypothesis E_92 : is_ecall (Z_to_bv 32 w_92) = false.
Hypothesis D_133 : decode_any (Z_to_bv 32 w_133) = Some (Auipc 10 hi_133, 4%Z).
Hypothesis E_133 : is_ecall (Z_to_bv 32 w_133) = false.
Hypothesis D_134 : decode_any (Z_to_bv 32 w_134) = Some (Load SZ8 true 22 10 lo_134, 4%Z).
Hypothesis E_134 : is_ecall (Z_to_bv 32 w_134) = false.
Hypothesis D_305 : decode_any (Z_to_bv 32 w_305) = Some (Auipc 11 hi_305, 4%Z).
Hypothesis E_305 : is_ecall (Z_to_bv 32 w_305) = false.
Hypothesis D_306 : decode_any (Z_to_bv 32 w_306) = Some (OpImm ALU_ADD 21 11 lo_306, 4%Z).
Hypothesis E_306 : is_ecall (Z_to_bv 32 w_306) = false.
Hypothesis D_333 : decode_any (Z_to_bv 32 w_333) = Some (Jal 1 joff_333, 4%Z).
Hypothesis E_333 : is_ecall (Z_to_bv 32 w_333) = false.
Hypothesis D_346 : decode_any (Z_to_bv 32 w_346) = Some (Jal 1 joff_346, 4%Z).
Hypothesis E_346 : is_ecall (Z_to_bv 32 w_346) = false.
Hypothesis D_352 : decode_any (Z_to_bv 32 w_352) = Some (Jal 1 joff_352, 4%Z).
Hypothesis E_352 : is_ecall (Z_to_bv 32 w_352) = false.
Hypothesis ANCH_80 : gw_anch (Z.shiftl (bv_signed hi_79) 12 + (base + 316) + bv_signed lo_80)%Z ISTAB.
Hypothesis ANCH_134 : gw_anch (Z.shiftl (bv_signed hi_133) 12 + (base + 532) + bv_signed lo_134)%Z G_10760.
Hypothesis ANCH_306 : gw_anch (Z.shiftl (bv_signed hi_305) 12 + (base + 1220) + bv_signed lo_306)%Z ISTAB.
Hypothesis LINK_91 : gw_anch (base + 364 + bv_signed joff_91)%Z (e_shlim + 0)%Z.
Hypothesis LINK_92 : gw_anch (base + 368 + bv_signed joff_92)%Z (e_errno_loc + 0)%Z.
Hypothesis LINK_333 : gw_anch (base + 1332 + bv_signed joff_333)%Z (e_errno_loc + 0)%Z.
Hypothesis LINK_346 : gw_anch (base + 1384 + bv_signed joff_346)%Z (e_errno_loc + 0)%Z.
Hypothesis LINK_352 : gw_anch (base + 1408 + bv_signed joff_352)%Z (e_errno_loc + 0)%Z.
Hypothesis CODE_e_errno_loc : code_at segs e_errno_loc errno_loc_code.
Hypothesis CODE_e_shlim : code_at segs e_shlim shlim_code.
Hypothesis RNG_ISTAB : gw_br ISTAB 257.
Hypothesis LAY_lo_ISTAB : gw_le 65536 ISTAB.
Hypothesis RNG_RATP : gw_br RATP 8.
Hypothesis LAY_lo_RATP : gw_le 65536 RATP.
Hypothesis RNG_RGLOBALS_TOP : gw_br RGLOBALS_TOP 8.
Hypothesis LAY_ISTAB_RATP : gw_le (ISTAB + 257) RATP.
Hypothesis LAY_RATP_RGLOBALS_TOP : gw_le (RATP + 8) RGLOBALS_TOP.
Hypothesis ROM_ISTAB : ro_bytes segs ISTAB [Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 2; Z_to_bv 8 3; Z_to_bv 8 4; Z_to_bv 8 5; Z_to_bv 8 6; Z_to_bv 8 7; Z_to_bv 8 8; Z_to_bv 8 9; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 10; Z_to_bv 8 11; Z_to_bv 8 12; Z_to_bv 8 13; Z_to_bv 8 14; Z_to_bv 8 15; Z_to_bv 8 16; Z_to_bv 8 17; Z_to_bv 8 18; Z_to_bv 8 19; Z_to_bv 8 20; Z_to_bv 8 21; Z_to_bv 8 22; Z_to_bv 8 23; Z_to_bv 8 24; Z_to_bv 8 25; Z_to_bv 8 26; Z_to_bv 8 27; Z_to_bv 8 28; Z_to_bv 8 29; Z_to_bv 8 30; Z_to_bv 8 31; Z_to_bv 8 32; Z_to_bv 8 33; Z_to_bv 8 34; Z_to_bv 8 35; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 10; Z_to_bv 8 11; Z_to_bv 8 12; Z_to_bv 8 13; Z_to_bv 8 14; Z_to_bv 8 15; Z_to_bv 8 16; Z_to_bv 8 17; Z_to_bv 8 18; Z_to_bv 8 19; Z_to_bv 8 20; Z_to_bv 8 21; Z_to_bv 8 22; Z_to_bv 8 23; Z_to_bv 8 24; Z_to_bv 8 25; Z_to_bv 8 26; Z_to_bv 8 27; Z_to_bv 8 28; Z_to_bv 8 29; Z_to_bv 8 30; Z_to_bv 8 31; Z_to_bv 8 32; Z_to_bv 8 33; Z_to_bv 8 34; Z_to_bv 8 35; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255].
Hypothesis RNG_G_10760 : gw_br G_10760 8.
Hypothesis ROM_G_10760 : ro_bytes segs G_10760 (le8 (Z_to_bv 64 1844674407370955162)).

Local Definition gw_tbl_0 := tt.

#[using="G_10760 ISTAB RATP RGLOBALS_TOP e_errno_loc e_shlim CODE BASE4 BASER D_79 E_79 D_80 E_80 D_91 E_91 D_92 E_92 D_133 E_133 D_134 E_134 D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_80 ANCH_134 ANCH_306 LINK_91 LINK_92 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc CODE_e_shlim RNG_ISTAB LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP ROM_ISTAB RNG_G_10760 ROM_G_10760"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 hi_79 hi_133 hi_305 lo_80 lo_134 lo_306 joff_91 joff_92 joff_333 joff_346 joff_352 G_10760 ISTAB RATP RGLOBALS_TOP e_errno_loc e_shlim CODE BASE4 BASER D_79 E_79 D_80 E_80 D_91 E_91 D_92 E_92 D_133 E_133 D_134 E_134 D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_80 ANCH_134 ANCH_306 LINK_91 LINK_92 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc CODE_e_shlim RNG_ISTAB LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP ROM_ISTAB RNG_G_10760 ROM_G_10760.

Ltac gw_expose_auto := try (gw_expose ISTAB); try (gw_expose RATP); try (gw_expose RGLOBALS_TOP).

Definition intscan_entry := (base + 0x0)%Z.

#[using="RATP RGLOBALS_TOP RNG_ISTAB ROM_ISTAB"] Lemma intscan_table_ro : forall m, mem_inv segs m -> ro_cells segs m ISTAB [CB 257 intscan_table].
Proof. clear - RATP RGLOBALS_TOP RNG_ISTAB ROM_ISTAB segs ISTAB. gw_expose_auto.
intros m MI.
split; [cbn; split; [reflexivity|exact I]|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
apply (ro_bytes_at segs m ISTAB intscan_table MI); [gw_expose ISTAB; lia | gw_expose ISTAB; cbn; lia | exact ROM_ISTAB].
Qed.

Definition intscan_W (SP F0 : Z) : list ivl :=
[(SP - 80, SP); (F0, F0 + 232); (RATP - 164, RATP - 160)]%Z.

Definition intscan_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(SP F0 A : Z) (str : list byte) (j0 j1 j2 j3 : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists x5 x6 x7 a0' a1' a2' a3' a4' a5' a6' a7' x28 x29 x30 x31 m' (k sc : Z) (e' : word),
ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch (intscan_W SP F0) m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rw_cells segs m' F0 (file_cells j0 j1 j2 j3 (A + k) A sc)
/\ (0 <= k <= Z.of_nat (length str))%Z /\ (0 <= sc + k <= Z.of_nat (length str))%Z
/\ bytes_at segs m' A (str ++ [b0])
/\ rw_cells segs m' (RATP - 164) [C4 e']
/\ stk segs m' lo SP.

Definition intscan_stmt : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (str j0 j1 j2 j3 : list byte) (A lo SP F0 : Z) (e : word),
a1 = Z_to_bv 64 10 -> a2 = Z_to_bv 64 1 ->
bv_unsigned sp = SP -> bv_unsigned a0 = F0 ->
rw_cells segs m F0 (file_cells j0 j1 j2 j3 A A 0) ->
bytes_at segs m A (str ++ [b0]) -> ~ In b0 str -> (A + Z.of_nat (length str) + 2 <= 2^64)%Z ->
rw_cells segs m (RATP - 164) [C4 e] ->
tp = Z_to_bv 64 RATP ->
stk segs m lo SP -> (RGLOBALS_TOP <= lo)%Z -> (lo <= SP - 80)%Z ->

(F0 + 232 <= SP - 80 \/ SP <= F0)%Z ->
(RGLOBALS_TOP <= F0)%Z ->
(A + Z.of_nat (length str) + 1 <= SP - 80 \/ SP <= A)%Z ->
(A + Z.of_nat (length str) + 1 <= F0 \/ F0 + 232 <= A)%Z ->
(A + Z.of_nat (length str) + 1 <= RATP - 164 \/ RATP - 160 <= A)%Z ->
mem_inv segs m ->
evt segs (intscan_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP F0 A str j0 j1 j2 j3 lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 f0 lim a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (str j0 j1 j2 j3 : list byte) (A lo : Z).
Notation F0 := (bv_unsigned f0).
Notation len := (Z.of_nat (length str)).
Notation W := (intscan_W (bv_unsigned sp) F0).
Notation POST := (intscan_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned sp) F0 A str j0 j1 j2 j3 lo m0).
Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -80)).
Notation FRC := [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Hypothesis NONUL : ~ In b0 str.
Hypothesis BND : (0 <= A /\ A + len + 2 <= 2^64 /\ RGLOBALS_TOP <= lo /\ lo <= bv_unsigned sp - 80 /\ bv_unsigned sp <= 2^64
/\ RGLOBALS_TOP <= F0 /\ F0 + 232 <= 2^64
/\ (F0 + 232 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= F0)
/\ (A + len + 1 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= A)
/\ (A + len + 1 <= F0 \/ F0 + 232 <= A)
/\ (A + len + 1 <= RATP - 164 \/ RATP - 160 <= A))%Z.
Hypothesis TPV : bv_unsigned tp = RATP.
Notation ERRA := (bv_unsigned tp + -164)%Z.

Definition ISI (m1 : word -> option byte) (rp : Z) (e : word) : Prop :=
rw_cells segs m1 F0 (file_cells j0 j1 j2 j3 rp A 0) /\
bytes_at segs m1 A (str ++ [b0]) /\
rw_cells segs m1 (bv_unsigned sp + -80) FRC /\
rw_cells segs m1 ERRA [C4 e] /\
ro_cells segs m1 ISTAB [CB 257 intscan_table] /\
stk segs m1 lo (bv_unsigned sp + -80) /\
mem_inv segs m1 /\ munch W m0 m1 /\ wmono segs m0 m1.

Ltac open_isi I := destruct I as (FILE & STR & FR & ERR & TAB & STK & MI & MU & WM); unfold file_cells in FILE.
Ltac close_isi :=
lazymatch goal with |- ISI ?m _ _ =>
split; [ match goal with H : rw_cells _ m (bv_unsigned f0) _ |- _ => exact H end
| split; [ match goal with H : bytes_at _ m A _ |- _ => exact H end
| split; [ match goal with H : rw_cells _ m (bv_unsigned sp + -80)%Z _ |- _ => exact H end
| split; [ match goal with H : rw_cells _ m _ [C4 _] |- _ => exact H end
| split; [ match goal with H : ro_cells _ m _ _ |- _ => exact H end
| split; [ match goal with H : stk _ m _ _ |- _ => exact H end
| split; [ match goal with H : mem_inv _ m |- _ => exact H end
| split; [ match goal with H : munch _ _ m |- _ => exact H end
| match goal with H : wmono _ _ m |- _ => exact H end ]]]]]]]] end.

Notation ST pc mm x1 x8 x10 x11 x12 x13 x18 x19 x20 x21 x22 x23 x24 :=
(MS (mkR x1 SP' gp tp t0 t1 t2 x8 f0 x10 x11 x12 x13 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom segs)).

#[using="NONUL"] Lemma str_nth : forall i, (0 <= i <= len)%Z -> exists b, nth_error (str ++ [b0]) (Z.to_nat i) = Some b /\ (bv_unsigned b <> 0%Z <-> (i < len)%Z).
Proof. clear - NONUL ra sp gp tp t0 t1 t2 s0 s1 f0 lim a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 str j0 j1 j2 j3 A lo BND TPV. first [clear BND | gw_hide BND | idtac]; first [clear TPV | gw_hide TPV | idtac]. gw_expose_auto.
intros i Hi. destruct (Z.lt_ge_cases i len) as [Hlt|Hge].
- destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E. 2:{ apply nth_error_None in E. klia. }
exists b. rewrite nth_error_app1 by klia. split; [exact E|]. split; [intros; klia|]. intros _. eapply notin0_nth; eauto.
- exists b0. rewrite nth_error_app2 by klia. replace (Z.to_nat i - length str)%nat with 0%nat by klia. cbn.
split; [reflexivity|]. split; [intros H; exfalso; apply H; reflexivity | klia].
Qed.

#[using="w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 RGLOBALS_TOP CODE RNG_RATP RNG_RGLOBALS_TOP LAY_RATP_RGLOBALS_TOP BND TPV"] Lemma is_ret : forall m1 (k sc : Z) (e : word) x1 x8 x10 x11 x12 x13 x14 x15 x16 x18 x19 x20 x21 x22 x23 x24,
rw_cells segs m1 F0 (file_cells j0 j1 j2 j3 (A + k) A sc) ->
bytes_at segs m1 A (str ++ [b0]) -> rw_cells segs m1 (bv_unsigned sp + -80) FRC ->
rw_cells segs m1 ERRA [C4 e] -> stk segs m1 lo (bv_unsigned sp + -80) ->
mem_inv segs m1 -> munch W m0 m1 -> wmono segs m0 m1 ->
(0 <= k <= len)%Z -> (0 <= sc + k <= len)%Z ->
evt segs POST (MS (mkR x1 SP' gp tp t0 t1 t2 x8 f0 x10 x11 x12 x13 x14 x15 x16 a7 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x5a4)) fc None m1 (seg_rom segs)).
Proof. clear - w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 RGLOBALS_TOP CODE RNG_RATP RNG_RGLOBALS_TOP LAY_RATP_RGLOBALS_TOP BND TPV segs base ra sp gp tp t0 t1 t2 s0 s1 f0 lim a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 str j0 j1 j2 j3 A lo NONUL. first [clear NONUL | gw_hide NONUL | idtac]. gw_expose_auto.
intros m1 k sc e x1 x8 x10 x11 x12 x13 x14 x15 x16 x18 x19 x20 x21 x22 x23 x24 FILE STR FR ERR STK MI MU WM Hk Hsc; pose proof BND as B.
do 12 zstep.
release_frame FR STK (bv_unsigned sp).
zstep. finish. 1: exact FILE. all: first [replace (RATP - 164)%Z with (bv_unsigned tp + -164)%Z by klia; exact ERR | klia].
Qed.

Ltac beta_state := lazymatch goal with |- evt _ _ ?ms => let ms' := eval cbv beta in ms in change ms with ms' end.

Ltac errno_store :=

zstep; zstep; zstep; zstep; zstep; zstep.

#[using="w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 joff_346 joff_352 RGLOBALS_TOP e_errno_loc CODE BASE4 BASER D_346 E_346 D_352 E_352 LINK_346 LINK_352 CODE_e_errno_loc RNG_RATP RNG_RGLOBALS_TOP LAY_RATP_RGLOBALS_TOP BND TPV"] Lemma is_tail : forall m1 (k sc : Z) (e : word) x1 x8 x10 x11 x12 x13 x18 x19 x20 x21 x22 x23 x24,
rw_cells segs m1 F0 (file_cells j0 j1 j2 j3 (A + k) A sc) ->
bytes_at segs m1 A (str ++ [b0]) -> rw_cells segs m1 (bv_unsigned sp + -80) FRC ->
rw_cells segs m1 ERRA [C4 e] -> stk segs m1 lo (bv_unsigned sp + -80) ->
mem_inv segs m1 -> munch W m0 m1 -> wmono segs m0 m1 ->
(0 <= k <= len)%Z -> (0 <= sc + k <= len)%Z ->
evt segs POST (ST (base + 0x4ec) m1 x1 x8 x10 x11 x12 x13 x18 x19 x20 x21 x22 x23 x24).
Proof. clear - w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 joff_346 joff_352 RGLOBALS_TOP e_errno_loc CODE BASE4 BASER D_346 E_346 D_352 E_352 LINK_346 LINK_352 CODE_e_errno_loc RNG_RATP RNG_RGLOBALS_TOP LAY_RATP_RGLOBALS_TOP BND TPV segs base ra sp gp tp t0 t1 t2 s0 s1 f0 lim a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 str j0 j1 j2 j3 A lo NONUL. first [clear NONUL | gw_hide NONUL | idtac]. gw_expose_auto.
intros m1 k sc e x1 x8 x10 x11 x12 x13 x18 x19 x20 x21 x22 x23 x24 FILE STR FR ERR STK MI MU WM Hk Hsc; pose proof BND as B.
unfold file_cells in FILE. unfold intscan_W in MU.
zstep. if_cases K1.
- zstep. zstep. if_cases K2.
+ zstep. if_cases K3.
* zstep. zstep. zstep. eapply is_ret; try eassumption; klia.
* errno_store. zstep. eapply is_ret; try eassumption; klia.
+ zstep. if_cases K3.
* zstep. if_cases K4.
-- zstep. zstep. zstep. eapply is_ret; try eassumption; klia.
-- errno_store. zstep. eapply is_ret; try eassumption; klia.
* errno_store. zstep. zstep. eapply is_ret; try eassumption; klia.
- zstep. zstep. zstep. eapply is_ret; try eassumption; klia.
Qed.

#[using="RATP"] Lemma tab_read : forall m1 (cb : byte), ro_cells segs m1 ISTAB [CB 257 intscan_table] ->
ov_read_bytes segs m1 (Z_to_bv 64 (ISTAB + bv_unsigned cb + 1)) 1 = Some [Z_to_bv 8 (itab (bv_unsigned cb))].
Proof. clear - RATP segs ISTAB ra sp gp tp t0 t1 t2 s0 s1 f0 lim a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 str j0 j1 j2 j3 A lo NONUL BND TPV. first [clear NONUL | gw_hide NONUL | idtac]; first [clear BND | gw_hide BND | idtac]; first [clear TPV | gw_hide TPV | idtac]. gw_expose_auto.
intros m1 cb [_ TAB]. cbn [cells_bytes cbytes app] in TAB. rewrite ?app_nil_r in TAB. pose proof (byte_range8 cb).
apply (u8ro_read segs m1 ISTAB intscan_table (bv_unsigned cb + 1) _ _ TAB).
- apply intscan_table_nth. klia.
- klia.
- unfold wa. f_equal. klia.
Qed.

Ltac lit_store_fix :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)) end;
mem_after_store.

#[using="w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 joff_91 joff_92 RGLOBALS_TOP e_errno_loc e_shlim CODE BASE4 BASER D_91 E_91 D_92 E_92 LINK_91 LINK_92 CODE_e_errno_loc CODE_e_shlim RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP BND TPV"] Lemma is_einval : forall m1 (p : Z) (e : word) x1 x8 x10 x11 x12 x13 x18 x19 x20 x21 x22 x23 x24,
ISI m1 (A + p) e -> (1 <= p <= len + 1)%Z ->
evt segs POST (ST (base + 0x150) m1 x1 x8 x10 x11 x12 x13 x18 x19 x20 x21 x22 x23 x24).
Proof. clear - w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 joff_91 joff_92 RGLOBALS_TOP e_errno_loc e_shlim CODE BASE4 BASER D_91 E_91 D_92 E_92 LINK_91 LINK_92 CODE_e_errno_loc CODE_e_shlim RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP BND TPV segs base ra sp gp tp t0 t1 t2 s0 s1 f0 lim a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 str j0 j1 j2 j3 A lo NONUL. first [clear NONUL | gw_hide NONUL | idtac]. gw_expose_auto.
intros m1 p e x1 x8 x10 x11 x12 x13 x18 x19 x20 x21 x22 x23 x24 I Hp; pose proof BND as B. open_isi I. unfold intscan_W in MU.
zstep. zstep. if_false.
zstep. zstep. zstep. zstep. zstep. zstep.

do 8 zstep. zstep. lit_store_fix. zstep. zstep. if_true. zstep. zstep.

do 8 zstep.
replace (A + p + -1)%Z with (A + (p - 1))%Z in * by klia.
replace (A - (A + (p - 1)))%Z with (1 - p)%Z in * by klia.
eapply (is_ret _ (p - 1) (1 - p)); try eassumption; klia.
Qed.

#[using="w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 joff_346 joff_352 RGLOBALS_TOP e_errno_loc CODE BASE4 BASER D_346 E_346 D_352 E_352 LINK_346 LINK_352 CODE_e_errno_loc RNG_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP BND TPV"] Lemma is_done : forall m1 (p : Z) (e : word) x1 x8 x10 x11 x12 x13 x18 x19 x20 x21 x22 x23 x24,
ISI m1 (A + p) e -> (1 <= p <= len + 1)%Z ->
evt segs POST (ST (base + 0x4d8) m1 x1 x8 x10 x11 x12 x13 x18 x19 x20 x21 x22 x23 x24).
Proof. clear - w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 joff_346 joff_352 RGLOBALS_TOP e_errno_loc CODE BASE4 BASER D_346 E_346 D_352 E_352 LINK_346 LINK_352 CODE_e_errno_loc RNG_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP BND TPV segs base ra sp gp tp t0 t1 t2 s0 s1 f0 lim a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 str j0 j1 j2 j3 A lo NONUL. first [clear NONUL | gw_hide NONUL | idtac]. gw_expose_auto.
intros m1 p e x1 x8 x10 x11 x12 x13 x18 x19 x20 x21 x22 x23 x24 I Hp; pose proof BND as B. open_isi I. unfold intscan_W in MU.
zstep. zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0 w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 joff_346 joff_352 RGLOBALS_TOP e_errno_loc CODE BASE4 BASER D_346 E_346 D_352 E_352 LINK_346 LINK_352 CODE_e_errno_loc RNG_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP segs base. klia. }
zstep. zstep. zstep.
replace (A + p + -1)%Z with (A + (p - 1))%Z in * by klia.
eapply (is_tail _ (p - 1) 0); try eassumption; klia.
Qed.

#[using="w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 joff_333 joff_346 joff_352 RGLOBALS_TOP e_errno_loc CODE BASE4 BASER D_333 E_333 D_346 E_346 D_352 E_352 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP NONUL BND TPV"] Lemma is_ovf_loop : forall (kk : nat) m1 (p : Z) (e : word) x1 x8 x10 x11 x12 x13 x19 x20 x22 x23 x24,
ISI m1 (A + p) e -> (0 <= p <= len)%Z -> Z.to_nat (len - p) = kk ->
evt segs POST (ST (base + 0x510) m1 x1 x8 x10 x11 x12 x13 (Z_to_bv 64 10) x19 x20 (Z_to_bv 64 ISTAB) x22 x23 x24).
Proof. clear - w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 joff_333 joff_346 joff_352 RGLOBALS_TOP e_errno_loc CODE BASE4 BASER D_333 E_333 D_346 E_346 D_352 E_352 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP NONUL BND TPV segs base ISTAB ra sp gp tp t0 t1 t2 s0 s1 f0 lim a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 str j0 j1 j2 j3 A lo. gw_expose_auto.
induction kk as [kk IH] using lt_wf_ind; intros m1 p e x1 x8 x10 x11 x12 x13 x19 x20 x22 x23 x24 I Hp Hk; pose proof BND as B.
open_isi I. unfold intscan_W in MU.
destruct (str_nth p ltac:(klia)) as (cb & Hcb & HcbZ). pose proof (byte_range8 cb) as Rcb.
zstep. zstep. zstep. if_cases Ke; zify_cond Ke. { exfalso. unfold M64m1 in Ke. klia. }
zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (u8ro_read segs mx A (str ++ [b0]) p cb _ STR Hcb ltac:(klia) eq_refl) as RD end.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (tab_read mx cb TAB) as RDT end.
zstep. zstep. beta_state. rewrite itab_unsigned. zstep. if_cases Kd; zify_cond Kd.
-
rewrite Z.mod_small in Kd by (generalize (itab_range (bv_unsigned cb)); klia).
apply (proj1 (itab_lt10 _ Rcb)) in Kd. assert (p < len)%Z by (apply HcbZ; klia).
replace (A + p + 1)%Z with (A + (p + 1))%Z in * by klia.
unshelve (eapply (IH (Z.to_nat (len - (p + 1))) _ _ (p + 1)%Z e)); [klia | close_isi | klia | klia].
-
errno_store. do 6 zstep. if_cases K0; zify_cond K0. 2:{ exfalso. clear - K0 w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 joff_333 joff_346 joff_352 RGLOBALS_TOP e_errno_loc CODE BASE4 BASER D_333 E_333 D_346 E_346 D_352 E_352 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP segs base ISTAB. klia. }
zstep. zstep. zstep.
replace (A + p + 1 + -1)%Z with (A + p)%Z in * by klia.
eapply (is_tail _ p 0); try eassumption; klia.
Qed.

#[using="w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 hi_305 lo_306 joff_333 joff_346 joff_352 RGLOBALS_TOP e_errno_loc CODE BASE4 BASER D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_306 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP NONUL BND TPV"] Lemma is_ovf : forall m1 (p : Z) (cb : byte) (e : word) x1 x8 x11 x12 x13 x19 x20 x21 x22 x23 x24,
ISI m1 (A + p) e -> (1 <= p <= len + 1)%Z -> nth_error (str ++ [b0]) (Z.to_nat (p - 1)) = Some cb ->
evt segs POST (ST (base + 0x4c4) m1 x1 x8 (Z_to_bv 64 (bv_unsigned cb)) x11 x12 x13 (Z_to_bv 64 10) x19 x20 x21 x22 x23 x24).
Proof. clear - w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 hi_305 lo_306 joff_333 joff_346 joff_352 RGLOBALS_TOP e_errno_loc CODE BASE4 BASER D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_306 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP NONUL BND TPV segs base ra sp gp tp t0 t1 t2 s0 s1 f0 lim a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 str j0 j1 j2 j3 A lo. gw_expose_auto.
intros m1 p cb e x1 x8 x11 x12 x13 x19 x20 x21 x22 x23 x24 I Hp Hcb; pose proof BND as B.
pose proof (byte_range8 cb) as Rcb. pose proof I as I'. open_isi I. unfold intscan_W in MU.
pose proof (tab_read m1 cb TAB) as RDT.
zstep. zstep. zstep. zstep. beta_state. rewrite itab_unsigned. zstep. if_cases Kd; zify_cond Kd.
- rewrite Z.mod_small in Kd by (generalize (itab_range (bv_unsigned cb)); klia).
apply (proj1 (itab_lt10 _ Rcb)) in Kd.
assert (p - 1 < len)%Z. { destruct (str_nth (p - 1) ltac:(klia)) as (cb' & Hcb' & Hz). rewrite Hcb in Hcb'. injection Hcb' as <-. apply Hz. klia. }
eapply (is_ovf_loop (Z.to_nat (len - p)) _ p); [exact I' | klia | klia].
- eapply (is_done _ p); [exact I' | klia].
Qed.

Ltac getc p cb Hcb :=
zstep; zstep; zstep;
let Ke := fresh "Ke" in
if_cases Ke; zify_cond Ke; [ exfalso; unfold M64m1 in Ke; klia | ];
zstep; zstep;
let RD := fresh "RD" in
lazymatch goal with STR : bytes_at _ ?mx A _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (u8ro_read segs mx A (str ++ [b0]) p cb _ STR Hcb ltac:(klia) eq_refl) as RD end;
zstep; beta_state; try clear RD.

Ltac fix_swrap cb := rewrite (swrap32_byte_off (bv_unsigned cb) (-48)) by (first [apply byte_range8 | klia]).

#[using="w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 hi_305 lo_306 joff_333 joff_346 joff_352 RGLOBALS_TOP e_errno_loc CODE BASE4 BASER D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_306 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP NONUL BND TPV"] Lemma is_l2 : forall (kk : nat) m1 (p : Z) (cb : byte) (e : word) x1 x8 x10 x11 x12 x13 x18 x19 x20 x24,
ISI m1 (A + p) e -> (1 <= p <= len)%Z -> Z.to_nat (len - p) = kk ->
nth_error (str ++ [b0]) (Z.to_nat (p - 1)) = Some cb -> (48 <= bv_unsigned cb <= 57)%Z ->
evt segs POST (ST (base + 0x228) m1 x1 x8 x10 x11 x12 x13 x18 x19 x20
(Z_to_bv 64 (bv_unsigned cb + -48)) (Z_to_bv 64 1844674407370955162) (Z_to_bv 64 9) x24).
Proof. clear - w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 hi_305 lo_306 joff_333 joff_346 joff_352 RGLOBALS_TOP e_errno_loc CODE BASE4 BASER D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_306 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP NONUL BND TPV segs base ra sp gp tp t0 t1 t2 s0 s1 f0 lim a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 str j0 j1 j2 j3 A lo. gw_expose_auto.
induction kk as [kk IH] using lt_wf_ind; intros m1 p cb e x1 x8 x10 x11 x12 x13 x18 x19 x20 x24 I Hp Hk Hcb Dcb; pose proof BND as B.
open_isi I. unfold intscan_W in MU. pose proof (byte_range8 cb) as Rcb.
destruct (str_nth p ltac:(klia)) as (cb' & Hcb' & HcbZ'). pose proof (byte_range8 cb') as Rcb'.
getc p cb' Hcb'.
zstep. zstep. fix_swrap cb'. zstep. if_cases Kd; zify_cond Kd.
-
apply (proj1 (digit_test _ Rcb')) in Kd. assert (p < len)%Z by (apply HcbZ'; klia).
replace (A + p + 1)%Z with (A + (p + 1))%Z in * by klia.
zstep. if_cases Ky; zify_cond Ky.
+
zstep. zstep. if_cases K9; zify_cond K9. { exfalso. clear - K9 Kd Rcb' w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 hi_305 lo_306 joff_333 joff_346 joff_352 RGLOBALS_TOP e_errno_loc CODE BASE4 BASER D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_306 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP segs base. Z.div_mod_to_equations. klia. }
zstep. eapply (is_ovf _ (p + 1) cb'); [close_isi | klia | replace (Z.to_nat (p + 1 - 1)) with (Z.to_nat p) by klia; exact Hcb'].
+ zstep. zstep. zstep. zstep. if_cases Km; zify_cond Km.
* unshelve (eapply (IH (Z.to_nat (len - (p + 1))) _ _ (p + 1)%Z cb' e)); [klia | close_isi | klia | klia | | klia].
replace (Z.to_nat (p + 1 - 1)) with (Z.to_nat p) by klia. exact Hcb'.
* zstep. eapply (is_ovf _ (p + 1) cb'); [close_isi | klia | replace (Z.to_nat (p + 1 - 1)) with (Z.to_nat p) by klia; exact Hcb'].
-
zstep. zstep. zstep. if_cases K9; zify_cond K9. 2:{ exfalso. clear - K9 Kd Rcb' w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 hi_305 lo_306 joff_333 joff_346 joff_352 RGLOBALS_TOP e_errno_loc CODE BASE4 BASER D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_306 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP segs base. Z.div_mod_to_equations. klia. }
replace (A + p + 1)%Z with (A + (p + 1))%Z in * by klia.
eapply (is_done _ (p + 1)); [close_isi | klia].
Qed.

#[using="w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 hi_133 hi_305 lo_134 lo_306 joff_333 joff_346 joff_352 G_10760 RGLOBALS_TOP e_errno_loc CODE BASE4 BASER D_133 E_133 D_134 E_134 D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_134 ANCH_306 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP RNG_G_10760 ROM_G_10760 NONUL BND TPV"] Lemma is_l2_entry : forall m1 (p : Z) (cb : byte) (e : word) x1 x8 x11 x12 x13 x18 x19 x20 x22 x23 x24,
ISI m1 (A + p) e -> (1 <= p <= len)%Z ->
nth_error (str ++ [b0]) (Z.to_nat (p - 1)) = Some cb -> (48 <= bv_unsigned cb <= 57)%Z ->
evt segs POST (ST (base + 0x214) m1 x1 x8 (Z_to_bv 64 (bv_unsigned cb)) x11 x12 x13 x18 x19 x20
(Z_to_bv 64 (bv_unsigned cb + -48)) x22 x23 x24).
Proof. clear - w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 hi_133 hi_305 lo_134 lo_306 joff_333 joff_346 joff_352 G_10760 RGLOBALS_TOP e_errno_loc CODE BASE4 BASER D_133 E_133 D_134 E_134 D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_134 ANCH_306 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP RNG_G_10760 ROM_G_10760 NONUL BND TPV segs base ra sp gp tp t0 t1 t2 s0 s1 f0 lim a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 str j0 j1 j2 j3 A lo. gw_expose_auto.
intros m1 p cb e x1 x8 x11 x12 x13 x18 x19 x20 x22 x23 x24 I Hp Hcb Dcb; pose proof BND as B.
pose proof I as I'. open_isi I. unfold intscan_W in MU.
do 5 zstep.
eapply (is_l2 (Z.to_nat (len - p)) _ p cb e); [exact I' | klia | klia | exact Hcb | exact Dcb].
Qed.

#[using="w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 hi_133 hi_305 lo_134 lo_306 joff_333 joff_346 joff_352 G_10760 RGLOBALS_TOP e_errno_loc CODE BASE4 BASER D_133 E_133 D_134 E_134 D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_134 ANCH_306 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP RNG_G_10760 ROM_G_10760 NONUL BND TPV"] Lemma is_l1 : forall (kk : nat) m1 (p : Z) (cb : byte) (e : word) x1 x8 x10 x11 x12 x13 x19 x20 x24,
ISI m1 (A + p) e -> (1 <= p <= len)%Z -> Z.to_nat (len - p) = kk ->
nth_error (str ++ [b0]) (Z.to_nat (p - 1)) = Some cb -> (48 <= bv_unsigned cb <= 57)%Z ->
evt segs POST (ST (base + 0x1e0) m1 x1 x8 x10 x11 x12 x13 (Z_to_bv 64 9) x19 x20
(Z_to_bv 64 (bv_unsigned cb + -48)) (Z_to_bv 64 10) (Z_to_bv 64 429496729) x24).
Proof. clear - w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 hi_133 hi_305 lo_134 lo_306 joff_333 joff_346 joff_352 G_10760 RGLOBALS_TOP e_errno_loc CODE BASE4 BASER D_133 E_133 D_134 E_134 D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_134 ANCH_306 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP RNG_G_10760 ROM_G_10760 NONUL BND TPV segs base ra sp gp tp t0 t1 t2 s0 s1 f0 lim a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 str j0 j1 j2 j3 A lo. gw_expose_auto.
induction kk as [kk IH] using lt_wf_ind; intros m1 p cb e x1 x8 x10 x11 x12 x13 x19 x20 x24 I Hp Hk Hcb Dcb; pose proof BND as B.
open_isi I. unfold intscan_W in MU. pose proof (byte_range8 cb) as Rcb.
destruct (str_nth p ltac:(klia)) as (cb' & Hcb' & HcbZ'). pose proof (byte_range8 cb') as Rcb'.
getc p cb' Hcb'.
zstep. zstep. zstep. fix_swrap cb'. zstep. if_cases Kd; zify_cond Kd.
-
apply (proj1 (digit_test _ Rcb')) in Kd. assert (p < len)%Z by (apply HcbZ'; klia).
replace (A + p + 1)%Z with (A + (p + 1))%Z in * by klia.
zstep. if_cases Kx; zify_cond Kx.
+
zstep. zstep. zstep. if_cases K9; zify_cond K9. { exfalso. clear - K9 Kd Rcb' w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 hi_133 hi_305 lo_134 lo_306 joff_333 joff_346 joff_352 G_10760 RGLOBALS_TOP e_errno_loc CODE BASE4 BASER D_133 E_133 D_134 E_134 D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_134 ANCH_306 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP RNG_G_10760 ROM_G_10760 segs base. Z.div_mod_to_equations. klia. }
eapply (is_l2_entry _ (p + 1) cb' e); [close_isi | klia | replace (Z.to_nat (p + 1 - 1)) with (Z.to_nat p) by klia; exact Hcb' | exact Kd].
+ unshelve (eapply (IH (Z.to_nat (len - (p + 1))) _ _ (p + 1)%Z cb' e)); [klia | close_isi | klia | klia | | klia].
replace (Z.to_nat (p + 1 - 1)) with (Z.to_nat p) by klia. exact Hcb'.
-
zstep. zstep. zstep. if_cases K9; zify_cond K9. 2:{ exfalso. clear - K9 Kd Rcb' w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 hi_133 hi_305 lo_134 lo_306 joff_333 joff_346 joff_352 G_10760 RGLOBALS_TOP e_errno_loc CODE BASE4 BASER D_133 E_133 D_134 E_134 D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_134 ANCH_306 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP RNG_G_10760 ROM_G_10760 segs base. Z.div_mod_to_equations. klia. }
replace (A + p + 1)%Z with (A + (p + 1))%Z in * by klia.
eapply (is_done _ (p + 1)); [close_isi | klia].
Qed.

#[using="w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 hi_133 hi_305 lo_134 lo_306 joff_333 joff_346 joff_352 G_10760 RGLOBALS_TOP e_errno_loc CODE BASE4 BASER D_133 E_133 D_134 E_134 D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_134 ANCH_306 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP RNG_G_10760 ROM_G_10760 NONUL BND TPV"] Lemma is_dig : forall m1 (p : Z) (cb : byte) (e : word) x1 x8 x11 x12 x13 x19 x20 x21 x22 x23 x24,
ISI m1 (A + p) e -> (1 <= p <= len)%Z ->
nth_error (str ++ [b0]) (Z.to_nat (p - 1)) = Some cb -> (48 <= bv_unsigned cb <= 57)%Z ->
evt segs POST (ST (base + 0x19c) m1 x1 x8 (Z_to_bv 64 (bv_unsigned cb)) x11 x12 x13 (Z_to_bv 64 10) x19 x20 x21 x22 x23 x24).
Proof. clear - w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 hi_133 hi_305 lo_134 lo_306 joff_333 joff_346 joff_352 G_10760 RGLOBALS_TOP e_errno_loc CODE BASE4 BASER D_133 E_133 D_134 E_134 D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_134 ANCH_306 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP RNG_G_10760 ROM_G_10760 NONUL BND TPV segs base ra sp gp tp t0 t1 t2 s0 s1 f0 lim a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 str j0 j1 j2 j3 A lo. gw_expose_auto.
intros m1 p cb e x1 x8 x11 x12 x13 x19 x20 x21 x22 x23 x24 I Hp Hcb Dcb; pose proof BND as B.
pose proof I as I'. open_isi I. unfold intscan_W in MU. pose proof (byte_range8 cb) as Rcb.
zstep. zstep. if_cases K10; zify_cond K10. { exfalso. clear - K10 w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 hi_133 hi_305 lo_134 lo_306 joff_333 joff_346 joff_352 G_10760 RGLOBALS_TOP e_errno_loc CODE BASE4 BASER D_133 E_133 D_134 E_134 D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_134 ANCH_306 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP RNG_G_10760 ROM_G_10760 segs base. cbn in K10. klia. }
zstep. fix_swrap cb. zstep. zstep. zstep. if_cases K9; zify_cond K9. { exfalso. clear - K9 Dcb Rcb w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 hi_133 hi_305 lo_134 lo_306 joff_333 joff_346 joff_352 G_10760 RGLOBALS_TOP e_errno_loc CODE BASE4 BASER D_133 E_133 D_134 E_134 D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_134 ANCH_306 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP RNG_G_10760 ROM_G_10760 segs base. Z.div_mod_to_equations. klia. }
do 4 zstep.
eapply (is_l1 (Z.to_nat (len - p)) _ p cb e); [exact I' | klia | klia | exact Hcb | exact Dcb].
Qed.

#[using="w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 hi_79 hi_133 hi_305 lo_80 lo_134 lo_306 joff_91 joff_92 joff_333 joff_346 joff_352 G_10760 RGLOBALS_TOP e_errno_loc e_shlim CODE BASE4 BASER D_79 E_79 D_80 E_80 D_91 E_91 D_92 E_92 D_133 E_133 D_134 E_134 D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_80 ANCH_134 ANCH_306 LINK_91 LINK_92 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc CODE_e_shlim LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP RNG_G_10760 ROM_G_10760 NONUL BND TPV"] Lemma is_chk : forall m1 (p : Z) (cb : byte) (e : word) x1 x8 x11 x12 x13 x19 x20 x21 x22 x23 x24,
ISI m1 (A + p) e -> (1 <= p <= len + 1)%Z -> nth_error (str ++ [b0]) (Z.to_nat (p - 1)) = Some cb ->
evt segs POST (ST (base + 0x134) m1 x1 x8 (Z_to_bv 64 (bv_unsigned cb)) x11 x12 x13 (Z_to_bv 64 10) x19 x20 x21 x22 x23 x24).
Proof. clear - w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 hi_79 hi_133 hi_305 lo_80 lo_134 lo_306 joff_91 joff_92 joff_333 joff_346 joff_352 G_10760 RGLOBALS_TOP e_errno_loc e_shlim CODE BASE4 BASER D_79 E_79 D_80 E_80 D_91 E_91 D_92 E_92 D_133 E_133 D_134 E_134 D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_80 ANCH_134 ANCH_306 LINK_91 LINK_92 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc CODE_e_shlim LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP RNG_G_10760 ROM_G_10760 NONUL BND TPV segs base ra sp gp tp t0 t1 t2 s0 s1 f0 lim a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 str j0 j1 j2 j3 A lo. gw_expose_auto.
intros m1 p cb e x1 x8 x11 x12 x13 x19 x20 x21 x22 x23 x24 I Hp Hcb; pose proof BND as B.
pose proof (byte_range8 cb) as Rcb. pose proof I as I'. open_isi I. unfold intscan_W in MU.
pose proof (tab_read m1 cb TAB) as RDT.
zstep. if_true.
zstep. zstep. zstep. zstep. beta_state. rewrite itab_unsigned. zstep. if_cases Kd; zify_cond Kd.
- rewrite Z.mod_small in Kd by (generalize (itab_range (bv_unsigned cb)); klia).
apply (proj1 (itab_lt10 _ Rcb)) in Kd.
assert (p - 1 < len)%Z. { destruct (str_nth (p - 1) ltac:(klia)) as (cb' & Hcb' & Hz). rewrite Hcb in Hcb'. injection Hcb' as <-. apply Hz. klia. }
eapply (is_dig _ p cb e); [exact I' | klia | exact Hcb | exact Kd].
- eapply (is_einval _ p e); [exact I' | klia].
Qed.

#[using="w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 hi_79 hi_133 hi_305 lo_80 lo_134 lo_306 joff_91 joff_92 joff_333 joff_346 joff_352 G_10760 RGLOBALS_TOP e_errno_loc e_shlim CODE BASE4 BASER D_79 E_79 D_80 E_80 D_91 E_91 D_92 E_92 D_133 E_133 D_134 E_134 D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_80 ANCH_134 ANCH_306 LINK_91 LINK_92 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc CODE_e_shlim LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP RNG_G_10760 ROM_G_10760 NONUL BND TPV"] Lemma is_sign : forall m1 (p : Z) (cb : byte) (e : word) x1 x8 x11 x12 x13 x19 x20 x21 x22 x23 x24,
ISI m1 (A + p) e -> (1 <= p <= len + 1)%Z -> nth_error (str ++ [b0]) (Z.to_nat (p - 1)) = Some cb ->
evt segs POST (ST (base + 0x8c) m1 x1 x8 (Z_to_bv 64 (bv_unsigned cb)) x11 x12 x13 (Z_to_bv 64 10) x19 x20 x21 x22 x23 x24).
Proof. clear - w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 hi_79 hi_133 hi_305 lo_80 lo_134 lo_306 joff_91 joff_92 joff_333 joff_346 joff_352 G_10760 RGLOBALS_TOP e_errno_loc e_shlim CODE BASE4 BASER D_79 E_79 D_80 E_80 D_91 E_91 D_92 E_92 D_133 E_133 D_134 E_134 D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_80 ANCH_134 ANCH_306 LINK_91 LINK_92 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc CODE_e_shlim LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP RNG_G_10760 ROM_G_10760 NONUL BND TPV segs base ra sp gp tp t0 t1 t2 s0 s1 f0 lim a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 str j0 j1 j2 j3 A lo. gw_expose_auto.
intros m1 p cb e x1 x8 x11 x12 x13 x19 x20 x21 x22 x23 x24 I Hp Hcb; pose proof BND as B.
pose proof (byte_range8 cb) as Rcb. pose proof I as I'. open_isi I. unfold intscan_W in MU.
assert (SGN : (bv_unsigned cb = 45 \/ bv_unsigned cb = 43)%Z ->
evt segs POST (ST (base + 0x9c) m1 x1 x8 (Z_to_bv 64 (bv_unsigned cb)) (Z_to_bv 64 45) x12 x13 (Z_to_bv 64 10) x19 x20 x21 x22 x23 x24)
/\ evt segs POST (ST (base + 0x9c) m1 x1 x8 (Z_to_bv 64 (bv_unsigned cb)) (Z_to_bv 64 43) x12 x13 (Z_to_bv 64 10) x19 x20 x21 x22 x23 x24)).
{ intros Hs.
assert (p - 1 < len)%Z. { destruct (str_nth (p - 1) ltac:(klia)) as (cb' & Hcb' & Hz). rewrite Hcb in Hcb'. injection Hcb' as <-. apply Hz. klia. }
destruct (str_nth p ltac:(klia)) as (cb' & Hcb' & HcbZ'). pose proof (byte_range8 cb') as Rcb'.
split.
all: do 6 zstep; if_cases Ke; zify_cond Ke; [ exfalso; unfold M64m1 in Ke; klia | ].
all: zstep; zstep.
all: lazymatch goal with STR : bytes_at _ ?mx A _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (u8ro_read segs mx A (str ++ [b0]) p cb' _ STR Hcb' ltac:(klia) eq_refl) as RD end.
all: zstep; beta_state; clear RD; zstep; zstep; if_false; zstep.
all: replace (A + p + 1)%Z with (A + (p + 1))%Z in * by klia.
all: eapply (is_chk _ (p + 1) cb'); [close_isi | klia | replace (Z.to_nat (p + 1 - 1)) with (Z.to_nat p) by klia; exact Hcb']. }
zstep. zstep. if_cases K45; zify_cond K45.
- apply (proj1 (SGN ltac:(left; exact K45))).
- zstep. zstep. if_cases K43; zify_cond K43.
+
zstep. zstep. zstep. if_false. zstep.
eapply (is_chk _ p cb e); [exact I' | klia | exact Hcb].
+ apply (proj2 (SGN ltac:(right; exact K43))).
Qed.

#[using="w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 hi_79 hi_133 hi_305 lo_80 lo_134 lo_306 joff_91 joff_92 joff_333 joff_346 joff_352 G_10760 RGLOBALS_TOP e_errno_loc e_shlim CODE BASE4 BASER D_79 E_79 D_80 E_80 D_91 E_91 D_92 E_92 D_133 E_133 D_134 E_134 D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_80 ANCH_134 ANCH_306 LINK_91 LINK_92 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc CODE_e_shlim LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP RNG_G_10760 ROM_G_10760 NONUL BND TPV"] Lemma is_ws : forall (kk : nat) m1 (p : Z) (e : word) x1 x8 x10 x11 x12 x13 x19 x22 x23 x24,
ISI m1 (A + p) e -> (0 <= p <= len)%Z -> Z.to_nat (len - p) = kk ->
evt segs POST (ST (base + 0x68) m1 x1 x8 x10 x11 x12 x13 (Z_to_bv 64 10) x19 (Z_to_bv 64 5) (Z_to_bv 64 32) x22 x23 x24).
Proof. clear - w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 hi_79 hi_133 hi_305 lo_80 lo_134 lo_306 joff_91 joff_92 joff_333 joff_346 joff_352 G_10760 RGLOBALS_TOP e_errno_loc e_shlim CODE BASE4 BASER D_79 E_79 D_80 E_80 D_91 E_91 D_92 E_92 D_133 E_133 D_134 E_134 D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_80 ANCH_134 ANCH_306 LINK_91 LINK_92 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc CODE_e_shlim LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP RNG_G_10760 ROM_G_10760 NONUL BND TPV segs base ra sp gp tp t0 t1 t2 s0 s1 f0 lim a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 str j0 j1 j2 j3 A lo. gw_expose_auto.
induction kk as [kk IH] using lt_wf_ind; intros m1 p e x1 x8 x10 x11 x12 x13 x19 x22 x23 x24 I Hp Hk; pose proof BND as B.
open_isi I. unfold intscan_W in MU.
destruct (str_nth p ltac:(klia)) as (cb & Hcb & HcbZ). pose proof (byte_range8 cb) as Rcb.
getc p cb Hcb.
replace (A + p + 1)%Z with (A + (p + 1))%Z in * by klia.
zstep. zstep. if_cases K9; zify_cond K9.
-
assert (p < len)%Z by (apply HcbZ; clear - K9 Rcb w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 hi_79 hi_133 hi_305 lo_80 lo_134 lo_306 joff_91 joff_92 joff_333 joff_346 joff_352 G_10760 RGLOBALS_TOP e_errno_loc e_shlim CODE BASE4 BASER D_79 E_79 D_80 E_80 D_91 E_91 D_92 E_92 D_133 E_133 D_134 E_134 D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_80 ANCH_134 ANCH_306 LINK_91 LINK_92 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc CODE_e_shlim LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP RNG_G_10760 ROM_G_10760 segs base; Z.div_mod_to_equations; klia).
unshelve (eapply (IH (Z.to_nat (len - (p + 1))) _ _ (p + 1)%Z e)); [klia | close_isi | klia | klia].
- zstep. if_cases K32; zify_cond K32.
+ assert (p < len)%Z by (apply HcbZ; klia).
unshelve (eapply (IH (Z.to_nat (len - (p + 1))) _ _ (p + 1)%Z e)); [klia | close_isi | klia | klia].
+ eapply (is_sign _ (p + 1) cb e); [close_isi | klia | replace (Z.to_nat (p + 1 - 1)) with (Z.to_nat p) by klia; exact Hcb].
Qed.
End Proofs.

#[using="w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 hi_79 hi_133 hi_305 lo_80 lo_134 lo_306 joff_91 joff_92 joff_333 joff_346 joff_352 G_10760 ISTAB e_errno_loc e_shlim CODE BASE4 BASER D_79 E_79 D_80 E_80 D_91 E_91 D_92 E_92 D_133 E_133 D_134 E_134 D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_80 ANCH_134 ANCH_306 LINK_91 LINK_92 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc CODE_e_shlim RNG_ISTAB LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP ROM_ISTAB RNG_G_10760 ROM_G_10760"] Lemma intscan_spec : intscan_stmt.
Proof. clear - w_23 w_56 w_79 w_80 w_91 w_92 w_98 w_114 w_133 w_134 w_149 w_160 w_161 w_162 w_182 w_183 w_185 w_186 w_197 w_224 w_243 w_244 w_253 w_281 w_305 w_306 w_320 w_333 w_346 w_352 w_359 hi_79 hi_133 hi_305 lo_80 lo_134 lo_306 joff_91 joff_92 joff_333 joff_346 joff_352 G_10760 ISTAB e_errno_loc e_shlim CODE BASE4 BASER D_79 E_79 D_80 E_80 D_91 E_91 D_92 E_92 D_133 E_133 D_134 E_134 D_305 E_305 D_306 E_306 D_333 E_333 D_346 E_346 D_352 E_352 ANCH_80 ANCH_134 ANCH_306 LINK_91 LINK_92 LINK_333 LINK_346 LINK_352 CODE_e_errno_loc CODE_e_shlim RNG_ISTAB LAY_lo_ISTAB RNG_RATP LAY_lo_RATP RNG_RGLOBALS_TOP LAY_ISTAB_RATP LAY_RATP_RGLOBALS_TOP ROM_ISTAB RNG_G_10760 ROM_G_10760. gw_expose_auto.
unfold intscan_stmt. intros until e. intros Ha1 Ha2 HSP HF0 FILE STR NONUL AB ERR TP ST LO LOS SEP1 F0LO SEP2 SEP3 SEP4 MI. subst SP F0.
pose proof (bytes_at_bound _ _ _ _ STR) as SB.
pose proof (rw_cells_bound _ _ _ _ FILE) as FB. unfold file_cells in FB. cbn [cells_size csize Nat.add] in FB.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof (munch_refl (intscan_W (bv_unsigned sp) (bv_unsigned a0)) m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (intscan_table_ro m MI) as TAB.
unfold file_cells in FILE. unfold intscan_W in MU.
subst a1 a2.
carve_frame 80%nat ST. do 11 zstep.
zstep. zstep. zstep. if_false. zstep. zstep. zstep. if_false.
zstep. zstep. zstep. zstep. zstep.
unshelve (eapply (is_ws ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str j0 j1 j2 j3 A lo
NONUL _ _ (Z.to_nat (Z.of_nat (length str) - 0)) _ 0%Z e)).
-  rewrite length_app in SB. cbn [length] in SB. repeat split; klia.
-  rewrite TP. apply unsigned_lit. klia.
- unfold ISI. rewrite Z.add_0_r.
replace (bv_unsigned tp + -164)%Z with (RATP - 164)%Z by (rewrite TP, unsigned_lit by klia; klia).
split; [exact FILE|]. split; [exact STR|]. split; [exact FR|]. split; [exact ERR|]. split; [exact TAB|].
split; [exact ST|]. split; [exact MI|]. split; [exact MU|]. exact WM.
- klia.
- reflexivity.
Qed.

End G.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 QZAi QqdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1.
Import QZAi.Mq1 QqdR.
Import QnDM_c1.
Import QVbl.Mq4.
Import QVbl.Mq3.
Import QQLG.Mq7.

Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition pad_code (w_7 w_8 w_21 w_33 w_41 w_52 : Z) : list Z :=
[0xed010113; 0x12113423; 0x12813023; 0x10913c23; 0x11213823; 0x11313423; 0x00050413; w_7; w_8; 0x00093503; 0x10a13023; 0x06c6de63; 0x00012537; 0x00a77533; 0x06051863; 0x40d604bb; 0x10000993; 0x00048613; 0x0134e463; 0x10000613; 0x00010513; w_21; 0x0334ea63; 0x0ff00993; 0x00c0006f; 0xf004849b; 0x0299f263; 0x00044503; 0x02057513; 0xfe0518e3; 0x00010513; 0x10000593; 0x00040613; w_33; 0xfddff06f; 0x00044503; 0x02057513; 0x00051a63; 0x00010513; 0x00048593; 0x00040613; w_41; 0x00093503; 0x10013583; 0x02b51063; 0x12813083; 0x12013403; 0x11813483; 0x11013903; 0x10813983; 0x13010113; 0x00008067; w_52]%Z.

Definition pad_n (w l fl : Z) : Z :=
if negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0)%Z || (w <=? l)%Z then 0 else w - l.

Lemma pad_model : forall o c w l fl, (w - l < 256)%Z ->
pad o c w l fl = Some (o ++ zrepeat c (pad_n w l fl)).
Proof.
intros o c w l fl H. unfold pad, pad_n.
destruct (negb _ || _); [cbn; now rewrite app_nil_r|].
change PAD_FUEL with (S 63). cbn [pad_loop].
destruct (Z.leb_spec0 256 (w - l)); [lia|]. reflexivity.
Qed.

Lemma rw_cells_bytes_at' : forall segs_ m A cs, rw_cells segs_ m A cs -> bytes_at segs_ m A (cells_bytes cs).
Proof. intros segs_ m A cs [[_ H] _]. exact H. Qed.

Ltac hyp := lazymatch goal with |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end end.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_7 w_8 w_21 w_33 w_41 w_52 : Z).
Variables (hi_7 : bv 20).
Variables (lo_8 : bv 12).
Variables (joff_21 joff_33 joff_41 joff_52 : bv 21).
Variables (got_ssp ssp_guard : Z).
Variables (e_197bc e_fwritex e_memset : Z).
Hypothesis CODE : code_at segs base (pad_code w_7 w_8 w_21 w_33 w_41 w_52).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 212.
Hypothesis D_7 : decode_any (Z_to_bv 32 w_7) = Some (Auipc 10 hi_7, 4%Z).
Hypothesis E_7 : is_ecall (Z_to_bv 32 w_7) = false.
Hypothesis D_8 : decode_any (Z_to_bv 32 w_8) = Some (Load SZ8 true 18 10 lo_8, 4%Z).
Hypothesis E_8 : is_ecall (Z_to_bv 32 w_8) = false.
Hypothesis D_21 : decode_any (Z_to_bv 32 w_21) = Some (Jal 1 joff_21, 4%Z).
Hypothesis E_21 : is_ecall (Z_to_bv 32 w_21) = false.
Hypothesis D_33 : decode_any (Z_to_bv 32 w_33) = Some (Jal 1 joff_33, 4%Z).
Hypothesis E_33 : is_ecall (Z_to_bv 32 w_33) = false.
Hypothesis D_41 : decode_any (Z_to_bv 32 w_41) = Some (Jal 1 joff_41, 4%Z).
Hypothesis E_41 : is_ecall (Z_to_bv 32 w_41) = false.
Hypothesis D_52 : decode_any (Z_to_bv 32 w_52) = Some (Jal 1 joff_52, 4%Z).
Hypothesis E_52 : is_ecall (Z_to_bv 32 w_52) = false.
Hypothesis ANCH_8 : gw_anch (Z.shiftl (bv_signed hi_7) 12 + (base + 28) + bv_signed lo_8)%Z got_ssp.
Hypothesis LINK_21 : gw_anch (base + 84 + bv_signed joff_21)%Z (e_memset + 0)%Z.
Hypothesis LINK_33 : gw_anch (base + 132 + bv_signed joff_33)%Z (e_fwritex + 0)%Z.
Hypothesis LINK_41 : gw_anch (base + 164 + bv_signed joff_41)%Z (e_fwritex + 0)%Z.
Hypothesis LINK_52 : gw_anch (base + 208 + bv_signed joff_52)%Z (e_197bc + 0)%Z.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis AL_got_ssp : gw_al got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis AL_ssp_guard : gw_al ssp_guard 8.
Hypothesis LAY_got_ssp_ssp_guard : gw_le (got_ssp + 8) ssp_guard.

Definition memset_post := Eval cbv beta delta [QVbl.Mq4.memset_post] in (QVbl.Mq4.memset_post segs).

Definition wfile := ltac:(let t := eval cbv beta delta [QQLG.Mq7.wfile] in (QQLG.Mq7.wfile segs) in let t := gw_subst t (QVbl.Mq4.memset_post segs) memset_post in exact t).
Definition fwritex_postZ := ltac:(let t := eval cbv beta delta [QQLG.Mq7.fwritex_postZ] in (QQLG.Mq7.fwritex_postZ segs) in let t := gw_subst t (QVbl.Mq4.memset_post segs) memset_post in let t := gw_subst t (QQLG.Mq7.wfile segs) wfile in exact t).

Hypothesis memset_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq4.memset_spec segs e_memset) 3%nat in let T := gw_subst T (QVbl.Mq4.memset_post segs) memset_post in let T := gw_subst T (QQLG.Mq7.wfile segs) wfile in let T := gw_subst T (QQLG.Mq7.fwritex_postZ segs) fwritex_postZ in exact T).

Hypothesis fwritex_call : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQLG.Mq7.gw_all) (@QQLG.Mq7.fwritex_call) e_fwritex)) in let T := gw_subst T (QVbl.Mq4.memset_post segs) memset_post in let T := gw_subst T (QQLG.Mq7.wfile segs) wfile in let T := gw_subst T (QQLG.Mq7.fwritex_postZ segs) fwritex_postZ in exact T).

#[using="CODE BASE4 BASER D_7 E_7 D_8 E_8 D_21 E_21 D_33 E_33 D_41 E_41 D_52 E_52 ANCH_8 LINK_21 LINK_33 LINK_41 LINK_52 RNG_got_ssp AL_got_ssp RNG_ssp_guard AL_ssp_guard LAY_got_ssp_ssp_guard memset_spec fwritex_call"] Lemma gw_all : True. Proof. exact I. Qed.

Definition pad_entry := (base + 0x0)%Z.

Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
rw_cells segs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells segs m ssp_guard [C8 canary].

Definition memset_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(D C N : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(D, D + N)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rw_cells segs m' D [CB (Z.to_nat N) (repeat (Z_to_bv 8 (C mod 256)) (Z.to_nat N))].
#[using="memset_spec"] Lemma memset_callZ : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q D C N : Z) (junk : list byte),
rw_cells segs m D [CB (Z.to_nat N) junk] ->
mem_inv segs m ->
(0 <= q < 2^64)%Z -> (0 <= D < 2^64)%Z -> (0 <= C < 2^64)%Z -> (0 <= N < 2^64)%Z ->
evt segs (memset_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D C N m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_memset + 0x0)) fc None m (seg_rom segs)).
Proof. clear - memset_spec segs e_memset.
intros until junk. intros DST MI Hq HD HC HN.
assert (Ed : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
assert (Ec : bv_unsigned (Z_to_bv 64 C) = C) by (apply unsigned_lit; lia).
assert (En : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
eapply evt_mono.
{ eapply (memset_spec ra (Z_to_bv 64 q)); rewrite ?Ed, ?En; eauto. }
intros ms' P. unfold memset_post in P. rewrite !Ed, !Ec, !En in P. exact P.
Qed.

Definition pad_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word)
(C n : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned sp - 368, bv_unsigned sp);
(B + Z.of_nat (length content), B + Z.of_nat (length content) + n);
(Fp + 40, Fp + 48)]%Z m m'
/\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' (bv_unsigned sp - 368) (bv_unsigned sp)
/\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ repeat (Z_to_bv 8 C) (Z.to_nat n)) (skipn (Z.to_nat n) junk)
/\ ssp_cells m' canary.

#[using="w_7 w_8 w_21 w_33 w_41 w_52 hi_7 lo_8 joff_21 joff_41 e_fwritex e_memset CODE BASE4 BASER D_7 E_7 D_8 E_8 D_21 E_21 D_41 E_41 ANCH_8 LINK_21 LINK_41 RNG_got_ssp RNG_ssp_guard LAY_got_ssp_ssp_guard memset_spec fwritex_call"] Lemma pad_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (C W L FL : Z)
(fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word),
wfile m (bv_unsigned a0) fl0 j1 j2 lbfw B content junk ->
ssp_cells m canary ->
stk segs m (bv_unsigned sp - 368) (bv_unsigned sp) ->
mem_inv segs m ->
(0 <= C < 256)%Z -> (-2^31 <= W < 2^31)%Z -> (0 <= L < 2^31)%Z -> (0 <= FL < 2^32)%Z ->
(W - L < 256)%Z ->
(pad_n W L FL <= Z.of_nat (length junk))%Z ->
(ssp_guard + 8 <= bv_unsigned sp - 368)%Z ->
(bv_unsigned sp <= bv_unsigned a0)%Z -> (bv_unsigned sp <= B)%Z ->
evt segs (pad_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
(bv_unsigned a0) fl0 j1 j2 lbfw B content junk canary C (pad_n W L FL) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 C) (Z_to_bv 64 W) (Z_to_bv 64 L) (Z_to_bv 64 FL) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof. clear - w_7 w_8 w_21 w_33 w_41 w_52 hi_7 lo_8 joff_21 joff_41 e_fwritex e_memset CODE BASE4 BASER D_7 E_7 D_8 E_8 D_21 E_21 D_41 E_41 ANCH_8 LINK_21 LINK_41 RNG_got_ssp RNG_ssp_guard LAY_got_ssp_ssp_guard memset_spec fwritex_call segs base ssp_guard.
intros until canary. intros WF (GOT & SSP) ST MI HC HW HL HFL HWL ROOM GLO AF AB.
pose proof WF as WF0. destruct WF as (FC & BUF & FLG & LBF & Bpos & Bhi & SEPfb).
pose_word_ranges.
set (Fp := bv_unsigned a0) in *. replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
pose proof (rw_cells_bound _ _ _ _ FC) as BF. cbn [cells_size csize Nat.add length] in BF.
pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB. rewrite Nat.add_0_r, Nat2Z.inj_add in BB.
gw_expose got_ssp; gw_expose ssp_guard.
pose proof (munch_refl [(bv_unsigned sp - 368, bv_unsigned sp);
(B + Z.of_nat (length content), B + Z.of_nat (length content) + pad_n W L FL);
(Fp + 40, Fp + 48)]%Z m) as MU.
pose proof (wmono_refl segs m) as WM.
unfold FILE_cells in FC.
carve_frame 304%nat ST.
do 6 zstep. zstep. zstep. zstep. zstep. zstep.

assert (EXIT : forall m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 (n : Z) pad256,
n = pad_n W L FL ->
mem_inv segs m1 ->
rw_cells segs m1 (bv_unsigned sp + -304) [CB 256 pad256; C8 canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk segs m1 (bv_unsigned sp - 368) (bv_unsigned sp + -304) ->
munch [(bv_unsigned sp - 368, bv_unsigned sp); (B + Z.of_nat (length content), B + Z.of_nat (length content) + pad_n W L FL); (Fp + 40, Fp + 48)]%Z m m1 ->
wmono segs m m1 ->
wfile m1 Fp fl0 j1 j2 lbfw B (content ++ repeat (Z_to_bv 8 C) (Z.to_nat n)) (skipn (Z.to_nat n) junk) ->
rw_cells segs m1 got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells segs m1 ssp_guard [C8 canary] ->
evt segs (pad_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp fl0 j1 j2 lbfw B content junk canary C (pad_n W L FL) m)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -304)) gp tp x5 x6 x7 (Z_to_bv 64 Fp) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ssp_guard) x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0xa8)) fc None m1 (seg_rom segs))).
{ intros until pad256. intros Hn MI1 FR1 ST1 MU1 WM1 WF1 GOT1 SSP1. gw_expose got_ssp; gw_expose ssp_guard.
zstep. zstep. zstep. if_cases Kc; zify_cond Kc.
{ exfalso. clear -Kc. apply Kc. reflexivity. }
do 6 zstep. zstep. release_frame FR1 ST1 (bv_unsigned sp).
apply evt_done. unfold pad_post.
repeat (lazymatch goal with |- ex _ => eexists end).
split; [ ms_eq | ].
split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
split; [rewrite <- Hn; exact WF1 | gw_expose got_ssp; gw_expose ssp_guard; unfold ssp_cells; split; [exact GOT1 | exact SSP1]]. }

Ltac mk_wfile FC BUF FLG LBF := split; [exact FC|]; split; [exact BUF|]; split; [exact FLG|]; split; [exact LBF|]; split; [lia|]; split; lia.
assert (PN0 : (W <= L \/ Z.land FL 73728 <> 0)%Z -> pad_n W L FL = 0%Z).
{ intros HH. unfold pad_n, LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z.
destruct (Z.eqb_spec (Z.land FL 73728) 0); destruct (Z.leb_spec0 W L); cbn; lia. }
zstep. if_cases Kw; zify_cond Kw; rewrite !signed_of_Z in Kw by lia.
-
eapply EXIT; [ reflexivity | exact MI | exact FR | exact ST | exact MU | exact WM | | exact GOT | exact SSP ].
rewrite PN0 by lia. rewrite !Z2Nat.inj_0. cbn [repeat]. rewrite skipn_O, app_nil_r. mk_wfile FC BUF FLG LBF.
- zstep. zstep. zstep. if_cases Kf; zify_cond Kf.
+
eapply EXIT; [ reflexivity | exact MI | exact FR | exact ST | exact MU | exact WM | | exact GOT | exact SSP ].
rewrite PN0 by lia. rewrite !Z2Nat.inj_0. cbn [repeat]. rewrite skipn_O, app_nil_r. mk_wfile FC BUF FLG LBF.
+ assert (PN : pad_n W L FL = (W - L)%Z).
{ unfold pad_n, LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z.
destruct (Z.eqb_spec (Z.land FL 73728) 0); destruct (Z.leb_spec0 W L); cbn; lia. }
rewrite PN in *. set (N := (W - L)%Z) in *.
zstep. rewrite Z_to_bv_swrap32, (sext32_small (W - L)) by lia. fold N.
zstep. zstep. zstep. if_cases Kn; zify_cond Kn.
2:{ exfalso. revert Kn. rewrite ?unsigned_lit by lia. lia. }

apply (rw_cells_split_CB segs _ _ [] 256 _ [C8 canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] [Z.to_nat N; 256 - Z.to_nat N]%nat) in FR; [ | cbn; lia ].
cbn [mk_CB_cells app] in FR.
apply (proj1 (rw_cells_app segs _ _ [_] _)) in FR. destruct FR as [FRa FRb].
cbn [cells_size csize] in FRb. rewrite Nat.add_0_r, Z2Nat.id in FRb by lia.
zstep. zstep. call memset_callZ.
1:{ exact FRa. } 1:{ hyp. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
rewrite (Z.mod_small C 256) in * by lia.
match goal with MSC : rw_cells _ _ (bv_unsigned sp + -304)%Z [CB (Z.to_nat N) _] |- _ => rename MSC into FRa end.
zstep. if_cases Kn2; zify_cond Kn2.
2:{ exfalso. revert Kn2. rewrite ?unsigned_lit by lia. lia. }
zstep. zstep. zstep. if_cases Ke; zify_cond Ke.
{ exfalso. exact (Ke FLG). }
zstep. zstep. zstep. zstep.
pose proof (rw_cells_bytes_at' _ _ _ _ FRa) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.

set (bsP := repeat (Z_to_bv 8 C) (Z.to_nat N)) in *.
assert (LbsP : length bsP = Z.to_nat N) by (subst bsP; apply repeat_length).
set (nc := length content) in *. set (nj := length junk) in *.

lazymatch goal with |- evt ?segs_ _ (MS _ _ _ _ _ ?m _) =>
eapply evt_cut;
[ eapply fwritex_call;
[ mk_wfile FC BUF FLG LBF
| exact SRC
| rewrite LbsP, Z2Nat.id by lia; reflexivity
| rewrite LbsP; lia
| replace (bv_unsigned sp + -304 - 64)%Z with (bv_unsigned sp - 368)%Z by lia; exact ST
| hyp
| lia | lia | lia | lia | lia | lia | lia | lia | lia ]
| post_call segs_ m ]
end.
match goal with X : stk _ _ (bv_unsigned sp + -304 - 64)%Z _ |- _ =>
replace (bv_unsigned sp + -304 - 64)%Z with (bv_unsigned sp - 368)%Z in X by lia end.
match goal with X : wfile _ _ _ _ _ _ _ _ (skipn (length _) _) |- _ => rewrite LbsP in X end.
match goal with X : rw_cells _ _ (bv_unsigned sp + -304)%Z [CB (Z.to_nat N) _] |- _ => rename X into FRa' end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
lazymatch type of FRb with rw_cells _ _ _ (?c2 :: ?rest) =>
assert (FR : rw_cells segs mm (bv_unsigned sp + -304) ([] ++ [CB (Z.to_nat N) bsP; c2] ++ rest));
[ cbn [app]; apply (proj2 (rw_cells_app segs _ _ [_] _)); split; [ exact FRa' |];
cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact FRb
| apply rw_cells_merge in FR; cbn [cells_size cells_bytes csize cbytes app Nat.add] in FR;
rewrite app_nil_r in FR; replace (Z.to_nat N + (256 - Z.to_nat N + 0))%nat with 256%nat in FR by lia ]
end end.
unfold bsP in *. eapply EXIT; [ reflexivity | hyp | exact FR | hyp | hyp | hyp | hyp | gw_expose got_ssp; gw_expose ssp_guard; hyp | gw_expose ssp_guard; hyp ].
Qed.

Definition pad_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word)
(C n : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(q - 368, q);
(B + Z.of_nat (length content), B + Z.of_nat (length content) + n);
(Fp + 40, Fp + 48)]%Z m m'
/\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' (q - 368) q
/\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ repeat (Z_to_bv 8 C) (Z.to_nat n)) (skipn (Z.to_nat n) junk)
/\ ssp_cells m' canary.

#[using="w_7 w_8 w_21 w_33 w_41 w_52 hi_7 lo_8 joff_21 joff_41 e_fwritex e_memset CODE BASE4 BASER D_7 E_7 D_8 E_8 D_21 E_21 D_41 E_41 ANCH_8 LINK_21 LINK_41 RNG_got_ssp RNG_ssp_guard LAY_got_ssp_ssp_guard memset_spec fwritex_call"] Lemma pad_call : forall ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q Fp C W L FL : Z)
(fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word),
wfile m Fp fl0 j1 j2 lbfw B content junk ->
ssp_cells m canary ->
stk segs m (q - 368) q ->
mem_inv segs m ->
(0 <= C < 256)%Z -> (-2^31 <= W < 2^31)%Z -> (0 <= L < 2^31)%Z -> (0 <= FL < 2^32)%Z ->
(W - L < 256)%Z ->
(pad_n W L FL <= Z.of_nat (length junk))%Z ->
(ssp_guard + 8 <= q - 368)%Z -> (q < 2^64)%Z ->
(q <= Fp < 2^64)%Z -> (q <= B)%Z ->
evt segs (pad_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
Fp fl0 j1 j2 lbfw B content junk canary C (pad_n W L FL) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 C) (Z_to_bv 64 W) (Z_to_bv 64 L) (Z_to_bv 64 FL) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof. clear - w_7 w_8 w_21 w_33 w_41 w_52 hi_7 lo_8 joff_21 joff_41 e_fwritex e_memset CODE BASE4 BASER D_7 E_7 D_8 E_8 D_21 E_21 D_41 E_41 ANCH_8 LINK_21 LINK_41 RNG_got_ssp RNG_ssp_guard LAY_got_ssp_ssp_guard memset_spec fwritex_call segs base ssp_guard.
intros until canary. intros WF SSP ST MI HC HW HL HFL HWL ROOM GLO Hq HF HB.
gw_expose ssp_guard.
assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
assert (Ef : bv_unsigned (Z_to_bv 64 Fp) = Fp) by (apply unsigned_lit; lia).
eapply evt_mono.
{ eapply (pad_spec ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp)); rewrite ?Eq, ?Ef; eauto; gw_expose ssp_guard; lia. }
intros ms' P. unfold pad_post in P. rewrite !Eq, !Ef in P. exact P.
Qed.

End G.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg.
Import QZAi.Mq1 QZAi.
Import QnDM_c1.
Import QVbl.Mq4.
Import QQLG.Mq1.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope bv_scope.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition pop_arg_code (w_4 w_5 : Z) : list Z :=
[0xff758593; 0x01100693; 0x0eb6ec63; 0x00259593; w_4; w_5; 0x00d585b3; 0x0005a583; 0x00d585b3; 0x00058067; 0x00063583; 0x00858693; 0x00d63023; 0x0005b583; 0x00b53023; 0x00008067; 0xff010113; 0x00113423; 0x00813023; 0x00063583; 0x00858693; 0x00d63023; 0x0005b507; 0x00050413; 0x1c1010ef; 0x00a43023; 0x00b43423; 0x00813083; 0x00013403; 0x01010113; 0x00008067; 0x00063583; 0x00858693; 0x00d63023; 0x00058583; 0x00b53023; 0x00008067; 0x00063583; 0x00858693; 0x00d63023; 0x0005e583; 0x00b53023; 0x00008067; 0x00063583; 0x00858693; 0x00d63023; 0x00059583; 0x00b53023; 0x00008067; 0x00063583; 0x00858693; 0x00d63023; 0x0005c583; 0x00b53023; 0x00008067; 0x00063583; 0x00f58593; 0xff05f593; 0x01058693; 0x00d63023; 0x0005b603; 0x0085b583; 0x00c53023; 0x00b53423; 0x00008067; 0x00063583; 0x00858693; 0x00d63023; 0x0005d583; 0x00b53023; 0x00008067; 0x00063583; 0x00858693; 0x00d63023; 0x0005a583; 0x00b53023; 0x00008067]%Z.

Definition T_PTR := 9%Z. Definition T_INT := 10%Z. Definition T_UINT := 11%Z. Definition T_DBL := 25%Z.
Definition T_LONG := 13%Z. Definition T_ULONG := 14%Z.

Definition pop_arg_lo (ty : Z) (slot : word) : word :=
if ((ty =? T_PTR) || (ty =? T_LONG) || (ty =? T_ULONG))%Z%bool then slot
else if (ty =? T_INT)%Z then sx32 slot
else if (ty =? T_UINT)%Z then zx32 slot
else Z_to_bv 64 (lo64 (f128_of_d (bv_unsigned slot))).
Definition pop_arg_hi (ty : Z) (slot y : word) : word :=
if (ty =? T_DBL)%Z then Z_to_bv 64 (hi64 (f128_of_d (bv_unsigned slot))) else y.

Lemma firstn4_le8 : forall w : word, firstn 4 (le8 w) = le4 w.
Proof. intros w. reflexivity. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac if_lit :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
let v := eval vm_compute in c in change c with v; cbv iota
end. Ltac mkr__if_lit_4 := lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
let v := eval vm_compute in c in change c with v; cbv iota
end.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_4 w_5 : Z).
Variables (hi_4 : bv 20).
Variables (lo_5 : bv 12).
Variables (G_11878 : Z).
Variables (jt_11878_o40 jt_11878_o284 jt_11878_o148 jt_11878_o64 : Z).
Hypothesis CODE : code_at segs base (pop_arg_code w_4 w_5).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 308.
Hypothesis D_4 : decode_any (Z_to_bv 32 w_4) = Some (Auipc 13 hi_4, 4%Z).
Hypothesis E_4 : is_ecall (Z_to_bv 32 w_4) = false.
Hypothesis D_5 : decode_any (Z_to_bv 32 w_5) = Some (OpImm ALU_ADD 13 13 lo_5, 4%Z).
Hypothesis E_5 : is_ecall (Z_to_bv 32 w_5) = false.
Hypothesis ANCH_5 : gw_anch (Z.shiftl (bv_signed hi_4) 12 + (base + 16) + bv_signed lo_5)%Z G_11878.
Hypothesis RNG_G_11878 : gw_br G_11878 68.
Hypothesis JTL_jt_11878_o40 : gw_anch (bv_unsigned (sx32 (Z_to_bv 64 jt_11878_o40)) + G_11878)%Z (base + 40)%Z.
Hypothesis ROM_jt_11878_0 : ro_bytes segs (G_11878 + 0) (le4 (Z_to_bv 64 jt_11878_o40)).
Hypothesis JTL_jt_11878_o284 : gw_anch (bv_unsigned (sx32 (Z_to_bv 64 jt_11878_o284)) + G_11878)%Z (base + 284)%Z.
Hypothesis ROM_jt_11878_1 : ro_bytes segs (G_11878 + 4) (le4 (Z_to_bv 64 jt_11878_o284)).
Hypothesis JTL_jt_11878_o148 : gw_anch (bv_unsigned (sx32 (Z_to_bv 64 jt_11878_o148)) + G_11878)%Z (base + 148)%Z.
Hypothesis ROM_jt_11878_2 : ro_bytes segs (G_11878 + 8) (le4 (Z_to_bv 64 jt_11878_o148)).
Hypothesis ROM_jt_11878_4 : ro_bytes segs (G_11878 + 16) (le4 (Z_to_bv 64 jt_11878_o40)).
Hypothesis ROM_jt_11878_5 : ro_bytes segs (G_11878 + 20) (le4 (Z_to_bv 64 jt_11878_o40)).
Hypothesis JTL_jt_11878_o64 : gw_anch (bv_unsigned (sx32 (Z_to_bv 64 jt_11878_o64)) + G_11878)%Z (base + 64)%Z.
Hypothesis ROM_jt_11878_16 : ro_bytes segs (G_11878 + 64) (le4 (Z_to_bv 64 jt_11878_o64)).

Local Definition gw_tbl_0 := tt.

Definition extenddftf2_post : ltac:(gw_rebind_ty (@QQLG.Mq1.extenddftf2_post segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QQLG.Mq1.extenddftf2_post segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post gw_tbl_0).

Hypothesis extenddftf2_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.Mq1.extenddftf2_spec segs (base + 6688)%Z) 3%nat in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_1))) in let T := gw_fold_pcs T base (6688)%Z [0]%Z in exact T).
#[using="G_11878 CODE BASE4 BASER D_4 E_4 D_5 E_5 ANCH_5 RNG_G_11878 JTL_jt_11878_o40 ROM_jt_11878_0 JTL_jt_11878_o284 ROM_jt_11878_1 JTL_jt_11878_o148 ROM_jt_11878_2 ROM_jt_11878_4 ROM_jt_11878_5 JTL_jt_11878_o64 ROM_jt_11878_16 extenddftf2_spec"] Lemma gw_all : True. Proof. exact I. Qed.

#[using="RNG_G_11878"] Lemma gw_jt_rd_G_11878 : forall m k jt, mem_inv segs m -> (0 <= k /\ k + 4 <= 68)%Z -> ro_bytes segs (G_11878 + k) (le4 (Z_to_bv 64 jt)) ->
ov_read_bytes segs m (Z_to_bv 64 (k + G_11878)) 4 = Some (le4 (Z_to_bv 64 jt)).
Proof. clear - RNG_G_11878 segs G_11878. intros m k jt MI Hk ROM. pose proof RNG_G_11878 as R; unfold gw_br in R.
assert (RN : gw_br (G_11878 + k) 4) by (unfold gw_br; lia).
pose proof (ro_bytes_read segs m (G_11878 + k) 4 _ 0 4 MI ROM RN eq_refl) as RD.
rewrite Z.add_0_r in RD. replace (k + G_11878)%Z with (G_11878 + k)%Z by lia. exact RD. Qed.

Ltac gw_jt rd k jt ROM := lazymatch goal with MI : mem_inv _ ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (rd mc k jt MI ltac:(lia) ROM) as RDjt end.

Definition pop_arg_entry := (base + 0x0)%Z.

Definition va_area (m : word -> option byte) (VA : Z) (slots : list word) : Prop :=
bytes_at segs m VA (u64s slots).

Definition pop_arg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(ARG AP VA : Z) (slots : list word) (i ty : Z) (slot y : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Ft m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (AP, AP + 8); (ARG, ARG + 16)]%Z m m'
/\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' (bv_unsigned sp - 16) (bv_unsigned sp)
/\ rw_cells segs m' AP [C8 (Z_to_bv 64 (VA + 8 * (i + 1)))]
/\ rw_cells segs m' ARG [C8 (pop_arg_lo ty slot); C8 (pop_arg_hi ty slot y)]
/\ va_area m' VA slots
/\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k).

#[using="Type"] Lemma va_read8 : forall m VA slots (i : Z) w a,
bytes_at segs m VA (u64s slots) -> nth_error slots (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (VA + 8 * i) ->
ov_read_bytes segs m a 8 = Some (le8 w).
Proof. clear - segs.
intros m VA slots i w a Hb Hn Hi ->.
destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
rewrite (bytes_at_ov_read segs m VA (u64s slots) (8 * Z.to_nat i) 8 Hb).
2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

#[using="Type"] Lemma va_read4 : forall m VA slots (i : Z) w a,
bytes_at segs m VA (u64s slots) -> nth_error slots (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (VA + 8 * i) ->
ov_read_bytes segs m a 4 = Some (le4 w).
Proof. clear - segs.
intros m VA slots i w a Hb Hn Hi ->.
destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
rewrite (bytes_at_ov_read segs m VA (u64s slots) (8 * Z.to_nat i) 4 Hb).
2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
rewrite firstn_app. rewrite length_le8. change (4 - 8)%nat with 0%nat. rewrite firstn_O, app_nil_r.
rewrite firstn4_le8. reflexivity.
Qed.

#[using="Type"] Lemma va_area_bound : forall m VA slots, va_area m VA slots -> (0 <= VA /\ VA + 8 * Z.of_nat (length slots) <= 2^64)%Z.
Proof. intros m VA slots H. pose proof (bytes_at_bound _ _ _ _ H) as B. rewrite u64s_length in B. lia. Qed.

#[using="w_4 w_5 hi_4 lo_5 G_11878 jt_11878_o40 jt_11878_o284 jt_11878_o148 jt_11878_o64 CODE BASE4 BASER D_4 E_4 D_5 E_5 ANCH_5 RNG_G_11878 JTL_jt_11878_o40 ROM_jt_11878_0 JTL_jt_11878_o284 ROM_jt_11878_1 JTL_jt_11878_o148 ROM_jt_11878_2 ROM_jt_11878_4 ROM_jt_11878_5 JTL_jt_11878_o64 ROM_jt_11878_16 extenddftf2_spec"] Lemma pop_arg_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte)
(VA : Z) (slots : list word) (i ty : Z) (slot x y : word),
rw_cells segs m (bv_unsigned a2) [C8 (Z_to_bv 64 (VA + 8 * i))] ->
va_area m VA slots -> nth_error slots (Z.to_nat i) = Some slot -> (0 <= i)%Z ->
rw_cells segs m (bv_unsigned a0) [C8 x; C8 y] ->
stk segs m (bv_unsigned sp - 16) (bv_unsigned sp) ->
mem_inv segs m ->
a1 = Z_to_bv 64 ty -> (ty = T_PTR \/ ty = T_INT \/ ty = T_UINT \/ ty = T_DBL \/ ty = T_LONG \/ ty = T_ULONG) ->
(16 <= bv_unsigned sp)%Z ->
(bv_unsigned sp <= bv_unsigned a2)%Z -> (bv_unsigned sp <= bv_unsigned a0)%Z ->
(bv_unsigned a2 + 8 <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= bv_unsigned a2)%Z ->
(VA + 8 * Z.of_nat (length slots) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= VA)%Z ->
(VA + 8 * Z.of_nat (length slots) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 <= VA)%Z ->
(VA + 8 * Z.of_nat (length slots) <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= VA)%Z ->
evt segs (pop_arg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
(bv_unsigned a0) (bv_unsigned a2) VA slots i ty slot y m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof. clear - w_4 w_5 hi_4 lo_5 G_11878 jt_11878_o40 jt_11878_o284 jt_11878_o148 jt_11878_o64 CODE BASE4 BASER D_4 E_4 D_5 E_5 ANCH_5 RNG_G_11878 JTL_jt_11878_o40 ROM_jt_11878_0 JTL_jt_11878_o284 ROM_jt_11878_1 JTL_jt_11878_o148 ROM_jt_11878_2 ROM_jt_11878_4 ROM_jt_11878_5 JTL_jt_11878_o64 ROM_jt_11878_16 extenddftf2_spec segs base.
intros until y. intros APC VAA NTH Hi ARGC ST MI -> TY SPLO A2 A0 SEP1 SEP2 SEP3 SEP4.
pose_word_ranges.
pose proof (va_area_bound _ _ _ VAA) as VB. unfold va_area in VAA.
assert (IL : (Z.to_nat i < length slots)%nat) by (apply nth_error_Some; rewrite NTH; discriminate).
set (AP := bv_unsigned a2) in *. replace a2 with (Z_to_bv 64 AP) by (unfold AP; rewrite Z_to_bv_bv_unsigned; reflexivity).
set (ARG := bv_unsigned a0) in *. replace a0 with (Z_to_bv 64 ARG) by (unfold ARG; rewrite Z_to_bv_bv_unsigned; reflexivity).
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (AP, AP + 8); (ARG, ARG + 16)]%Z m) as MU.
pose proof (wmono_refl segs m) as WM.
destruct TY as [-> | [-> | [-> | [-> | [-> | ->]]]]]; unfold T_PTR, T_INT, T_UINT, T_DBL, T_LONG, T_ULONG.
5:{
zstep. zstep. zstep. if_lit. do 4 zstep. gw_jt gw_jt_rd_G_11878 16%Z jt_11878_o40 ROM_jt_11878_4. zstep. clear RDjt. zstep. zstep.
zstep. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read8 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
zstep. clear RD. zstep. zstep.
replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
finish. { intros k Hk. reflexivity. } }
5:{
zstep. zstep. zstep. if_lit. do 4 zstep. gw_jt gw_jt_rd_G_11878 20%Z jt_11878_o40 ROM_jt_11878_5. zstep. clear RDjt. zstep. zstep.
zstep. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read8 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
zstep. clear RD. zstep. zstep.
replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
finish. { intros k Hk. reflexivity. } }
-
zstep. zstep. zstep. if_lit. do 4 zstep. gw_jt gw_jt_rd_G_11878 0%Z jt_11878_o40 ROM_jt_11878_0. zstep. clear RDjt. zstep. zstep.
zstep. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read8 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
zstep. clear RD. zstep. zstep.
replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
finish. { intros k Hk. reflexivity. }
-
zstep. zstep. zstep. if_lit. do 4 zstep. gw_jt gw_jt_rd_G_11878 4%Z jt_11878_o284 ROM_jt_11878_1. zstep. clear RDjt. zstep. zstep.
zstep. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read4 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
zstep. clear RD. zstep. zstep.
replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
finish. { intros k Hk. reflexivity. }
-
zstep. zstep. zstep. if_lit. do 4 zstep. gw_jt gw_jt_rd_G_11878 8%Z jt_11878_o148 ROM_jt_11878_2. zstep. clear RDjt. zstep. zstep.
zstep. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read4 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
zstep. clear RD. zstep. zstep.
replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
finish. { intros k Hk. reflexivity. }
-
zstep. zstep. zstep. if_lit. do 4 zstep. gw_jt gw_jt_rd_G_11878 64%Z jt_11878_o64 ROM_jt_11878_16. zstep. clear RDjt. zstep. zstep.
carve_frame 16%nat ST.
zstep. zstep. zstep.
zstep. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read8 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
zstep. clear RD. zstep.
zstep. call extenddftf2_spec. 1:{ exact MI. }
idtac. idtac.
rewrite freg_get_same by reflexivity.
zstep. zstep. zstep. zstep. zstep. zstep.
replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
release_frame FR ST (bv_unsigned sp).
finish.
{ intros k Hk. apply freg_get_other. unfold bv_eqb. apply Z.eqb_neq. change (bv_unsigned 10) with 10%Z. lia. }
Qed.

End G.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope bv_scope.

Definition scalbn_code (w_2 w_3 w_16 w_17 : Z) : list Z :=
[0x40000593; 0x02b54a63; w_2; w_3; 0x7ff00593; 0x12f57553; 0x04b56c63; 0x000015b7; 0xbfd5859b; 0x00b56463; 0x00058513; 0x12f57553; 0x80250513; 0x0480006f; 0xc0100593; 0x04a5c063; w_16; w_17; 0x83800593; 0x12f57553; 0x02a5e463; 0xfffff5b7; 0x4705859b; 0x00a5e463; 0x00058513; 0x12f57553; 0x79250513; 0x0100006f; 0xc0150513; 0x0080006f; 0x3c950513; 0x03451513; 0x3ff00593; 0x03459593; 0x00b50533; 0xf20507d3; 0x12f57553; 0x00008067]%Z.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition two_p1023 : word := Z_to_bv 64 0x7FE0000000000000.
Definition two_m969  : word := Z_to_bv 64 0x0360000000000000.

Definition scalbn_u (n : Z) : word := Z_to_bv 64 (Z.shiftl (1023 + n) 52).

Definition scalbn_reduce (x : word) (n : Z) : word * Z :=
if (1023 <? n)%Z then
let y := fmul_d RNE x two_p1023 in let n := (n - 1023)%Z in
if (1023 <? n)%Z then
let y := fmul_d RNE y two_p1023 in let n := (n - 1023)%Z in
(y, if (1023 <? n)%Z then 1023%Z else n)
else (y, n)
else if (n <? -1022)%Z then
let y := fmul_d RNE x two_m969 in let n := (n + 969)%Z in
if (n <? -1022)%Z then
let y := fmul_d RNE y two_m969 in let n := (n + 969)%Z in
(y, if (n <? -1022)%Z then (-1022)%Z else n)
else (y, n)
else (x, n).

Definition scalbn_model (x : word) (n : Z) : word :=
let (y, n') := scalbn_reduce x n in fmul_d RNE y (scalbn_u n').

Lemma word_signed_cases : forall a : word,
((0 <= bv_unsigned a < 2^63)%Z /\ bv_signed a = bv_unsigned a) \/
((2^63 <= bv_unsigned a < 2^64)%Z /\ bv_signed a = (bv_unsigned a - 2^64)%Z).
Proof.
intros a. pose proof (bv_unsigned_in_range 64 a) as Hr. unfold bv_modulus in Hr.
unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ (Z.of_N 64 - 1))%Z with (2^63)%Z. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in *.
destruct (Z.lt_ge_cases (bv_unsigned a) (2^63)).
- left. rewrite Z.mod_small by lia. lia.
- right. rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma scalbn_pack : forall (a : word) (n : Z),
bv_signed a = n -> (-1023 <= n <= 1023)%Z ->
Z_to_bv 64 (Z.shiftl (bv_unsigned a) 52 + 4607182418800017408) = scalbn_u n.
Proof.
intros a n Hn Hr. unfold scalbn_u. change 4607182418800017408%Z with (Z.shiftl 1023 52).
apply bv_eq. rewrite !Z_to_bv_unsigned.
change (bv_wrap 64 ?x = bv_wrap 64 ?y) with (x mod 2^64 = y mod 2^64)%Z.
rewrite !Z.shiftl_mul_pow2 by lia.
destruct (word_signed_cases a) as [[H1 H2]|[H1 H2]].
- f_equal. lia.
- replace (bv_unsigned a) with (n + 2^12 * 2^52)%Z by lia.
rewrite Z.mul_add_distr_r. change (2^64)%Z with (2^12 * 2^52)%Z at 1.
rewrite <- Z.add_assoc, (Z.add_comm (2^12 * 2^52 * 2^52)), Z.add_assoc.
replace (2 ^ 12 * 2 ^ 52 * 2 ^ 52)%Z with ((2^52) * (2^12 * 2^52))%Z by lia.
rewrite Z.mod_add by lia. change (2^12 * 2^52)%Z with (2^64)%Z. f_equal. lia.
Qed.

Lemma signed_of_add : forall (a : word) (d n : Z),
bv_signed a = n -> (-2^63 <= n + d < 2^63)%Z ->
bv_signed (Z_to_bv 64 (bv_unsigned a + d)) = (n + d)%Z.
Proof.
intros a d n Hn Hr. rewrite Z_to_bv_signed.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 64)%Z with (2^64)%Z. change (2^64 / 2)%Z with (2^63)%Z.
destruct (word_signed_cases a) as [[H1 H2]|[H1 H2]].
- rewrite Z.mod_small by lia. lia.
- replace (bv_unsigned a + d + 2^63)%Z with ((n + d + 2^63) + 1 * 2^64)%Z by lia.
rewrite Z.mod_add, Z.mod_small by lia. lia.
Qed.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_2 w_3 w_16 w_17 : Z).
Variables (hi_2 hi_16 : bv 20).
Variables (lo_3 lo_17 : bv 12).
Variables (G_107a8 G_107c8 : Z).
Hypothesis CODE : code_at segs base (scalbn_code w_2 w_3 w_16 w_17).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 152.
Hypothesis D_2 : decode_any (Z_to_bv 32 w_2) = Some (Auipc 11 hi_2, 4%Z).
Hypothesis E_2 : is_ecall (Z_to_bv 32 w_2) = false.
Hypothesis D_3 : decode_any (Z_to_bv 32 w_3) = Some (FLoad FMT_D 15 11 lo_3, 4%Z).
Hypothesis E_3 : is_ecall (Z_to_bv 32 w_3) = false.
Hypothesis D_16 : decode_any (Z_to_bv 32 w_16) = Some (Auipc 11 hi_16, 4%Z).
Hypothesis E_16 : is_ecall (Z_to_bv 32 w_16) = false.
Hypothesis D_17 : decode_any (Z_to_bv 32 w_17) = Some (FLoad FMT_D 15 11 lo_17, 4%Z).
Hypothesis E_17 : is_ecall (Z_to_bv 32 w_17) = false.
Hypothesis ANCH_3 : gw_anch (Z.shiftl (bv_signed hi_2) 12 + (base + 8) + bv_signed lo_3)%Z G_107a8.
Hypothesis ANCH_17 : gw_anch (Z.shiftl (bv_signed hi_16) 12 + (base + 64) + bv_signed lo_17)%Z G_107c8.
Hypothesis RNG_G_107a8 : gw_br G_107a8 8.
Hypothesis ROM_G_107a8 : ro_bytes segs G_107a8 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 224; Z_to_bv 8 127].
Hypothesis RNG_G_107c8 : gw_br G_107c8 8.
Hypothesis ROM_G_107c8 : ro_bytes segs G_107c8 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 96; Z_to_bv 8 3].

Local Definition gw_tbl_0 := tt.

#[using="G_107a8 G_107c8 CODE BASE4 BASER D_2 E_2 D_3 E_3 D_16 E_16 D_17 E_17 ANCH_3 ANCH_17 RNG_G_107a8 ROM_G_107a8 RNG_G_107c8 ROM_G_107c8"] Lemma gw_all : True. Proof. exact I. Qed.

Definition scalbn_entry := (base + 0x0)%Z.
Definition scalbn_tailpc := (base + 0x7c)%Z.

Definition scalbn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(x : word) (n : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (f15 : word) fc' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 10 (scalbn_model x n) (bvmap_set 15 f15 F)) (ret_pc ra) fc' None m' (seg_rom segs)
/\ munch [] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ frm0 fc'.

#[using="w_2 w_3 w_16 w_17 CODE"] Lemma scalbn_tail : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(Ft : bvmap 5 word) fc (m : word -> option byte) (n' : Z) (Q : machine_state -> Prop),
mem_inv segs m -> frm0 fc -> bv_signed a0 = n' -> (-1022 <= n' <= 1023)%Z ->
(forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc',
frm0 fc' ->
Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 10 (fmul_d RNE (reg_get Ft 10) (scalbn_u n')) (bvmap_set 15 (scalbn_u n') Ft))
(ret_pc ra) fc' None m (seg_rom segs))) ->
evt segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 (base + 0x7c)) fc None m (seg_rom segs)).
Proof. clear - w_2 w_3 w_16 w_17 CODE segs base.
intros until Q. intros MI FRM Hn Hr HQ.
do 4 step. rewrite (scalbn_pack a0 n' Hn) by lia.
do 3 step.
apply evt_done. apply HQ. exact FRM.
Qed.

Ltac scalbn_close :=
intros; unfold scalbn_post;
repeat (lazymatch goal with |- ex _ => eexists end);
split;
[ simp_regs; f_equal; f_equal; unfold scalbn_model, scalbn_reduce, two_p1023, two_m969;
repeat match goal with
| |- context [Z.ltb ?a ?b] =>
first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ]
end;

repeat match goal with |- context [if Z.ltb ?a ?b then _ else _] => destruct (Z.ltb_spec0 a b) end;
match goal with |- fmul_d _ _ (scalbn_u ?a) = fmul_d _ _ (scalbn_u ?b) => replace b with a by lia end;
reflexivity
| repeat match goal with |- _ /\ _ => split end; assumption ].

Ltac scalbn_go_tail n' :=
lazymatch goal with
| |- evt _ _ (MS _ ?Ft _ _ _ ?m _) =>
eapply (scalbn_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft _ m n');
[ assumption | assumption | | lia | scalbn_close ]
end.

#[using="w_2 w_3 w_16 w_17 hi_2 hi_16 lo_3 lo_17 G_107a8 G_107c8 CODE D_2 E_2 D_3 E_3 D_16 E_16 D_17 E_17 ANCH_3 ANCH_17 RNG_G_107a8 ROM_G_107a8 RNG_G_107c8 ROM_G_107c8"] Lemma scalbn_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (n : Z),
mem_inv segs m -> frm0 fc -> bv_signed a0 = n -> (-2^31 <= n < 2^31)%Z ->
evt segs (scalbn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (reg_get F 10) n m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof. clear - w_2 w_3 w_16 w_17 hi_2 hi_16 lo_3 lo_17 G_107a8 G_107c8 CODE D_2 E_2 D_3 E_3 D_16 E_16 D_17 E_17 ANCH_3 ANCH_17 RNG_G_107a8 ROM_G_107a8 RNG_G_107c8 ROM_G_107c8 segs base.
intros until n. intros MI FRM Hn Hr.
pose proof (word_signed_cases a0) as SC.
pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl segs m) as WM.
step. step.
if_cases LT1024; zify_cond LT1024.
-
step. step. if_cases GTm1023; zify_cond GTm1023.
+
scalbn_go_tail n. exact Hn.
+
do 5 step. if_cases GTm1992; zify_cond GTm1992.
*  step. scalbn_go_tail (n + 969)%Z. apply (signed_of_add a0 969 n Hn). lia.
* do 3 step. if_cases GTm2960; zify_cond GTm2960.
--  do 3 step. scalbn_go_tail (n + 1938)%Z. apply (signed_of_add a0 1938 n Hn). lia.
--  do 4 step. scalbn_go_tail (-1022)%Z. vm_compute; reflexivity.
-
do 4 step. step. if_cases LT2047; zify_cond LT2047.
+  do 2 step. scalbn_go_tail (n - 1023)%Z. apply (signed_of_add a0 (-1023) n Hn). lia.
+ do 3 step. if_cases LT3069; zify_cond LT3069.
*  do 3 step. scalbn_go_tail (n - 2046)%Z. apply (signed_of_add a0 (-2046) n Hn). lia.
*  do 4 step. scalbn_go_tail 1023%Z. vm_compute; reflexivity.
Qed.

End G.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope bv_scope.

Definition strncmp_code : list Z :=
[0x04060663; 0x00054683; 0x04068663; 0xfff60613; 0x00150513; 0x0005c703; 0x02e69263; 0x02070063; 0x00c03733; 0x00070c63; 0x00054683; 0xfff60613; 0x00158593; 0x00150513; 0xfc069ee3; 0x0ff6f513; 0x0005c583; 0x40b50533; 0x00008067; 0x00000513; 0x00008067; 0x0005c583; 0x40b00533; 0x00008067]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base strncmp_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 96.

Local Definition gw_tbl_0 := tt.

#[using="CODE BASE4 BASER"] Lemma gw_all : True. Proof. exact I. Qed.

Definition strncmp_entry := (base + 0x0)%Z.

Definition strncmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 : word) (ls rs : list byte) (v : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ bytes_at segs m' (bv_unsigned a0) ls /\ bytes_at segs m' (bv_unsigned a1) rs.

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ls rs : list byte) (v : Z).
Hypothesis MI : mem_inv segs m.
Hypothesis LS : bytes_at segs m (bv_unsigned a0) ls.
Hypothesis RS : bytes_at segs m (bv_unsigned a1) rs.
Let MU : munch [] m m := munch_refl [] m.
Let WM : wmono segs m m := wmono_refl segs m.

Notation A := (bv_unsigned a0).
Notation B := (bv_unsigned a1).
Notation n := (bv_unsigned a2).
Notation POST := (strncmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs v m).

Notation ST pc x10 x11 x12 x13 x14 :=
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom segs)).

#[using="segs m LS RS"] Lemma bounds : (0 <= A /\ A + Z.of_nat (length ls) <= 2^64 /\ 0 <= B /\ B + Z.of_nat (length rs) <= 2^64)%Z.
Proof. clear - segs m LS RS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ls rs v MI MU WM. first [clear MI | gw_hide MI | idtac]. pose proof (bytes_at_bound _ _ _ _ LS). pose proof (bytes_at_bound _ _ _ _ RS). lia. Qed.

#[using="Type"] Lemma byte_range : forall b : byte, (0 <= bv_unsigned b < 256)%Z.
Proof. clear - ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ls rs v MI LS RS MU WM. first [clear MI | gw_hide MI | idtac]; first [clear LS | gw_hide LS | idtac]; first [clear RS | gw_hide RS | idtac]. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.

#[using="Type"] Lemma walk_at : forall i k r,
strncmp_walk (skipn i ls) (skipn i rs) k = Some r ->
exists a b, nth_error ls i = Some a /\ nth_error rs i = Some b /\
(if ((bv_unsigned a =? 0) || (bv_unsigned b =? 0) || Nat.eqb k 0 || negb (bv_unsigned a =? bv_unsigned b))%Z%bool
then r = (bv_unsigned a - bv_unsigned b)%Z
else exists k', k = S k' /\ strncmp_walk (skipn (S i) ls) (skipn (S i) rs) k' = Some r).
Proof. clear - ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ls rs v MI LS RS MU WM. first [clear MI | gw_hide MI | idtac]; first [clear LS | gw_hide LS | idtac]; first [clear RS | gw_hide RS | idtac].
intros i k r H.
destruct (skipn i ls) as [|a l'] eqn:EL; [cbn in H; discriminate|].
destruct (skipn i rs) as [|b r'] eqn:ER; [cbn in H; discriminate|].
apply skipn_cons_nth in EL. apply skipn_cons_nth in ER. destruct EL as [Hna ->]. destruct ER as [Hnb ->].
exists a, b. split; [exact Hna|]. split; [exact Hnb|].
cbn [strncmp_walk] in H.
destruct ((bv_unsigned a =? 0) || (bv_unsigned b =? 0) || Nat.eqb k 0 || negb (bv_unsigned a =? bv_unsigned b))%Z%bool eqn:E.
- congruence.
- destruct k as [|k']. { cbn [Nat.eqb] in E. rewrite !orb_true_r in E. cbn in E. congruence. } exists k'. auto.
Qed.

#[using="CODE MI LS RS MU WM"] Lemma strncmp_ret : forall (i : Z) (a b : byte) x10 x12 x14,
(0 <= i)%Z -> nth_error rs (Z.to_nat i) = Some b -> v = (bv_unsigned a - bv_unsigned b)%Z ->
evt segs POST (ST (base + 0x3c) x10 (Z_to_bv 64 (B + i)) x12 (Z_to_bv 64 (bv_unsigned a)) x14).
Proof. clear - CODE MI LS RS MU WM segs base ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ls rs v.
intros i a b x10 x12 x14 Hi Hnb Hv; pose proof bounds as BD. pose proof (nth_error_lt _ _ _ Hnb).
pose proof (byte_range a). pose proof (byte_range b).
pose proof (u8ro_read segs m B rs i b _ RS Hnb ltac:(lia) eq_refl) as RD.
zstep. replace (Z.land (bv_unsigned a) 255) with (bv_unsigned a).
2:{ change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask, Z.mod_small by lia. reflexivity. }
zstep. zstep. zstep. subst v. finish.
Qed.

#[using="CODE MI LS RS MU WM"] Lemma strncmp_loop : forall (k : nat) (i : Z) (li : byte) x14,
(0 <= i)%Z -> nth_error ls (Z.to_nat i) = Some li -> bv_unsigned li <> 0%Z ->
strncmp_walk (skipn (Z.to_nat i) ls) (skipn (Z.to_nat i) rs) k = Some v -> (Z.of_nat k < 2^64)%Z ->
evt segs POST (ST (base + 0x14) (Z_to_bv 64 (A + i + 1)) (Z_to_bv 64 (B + i)) (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 (bv_unsigned li)) x14).
Proof. clear - CODE MI LS RS MU WM segs base ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ls rs v.
induction k as [|k IH]; intros i li x14 Hi Hli Hnz HW Hk; pose proof bounds as BD; pose proof (nth_error_lt _ _ _ Hli);
pose proof (byte_range li);
destruct (walk_at _ _ _ HW) as (a & b & Hna & Hnb & HC); rewrite Hli in Hna; injection Hna as <-;
pose proof (nth_error_lt _ _ _ Hnb); pose proof (byte_range b);
pose proof (u8ro_read segs m B rs i b _ RS Hnb ltac:(lia) eq_refl) as RD.
-
zstep. zstep. if_cases Kne; zify_cond Kne.
+ apply (strncmp_ret i li b); try lia; try assumption.
replace (negb (bv_unsigned li =? bv_unsigned b))%Z with true in HC by (symmetry; apply negb_true_iff, Z.eqb_neq; exact Kne).
rewrite !orb_true_r in HC. exact HC.
+ zstep. if_cases Kb0; zify_cond Kb0. { exfalso. lia. }
zstep. zstep. if_cases K0; zify_cond K0. 2:{ exfalso. cbn in K0. lia. }
apply (strncmp_ret i li b); try lia; try assumption.
cbn [Nat.eqb] in HC. rewrite !orb_true_r in HC. cbn in HC. exact HC.
- zstep. zstep. if_cases Kne; zify_cond Kne.
+ apply (strncmp_ret i li b); try lia; try assumption.
replace (negb (bv_unsigned li =? bv_unsigned b))%Z with true in HC by (symmetry; apply negb_true_iff, Z.eqb_neq; exact Kne).
rewrite !orb_true_r in HC. exact HC.
+ zstep. if_cases Kb0; zify_cond Kb0. { exfalso. lia. }
zstep. zstep. if_cases K0; zify_cond K0. { exfalso. lia. }

replace ((bv_unsigned li =? 0) || (bv_unsigned b =? 0) || Nat.eqb (S k) 0 || negb (bv_unsigned li =? bv_unsigned b))%Z%bool
with false in HC.
2:{ symmetry. rewrite (proj2 (Z.eqb_neq _ _) Hnz), (proj2 (Z.eqb_neq _ _) Kb0). cbn [orb Nat.eqb].
rewrite (proj2 (Z.eqb_eq _ _) Kne). reflexivity. }
destruct HC as (k' & Ek & HW'). injection Ek as <-.
destruct (walk_at _ _ _ HW') as (a' & b' & Hna' & Hnb' & _).
pose proof (nth_error_lt _ _ _ Hna'). pose proof (byte_range a').
pose proof (u8ro_read segs m A ls (i + 1) a' (Z_to_bv 64 (A + i + 1)) LS ltac:(replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia; exact Hna') ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD2.
zstep. zstep. zstep. zstep. zstep. if_cases Kz; zify_cond Kz.
* replace (A + i + 2)%Z with (A + (i + 1) + 1)%Z by lia. replace (B + i + 1)%Z with (B + (i + 1))%Z by lia.
replace (Z.of_nat (S k) + -1)%Z with (Z.of_nat k) by lia.
apply (IH (i + 1)%Z a'); try lia; try assumption.
all: replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia; assumption.
* replace (B + i + 1)%Z with (B + (i + 1))%Z by lia.
destruct (walk_at _ _ _ HW') as (a2' & b2 & Hna2 & Hnb2 & HC2). rewrite Hna' in Hna2. injection Hna2 as <-.
apply (strncmp_ret (i + 1) a' b2); try lia.
{ replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. exact Hnb2. }
rewrite (proj2 (Z.eqb_eq _ _) Kz) in HC2. cbn [orb] in HC2. exact HC2.
Qed.

#[using="CODE MI LS RS MU WM"] Lemma strncmp_body :
strncmp_model ls rs n = Some v ->
evt segs POST (ST (base + 0x0) a0 a1 a2 a3 a4).
Proof. clear - CODE MI LS RS MU WM segs base ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ls rs v.
intros HM; pose proof bounds as BD. unfold strncmp_model in HM.
pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2. cbn in R2.
zstep. if_cases K0; zify_cond K0.
- rewrite K0 in HM. cbn in HM. injection HM as <-. zstep. zstep. finish.
- rewrite (proj2 (Z.eqb_neq _ _) K0) in HM.
rewrite <- (skipn_O ls), <- (skipn_O rs) in HM.
destruct (walk_at _ _ _ HM) as (a & b & Hna & Hnb & HC).
pose proof (nth_error_lt _ _ _ Hna). pose proof (nth_error_lt _ _ _ Hnb). pose proof (byte_range a). pose proof (byte_range b).
pose proof (u8ro_read segs m A ls 0 a a0 LS Hna ltac:(lia) (eq_sym (Z_to_bv_plus0 a0))) as RD.
zstep. zstep. if_cases Ka; zify_cond Ka.
+
pose proof (u8ro_read segs m B rs 0 b a1 RS Hnb ltac:(lia) (eq_sym (Z_to_bv_plus0 a1))) as RD2.
zstep. zstep. zstep.
rewrite Ka in HC. cbn [Z.eqb orb] in HC. subst v.
replace (0 - bv_unsigned b)%Z with (bv_unsigned a - bv_unsigned b)%Z by lia. finish.
+ zstep. zstep.
eapply evt_eq.
2:{ apply (strncmp_loop (Z.to_nat (n - 1)) 0 a a4); try lia; try assumption. }
unfold mkR. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. repeat f_equal; lia.
Qed.
End Proofs.

#[using="CODE"] Lemma strncmp_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte) (v : Z),
bytes_at segs m (bv_unsigned a0) ls ->
bytes_at segs m (bv_unsigned a1) rs ->
strncmp_model ls rs (bv_unsigned a2) = Some v ->
mem_inv segs m ->
evt segs (strncmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs v m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof. clear - CODE segs base. intros until v. intros LS RS HM MI. apply strncmp_body; assumption. Qed.

End G.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QQLG.Mq8.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope bv_scope.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition strnlen_code (w_8 : Z) : list Z :=
[0xfe010113; 0x00113c23; 0x00813823; 0x00913423; 0x00058413; 0x00050493; 0x00000593; 0x00040613; w_8; 0x00050463; 0x40950433; 0x00040513; 0x01813083; 0x01013403; 0x00813483; 0x02010113; 0x00008067]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_8 : Z).
Variables (joff_8 : bv 21).
Variables (e_memchr : Z).
Hypothesis CODE : code_at segs base (strnlen_code w_8).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 68.
Hypothesis D_8 : decode_any (Z_to_bv 32 w_8) = Some (Jal 1 joff_8, 4%Z).
Hypothesis E_8 : is_ecall (Z_to_bv 32 w_8) = false.
Hypothesis LINK_8 : gw_anch (base + 32 + bv_signed joff_8)%Z (e_memchr + 0)%Z.

Local Definition gw_tbl_0 := tt.

Definition memchr_post : ltac:(gw_rebind_ty (@QQLG.Mq8.memchr_post segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QQLG.Mq8.memchr_post segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@QQLG.Mq8.memchr_post segs) memchr_post gw_tbl_0).

Hypothesis memchr_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQLG.Mq8.gw_all) (@QQLG.Mq8.memchr_spec) e_memchr)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_1))) in exact T).  Arguments memchr_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_list_scope.
#[using="e_memchr CODE BASE4 BASER D_8 E_8 LINK_8 memchr_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Definition strnlen_entry := (base + 0x0)%Z.

Definition strnlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 : word) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
(Z_to_bv 64 (strnlen_res (bv_unsigned a1) buf))
a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp)
/\ bytes_at segs m' (bv_unsigned a0) buf.

#[using="w_8 joff_8 e_memchr CODE BASE4 BASER D_8 E_8 LINK_8 memchr_spec"] Lemma strnlen_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte) (lo : Z),
stk segs m lo (bv_unsigned sp) ->
bytes_at segs m (bv_unsigned a0) buf ->
memchr_ok (bv_unsigned a0) 0 (bv_unsigned a1) buf ->
mem_inv segs m ->
(lo <= bv_unsigned sp - 32)%Z ->
(bv_unsigned a0 + Z.of_nat (length buf) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
(0 < bv_unsigned a0)%Z ->
evt segs (strnlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 buf lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof. clear - w_8 joff_8 e_memchr CODE BASE4 BASER D_8 E_8 LINK_8 memchr_spec segs base.
intros until lo. intros ST BUF OK MI LO SEP A0.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (bytes_at_bound _ _ _ _ BUF) as AB.
assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
carve_frame 32%nat ST.
do 9 zstep.
call memchr_spec.
1:{ exact BUF. }
1:{ rewrite unsigned_lit by lia. exact OK. }
1:{ assumption. }
rewrite unsigned_lit by lia. change (0 mod 256)%Z with 0%Z.
unfold memchr_res.
destruct (find_byte 0 (firstn (Z.to_nat (bv_unsigned a1)) buf)) as [i|] eqn:FB.
- pose proof (find_byte_Some _ _ _ FB) as (Hl & _). rewrite firstn_length in Hl.
zstep. if_cases K; zify_cond K. { exfalso. lia. }
do 7 zstep.
replace (bv_unsigned a0 + Z.of_nat i - bv_unsigned a0)%Z with (strnlen_res (bv_unsigned a1) buf)
by (unfold strnlen_res; rewrite FB; lia).
release_frame FR ST (bv_unsigned sp). finish.
- zstep. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
do 6 zstep.
lazymatch goal with |- evt _ ?Q _ => set (P := Q) end.
replace a1 with (Z_to_bv 64 (strnlen_res (bv_unsigned a1) buf))
by (unfold strnlen_res; rewrite FB; apply Z_to_bv_bv_unsigned).
release_frame FR ST (bv_unsigned sp). finish.
Qed.

End G.
End Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1 Qfw3_c1 G.GwFamMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QlEo_c1.Mq0 QWxq_c1.Mq1 Qfw3_c1.Mq2.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope bv_scope.

Definition sysret_code (w_7 : Z) : list Z :=
[0xfffff5b7; 0x0015859b; 0x02b56663; 0xff010113; 0x00113423; 0x00813023; 0x40a0043b; w_7; 0x00852023; 0xfff00513; 0x00813083; 0x00013403; 0x01010113; 0x00008067]%Z.

Definition errno_loc_code : list Z :=
[0x00020513; 0xf5c50513; 0x00008067]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rerrno_loc_entry : Z).
Variables (w_7 : Z).
Variables (joff_7 : bv 21).
Hypothesis CODE : code_at segs base (sysret_code w_7).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 56.
Hypothesis D_7 : decode_any (Z_to_bv 32 w_7) = Some (Jal 1 joff_7, 4%Z).
Hypothesis E_7 : is_ecall (Z_to_bv 32 w_7) = false.
Hypothesis LINK_7 : gw_anch (base + 28 + bv_signed joff_7)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis CODE_rerrno_loc_entry : code_at segs rerrno_loc_entry errno_loc_code.
Hypothesis AL_rerrno_loc_entry_b4 : gw_b4 rerrno_loc_entry.
Hypothesis RNG_rerrno_loc_entry_code : gw_br rerrno_loc_entry 12.
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
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis AL_rerrno_loc_entry : gw_al rerrno_loc_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.

#[using="rerrno_loc_entry RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_7 E_7 LINK_7 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT LAY_ref_reserved AL_rerrno_loc_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay"] Lemma gw_all : True. Proof. exact I. Qed.

Definition sysret_entry := (base + 0x0)%Z.

Definition sysret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r errv : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
/\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp)
/\ rw_cells segs m' (errno_addr tp) [C4 (sysret_errno r errv)].

#[using="rerrno_loc_entry w_7 joff_7 CODE BASE4 BASER D_7 E_7 LINK_7 CODE_rerrno_loc_entry"] Lemma sysret_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(errv : word) (lo : Z),
stk segs m lo (bv_unsigned sp) ->
rw_cells segs m (errno_addr tp) [C4 errv] ->
mem_inv segs m ->
(lo <= bv_unsigned sp - 16)%Z ->
(errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
(164 <= bv_unsigned tp)%Z ->
evt segs (sysret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 errv F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof. clear - rerrno_loc_entry w_7 joff_7 CODE BASE4 BASER D_7 E_7 LINK_7 CODE_rerrno_loc_entry segs base.
intros until lo. intros ST ERR MI LO SEP TP.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
pose proof (wmono_refl segs m) as WM.
do 3 step. if_cases Hc; zify_cond Hc.
-
step. unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_small a0) by lia. finish.
- carve_frame 16%nat ST.
do 14 step.
pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
rewrite negw_errno in ERR by lia.
unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_big a0) by lia.
release_frame FR ST (bv_unsigned sp).
finish.
Qed.

End G.
End Mq7.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA QEpW QZDE QbrW Ql2m QUZl Q7S0 QGeV Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QsjA QEpW QZDE QbrW QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.

Import QZAi.Mq1 Ql2m.Mq3 QZAi.Mq2 QUZl Q7S0.Mq0 Q7S0.Mq1 QGeV.
Import Q6q3.
Import ListNotations.
Import QlEo_c1.Mq0.Exc.
Open Scope Z_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Section G.
Variables (segs : list Segment).

#[using="Type"] Lemma gw_all : True. Proof. exact I. Qed.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rimpl_vis_unfold' {R} n (k : resp -> itree node R) Q ms :
impl segs (at_node segs) (Vis n k) Q ms = evt segs (fun ms1 => at_node segs n ms1 /\ forall rsp, impl segs (at_node segs) (k rsp) Q (nret ms1 rsp)) ms.
Proof. clear - segs R n k Q ms RC__. reflexivity. Qed.

#[using="Type"] Lemma impl_bind_inv' : forall {A B} (t : itree node A) (f : A -> itree node B) Q ms,
impl segs (at_node segs) (QlEo_c1.Mq0.bind _ t f) Q ms ->
impl segs (at_node segs) t (fun r ms' => impl segs (at_node segs) (f r) Q ms') ms.
Proof. clear - segs RC__.
induction t as [r|n k IH]; intros f Q ms H; cbn [QlEo_c1.Mq0.bind] in H.
- cbn. apply evt_done. exact H.
- rewrite rimpl_vis_unfold' in H. rewrite rimpl_vis_unfold'. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp. apply IH. apply Hk.
Qed.

#[using="Type"] Lemma implM_bind_inv' : forall {St A B} (m : Ql2m.Mq3.M St A) (f : A -> Ql2m.Mq3.M St B) s Q ms,
implM segs (mbind m f) s Q ms ->
implM segs m s (fun a s' ms' => implM segs (f a) s' Q ms') ms.
Proof. clear - segs RC__.
intros St A B m f s Q ms H. unfold implM, mbind, ebind in *. apply impl_bind_inv' in H.
eapply impl_mono; [exact H|]. intros [|[a s']] ms'; cbn; auto.
Qed.

#[using="Type"] Lemma implM_ret_inv' : forall {St A} (a : A) (s : St) Q ms,
implM segs (mret a) s Q ms -> evt segs (Q a s) ms.
Proof. clear - segs RC__. intros St A a s Q ms H. exact H. Qed.

#[using="Type"] Lemma implM_upd_inv' : forall {St} (f : St -> St) s Q ms,
implM segs (mupd f) s Q ms -> evt segs (Q tt (f s)) ms.
Proof. clear - segs RC__. intros St f s Q ms H. exact H. Qed.

#[using="Type"] Lemma implM_get_inv' : forall {St} (s : St) Q ms,
implM segs mget s Q ms -> evt segs (Q s s) ms.
Proof. clear - segs RC__. intros St s Q ms H. exact H. Qed.

#[using="Type"] Lemma implM_msys_inv {St A} n (dec : resp -> option A) (s : St) Q ms :
implM segs (msys n dec) s Q ms ->
evt segs (fun ms1 => at_node segs n ms1 /\ forall rsp a, dec rsp = Some a -> evt segs (Q a s) (nret ms1 rsp)) ms.
Proof. clear - segs St A n dec s Q ms RC__.
intros H. unfold implM, msys in H. unfold enode in H. rewrite rimpl_vis_unfold' in H.
eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp a E. specialize (Hk rsp). rewrite E in Hk. cbn in Hk. exact Hk.
Qed.

#[using="Type"] Lemma ev_step_set_m e : forall s cs Q ms,
implM segs (ev_step e) (set_m cs s) Q ms ->
implM segs (ev_step e) s (fun z s2 ms2 => Q z (set_m cs s2) ms2) ms.
Proof. clear - segs e RC__.
intros s cs Q ms H.

assert (SYS : forall {A} n (dec : resp -> option A) (f : A -> Ql2m.Mq3.M PState Z) (s1 : PState),
implM segs (mbind (msys n dec) f) (set_m cs s1) Q ms ->
(forall a ms', implM segs (f a) (set_m cs s1) Q ms' -> implM segs (f a) s1 (fun z s2 ms2 => Q z (set_m cs s2) ms2) ms') ->
implM segs (mbind (msys n dec) f) s1 (fun z s2 ms2 => Q z (set_m cs s2) ms2) ms).
{ intros A n dec f s1 H1 K. apply implM_bind_inv' in H1.
eapply (implM_bind segs _ _ _ (fun a s' ms' => s' = s1 /\ implM segs (f a) (set_m cs s') Q ms')).
{ apply implM_sys. eapply evt_mono; [exact (implM_msys_inv _ _ _ _ _ H1)|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp a E. eapply evt_mono; [exact (Hk rsp a E)|]. cbv beta. intros ms' H2. split; [reflexivity| exact H2]. }
cbv beta. intros a s' ms' [-> H2]. apply K. exact H2. }
assert (GETB : forall {A} (f : PState -> Ql2m.Mq3.M PState A) st Q' ms', implM segs (mbind mget f) st Q' ms' <-> implM segs (f st) st Q' ms').
{ intros. split; intros X; exact X. }
destruct e as [req|addr len prot flags|addr len|addr len prot|pp c h|w|old ol nl fl]; cbn [ev_step] in H |- *.
- destruct (req =? 0).
+ eapply SYS; [exact H|]. intros a ms' H2. exact H2.
+ apply (proj1 (GETB _ _ _ _ _)) in H. apply (proj2 (GETB _ _ _ _ _)). cbn [ps_brk set_m] in H |- *.
eapply SYS; [exact H|]. intros [|] ms' H2; exact H2.
- destruct (negb (Z.land flags MAP_FIXED_Z =? 0)); [|destruct (prot =? 0)].
all: eapply SYS; [exact H|]; intros a ms' H2; exact H2.
- eapply SYS; [exact H|]. intros a ms' H2. exact H2.
- eapply SYS; [exact H|]. intros a ms' H2. exact H2.
- apply implM_unr.
- apply implM_unr.
- eapply SYS; [exact H|]. intros a ms' H2. exact H2.
Qed.

#[using="Type"] Lemma implM_membed_set_m {R} (t : QUZl.M R) : forall s cs Q ms,
implM segs (membed t) (set_m cs s) Q ms ->
implM segs (membed t) s (fun x s2 ms2 => Q x (set_m cs s2) ms2) ms.
Proof. clear - segs R t RC__.
induction t as [r|e k IH]; intros s cs Q ms H; cbn [membed] in H |- *.
- exact H.
- apply implM_bind_inv' in H. eapply implM_bind.
{ apply ev_step_set_m. exact H. }
cbv beta. intros z s2 ms2 H2. apply IH. exact H2.
Qed.

#[using="Type"] Lemma set_m_set_m cs cs' s : set_m cs (set_m cs' s) = set_m cs s.
Proof. clear - cs cs' s RC__. reflexivity. Qed.

End RC__1.

End G.
End Mq8.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQLG.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
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

Definition multf3_core1 := QQLG.multf3_core1 segs base CODE BASE4 BASER.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= g_step_fast.
Local Ltac zsimp ::= zsimp_fast.

Definition multf3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' (bv_unsigned sp - 80) (bv_unsigned sp).

Definition saved9 (s8 s7 s6 s5 s4 s3 s2 s1 s0 : word) (j : list byte) : list cell :=
[CB 8 j; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0].

#[using="CODE BASE4 BASER"] Lemma land_M32_small : forall x, 0 <= x < 4294967296 -> Z.land x 4294967295 = x.
Proof. intros. rewrite landM32_mod. apply Z.mod_small. lia. Qed.
#[using="CODE BASE4 BASER"] Lemma land_ones_r : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros. rewrite land_W64. apply Z.mod_small. lia. Qed.
#[using="CODE BASE4 BASER"] Lemma land_ones_l : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 x = x.
Proof. intros. rewrite Z.land_comm. apply land_ones_r. assumption. Qed.

#[using="CODE BASE4 BASER"] Lemma sra63_neg : forall x, -2^63 <= x < 0 -> Z.shiftr (bv_signed (Z_to_bv 64 x)) 63 = -1.
Proof.
intros x Hx. rewrite Z_to_bv_signed, bv_swrap_small.
2:{ unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64 `div` 2) with (2^63). lia. }
rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia.
Qed.
#[using="CODE BASE4 BASER"] Lemma sra63_negw : forall x, 2^63 <= x < 2^64 -> Z.shiftr (bv_signed (Z_to_bv 64 x)) 63 = -1.
Proof.
intros x Hx. replace (Z_to_bv 64 x) with (Z_to_bv 64 (x - 2^64)) by (apply Z_to_bv_eqm; Z.div_mod_to_equations; lia).
apply sra63_neg. lia.
Qed.
#[using="CODE BASE4 BASER"] Lemma sra63_pos : forall x, 0 <= x < 2^63 -> Z.shiftr (bv_signed (Z_to_bv 64 x)) 63 = 0.
Proof.
intros x Hx. rewrite Z_to_bv_signed, bv_swrap_small.
2:{ unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64 `div` 2) with (2^63). lia. }
rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia.
Qed.
#[using="CODE BASE4 BASER"] Lemma lxor_b2z_1 : forall b, Z.lxor (Z.b2z b) 1 = Z.b2z (negb b).
Proof. intros [|]; reflexivity. Qed.

Ltac zzr := zsimp; rewrite ?Z.add_0_r;
try rewrite !land_sub_neg by alia;
try rewrite !land_M32_small by alia;
try rewrite !sra63_neg by alia; try rewrite !sra63_pos by alia;
try rewrite !land_ones_l by (first [zrange | alia]);
rewrite ?Z.land_0_l.
Ltac zrstep := step; zzr.

#[using="CODE BASE4 BASER"] Lemma mfr_normal : forall s pe hh hl lh ll,
0 < pe <= 131072 -> 0 <= hl < 2^64 ->
mul_finish s pe hh hl lh ll =
mul_round s (Z.lor (Z.land (pe ≪ 48) 18446744073709551615) (Z.land hh 281474976710655)) (Z.land hl 18446744073709551615) lh ll.
Proof.
intros * Hpe Hhl. rewrite (land_ones_r hl) by lia. apply mf_normal. lia.
Qed.

#[using="CODE BASE4 BASER"] Lemma mfr_caseA : forall s pe hh hl lh ll,
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

#[using="CODE BASE4 BASER"] Lemma mfr_caseB : forall s pe hh hl lh ll,
pe = -63 -> 0 <= hh < 2^64 -> 0 <= hl < 2^64 -> 0 <= lh < 2^64 -> 0 <= ll < 2^64 ->
mul_finish s pe hh hl lh ll =
mul_round s 0 (hh ≫ Z.land (1 - pe) 63)
(Z.lor (Z.land (hl ≪ Z.land (pe + 127) 63) 18446744073709551615) 0)
(Z.lor (Z.lor 0 (Z.land (lh ≫ Z.land (1 - pe) 63) 18446744073709551615))
(Z.b2z (0 <? Z.lor 0 (Z.land (ll ≪ Z.land (pe + 127) 63) 18446744073709551615)))).
Proof. intros * Hpe Hhh Hhl Hlh Hll. mf_pure. Qed.

#[using="CODE BASE4 BASER"] Lemma mfr_caseC : forall s pe hh hl lh ll,
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

#[using="CODE BASE4 BASER"] Lemma Lepi : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w0 w1
y5 y6 y7 y8 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv segs m1 ->
munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stk segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
rw_cells segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
(4096 <= bv_unsigned sp)%Z ->
Z_to_bv 64 (lo64 R) = w0 -> Z_to_bv 64 (hi64 R) = w1 ->
evt segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR ra spw gp tp y5 y6 y7 y8 y9 w0 w1 y12 y13 y14 y15 y16 y17
y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
F (Z_to_bv 64 (base + 0x59c)) fc None m1 (seg_rom segs)).
Proof.
intros until R. intros MI MU WM ST FR SPLO H0 H1. unfold saved9 in FR.
pose_word_ranges.
do 11 zstep.
release_frame FR ST (bv_unsigned sp).
rewrite <- H0, <- H1. finish.
Qed.

Ltac res_words :=
rewrite ?lo64_mk128, ?hi64_mk128 by zrange; weq.

#[using="CODE BASE4 BASER"] Lemma Linf : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (sgn : Z)
y5 y6 y7 y8 y9 y10 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv segs m1 ->
munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stk segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
rw_cells segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
(4096 <= bv_unsigned sp)%Z ->
(0 <= sgn < 2^64)%Z ->
R = mk128 (Z.lor sgn 9223090561878065152) 0 ->
evt segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR ra spw gp tp y5 y6 y7 y8 y9 y10 (Z_to_bv 64 sgn) y12 y13 y14 y15 y16 y17
y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
F (Z_to_bv 64 (base + 0x2bc)) fc None m1 (seg_rom segs)).
Proof.
intros until R. intros MI MU WM ST FR SPLO Rs HR. subst R.
do 5 zstep. join Lepi; res_words.
Qed.

#[using="CODE BASE4 BASER"] Lemma Lup : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (rl rh1 : Z)
y5 y6 y7 y8 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv segs m1 ->
munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stk segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
rw_cells segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
(4096 <= bv_unsigned sp)%Z ->
(0 <= rl < 2^64)%Z -> (0 <= rh1 < 2^64)%Z ->
R = mk128 (Z.land (rh1 + Z.b2z (Z.land (rl + 1) 18446744073709551615 =? 0)) 18446744073709551615) (Z.land (rl + 1) 18446744073709551615) ->
evt segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR ra spw gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 rl) (Z_to_bv 64 rh1) y12 y13 y14 y15 y16 y17
y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
F (Z_to_bv 64 (base + 0x590)) fc None m1 (seg_rom segs)).
Proof.
intros until R. intros MI MU WM ST FR SPLO R0 R1 HR. subst R.
do 3 zstep. join Lepi; res_words.
Qed.

#[using="CODE BASE4 BASER"] Lemma Ltie : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (rl rh1 lh2 ll2 : Z)
y5 y6 y7 y8 y9 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv segs m1 ->
munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stk segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
rw_cells segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
(4096 <= bv_unsigned sp)%Z ->
(0 <= rl < 2^64)%Z -> (0 <= rh1 < 2^64)%Z -> (0 <= lh2 < 2^64)%Z -> (0 <= ll2 < 2^64)%Z ->
R = (if Z.lor ll2 (Z.lxor lh2 9223372036854775808) =? 0
then mk128 (Z.land (rh1 + Z.b2z (Z.land (rl + Z.land rl 1) 18446744073709551615 <? rl)) 18446744073709551615)
(Z.land (rl + Z.land rl 1) 18446744073709551615)
else mk128 rh1 rl) ->
evt segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR ra spw gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 rl) (Z_to_bv 64 rh1) (Z_to_bv 64 ll2) (Z_to_bv 64 lh2) y14 y15 y16 y17
y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
F (Z_to_bv 64 (base + 0x300)) fc None m1 (seg_rom segs)).
Proof.
intros until R. intros MI MU WM ST FR SPLO R0 R1 R2 R3 HR.
do 4 zstep. zstep. if_cases K; zify_cond K.
-  decide_head HR. subst R. join Lepi; res_words.
- decide_head HR. subst R. do 7 zstep. join Lepi; res_words.
Qed.

#[using="CODE BASE4 BASER"] Lemma Lrnd2 : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (rl rh lh2 ll2 sgn : Z)
y5 y6 y7 y8 y9 y16 y17 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv segs m1 ->
munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stk segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
rw_cells segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
(4096 <= bv_unsigned sp)%Z ->
(0 <= rl < 2^64)%Z -> (0 <= rh < 2^64)%Z -> (0 <= lh2 < 2^64)%Z -> (0 <= ll2 < 2^64)%Z -> (0 <= sgn < 2^64)%Z ->
lh2 <> 9223372036854775808 ->
R = mul_round sgn rh rl lh2 ll2 ->
evt segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR ra spw gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 rl) (Z_to_bv 64 sgn) (Z_to_bv 64 ll2) (Z_to_bv 64 lh2) (Z_to_bv 64 rh)
(Z_to_bv 64 9223372036854775808) y16 y17
y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
F (Z_to_bv 64 (base + 0x2f0)) fc None m1 (seg_rom segs)).
Proof.
intros until R. intros MI MU WM ST FR SPLO R0 R1 R2 R3 R4 Kh HR.
unfold mul_round in HR. model_in HR. decide_head HR.
do 2 zstep. rewrite lxor_b2z_1. zstep.
zstep. if_cases K; zify_cond K; rewrite zb_lxor_sign in K by lia.
-  decide_head HR. join Lup.
- decide_head HR. join Ltie.
Qed.

#[using="CODE BASE4 BASER"] Lemma Lhalf : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (rl rh lh2 ll2 sgn : Z)
y5 y6 y7 y8 y9 y16 y17 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv segs m1 ->
munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stk segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
rw_cells segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
(4096 <= bv_unsigned sp)%Z ->
(0 <= rl < 2^64)%Z -> (0 <= rh < 2^64)%Z -> (0 <= lh2 < 2^64)%Z -> (0 <= ll2 < 2^64)%Z -> (0 <= sgn < 2^64)%Z ->
lh2 = 9223372036854775808 ->
R = mul_round sgn rh rl lh2 ll2 ->
evt segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR ra spw gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 rl) (Z_to_bv 64 sgn) (Z_to_bv 64 ll2) (Z_to_bv 64 lh2) (Z_to_bv 64 rh)
(Z_to_bv 64 9223372036854775808) y16 y17
y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
F (Z_to_bv 64 (base + 0x584)) fc None m1 (seg_rom segs)).
Proof.
intros until R. intros MI MU WM ST FR SPLO R0 R1 R2 R3 R4 Kh HR.
unfold mul_round in HR. model_in HR. decide_head HR.
do 2 zstep.
zstep. if_cases K; zify_cond K.
-  decide_head HR. join Ltie.
- decide_head HR. join Lup.
Qed.

#[using="CODE BASE4 BASER"] Lemma Lfin : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (pe hh hl lh ll sgn : Z)
y6 y8 y9 y10 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv segs m1 ->
munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stk segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
rw_cells segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
(4096 <= bv_unsigned sp)%Z ->
(-131072 <= pe < 32767)%Z -> (0 <= hh < 2^64)%Z -> (0 <= hl < 2^64)%Z -> (0 <= lh < 2^64)%Z -> (0 <= ll < 2^64)%Z ->
(0 <= sgn < 2^64)%Z ->
R = mul_finish sgn pe hh hl lh ll ->
evt segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR ra spw gp tp (Z_to_bv 64 pe) y6 (Z_to_bv 64 (-16383)) y8 y9
y10 (Z_to_bv 64 sgn) (Z_to_bv 64 ll) (Z_to_bv 64 lh) (Z_to_bv 64 hh)
(Z_to_bv 64 18446744073709551615) (Z_to_bv 64 281474976710655) (Z_to_bv 64 hl)
y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
F (Z_to_bv 64 (base + 0x2d0)) fc None m1 (seg_rom segs)).
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

#[using="CODE BASE4 BASER"] Lemma Ltail : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (es hh hl lh ll scale sgn : Z)
y6 y8 y9 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv segs m1 ->
munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stk segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
rw_cells segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
(4096 <= bv_unsigned sp)%Z ->
(0 <= es < 65536)%Z -> (0 <= hh < 2^64)%Z -> (0 <= hl < 2^64)%Z -> (0 <= lh < 2^64)%Z -> (0 <= ll < 2^64)%Z ->
(-1024 <= scale <= 1024)%Z -> (0 <= sgn < 2^64)%Z ->
R = MC_tail sgn es hh hl lh ll scale ->
evt segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR ra spw gp tp (Z_to_bv 64 es) y6 (Z_to_bv 64 (-16383)) y8 y9
(Z_to_bv 64 scale) (Z_to_bv 64 sgn) (Z_to_bv 64 ll) (Z_to_bv 64 lh) (Z_to_bv 64 hh)
(Z_to_bv 64 18446744073709551615) (Z_to_bv 64 281474976710655) (Z_to_bv 64 hl)
y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
F (Z_to_bv 64 (base + 0x20c)) fc None m1 (seg_rom segs)).
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

#[using="CODE BASE4 BASER"] Lemma multf3_core : forall ra sp gp tp w1 w2 s0 s1 (scale sgn ea eb : Z) w4 a3 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 t5 t6
y8 y9 y18 y19 y20 y21 y22 y23 y24 y28
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
y28 = Z_to_bv 64 (Z.shiftr (bv_unsigned w1) 32) ->
mem_inv segs m1 ->
munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stk segs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
rw_cells segs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
(4096 <= bv_unsigned sp)%Z ->
(0 <= ea < 32768)%Z -> (0 <= eb < 32768)%Z -> (-1024 <= scale <= 1024)%Z -> (0 <= sgn < 2^64)%Z ->
R = mul_core sgn ea eb (bv_unsigned w1) (bv_unsigned w3) (bv_unsigned w2) (bv_unsigned w4) scale ->
evt segs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp (Z_to_bv 64 eb) w1 w2 y8 y9 (Z_to_bv 64 scale) (Z_to_bv 64 sgn) w4 a3 a4
(Z_to_bv 64 18446744073709551615) (Z_to_bv 64 281474976710655) (Z_to_bv 64 ea)
y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 w3 t5 t6)
F (Z_to_bv 64 (base + 0x80)) fc None m1 (seg_rom segs)).
Proof.
intros until R. intros Hy28 MI MU WM ST FR SPLO Ra Rb Rsc Rsg HR. subst y28 R.
eapply evt_cut. { eapply multf3_core1; eauto. }
intros ms' P.
destruct P as (es & hh & hl & lh & ll & y5' & t1 & t2' & x8 & x9 & a5' & a6' & s2' & s3' & s4' & s5' & s6' & s7' & s8' & t3 & t4 & t5' & t6'
& EQ & Res & Rhh & Rhl & Rlh & Rll & E5 & Ea5 & Ea6 & Et2 & E).
subst ms' y5' a5' a6' t2'. rewrite EQ.
eapply Ltail; eauto.
Qed.

End G.
