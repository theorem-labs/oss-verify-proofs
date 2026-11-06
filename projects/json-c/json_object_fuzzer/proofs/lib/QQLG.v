(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1 Q2qa QVbl QZAa Lib.CodeAt Lib.StepGen Lib.StepGenSF Lib.GwCallee.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QnDM_c1 Q2qa.
Import QVbl.Mq0.

Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope bv_scope.

Import QZAa.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenSF OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition addtf3_code : list Z :=
[0xfd010113; 0x02113423; 0x02813023; 0x00913c23; 0x01213823; 0x01313423; 0x01413023; 0x00068413; 0x00060493; 0xfff00713; 0x00175713; 0x00e5f6b3; 0xf8001637; 0x02461613; 0x00068c63; 0x00c687b3; 0x00c7b7b3; 0x00e47733; 0x00078a63; 0x07c0006f; 0x00153793; 0x00e47733; 0x06079863; 0x00c70633; 0xf80017b7; 0x02479793; 0x00f60863; 0x00c7b633; 0x00061863; 0x0540006f; 0x00903633; 0x04060663; 0xfff00613; 0x0ad70c63; 0x00e6b733; 0x01065693; 0x0a070c63; 0x00050813; 0x00058313; 0x00048513; 0x00040713; 0x00141793; 0x00159893; 0x0317d793; 0x0318d293; 0x00d478b3; 0x0a078a63; 0x00d37333; 0x2e029463; 0x1e40006f; 0x07fff637; 0x02461613; 0x16c68a63; 0x00c6b633; 0x16060a63; 0x07fff637; 0x02461613; 0x16c70e63; 0x00c73633; 0x16060e63; 0x07fff637; 0x02461613; 0x00c6c7b3; 0x00f567b3; 0x50079263; 0x00a4c4b3; 0x00b44433; 0xfff00613; 0x03f61613; 0x00c44633; 0x00c4e4b3; 0x0014b613; 0x00049663; 0x0ffff5b7; 0x02359593; 0xfff60613; 0x00a674b3; 0x00058413; 0x64c0006f; 0x00953733; 0x01065693; 0xf40718e3; 0x00048813; 0x00040313; 0x00058713; 0x00159793; 0x00141893; 0x0317d793; 0x0318d293; 0x00d5f8b3; 0xf4079ae3; 0x0018b793; 0x00050393; 0x00088463; 0x00088393; 0x0013de13; 0x55555eb7; 0x33333f37; 0x0f0f1fb7; 0x01c3e3b3; 0x555e8e1b; 0x333f0e9b; 0xf0ff8f1b; 0x0023df93; 0x01f3e3b3; 0x020e1f93; 0x01fe0e33; 0x020e9f93; 0x01fe8eb3; 0x020f1f93; 0x01ff0f33; 0x0043df93; 0x01f3e3b3; 0x0083df93; 0x01f3e3b3; 0x0103df93; 0x01f3e3b3; 0x0203df93; 0x01f3e3b3; 0xfff3c393; 0x0013df93; 0x01cffe33; 0x00679793; 0x41c383b3; 0x01d3fe33; 0x0023d393; 0x01d3f3b3; 0x01010eb7; 0x101e8e9b; 0x007e03b3; 0x0043de13; 0x01c383b3; 0x020e9e13; 0x01e3f3b3; 0x01ce8e33; 0x03c383b3; 0x0383d393; 0x00f3e7b3; 0xff178393; 0x02039e13; 0x020e5e93; 0xfc0e8e13; 0x040e4063; 0x01d518b3; 0x04c0006f; 0x00153613; 0xe8061ae3; 0x00100613; 0x02f61613; 0x00c5e433; 0x00050493; 0x5280006f; 0x0014b613; 0xe80616e3; 0x00100513; 0x02f51513; 0x00a46433; 0x5100006f; 0x007898b3; 0xfffece93; 0x00155f13; 0x01df5eb3; 0x01d8e8b3; 0x00751533; 0x43fe5393; 0x01000e13; 0x00a3f533; 0x40fe07b3; 0x00d37333; 0x10029263; 0x00133293; 0x00080393; 0x00030463; 0x00030393; 0x0013de13; 0x55555eb7; 0x33333f37; 0x0f0f1fb7; 0x01c3e3b3; 0x555e8e1b; 0x333f0e9b; 0xf0ff8f1b; 0x0023df93; 0x01f3e3b3; 0x020e1f93; 0x01fe0e33; 0x020e9f93; 0x01fe8eb3; 0x020f1f93; 0x01ff0f33; 0x0043df93; 0x01f3e3b3; 0x0083df93; 0x01f3e3b3; 0x0103df93; 0x01f3e3b3; 0x0203df93; 0x01f3e3b3; 0xfff3c393; 0x0013df93; 0x01cffe33; 0x00629293; 0x41c383b3; 0x01d3fe33; 0x0023d393; 0x01d3f3b3; 0x01010eb7; 0x101e8e9b; 0x007e03b3; 0x0043de13; 0x01c383b3; 0x020e9e13; 0x01e3f3b3; 0x01ce8e33; 0x03c383b3; 0x0383d393; 0x0053e2b3; 0xff128393; 0x02039e13; 0x020e5e93; 0xfc0e8e13; 0x000e4663; 0x01d81333; 0x0180006f; 0x00731333; 0xfffece93; 0x00185f13; 0x01df5eb3; 0x01d36333; 0x00781833; 0x43fe5393; 0x01000e13; 0x0103f833; 0x405e02b3; 0x00b445b3; 0x03d55e13; 0x00389893; 0x00100393; 0x03d85e93; 0x00331f13; 0x01c8e8b3; 0x03339313; 0x00381e13; 0x006ee833; 0x010f6833; 0x00579c63; 0x000e0393; 0x00351293; 0x0068e533; 0x1c05d263; 0x0440006f; 0x405782b3; 0x07f00e93; 0x025ee463; 0x08000393; 0x405383bb; 0x02039393; 0x0203df13; 0xfc0f0393; 0x40500ebb; 0x1203c463; 0x01ee1f33; 0x1340006f; 0x00000813; 0x00351293; 0x0068e533; 0x1805d063; 0x0072c5b3; 0x010548b3; 0x0115e5b3; 0x00059863; 0x00000493; 0x00000413; 0x3400006f; 0x0072b5b3; 0x41050533; 0x40b50533; 0x03355813; 0x407285b3; 0x18081063; 0x00153813; 0x00058893; 0x00050463; 0x00050893; 0x0018d293; 0x55555337; 0x333333b7; 0x0f0f1e37; 0x0058e8b3; 0x5553029b; 0x3333831b; 0xf0fe039b; 0x0028de13; 0x01c8e8b3; 0x02029e13; 0x01c282b3; 0x02031e13; 0x01c30333; 0x02039e13; 0x01c383b3; 0x0048de13; 0x01c8e8b3; 0x0088de13; 0x01c8e8b3; 0x0108de13; 0x01c8e8b3; 0x0208de13; 0x01c8e8b3; 0xfff8c893; 0x0018de13; 0x005e72b3; 0x00681813; 0x405888b3; 0x0068f2b3; 0x0028d893; 0x0068f8b3; 0x01010337; 0x1013031b; 0x011288b3; 0x0048d293; 0x005888b3; 0x02031293; 0x0078f8b3; 0x005302b3; 0x025888b3; 0x0388d893; 0x0108e833; 0xff480813; 0x02081893; 0x0208d293; 0xfc028893; 0x1008c063; 0x00559533; 0x10c0006f; 0x01d81fb3; 0xffff4f13; 0x001e5413; 0x01e45f33; 0x01efef33; 0x01de1eb3; 0x43f3d393; 0x01d3f3b3; 0x02029e93; 0x020edf93; 0x01e3e3b3; 0xfc0f8e93; 0x007033b3; 0x000ec663; 0x01f85e33; 0x0180006f; 0x005e5e33; 0x00181f13; 0xffffcf93; 0x01ff1f33; 0x01ee6e33; 0x00585833; 0x43fed293; 0x0102f833; 0x007e63b3; 0x00351293; 0x0068e533; 0xe805c4e3; 0x005385b3; 0x0075b8b3; 0x00a80533; 0x01150533; 0x00b51813; 0x02085063; 0x0013f813; 0x0015d593; 0x03f51893; 0x00155513; 0x0105e5b3; 0x0115e5b3; 0x00178793; 0x03f75713; 0x00008837; 0xfff8081b; 0x03f71913; 0x0707cc63; 0x00000493; 0x07fff537; 0x02451513; 0x00a96433; 0x1840006f; 0x00c74633; 0x00c4e633; 0x16060c63; 0x00d56633; 0x1a060263; 0x00e4e633; 0xa60612e3; 0x00050493; 0x00058413; 0x15c0006f; 0x01051533; 0xfff2c293; 0x0015d313; 0x005352b3; 0x00556533; 0x010595b3; 0x43f8d893; 0x00b8f5b3; 0x410787b3; 0x03f75713; 0x00008837; 0xfff8081b; 0x03f71913; 0xf907d8e3; 0x08f04a63; 0x00100713; 0x04000813; 0x40f70733; 0x40e008bb; 0x40e80833; 0x011597b3; 0x00084663; 0x00078893; 0x0200006f; 0x08000293; 0x011518b3; 0x40e282bb; 0xfff2c293; 0x0015d313; 0x005352b3; 0x0058e8b3; 0x43f85293; 0x00e55833; 0x02071313; 0x00f2f2b3; 0x02035793; 0x0112e8b3; 0xfc078313; 0x011038b3; 0x43f35293; 0x00034663; 0x00f555b3; 0x0180006f; 0x00e5d5b3; 0xfff7c713; 0x00151513; 0x00e51533; 0x00a5e5b3; 0x00000793; 0x0102f533; 0x0115e5b3; 0x0075f993; 0x0035d593; 0x03d51713; 0x00355513; 0x03079793; 0x00e5ea33; 0x00d57533; 0x0127e433; 0x00ca74b3; 0x00a46433; 0x0ac000ef; 0x00200593; 0x02b50c63; 0x00100593; 0x02b50463; 0x04051463; 0x00400513; 0x06a99863; 0x001a7513; 0x00a48533; 0x009535b3; 0x00b40433; 0x00050493; 0x02c0006f; 0x01203533; 0x0080006f; 0x00193513; 0x013035b3; 0x00b57533; 0x00a48533; 0x009535b3; 0x00b40433; 0x00050493; 0x00098463; 0x07c000ef; 0x00048513; 0x00040593; 0x02813083; 0x02013403; 0x01813483; 0x01013903; 0x00813983; 0x00013a03; 0x03010113; 0x00008067; 0x0059b513; 0x00154513; 0xfb9ff06f; 0x00e4e733; 0xfc0714e3; 0x00a4f4b3; 0x00b47433; 0xfbdff06f]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base addtf3_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 1996.

Hypothesis fe_getround_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq0.fe_getround_spec segs (base + 1996)%Z 0%Z 0%Z) 3%nat in let T := gw_fold_pcs T base (1996)%Z [0; 48]%Z in exact T).
Hypothesis fe_raise_inexact_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq0.fe_raise_inexact_spec segs (base + 1996)%Z 0%Z 0%Z) 3%nat in let T := gw_fold_pcs T base (1996)%Z [0; 48]%Z in exact T).

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= g_step_fast.
Local Ltac zsimp ::= zsimp_fast.

Definition addtf3_entry := (base + 0x0)%Z.

Definition addtf3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc' None m' (seg_rom segs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ frm0 fc'
/\ stk segs m' (bv_unsigned sp - 48) (bv_unsigned sp).

Ltac unfold_sfw := cbv beta delta [add64 sub64 shl64 not64 is_neg64 sra63 lt_s64 eqz64 nez64 zext32 lo64 hi64 wrap64
ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI IMPL3_HI SPEC_K].

Ltac showregs := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in
idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "t3=" x28; idtac "t4=" x29.

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

Lemma add_Lret : forall fcx x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 (lo hi r : Z),
frm0 fcx -> (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z ->
r = mk128 hi lo ->
evt segs (POST r) (ST (base + 0x784) fcx x1 x5 x6 x7 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
Proof using CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec FR MI MU STK WM.
intros until r. intros FRMx Rlo Rhi HR. subst r.
pose proof FR as FR'. pose proof STK as ST'.
do 10 zstep.
release_frame FR' ST' (bv_unsigned sp).
replace (bv_unsigned sp + -48)%Z with (bv_unsigned sp - 48)%Z in ST' by lia.
sf_finish.
Qed.

Lemma add_Lround : forall x1 x5 x6 x7 x8 x9 x14 x16 x17 x19 x20 x28 x29 x30 x31 (SHi SLo aExp signHi r : Z),
(0 <= SHi < 2^64)%Z -> (0 <= SLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z -> (0 <= signHi < 2^64)%Z ->
r = round_mirror SHi SLo aExp signHi ->
evt segs (POST r) (ST (base + 0x6f8) fc x1 x5 x6 x7 x8 x9 (Z_to_bv 64 SHi) (Z_to_bv 64 SLo) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) x14 (Z_to_bv 64 aExp) x16 x17 (Z_to_bv 64 signHi) x19 x20 x28 x29 x30 x31).
Proof using CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec FR FRM MI MU STK WM.
intros until r. intros R1 R2 R3 R4 HR. subst r. unfold round_mirror. unfold_sfw. rewrite ?b2z_Zb2z.
zstep. name_reg 19%Z rgs.
do 5 zstep. name_reg 20%Z resLo0.
do 2 zstep. zstep. showregs. name_reg 9%Z resLo. zstep. name_reg 8%Z resHi.
zstep. call fe_getround_spec. 1-2: assumption.
zstep. zstep. if_cases Kc; zify_cond Kc; [exfalso; clear -Kc; lia|].
zstep. zstep. if_cases Kc2; zify_cond Kc2; [exfalso; clear -Kc2; lia|].
zstep. if_cases Kc3; zify_cond Kc3. { exfalso. clear -Kc3. lia. }
zstep. zstep. if_cases Kt; zify_cond Kt; decide_tests_b.
-
zstep. zstep. rewrite lxor1_b2z. name_reg 10%Z inc. zstep.
zstep. model_reg 10%Z sumLo (Z.land (resLo + inc) W64).
zstep. zstep. model_reg 8%Z resHi2 (Z.land (resHi + Z.b2z (sumLo <? resLo)) W64).
zstep. zstep. if_cases Kz; zify_cond Kz.
+
eapply add_Lret; [exact FRM | zrange | zrange | reflexivity].
+ zstep. call fe_raise_inexact_spec. 1-2: assumption.
eapply add_Lret; [assumption | zrange | zrange | reflexivity].
-
zstep. name_reg 10%Z inc.
zstep. model_reg 10%Z sumLo (Z.land (resLo + inc) W64).
zstep. zstep. model_reg 8%Z resHi2 (Z.land (resHi + Z.b2z (sumLo <? resLo)) W64).
zstep. zstep. zstep. call fe_raise_inexact_spec. 1-2: assumption.
eapply add_Lret; [assumption | zrange | zrange | reflexivity].
Qed.

Lemma add_L704 : forall x1 x6 x7 x8 x9 x10 x14 x15 x19 x20 x28 x29 x30 x31 (signHi hiSh mask4 sticky newLo r : Z),
(0 <= signHi < 2^64)%Z -> (0 <= hiSh < 2^64)%Z -> (0 <= mask4 < 2^64)%Z -> (0 <= sticky < 2^64)%Z -> (0 <= newLo < 2^64)%Z ->
r = denorm_3 signHi hiSh mask4 sticky newLo ->
evt segs (POST r) (ST (base + 0x6ec) fc x1 (Z_to_bv 64 mask4) x6 x7 x8 x9 x10 (Z_to_bv 64 newLo) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) x14 x15 (Z_to_bv 64 hiSh) (Z_to_bv 64 sticky) (Z_to_bv 64 signHi) x19 x20 x28 x29 x30 x31).
Proof using CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec FR FRM MI MU STK WM.
intros until r. intros R1 R2 R3 R4 R5 HR. subst r. unfold denorm_3.
do 3 zstep.
eapply add_Lround; [zrange | zrange | lia | zrange | reflexivity].
Qed.

Lemma add_L6c0 : forall x1 x5 x6 x7 x8 x9 x19 x20 x28 x29 x30 x31 (signHi SHi SLo shift d3 mask3 t outHi r : Z),
(0 <= signHi < 2^64)%Z -> (0 <= SHi < 2^64)%Z -> (0 <= SLo < 2^64)%Z -> (0 <= shift < 2^64)%Z ->
(0 <= d3 < 2^64)%Z -> (0 <= t < 2^64)%Z -> (0 <= outHi < 2^64)%Z ->
(if 9223372036854775808 <=? d3 then 18446744073709551615 else 0)%Z = mask3 ->
r = denorm_2 signHi SHi SLo shift mask3 t outHi ->
evt segs (POST r) (ST (base + 0x6a8) fc x1 x5 x6 x7 x8 x9 (Z_to_bv 64 SHi) (Z_to_bv 64 SLo) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 shift) (Z_to_bv 64 t) (Z_to_bv 64 d3) (Z_to_bv 64 outHi) (Z_to_bv 64 signHi) x19 x20 x28 x29 x30 x31).
Proof using CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec FR FRM MI MU STK WM.
intros until r. intros R1 R2 R3 R4 R5 R6 R7 Hm HR. subst r. unfold denorm_2. unfold_sfw. rewrite ?b2z_Zb2z.
assert (Rm3 : (0 <= mask3 < 2^64)%Z) by (rewrite <- Hm; destruct (Z.leb _ _); lia).
zstep. rewrite (srai63_word d3), Hm by lia.
zstep. name_as_by hiSh (Z.shiftr SHi (Z.land shift 63))
(change (inr64 (Z.shiftr SHi (Z.land shift 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
zstep. zstep. name_reg 5%Z outLo.
zstep. name_reg 15%Z n3.
zstep. name_reg 17%Z lor1. rewrite (zb_negb_eqb0 lor1) by zrange_nonneg.
zstep. model_reg 6%Z d4 (Z.land (n3 - 64) W64).
rewrite (sra63_leb d4) by lia.
zstep. name_reg 17%Z sticky.
zstep. rewrite (srai63_word d4) by lia. name_reg 5%Z mask4.
zstep. if_cases K4; zify_cond K4; decide_tests_b.
-
zstep. name_as_by sr1 (Z.shiftr SLo (Z.land shift 63))
(change (inr64 (Z.shiftr SLo (Z.land shift 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
do 4 zstep. name_reg 11%Z newLo.
eapply add_L704; [zrange | zrange | zrange | zrange | zrange | reflexivity].
- zstep. name_as_by newLo (Z.shiftr SHi (Z.land n3 63))
(change (inr64 (Z.shiftr SHi (Z.land n3 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
zstep. eapply add_L704; [zrange | zrange | zrange | zrange | zrange | reflexivity].
Qed.

Lemma add_LM8 : forall x1 x5 x6 x7 x8 x9 x14 x16 x17 x19 x20 x28 x29 x30 x31 (SHi SLo aExp signHi r : Z),
(0 <= SHi < 2^64)%Z -> (0 <= SLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z -> (0 <= signHi < 2^64)%Z ->
r = add_M8 SHi SLo aExp signHi ->
evt segs (POST r) (ST (base + 0x664) fc x1 x5 x6 x7 x8 x9 (Z_to_bv 64 SHi) (Z_to_bv 64 SLo) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) x14 (Z_to_bv 64 aExp) x16 x17 (Z_to_bv 64 signHi) x19 x20 x28 x29 x30 x31).
Proof using CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec FR FRM MI MU STK WM.
intros until r. intros R1 R2 R3 R4 HR. subst r. unfold add_M8. unfold_sfw.
zstep. if_cases K; rewrite ?bv_lts_lxor in K; zify_cond K; decide_tests_b.
-  eapply add_Lround; [zrange | zrange | zrange | zrange | reflexivity].
-
unfold denorm_mirror. unfold_sfw. rewrite ?b2z_Zb2z.
do 3 zstep. model_reg 14%Z shift (Z.land (1 - aExp) W64).
zstep. rewrite Z_to_bv_swrap32. rewrite (sext32_land64 (0 - shift)).
name_as_by negsh (sext32 (0 - shift)) (apply sext32_range).
zstep. model_reg 16%Z d3 (Z.land (64 - shift) W64).
zstep. model_reg 15%Z t (Z.land (Z.shiftl SLo (Z.land negsh 63)) W64).
zstep. if_cases K3; zify_cond K3; decide_tests_b.
+
zstep. zstep. zstep. rewrite Z_to_bv_swrap32. rewrite (sext32_land64 (128 - shift)).
name_as_by mm (sext32 (128 - shift)) (apply sext32_range).
zstep. zstep. zstep. name_as_by sr0 (Z.shiftr (Z.shiftr SLo 1) (Z.land (Z.lxor mm W64) 63))
(change (inr64 (Z.shiftr (Z.shiftr SLo 1) (Z.land (Z.lxor mm W64) 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
zstep. name_reg 17%Z outHi.
eapply add_L6c0 with (mask3 := 18446744073709551615%Z);
[zrange | zrange | zrange | zrange | zrange | zrange | zrange | decide_tests_b; reflexivity | reflexivity].
+
zstep. zstep.
eapply add_L6c0 with (mask3 := 0%Z);
[zrange | zrange | zrange | zrange | zrange | zrange | zrange | decide_tests_b; reflexivity | reflexivity].
Qed.

Lemma add_LM7 : forall x1 x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x28 x29 x30 x31 (xHi SHi SLo aExp r : Z),
(0 <= xHi < 2^64)%Z -> (0 <= SHi < 2^64)%Z -> (0 <= SLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
r = add_M7 xHi SHi SLo aExp ->
evt segs (POST r) (ST (base + 0x5dc) fc x1 x5 x6 x7 x8 x9 (Z_to_bv 64 SHi) (Z_to_bv 64 SLo) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) x16 x17 x18 x19 x20 x28 x29 x30 x31).
Proof using CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec FR FRM MI MU STK WM.
intros until r. intros R1 R2 R3 R4 HR. subst r. unfold add_M7. unfold_sfw.
do 3 zstep. zstep. model_reg 18%Z signHi (Z.land (Z.shiftl (Z.shiftr xHi 63) 63) W64).
zstep. if_cases K; rewrite ?bv_lts_lxor in K; zify_cond K; decide_tests_b.
-  eapply add_LM8; [zrange | zrange | zrange | zrange | reflexivity].
-
do 5 zstep. eapply add_Lret; [exact FRM | lia | zrange | reflexivity].
Qed.
End Proofs.

End G.
End Mq0.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QnDM_c1.

Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope bv_scope.

Import QZAa.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenSF OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.

Definition extenddftf2_code : list Z :=
[0xe20505d3; 0x00159613; 0x03565613; 0x00c59513; 0x00c55513; 0x02060a63; 0x7ff00693; 0x0ed61863; 0x00455693; 0x03c51513; 0x00008637; 0xfff60613; 0x03f5d593; 0x03061613; 0x03f59593; 0x00d66633; 0x00b665b3; 0x00008067; 0x0e050863; 0x00155613; 0x555556b7; 0x33333737; 0x0f0f17b7; 0x01010837; 0x00c568b3; 0x5556869b; 0x3337071b; 0xf0f7879b; 0x1018081b; 0x0028d293; 0x0058e8b3; 0x02069293; 0x005686b3; 0x02071293; 0x00570733; 0x02079293; 0x005787b3; 0x02081293; 0x00580833; 0x0048d293; 0x0058e8b3; 0x0088d293; 0x0058e8b3; 0x0108d293; 0x0058e8b3; 0x0208d293; 0x0058e8b3; 0xfff8c893; 0x0018d293; 0x00d2f6b3; 0x40d886b3; 0x00e6f8b3; 0x0026d693; 0x00e6f6b3; 0x00d886b3; 0x0046d713; 0x00e686b3; 0x00004737; 0x00f6f6b3; 0x030686b3; 0x0386d693; 0xc0c70713; 0xff168813; 0x03168793; 0x04084863; 0x010518b3; 0x0540006f; 0x00f00693; 0x00a69693; 0x00d60633; 0x00455693; 0x03c51513; 0x03f5d593; 0x03061613; 0x03f59593; 0x00d66633; 0x00b665b3; 0x00008067; 0x03f5d593; 0x03001613; 0x03f59593; 0x00066633; 0x00b665b3; 0x00008067; 0x00e00893; 0x40d888bb; 0x011658b3; 0x40d70633; 0x43f85693; 0x00f51533; 0x00100713; 0x00a6f533; 0x03071713; 0x00e8c6b3; 0x03f5d593; 0x03061613; 0x03f59593; 0x00d66633; 0x00b665b3; 0x00008067]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base extenddftf2_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 400.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= g_step_fast.
Local Ltac zsimp ::= zsimp_fast.

Definition extenddftf2_entry := (base + 0x0)%Z.

Definition extenddftf2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [] m m' /\ wmono segs m m' /\ mem_inv segs m'.

Local Ltac extend_tail shM64 :=
zstep; zstep; rewrite (srai63_word shM64) by lia; decide_tests_b;
do 11 zstep.

#[using="CODE BASE4 BASER"] Lemma extenddftf2_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
mem_inv segs m ->
evt segs (extenddftf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
(f128_of_d (bv_unsigned (reg_get F 10))) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof.
intros until m. intros MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM.
unfold f128_of_d.
cbv beta delta [add64 sub64 shl64 not64 is_neg64 sra63 lo64 hi64 wrap64 b2z ONES64 IMPLICIT_HI INF_HI]. zb_fold_lits.
zstep. remember (reg_get F 10) as dw eqn:Edw.
assert (Rdw : (0 <= bv_unsigned dw < 2^64)%Z) by apply (zr_word dw).
rewrite (land_W64_small (bv_unsigned dw)) by lia.
do 4 zstep. name_reg 12%Z aExp. name_reg 10%Z aSig.
zstep. if_cases K0; zify_cond K0; decide_tests_b.
-
zstep. if_cases K2; zify_cond K2; decide_tests_b.
+  do 6 zstep. sf_finish.
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
+  do 11 zstep. sf_finish.
+  do 10 zstep. sf_finish.
Qed.

End G.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.StepGenX Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QnDM_c1.

Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope bv_scope.

Import QZAa.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.

Definition fixunstfsi_code : list Z :=
[0x00000613; 0x0605c663; 0x00159693; 0x00004737; 0x0316d693; 0xfff7071b; 0x04e6ec63; 0xffffc637; 0xfe16061b; 0x00c68633; 0xfe000713; 0x00e67863; 0xfff00613; 0x0006051b; 0x00008067; 0x01059593; 0x00100613; 0x00004737; 0x0105d793; 0x03061813; 0x06f70613; 0x40d6063b; 0x02061593; 0x0205d593; 0xfc058713; 0x0107e6b3; 0x00074863; 0x00b6d633; 0x0006051b; 0x00008067; 0x00c55533; 0xfff5c593; 0x00169693; 0x00b69633; 0x00c56633; 0x0006051b; 0x00008067]%Z.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_3 := flia_fast.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_4 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_5 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_6 := zsimp_fast.

Lemma lo64_words : forall lo hi, (0 <= lo < 2^64)%Z -> lo64 (lo + 2^64 * hi) = lo.
Proof.
intros lo hi H. unfold lo64. rewrite wrap64_mod.
rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma hi64_words : forall lo hi, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> hi64 (lo + 2^64 * hi) = hi.
Proof.
intros lo hi Hl Hh. unfold hi64. rewrite wrap64_mod, Z.shiftr_div_pow2 by lia.
rewrite Z.mul_comm, Z.div_add, Z.div_small by lia. apply Z.mod_small. lia.
Qed.

Lemma fixunstfsi_a0_split : forall a_lo a_hi,
(0 <= a_lo < 2^64)%Z -> (0 <= a_hi < 2^64)%Z ->
fixunstfsi_a0 (a_lo + 2^64 * a_hi) = sext32 (fixunstfsi_a2 a_hi a_lo).
Proof. intros. unfold fixunstfsi_a0. rewrite lo64_words, hi64_words by assumption. reflexivity. Qed.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base fixunstfsi_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 148.

#[using="CODE BASE4 BASER"] Lemma gw_all : True. Proof. exact I. Qed.

Definition fixunstfsi_entry := (base + 0x0)%Z.

Definition fixunstfsi_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [] m m' /\ wmono segs m m' /\ mem_inv segs m'.

#[using="CODE"] Lemma fixunstfsi_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
mem_inv segs m ->
evt segs (fixunstfsi_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
(fixunstfsi_a0 (bv_unsigned a0 + 2^64 * bv_unsigned a1)) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof. clear - CODE segs base.
intros until m. intros MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM.
pose_word_ranges.
rewrite fixunstfsi_a0_split by lia.
unfold fixunstfsi_a2.
cbv beta delta [add64 sub64 shl64 not64 is_neg64 lo64 hi64 wrap64 b2z ONES64 IMPLICIT_HI]. zb_fold_lits.
do 2 zstep. if_cases K1; zify_cond K1.
-
decide_tests_b. rewrite (sext32_small 0) by lia. zstep. zstep. finish.
- do 3 zstep. name_reg 13%Z e.
assert (He15 : (0 <= e < 2^(64-49))%Z)
by (apply shiftr_bound; [change (inr64 (Z.land (Z.shiftl (bv_unsigned a1) 1) 18446744073709551615)); zrange| lia]).
do 2 zstep. if_cases K2; zify_cond K2.
+
decide_tests_b. rewrite (sext32_small 0) by lia. zstep. zstep. finish.
+ do 5 zstep. if_cases K3; zify_cond K3; decide_tests_b.
*
assert (He : (16383 <= e <= 16414)%Z) by (clear -K2 K3 He15; revert K3; zb_masks; intros K3; mlia).
clear K2 K3.

rewrite (land_W64_small (16495 - e)) by lia. rewrite (sext32_small (16495 - e)) by lia.
rewrite (zext32_small (16495 - e)) by lia. rewrite (land_W64_small (16495 - e - 64)) by lia.
rewrite (shiftr63_small (16495 - e - 64)) by lia. cbn [Z.eqb negb].
rewrite (land63_64_128 (16495 - e)) by lia.
do 7 zstep. rewrite (swrap32_small (16495 - e)) by lia.
do 2 zstep. rewrite (land_M32_small (16495 - e)) by lia.
do 3 zstep. if_cases K4; zify_cond K4.
--
exfalso. clear -K4 He. lia.
-- zstep. rewrite (land63_64_128 (16495 - e)) by lia.
zstep. rewrite ?Z.add_0_r. rewrite Z_to_bv_swrap32.
zstep. finish.
*
do 2 zstep.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (sext32 18446744073709551615)) by (apply Z_to_bv_eqm; vm_compute; reflexivity).
zstep. finish.
Qed.

End G.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QnDM_c1.

Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope bv_scope.

Import QZAa.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenSF OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.

Definition floatsitf_code : list Z :=
[0x0c050263; 0x41f5559b; 0x80000637; 0x555556b7; 0x33333737; 0x00b547b3; 0x00c57633; 0x5556869b; 0x40b787bb; 0x0017d51b; 0x00a7e5b3; 0x0025d81b; 0x0105e5b3; 0x0045d81b; 0x0105e5b3; 0x0085d81b; 0x0105e5b3; 0x0105d81b; 0x0105e5b3; 0xfff5c593; 0x0015d813; 0x00d876b3; 0x0f0f1837; 0x3337071b; 0x40d585b3; 0x00e5f6b3; 0x0025d593; 0x00e5f5b3; 0x01010737; 0x00b685b3; 0x0045d693; 0x00d586b3; 0x07000893; 0xf0f80813; 0x10170713; 0x02061593; 0x0106f633; 0x02e60633; 0x0186561b; 0x01f64693; 0x40d886bb; 0x02079813; 0x02069713; 0x02075713; 0xfc070793; 0x02085813; 0x0007ca63; 0x00e81733; 0x0140006f; 0x00000593; 0x00008067; 0xfff74713; 0x00e55733; 0x00d81533; 0x43f7d793; 0x00100693; 0x00a7f533; 0x000047b7; 0x03069693; 0x01e78793; 0x00d746b3; 0x40c787bb; 0x03079793; 0x00f686b3; 0x00b6e5b3; 0x00008067]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base floatsitf_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 264.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= g_step_fast.
Local Ltac zsimp ::= zsimp_fast.

Definition floatsitf_entry := (base + 0x0)%Z.

Definition floatsitf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [] m m' /\ wmono segs m m' /\ mem_inv segs m'.

Local Ltac sitf_tail nM64 clz :=
zstep; zstep; rewrite (srai63_word nM64) by lia; decide_tests_b;
do 7 zstep; rewrite Z_to_bv_swrap32; rewrite (sext32_land64 (16414 - clz));
name_as_by expW (sext32 (16414 - clz)) (apply sext32_range);
zstep;
match goal with |- context [Z_to_bv 64 (Z.shiftl ?x 48)] =>
model_reg 15%Z expSh (Z.land (Z.shiftl x 48) W64) end;
do 3 zstep.

#[using="CODE BASE4 BASER"] Lemma floatsitf_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (i : Z),
mem_inv segs m ->
bv_unsigned a0 = sext32 i ->
evt segs (floatsitf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_i32 i) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof.
intros until i. intros MI U.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM.
assert (Ra0 : (0 <= bv_unsigned a0 < 2^64)%Z) by apply (zr_word a0).
unfold f128_of_i32. rewrite <- U.
cbv beta delta [add64 sub64 shl64 not64 is_neg64 sra63 lo64 hi64 wrap64 b2z ONES64 IMPLICIT_HI]. zb_fold_lits.
zstep. if_cases K0; zify_cond K0; decide_tests_b.
-  zstep. zstep. sf_finish.
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

End G.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QnDM_c1.

Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope bv_scope.

Import QZAa.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenSF OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.

Definition floatunsitf_code : list Z :=
[0x0a050663; 0x0015559b; 0x55555637; 0x333336b7; 0x00b56733; 0x5556061b; 0x0027579b; 0x00f76733; 0x0047579b; 0x00f76733; 0x0087579b; 0x00f76733; 0x0107579b; 0x00f76733; 0xfff74713; 0x00175793; 0x00c7f633; 0x0f0f17b7; 0x3336869b; 0x40c70733; 0x00d77633; 0x00275713; 0x00d776b3; 0x01010737; 0x02051813; 0xf0f78513; 0x10170713; 0x00d60633; 0x00465693; 0x00d60633; 0x00a67533; 0x02e50533; 0x0185561b; 0x01f64513; 0x07000693; 0x40a6853b; 0x02051793; 0x0207d793; 0xfc078693; 0x02085713; 0x0006ca63; 0x00f715b3; 0x0140006f; 0x00000593; 0x00008067; 0xfff7c793; 0x00f5d5b3; 0x00a71533; 0x43f6d693; 0x00100713; 0x00a6f533; 0x000046b7; 0x03071713; 0x01e68693; 0x00e5c5b3; 0x40c686bb; 0x03069693; 0x00d585b3; 0x00008067]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base floatunsitf_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 236.

#[using="CODE BASE4 BASER"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= g_step_fast.
Local Ltac zsimp ::= zsimp_fast.

Definition floatunsitf_entry := (base + 0x0)%Z.

Definition floatunsitf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [] m m' /\ wmono segs m m' /\ mem_inv segs m'.

Local Ltac unsitf_tail nM64 clz :=
zstep; zstep; rewrite (srai63_word nM64) by lia; decide_tests_b;
do 7 zstep; rewrite Z_to_bv_swrap32; rewrite (sext32_land64 (16414 - clz));
name_as_by expW (sext32 (16414 - clz)) (apply sext32_range);
do 3 zstep.

#[using="CODE"] Lemma floatunsitf_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (u : Z),
mem_inv segs m ->
bv_unsigned a0 = sext32 u ->
evt segs (floatunsitf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_u32 u) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof. clear - CODE segs base.
intros until u. intros MI U.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM.
assert (Ra0 : (0 <= bv_unsigned a0 < 2^64)%Z) by apply (zr_word a0).
unfold f128_of_u32. rewrite <- U.
cbv beta delta [add64 sub64 shl64 not64 is_neg64 sra63 lo64 hi64 wrap64 b2z ONES64 IMPLICIT_HI]. zb_fold_lits.
zstep. if_cases K0; zify_cond K0; decide_tests_b.
-  zstep. zstep. sf_finish.
-
wstep. model_reg_w 11%Z half (srliw (bv_unsigned a0) 1).
do 3 wstep. model_reg 14%Z x1 (Z.lor (bv_unsigned a0) half).
do 3 wstep. model_reg_w 14%Z x2 (Z.lor x1 (srliw x1 2)).
do 2 wstep. model_reg_w 14%Z x3 (Z.lor x2 (srliw x2 4)).
do 2 wstep. model_reg_w 14%Z x4 (Z.lor x3 (srliw x3 8)).
do 2 wstep. model_reg_w 14%Z x5 (Z.lor x4 (srliw x4 16)).
wstep. model_reg 14%Z y (Z.lxor x5 W64).
do 5 wstep. model_reg 14%Z c1 (Z.land (y - Z.land (Z.shiftr y 1) 1431655765) W64).
do 8 wstep. model_reg 12%Z c2 (Z.land (Z.land c1 858993459 + Z.land (Z.shiftr c1 2) 858993459) W64).
do 3 wstep. model_reg 10%Z c3 (Z.land (Z.land (c2 + Z.shiftr c2 4) W64) 252645135).
do 2 wstep. model_reg_w 12%Z c4 (srliw (Z.land (c3 * 16843009) W64) 24).
replace (Z_to_bv 64 c4) with (Z_to_bv 64 (clz32_mirror (bv_unsigned a0))) by (f_equal; model_eval; reflexivity).
name_as_by clz (clz32_mirror (bv_unsigned a0)) (apply clz32_mirror_range).

zstep. model_reg 10%Z e (Z.lxor clz 31).
zstep. zstep. rewrite Z_to_bv_swrap32. rewrite (sext32_land64 (112 - e)).
name_as_by shW (sext32 (112 - e)) (apply sext32_range).
zstep. zstep. replace (Z_to_bv 64 (Z.land shW 4294967295)) with (Z_to_bv 64 (zext32 shW)) by reflexivity.
name_as_by n (zext32 shW) (rewrite zext32_eq; pose proof (Z.mod_pos_bound shW 4294967296 ltac:(lia)); lia).
zstep. model_reg 13%Z nM64 (Z.land (n - 64) W64).
zstep. replace (Z_to_bv 64 (Z.land (bv_unsigned a0) 4294967295)) with (Z_to_bv 64 (zext32 (bv_unsigned a0))) by reflexivity.
name_as_by aZ (zext32 (bv_unsigned a0)) (rewrite zext32_eq; pose proof (Z.mod_pos_bound (bv_unsigned a0) 4294967296 ltac:(lia)); lia).
zstep. if_cases K1; zify_cond K1; decide_tests_b.
+
zstep. zstep.
name_as_by hi0 (Z.shiftr half (Z.land (Z.lxor n W64) 63))
(change (inr64 (Z.shiftr half (Z.land (Z.lxor n W64) 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
unsitf_tail nM64 clz. sf_finish.
+
zstep. zstep.
unsitf_tail nM64 clz. sf_finish.
Qed.

End G.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 QZAi QqdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1.
Import QZAi QqdR.
Import QnDM_c1.

Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.

Definition fpclassifyl_code : list Z :=
[0x00159613; 0x01059593; 0x000086b7; 0x03165613; 0xfff6869b; 0x0105d593; 0x00d60c63; 0x02061063; 0x00a5e533; 0x00153513; 0x00354513; 0x00008067; 0x00a5e533; 0x00153513; 0x00008067; 0x00400513; 0x00008067]%Z.

Lemma fpc_exp_field : forall h, (0 <= h < 2^64)%Z ->
Z.shiftr (Z.land (Z.shiftl h 1) 18446744073709551615) 49 = Z.land (Z.shiftr h 48) 32767.
Proof.
intros h Hh. apply Z.bits_inj'. intros i Hi.
rewrite Z.shiftr_spec, Z.land_spec, Z.land_spec, Z.shiftr_spec by lia.
change 18446744073709551615%Z with (Z.ones 64). change 32767%Z with (Z.ones 15).
destruct (Z.lt_ge_cases i 15).
- rewrite Z.shiftl_spec, !Z.ones_spec_low by lia. rewrite !Bool.andb_true_r. f_equal. lia.
- rewrite (Z.ones_spec_high 64), (Z.ones_spec_high 15) by lia. now rewrite !Bool.andb_false_r.
Qed.
Lemma fpc_mant_field : forall h, (0 <= h < 2^64)%Z ->
Z.shiftr (Z.land (Z.shiftl h 16) 18446744073709551615) 16 = Z.land h 281474976710655.
Proof.
intros h Hh. apply Z.bits_inj'. intros i Hi.
rewrite Z.shiftr_spec, Z.land_spec, Z.land_spec by lia.
change 18446744073709551615%Z with (Z.ones 64). change 281474976710655%Z with (Z.ones 48).
destruct (Z.lt_ge_cases i 48).
- rewrite Z.shiftl_spec, !Z.ones_spec_low by lia. rewrite !Bool.andb_true_r. f_equal. lia.
- rewrite (Z.ones_spec_high 64), (Z.ones_spec_high 48) by lia. now rewrite !Bool.andb_false_r.
Qed.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base fpclassifyl_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 68.

#[using="CODE BASE4 BASER"] Lemma gw_all : True. Proof. exact I. Qed.

Definition fpclassifyl_entry := (base + 0x0)%Z.

Definition fpclassifyl_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a1 a2 a3,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom segs)
/\ munch [] m m /\ wmono segs m m /\ mem_inv segs m.

#[using="CODE"] Lemma fpclassifyl_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
mem_inv segs m ->
evt segs (fpclassifyl_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
(fpclassifyl (bv_unsigned a0 + 2^64 * bv_unsigned a1)) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof. clear - CODE segs base.
intros until m. intros MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM. pose_word_ranges.
unfold fpclassifyl. rewrite hi64_words, lo64_words by lia. cbv zeta. rewrite ?b2z_Zb2z.
rewrite (Z.lor_comm (bv_unsigned a0)).
do 3 zstep. zstep. rewrite ?fpc_exp_field by lia. name_reg 12%Z e.
zstep. zstep. rewrite ?fpc_mant_field by lia. name_reg 11%Z mant.
zstep. if_cases Ki; zify_cond Ki; decide_tests_b.
-  zstep. zstep. rewrite (ltb1_eqb0 (Z.lor mant (bv_unsigned a0))) by zrange_nonneg.
destruct (Z.lor mant (bv_unsigned a0) =? 0)%Z; cbn [negb Z.b2z]; zstep; sf_finish.
- zstep. if_cases Kz; zify_cond Kz; decide_tests_b.
+  zstep. zstep. sf_finish.
+  zstep. zstep. rewrite (ltb1_eqb0 (Z.lor mant (bv_unsigned a0))) by zrange_nonneg.
zstep. destruct (Z.lor mant (bv_unsigned a0) =? 0)%Z; cbn [negb Z.b2z Z.lxor];
[change (Z.lxor 1 3) with 2%Z | change (Z.lxor 0 3) with 3%Z]; zstep; sf_finish.
Qed.

End G.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1.
Import QZAi QqdR.
Import QnDM_c1.
Import QVbl.Mq2.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4.
Open Scope bv_scope.

Import QZAa.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition frexpl_code (w_17 w_18 : Z) : list Z :=
[0xfe010113; 0x00113c23; 0x00813823; 0x00913423; 0x01213023; 0x00060413; 0x0305d693; 0x00008637; 0xfff6071b; 0x00e6f633; 0x08e60c63; 0x04061863; 0x00050493; 0x00058913; 0x00000693; 0x09c000ef; 0x06050a63; w_17; w_18; 0xdd9ff0ef; 0x00050613; 0x00058693; 0x00048513; 0x00090593; 0x1fc000ef; 0x00040613; 0xf99ff0ef; 0x00042603; 0xf8860613; 0x00c42023; 0x0480006f; 0x00008737; 0x00e6f6b3; 0xffffc737; 0x01059593; 0x00270713; 0x00e60633; 0x01fff737; 0x0105d593; 0x02571713; 0x03069693; 0x00e5e5b3; 0x00c42023; 0x00b6e5b3; 0x0100006f; 0x00048513; 0x00090593; 0x00042023; 0x01813083; 0x01013403; 0x00813483; 0x00013903; 0x02010113; 0x00008067]%Z.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_4 := flia_fast.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_5 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_6 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_7 := zsimp_fast.

Lemma frexpl_unfold : forall n x e,
frexpl (S n) x e =
(let hi := hi64 x in
let se := Z.shiftr hi 48 in
let ee := Z.land se 0x7fff in
if ee =? 0 then
if negb (f128_le x F128_ZERO =? 0) then
let k := f128_of_d D_0x1p120 in
match frexpl n (f128_mul x k) e with Some (x, e) => Some (x, e - 120) | None => None end
else Some (x, 0)
else if ee =? 0x7fff then Some (x, e)
else
let e := ee - 0x3ffe in
let hi := Z.lor (Z.lor (Z.land hi 0x8000000000000000) (Z.land hi 0x0000ffffffffffff)) 0x3ffe000000000000 in
Some (mk128 hi (lo64 x), e))%Z.
Proof. reflexivity. Qed.

Lemma frx_mant : forall h, (0 <= h < 2^64)%Z ->
Z.shiftr (Z.land (Z.shiftl h 16) 18446744073709551615) 16 = Z.land h 281474976710655.
Proof.
intros h Hh. apply Z.bits_inj'. intros i Hi.
rewrite Z.shiftr_spec, Z.land_spec, Z.land_spec by lia.
change 18446744073709551615%Z with (Z.ones 64). change 281474976710655%Z with (Z.ones 48).
destruct (Z.lt_ge_cases i 48).
- rewrite Z.shiftl_spec, !Z.ones_spec_low by lia. rewrite !Bool.andb_true_r. f_equal. lia.
- rewrite (Z.ones_spec_high 64), (Z.ones_spec_high 48) by lia. now rewrite !Bool.andb_false_r.
Qed.
Lemma frx_sign : forall h, (0 <= h < 2^64)%Z ->
Z.land (Z.shiftl (Z.land (Z.shiftr h 48) 32768) 48) 18446744073709551615 = Z.land h 9223372036854775808.
Proof.
intros h Hh. apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec, Z.land_spec. change 18446744073709551615%Z with (Z.ones 64).
change 32768%Z with (2^15)%Z. change 9223372036854775808%Z with (2^63)%Z.
rewrite (Z.pow2_bits_eqb 63) by lia.
destruct (Z.lt_ge_cases i 48).
- rewrite Z.shiftl_spec_low by lia. destruct (Z.eqb_spec 63 i); [lia|]. now rewrite Bool.andb_false_r.
- rewrite Z.shiftl_spec_high, Z.land_spec, Z.shiftr_spec, Z.pow2_bits_eqb by lia.
destruct (Z.lt_ge_cases i 64).
+ rewrite Z.ones_spec_low by lia. replace (i - 48 + 48)%Z with i by lia.
destruct (Z.eqb_spec 15 (i - 48)), (Z.eqb_spec 63 i); try lia; now rewrite ?Bool.andb_true_r, ?Bool.andb_false_r.
+ rewrite Z.ones_spec_high by lia. destruct (Z.eqb_spec 63 i); [lia|]. now rewrite !Bool.andb_false_r.
Qed.

Lemma f128_le_cases : forall a b, (f128_le a b = -1 \/ f128_le a b = 0 \/ f128_le a b = 1)%Z.
Proof.
intros a b. unfold f128_le, nez64. cbv zeta.
repeat match goal with |- context [if ?c then _ else _] => destruct c end; try lia.
all: destruct (Z.eqb _ 0); cbn; lia.
Qed.
Lemma f128_le_land64_zero : forall a b, Z.land (f128_le a b) 18446744073709551615 = 0%Z <-> f128_le a b = 0%Z.
Proof.
intros a b. destruct (f128_le_cases a b) as [E|[E|E]]; rewrite E; vm_compute; split; intros; lia.
Qed.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_17 w_18 : Z).
Variables (hi_17 : bv 20).
Variables (lo_18 lo_20 : bv 12).
Variables (G_107d0 G_10d38 : Z).
Hypothesis CODE : code_at segs base (frexpl_code w_17 w_18).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 216.
Hypothesis D_17 : decode_any (Z_to_bv 32 w_17) = Some (Auipc 10 hi_17, 4%Z).
Hypothesis E_17 : is_ecall (Z_to_bv 32 w_17) = false.
Hypothesis D_18 : decode_any (Z_to_bv 32 w_18) = Some (FLoad FMT_D 10 10 lo_18, 4%Z).
Hypothesis E_18 : is_ecall (Z_to_bv 32 w_18) = false.
Hypothesis ANCH_18 : gw_anch (Z.shiftl (bv_signed hi_17) 12 + (base + 68) + bv_signed lo_18)%Z G_107d0.
Hypothesis ANCH_20 : gw_anch (Z.shiftl (bv_signed hi_17) 12 + (base + 68) + bv_signed lo_20)%Z G_10d38.
Hypothesis RNG_G_107d0 : gw_br G_107d0 8.
Hypothesis ROM_G_107d0 : ro_bytes segs G_107d0 (le8 (Z_to_bv 64 5147614374084476928)).

Definition letf2_post := Eval cbv beta delta [QVbl.Mq2.letf2_post] in (QVbl.Mq2.letf2_post segs).

Hypothesis lo64_words : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq2.lo64_words segs (base + 216)%Z) 3%nat in let T := gw_subst T (QVbl.Mq2.letf2_post segs) letf2_post in let T := gw_fold_pcs T base (216)%Z [0; 56; 92; 180]%Z in exact T).
Hypothesis hi64_words : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq2.hi64_words segs (base + 216)%Z) 3%nat in let T := gw_subst T (QVbl.Mq2.letf2_post segs) letf2_post in let T := gw_fold_pcs T base (216)%Z [0; 56; 92; 180]%Z in exact T).
Hypothesis letf2_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq2.letf2_spec segs (base + 216)%Z) 3%nat in let T := gw_subst T (QVbl.Mq2.letf2_post segs) letf2_post in let T := gw_fold_pcs T base (216)%Z [0; 56; 92; 180]%Z in exact T).

#[using="CODE BASE4 BASER D_17 E_17 D_18 E_18 ANCH_18 ANCH_20 RNG_G_107d0 ROM_G_107d0 lo64_words hi64_words letf2_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Definition frexpl_entry := (base + 0x0)%Z.

Definition frexpl_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(P x E : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists x' e' t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 x')) (Z_to_bv 64 (hi64 x')) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (P, P + 4)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' (bv_unsigned sp - 32) (bv_unsigned sp)
/\ rw_cells segs m' P [C4 (Z_to_bv 64 e')]
/\ frexpl FREXPL_FUEL x E = Some (x', e').

Ltac frx_finish X E' :=
apply evt_done; unfold frexpl_post; exists X, E';
repeat (lazymatch goal with |- ex _ => eexists end);
split; [ rewrite ?lo64_mk128, ?hi64_mk128 by zrange; rewrite ?lo64_words, ?hi64_words by lia; ms_eq
| repeat match goal with |- _ /\ _ => split end; try assumption ].

#[using="w_17 w_18 CODE BASE4 BASER lo64_words hi64_words letf2_spec"] Lemma frexpl_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (E : Z),
stk segs m (bv_unsigned sp - 32) (bv_unsigned sp) ->
mem_inv segs m ->
rw_cells segs m (bv_unsigned a2) [C4 (Z_to_bv 64 E)] ->
(bv_unsigned a2 + 4 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
(32 <= bv_unsigned sp)%Z ->
(let x := (bv_unsigned a0 + 2^64 * bv_unsigned a1)%Z in
Z.land (Z.shiftr (hi64 x) 48) 0x7fff <> 0%Z \/ f128_le x F128_ZERO = 0%Z) ->
evt segs (frexpl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
(bv_unsigned a2) (bv_unsigned a0 + 2^64 * bv_unsigned a1) E m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof. clear - w_17 w_18 CODE BASE4 BASER lo64_words hi64_words letf2_spec segs base.
intros until E. intros ST MI CE SEP SPLO PRE.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned a2, bv_unsigned a2 + 4)]%Z m) as MU.
pose proof (wmono_refl segs m) as WM. pose_word_ranges.

set (P := bv_unsigned a2) in *. replace a2 with (Z_to_bv 64 P) by (unfold P; rewrite Z_to_bv_bv_unsigned; reflexivity).
cbv zeta in PRE. rewrite hi64_words in PRE by lia.
unfold frexpl_post. change FREXPL_FUEL with 2%nat. rewrite frexpl_unfold.
rewrite hi64_words, lo64_words by lia. cbv zeta.
carve_frame 32%nat ST.
do 6 zstep. do 4 zstep. name_reg 12%Z ee.
zstep. if_cases Ki; zify_cond Ki; decide_tests_b.
-
do 6 zstep. release_frame FR ST (bv_unsigned sp).
frx_finish (bv_unsigned a0 + 2^64 * bv_unsigned a1)%Z E. decide_tests_b. reflexivity.
- zstep. if_cases Kz; zify_cond Kz; decide_tests_b.
+
do 7 zstep. zstep. zstep. zstep.
replace (Z_to_bv 64 (Z.shiftl (Z.land (Z.shiftr (bv_unsigned a1) 48) 32768) 48)) with (Z_to_bv 64 (Z.land (bv_unsigned a1) 9223372036854775808))
by (rewrite <- (Z_to_bv_land64 (Z.shiftl _ 48)); f_equal; symmetry; apply frx_sign; lia).
zstep. zstep. zstep. reg_rewrite 11%Z Z.lor_assoc.
zstep. do 6 zstep. release_frame FR ST (bv_unsigned sp).
frx_finish (mk128 (Z.lor (Z.lor (Z.land (bv_unsigned a1) 0x8000000000000000) (Z.land (bv_unsigned a1) 0x0000ffffffffffff)) 0x3ffe000000000000) (bv_unsigned a0))%Z (ee - 16382)%Z.
decide_tests_b. reflexivity.
+
do 3 zstep. zstep. call letf2_spec. 1:{ assumption. }
zsimp. rewrite Kz. rewrite Z.mul_0_r, Z.add_0_r.
zstep. if_cases Kl; zify_cond Kl; rewrite f128_le_land64_zero in Kl.
*  do 3 zstep. do 6 zstep. release_frame FR ST (bv_unsigned sp).
frx_finish (bv_unsigned a0 + 2^64 * bv_unsigned a1)%Z 0%Z. decide_tests_b. unfold F128_ZERO. rewrite Kl. reflexivity.
* exfalso. unfold F128_ZERO in PRE. change (2^64)%Z with 18446744073709551616%Z in PRE.
destruct PRE as [PRE|PRE]; [exact (PRE Kz)|]. rewrite PRE in Kl. exact (Kl eq_refl).
Qed.

End G.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1.
Import QnDM_c1.
Import QVbl.Mq3.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition fwritex_code (w_46 w_64 : Z) : list Z :=
[0xfc010113; 0x02113c23; 0x02813823; 0x02913423; 0x03213023; 0x01313c23; 0x01413823; 0x01513423; 0x00060413; 0x00058493; 0x02063583; 0x00050913; 0x08058263; 0x02843503; 0x40a585b3; 0x0295fc63; 0x04843303; 0x00040513; 0x00090593; 0x00048613; 0x03813083; 0x03013403; 0x02813483; 0x02013903; 0x01813983; 0x01013a03; 0x00813a83; 0x04010113; 0x00030067; 0x09042583; 0x00000993; 0x0605ce63; 0x06048c63; 0x00000a13; 0x00990ab3; 0xfff00593; 0x00a00613; 0x00ba86b3; 0x0006c683; 0x02c68a63; 0x001a0a13; 0xfff58593; 0xff4496e3; 0x00000993; 0x0480006f; 0x00040513; w_46; 0x00050663; 0x00000513; 0x0500006f; 0x02043583; 0xf69ff06f; 0x04843683; 0x414489b3; 0x00040513; 0x00090593; 0x00098613; 0x000680e7; 0x03356663; 0x02843503; 0x414a8933; 0x000a0493; 0x00090593; 0x00048613; w_64; 0x02843503; 0x00950533; 0x02a43423; 0x00998533; 0x03813083; 0x03013403; 0x02813483; 0x02013903; 0x01813983; 0x01013a03; 0x00813a83; 0x04010113; 0x00008067]%Z.

Definition FILE_cells (fl0 : byte) (j1 : list byte) (WEND WPOS : Z) (j2 : list byte) (lbfw : word) : list cell :=
[CB 1 [fl0]; CB 31 j1; C8 (Z_to_bv 64 WEND); C8 (Z_to_bv 64 WPOS); CB 96 j2; C4 lbfw].

Lemma wr_at_app : forall segs_ m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
wr_at segs_ m a (n1 + n2) <-> wr_at segs_ m a n1 /\ wr_at segs_ m (a + n1) n2.
Proof.
intros segs_ m a n1 n2 H1 H2. unfold wr_at. split.
- intros (Ha & Hb & H). repeat split; try lia.
+ intros i Hi. apply H. lia.
+ intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
- intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
intros i Hi. destruct (Z.lt_ge_cases i n1).
+ apply HA. lia.
+ replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.

Lemma rw_cells_app : forall segs_ m A cs1 cs2,
rw_cells segs_ m A (cs1 ++ cs2) <-> rw_cells segs_ m A cs1 /\ rw_cells segs_ m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros segs_ m A cs1 cs2. unfold rw_cells, cells_at.
rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
rewrite wr_at_app by lia. rewrite bytes_at_app.
split.
- intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
rewrite (cells_bytes_length cs1 W1) in B2. tauto.
- intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma sx32_neg : forall w : word, (2147483648 <= bv_unsigned w mod 4294967296)%Z ->
(9223372036854775808 <= bv_unsigned (sx32 w))%Z.
Proof.
intros w H. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq.
pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
change (2^64)%Z with 18446744073709551616%Z in *.
Z.div_mod_to_equations. lia.
Qed.

Ltac unwrap_in K := rewrite ?land_W64 in K; change (2^64)%Z with 18446744073709551616%Z in K; rewrite ?Z.mod_small in K by lia.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_46 w_64 : Z).
Variables (joff_46 joff_64 : bv 21).
Variables (e_1cb6c e_memcpy : Z).
Hypothesis CODE : code_at segs base (fwritex_code w_46 w_64).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 312.
Hypothesis D_46 : decode_any (Z_to_bv 32 w_46) = Some (Jal 1 joff_46, 4%Z).
Hypothesis E_46 : is_ecall (Z_to_bv 32 w_46) = false.
Hypothesis D_64 : decode_any (Z_to_bv 32 w_64) = Some (Jal 1 joff_64, 4%Z).
Hypothesis E_64 : is_ecall (Z_to_bv 32 w_64) = false.
Hypothesis LINK_46 : gw_anch (base + 184 + bv_signed joff_46)%Z (e_1cb6c + 0)%Z.
Hypothesis LINK_64 : gw_anch (base + 256 + bv_signed joff_64)%Z (e_memcpy + 0)%Z.

Definition memcpy_post := Eval cbv beta delta [QVbl.Mq3.memcpy_post] in (QVbl.Mq3.memcpy_post segs).

Hypothesis memcpy_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq3.memcpy_spec segs e_memcpy) 3%nat in let T := gw_subst T (QVbl.Mq3.memcpy_post segs) memcpy_post in exact T).

#[using="CODE BASE4 BASER D_46 E_46 D_64 E_64 LINK_46 LINK_64 memcpy_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Definition fwritex_entry := (base + 0x0)%Z.

Definition wfile (m : word -> option byte) (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word)
(B : Z) (content junk : list byte) : Prop :=
rw_cells segs m Fp (FILE_cells fl0 j1 (B + Z.of_nat (length content) + Z.of_nat (length junk))
(B + Z.of_nat (length content)) j2 lbfw)
/\ rw_cells segs m B [CB (length content) content; CB (length junk) junk]
/\ Z.land (bv_unsigned fl0) 32 = 0%Z
/\ (2147483648 <= bv_unsigned lbfw mod 4294967296)%Z
/\ (0 < B)%Z /\ (B + Z.of_nat (length content) + Z.of_nat (length junk) < 2^64)%Z
/\ (Fp + 148 <= B \/ B + Z.of_nat (length content) + Z.of_nat (length junk) <= Fp)%Z.

Definition fwritex_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte)
(S : Z) (bs : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length bs))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp);
(B + Z.of_nat (length content), B + Z.of_nat (length content) + Z.of_nat (length bs));
(Fp + 40, Fp + 48)]%Z m m'
/\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' (bv_unsigned sp - 64) (bv_unsigned sp)
/\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ bs) (skipn (length bs) junk)
/\ bytes_at segs m' S bs.

Definition memcpy_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(D : Z) (a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(D, D + bv_unsigned a2)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rw_cells segs m' D [CB (Z.to_nat (bv_unsigned a2)) src]
/\ bytes_at segs m' (bv_unsigned a1) src.
#[using="memcpy_spec"] Lemma memcpy_callZ : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (D : Z) (src junk : list byte),
bytes_at segs m (bv_unsigned a1) src ->
length src = Z.to_nat (bv_unsigned a2) ->
rw_cells segs m D [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(0 <= D < 2^64)%Z ->
(bv_unsigned a1 + bv_unsigned a2 <= D \/ D + bv_unsigned a2 <= bv_unsigned a1)%Z ->
mem_inv segs m ->
evt segs (memcpy_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D a1 a2 src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_memcpy + 0x0)) fc None m (seg_rom segs)).
Proof. clear - memcpy_spec segs e_memcpy.
intros until junk. intros SRC LEN DST HD SEP MI.
assert (E : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
eapply evt_mono.
{ eapply (memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D)); rewrite ?E; eauto. }
intros ms' P. unfold memcpy_post in P. rewrite !E in P. exact P.
Qed.

#[using="w_46 w_64 joff_64 e_memcpy CODE BASE4 BASER D_64 E_64 LINK_64 memcpy_spec"] Lemma fwritex_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte)
(fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk bs : list byte),
wfile m (bv_unsigned a2) fl0 j1 j2 lbfw B content junk ->
bytes_at segs m (bv_unsigned a0) bs ->
Z.of_nat (length bs) = bv_unsigned a1 ->
(length bs <= length junk)%nat ->
stk segs m (bv_unsigned sp - 64) (bv_unsigned sp) ->
mem_inv segs m ->
(64 <= bv_unsigned sp)%Z ->
(bv_unsigned a2 + 148 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
(B + Z.of_nat (length content) + Z.of_nat (length junk) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= B)%Z ->
(bv_unsigned a0 + Z.of_nat (length bs) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
(bv_unsigned a0 + Z.of_nat (length bs) <= B + Z.of_nat (length content)
\/ B + Z.of_nat (length content) + Z.of_nat (length bs) <= bv_unsigned a0)%Z ->
(bv_unsigned a0 + Z.of_nat (length bs) <= bv_unsigned a2 \/ bv_unsigned a2 + 148 <= bv_unsigned a0)%Z ->
evt segs (fwritex_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
(bv_unsigned a2) fl0 j1 j2 lbfw B content junk (bv_unsigned a0) bs m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof. clear - w_46 w_64 joff_64 e_memcpy CODE BASE4 BASER D_64 E_64 LINK_64 memcpy_spec segs base.
intros until bs. intros (FC & BUF & FL & LBF & Bpos & Bhi & SEPfb) SRC LEN LE ST MI SPLO SEP1 SEP2 SEP3 SEP4 SEP5.
pose_word_ranges.
set (Fp := bv_unsigned a2) in *. replace a2 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
set (S := bv_unsigned a0) in *.
set (nc := length content) in *. set (nj := length junk) in *. set (lb := length bs) in *.
pose proof (rw_cells_bound _ _ _ _ FC) as BF. cbn [cells_size csize Nat.add length] in BF.
pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB. rewrite Nat.add_0_r, Nat2Z.inj_add in BB.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (B + Z.of_nat nc, B + Z.of_nat nc + Z.of_nat lb); (Fp + 40, Fp + 48)]%Z m) as MU.
pose proof (wmono_refl segs m) as WM.
unfold FILE_cells in FC.
carve_frame 64%nat ST.
do 8 zstep.
zstep. zstep. zstep. zstep.
zstep. if_cases Kw; zify_cond Kw; unwrap_in Kw.
{ exfalso. lia. }
zstep. zstep.
zstep. if_cases Kr; zify_cond Kr; unwrap_in Kr.
2:{ exfalso. lia. }
zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
2:{ exfalso. pose proof (sx32_neg lbfw LBF). lia. }
zstep. zstep.

apply (rw_cells_split_CB segs _ _ [CB nc content] nj junk [] [lb; nj - lb]%nat) in BUF; [ | cbn; lia ].
cbn [mk_CB_cells app] in BUF.
apply (proj1 (rw_cells_app segs _ _ [_] _)) in BUF. destruct BUF as [BUFa BUF].
cbn [cells_size csize Nat.add] in BUF. rewrite Nat.add_0_r in BUF.
apply (proj1 (rw_cells_app segs _ _ [_] _)) in BUF. destruct BUF as [BUFb BUFc].
cbn [cells_size csize] in BUFc. rewrite Nat.add_0_r in BUFc.
zstep. call memcpy_callZ.
1:{ exact SRC. }
1:{ unfold lb in LEN. rewrite <- LEN, Nat2Z.id. reflexivity. }
1:{ rewrite <- LEN, Nat2Z.id. exact BUFb. }
1:{ lia. } 1:{ lia. } 1:{ assumption. }
rewrite <- !LEN in *. rewrite !Nat2Z.id in *.
rewrite firstn_all2 in BUFc by (rewrite length_skipn; lia).
match goal with MC : rw_cells _ _ (B + Z.of_nat nc)%Z [CB lb bs] |- _ => rename MC into BUFb end.
zstep. zstep. zstep. zstep.
replace (0 + bv_unsigned a1)%Z with (Z.of_nat lb) by lia.
replace (B + Z.of_nat nc + bv_unsigned a1)%Z with (B + Z.of_nat (length (content ++ bs)))%Z by (rewrite length_app; lia).
do 9 zstep. release_frame FR ST (bv_unsigned sp).

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (BUF : rw_cells segs mm B ([] ++ [CB nc content; CB lb bs] ++ [CB (nj - lb)%nat (skipn lb junk)]));
[ cbn [app]; apply (proj2 (rw_cells_app segs _ _ [_] _)); split; [ exact BUFa |];
cbn [cells_size csize]; rewrite Nat.add_0_r;
apply (proj2 (rw_cells_app segs _ _ [_] _)); split; [ exact BUFb |];
cbn [cells_size csize]; rewrite Nat.add_0_r; exact BUFc
| apply rw_cells_merge in BUF; cbn [cells_size cells_bytes csize cbytes app Nat.add] in BUF;
rewrite Nat.add_0_r, app_nil_r in BUF; clear BUFa BUFb BUFc ]
end.
apply evt_done. unfold fwritex_post.
repeat (lazymatch goal with |- ex _ => eexists end).
split; [ ms_eq | ].
repeat match goal with |- _ /\ _ => split end; try assumption;
try (replace (bv_unsigned sp - 64)%Z with (bv_unsigned sp + -64)%Z by lia; assumption).

unfold wfile, FILE_cells. rewrite !length_app, !length_skipn. fold nc lb nj.
rewrite !Nat2Z.inj_add, !Nat2Z.inj_sub by lia.
replace (B + (Z.of_nat nc + Z.of_nat lb) + (Z.of_nat nj - Z.of_nat lb))%Z with (B + Z.of_nat nc + Z.of_nat nj)%Z by lia.
replace (B + Z.of_nat nc + bv_unsigned a1)%Z with (B + (Z.of_nat nc + Z.of_nat lb))%Z in FC by lia.
split; [exact FC|]. split; [exact BUF|]. split; [exact FL|]. split; [exact LBF|]. split; [lia|]. split; lia.
Qed.

Definition fwritex_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte)
(S : Z) (bs : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length bs))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(q - 64, q);
(B + Z.of_nat (length content), B + Z.of_nat (length content) + Z.of_nat (length bs));
(Fp + 40, Fp + 48)]%Z m m'
/\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' (q - 64) q
/\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ bs) (skipn (length bs) junk)
/\ bytes_at segs m' S bs.

#[using="w_46 w_64 joff_64 e_memcpy CODE BASE4 BASER D_64 E_64 LINK_64 memcpy_spec"] Lemma fwritex_call : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q S L Fp : Z)
(fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk bs : list byte),
wfile m Fp fl0 j1 j2 lbfw B content junk ->
bytes_at segs m S bs ->
Z.of_nat (length bs) = L ->
(length bs <= length junk)%nat ->
stk segs m (q - 64) q ->
mem_inv segs m ->
(64 <= q < 2^64)%Z -> (0 <= S)%Z -> (S + L < 2^64)%Z -> (0 <= Fp)%Z ->
(Fp + 148 <= q - 64 \/ q <= Fp)%Z ->
(B + Z.of_nat (length content) + Z.of_nat (length junk) <= q - 64 \/ q <= B)%Z ->
(S + L <= q - 64 \/ q <= S)%Z ->
(S + L <= B + Z.of_nat (length content) \/ B + Z.of_nat (length content) + L <= S)%Z ->
(S + L <= Fp \/ Fp + 148 <= S)%Z ->
evt segs (fwritex_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
Fp fl0 j1 j2 lbfw B content junk S bs m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 L) (Z_to_bv 64 Fp) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof. clear - w_46 w_64 joff_64 e_memcpy CODE BASE4 BASER D_64 E_64 LINK_64 memcpy_spec segs base.
intros until bs. intros WF SRC LEN LE ST MI Hq HS HSL HFp SEP1 SEP2 SEP3 SEP4 SEP5.
assert (HF : (Fp + 148 <= 2^64)%Z).
{ destruct WF as (FC & _). pose proof (rw_cells_bound _ _ _ _ FC) as BF. unfold FILE_cells in BF. cbn [cells_size csize Nat.add length] in BF.
lia. }
assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
assert (Es : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
assert (El : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
assert (Ef : bv_unsigned (Z_to_bv 64 Fp) = Fp) by (apply unsigned_lit; lia).
eapply evt_mono.
{ eapply (fwritex_spec ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 L) (Z_to_bv 64 Fp)); rewrite ?Eq, ?Es, ?El, ?Ef; eauto; lia. }
intros ms' P. unfold fwritex_post in P. rewrite !Eq, !Es, !Ef in P. exact P.
Qed.

End G.
End Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.

Definition memchr_code (w_22 w_23 w_24 w_25 : Z) : list Z :=
[0x0ff5f593; 0x00757693; 0x00c03733; 0x02068c63; 0x02060a63; 0x00150793; 0x00100813; 0x00054703; 0x00060693; 0x06b70e63; 0x00150513; 0xfff68613; 0x0077f893; 0x00c03733; 0x00088663; 0x00178793; 0xfd069ee3; 0x06070863; 0x00054683; 0x04b68663; 0x00800693; 0x04d66263; w_22; w_23; w_24; w_25; 0x00168793; 0x02f587b3; 0x00700813; 0x00053883; 0x00f8c8b3; 0x411682b3; 0x0112e8b3; 0x00e8f8b3; 0x02e89a63; 0xff860613; 0x00850513; 0xfec860e3; 0x00060693; 0x00060c63; 0x00054603; 0x00b60a63; 0xfff68693; 0x00150513; 0xfe0698e3; 0x00000513; 0x00008067; 0x00060693; 0x00054603; 0xfeb612e3; 0xff1ff06f]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_22 w_23 w_24 w_25 : Z).
Variables (hi_22 hi_24 : bv 20).
Variables (lo_23 lo_25 : bv 12).
Variables (G_10780 G_10790 : Z).
Hypothesis CODE : code_at segs base (memchr_code w_22 w_23 w_24 w_25).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 204.
Hypothesis D_22 : decode_any (Z_to_bv 32 w_22) = Some (Auipc 13 hi_22, 4%Z).
Hypothesis E_22 : is_ecall (Z_to_bv 32 w_22) = false.
Hypothesis D_23 : decode_any (Z_to_bv 32 w_23) = Some (Load SZ8 true 13 13 lo_23, 4%Z).
Hypothesis E_23 : is_ecall (Z_to_bv 32 w_23) = false.
Hypothesis D_24 : decode_any (Z_to_bv 32 w_24) = Some (Auipc 14 hi_24, 4%Z).
Hypothesis E_24 : is_ecall (Z_to_bv 32 w_24) = false.
Hypothesis D_25 : decode_any (Z_to_bv 32 w_25) = Some (Load SZ8 true 14 14 lo_25, 4%Z).
Hypothesis E_25 : is_ecall (Z_to_bv 32 w_25) = false.
Hypothesis ANCH_23 : gw_anch (Z.shiftl (bv_signed hi_22) 12 + (base + 88) + bv_signed lo_23)%Z G_10790.
Hypothesis ANCH_25 : gw_anch (Z.shiftl (bv_signed hi_24) 12 + (base + 96) + bv_signed lo_25)%Z G_10780.
Hypothesis RNG_G_10790 : gw_br G_10790 8.
Hypothesis ROM_G_10790 : ro_bytes segs G_10790 (le8 (Z_to_bv 64 72340172838076672)).
Hypothesis RNG_G_10780 : gw_br G_10780 8.
Hypothesis ROM_G_10780 : ro_bytes segs G_10780 (le8 (Z_to_bv 64 9259542123273814144)).

#[using="CODE BASE4 BASER D_22 E_22 D_23 E_23 D_24 E_24 D_25 E_25 ANCH_23 ANCH_25 RNG_G_10790 ROM_G_10790 RNG_G_10780 ROM_G_10780"] Lemma gw_all : True. Proof. exact I. Qed.

Definition memchr_entry := (base + 0x0)%Z.

Section ZFacts.
Open Scope Z_scope.
#[using="Type"] Lemma lxor_lt_256 : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lxor a b < 256.
Proof.
intros a b Ha Hb. pose proof (Z.lxor_nonneg a b) as Hnn. split; [lia|].
destruct (Z.eq_dec (Z.lxor a b) 0) as [->|Hnz]; [lia|].
apply (proj2 (Z.log2_lt_pow2 (Z.lxor a b) 8 ltac:(lia))).
pose proof (Z.log2_lxor a b ltac:(lia) ltac:(lia)) as Hl.
assert (Z.log2 a < 8). { destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
assert (Z.log2 b < 8). { destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
lia.
Qed.

#[using="Type"] Lemma lxor_split : forall x y x' y', 0 <= x < 256 -> 0 <= x' < 256 -> 0 <= y -> 0 <= y' ->
Z.lxor (x + 256 * y) (x' + 256 * y') = Z.lxor x x' + 256 * Z.lxor y y'.
Proof.
intros x y x' y' Hx Hx' Hy Hy'.
pose proof (lxor_lt_256 x x' Hx Hx') as Hl.
apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, !testbit_split by lia.
destruct (i <? 8); rewrite Z.lxor_spec; reflexivity.
Qed.

#[using="Type"] Lemma le_val_nonneg : forall bs, bytes_ok bs -> 0 <= le_val bs.
Proof. intros bs H. pose proof (le_val_range bs H). lia. Qed.

#[using="Type"] Lemma le_val_xor_bcast : forall bs c, bytes_ok bs -> 0 <= c < 256 ->
Z.lxor (le_val bs) (c * ones (length bs)) = le_val (map (fun b => Z.lxor b c) bs).
Proof.
induction bs as [|b bs IH]; intros c Hok Hc.
- cbn. rewrite Z.mul_0_r. reflexivity.
- inversion Hok as [|b0 bs0 Hb Hbs]; subst. cbn [le_val ones length map].
replace (c * (1 + 256 * ones (length bs))) with (c + 256 * (c * ones (length bs))) by lia.
rewrite lxor_split; try lia.
+ rewrite IH by assumption. reflexivity.
+ apply le_val_nonneg. exact Hbs.
+ pose proof (le_val_range (repeat 1 (length bs))) as Hr. assert (0 <= ones (length bs)); [|nia].
clear. induction (length bs); cbn; lia.
Qed.

#[using="Type"] Lemma bytes_ok_xor : forall bs c, bytes_ok bs -> 0 <= c < 256 -> bytes_ok (map (fun b => Z.lxor b c) bs).
Proof.
intros bs c H Hc. unfold bytes_ok in *. rewrite Forall_map. eapply Forall_impl; [|exact H].
intros b Hb. apply lxor_lt_256; assumption.
Qed.

#[using="Type"] Lemma In0_xor : forall bs c, In 0 (map (fun b => Z.lxor b c) bs) <-> In c bs.
Proof.
intros bs c. rewrite in_map_iff. split.
- intros (b & Hb & Hin). apply Z.lxor_eq in Hb. subst. exact Hin.
- intros Hin. exists c. split; [apply Z.lxor_nilpotent| exact Hin].
Qed.
End ZFacts.

Definition memchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (buf : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
(Z_to_bv 64 (memchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf))
a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ bytes_at segs m' (bv_unsigned a0) buf.

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf : list byte).
Hypothesis MI : mem_inv segs m.
Hypothesis BUF : bytes_at segs m (bv_unsigned a0) buf.
Hypothesis OK : memchr_ok (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf.
Let MU : munch [] m m := munch_refl [] m.
Let WM : wmono segs m m := wmono_refl segs m.

Notation A := (bv_unsigned a0).
Notation n := (bv_unsigned a2).
Notation c := ((bv_unsigned a1) mod 256)%Z.
Notation len := (Z.of_nat (length buf)).
Notation POST := (memchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf m).

Notation ST pc x5 x10 x12 x13 x14 x15 x16 x17 :=
(MS (mkR ra sp gp tp x5 t1 t2 s0 s1 x10 (Z_to_bv 64 c) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom segs)).
Notation CMAGIC := 72340172838076672%Z.
Notation HIGHS := 9259542123273814144%Z.
Notation ONES := 72340172838076673%Z.

Definition NOB (i : Z) : Prop :=
forall j b, (j < Z.to_nat i)%nat -> nth_error buf j = Some b -> bv_unsigned b <> c.

#[using="segs m BUF"] Lemma A_bound : (0 <= A /\ A + len <= 2^64 /\ 0 <= n < 2^64 /\ 0 <= c < 256)%Z.
Proof. clear - segs m BUF.
pose proof (bytes_at_bound _ _ _ _ BUF).
pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R.
pose proof (Z.mod_pos_bound (bv_unsigned a1) 256). cbn. lia.
Qed.

#[using="Type"] Lemma NOB_0 : NOB 0.
Proof. intros j b Hj. cbn in Hj. lia. Qed.

#[using="Type"] Lemma NOB_S : forall i b, (0 <= i)%Z -> NOB i -> nth_error buf (Z.to_nat i) = Some b -> bv_unsigned b <> c -> NOB (i + 1).
Proof.
intros i b Hi H Hn Hb j b' Hj Hn'.
destruct (Nat.eq_dec j (Z.to_nat i)) as [->|NE]. { rewrite Hn in Hn'. injection Hn' as <-. exact Hb. }
eapply H; [|exact Hn']. lia.
Qed.

#[using="OK"] Lemma ok_cases :
(exists j b, Z.of_nat j < n /\ nth_error buf j = Some b /\ bv_unsigned b = c /\
(forall j' b', (j' < j)%nat -> nth_error buf j' = Some b' -> bv_unsigned b' <> c) /\
(n <= len \/ Z.of_nat j + 1 + (- (A + Z.of_nat j + 1)) mod 8 <= len))%Z
\/ ((forall j b, (Z.of_nat j < n)%Z -> nth_error buf j = Some b -> bv_unsigned b <> c) /\ (n <= len)%Z).
Proof. clear - OK.
pose proof OK as H. unfold memchr_ok in H.
destruct (find_byte c (firstn (Z.to_nat n) buf)) as [j|] eqn:FB.
- left. destruct (find_byte_Some _ _ _ FB) as (Hl & (b & Hn & Hb) & Hmin).
rewrite firstn_length in Hl.
rewrite nth_error_firstn in Hn. replace (Nat.ltb j (Z.to_nat n)) with true in Hn by (symmetry; apply Nat.ltb_lt; lia).
exists j, b. repeat split; try assumption; try lia.
intros j' b' Hj' Hn'. eapply Hmin; [exact Hj'|]. rewrite nth_error_firstn.
replace (Nat.ltb j' (Z.to_nat n)) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn'.
- right. split; [|exact H]. intros j b Hj Hn. eapply (find_byte_None _ _ FB j). rewrite nth_error_firstn.
replace (Nat.ltb j (Z.to_nat n)) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn.
Qed.

#[using="a0 OK"] Lemma readable : forall i, (0 <= i < n)%Z -> NOB i -> exists b, nth_error buf (Z.to_nat i) = Some b.
Proof. clear - a0 OK.
intros i Hi HN. destruct (nth_error buf (Z.to_nat i)) as [b|] eqn:E; [exists b; reflexivity|].
exfalso. apply nth_error_None in E.
destruct ok_cases as [(j & b & Hj & Hn & Hb & Hmin & _)|(Hall & Hlen)]; [|lia].
pose proof (nth_error_lt _ _ _ Hn).
destruct (Nat.lt_ge_cases j (Z.to_nat i)) as [Hlt|Hge]; [|lia].
exact (HN _ _ Hlt Hn Hb).
Qed.

#[using="OK"] Lemma readable8 : forall i, (0 <= i)%Z -> (i + 8 <= n)%Z -> ((A + i) mod 8 = 0)%Z -> NOB i ->
(Z.to_nat i + 8 <= length buf)%nat.
Proof. clear - OK.
intros i Hi Hi8 Hal HN.
destruct ok_cases as [(j & b & Hj & Hn & Hb & Hmin & Hsl)|(Hall & Hlen)]; [|lia].
pose proof (nth_error_lt _ _ _ Hn).
destruct (Nat.lt_ge_cases j (Z.to_nat i)) as [Hlt|Hge]. { exfalso. exact (HN _ _ Hlt Hn Hb). }
destruct Hsl as [Hsl|Hsl]; [lia|].
destruct (Nat.lt_ge_cases j (Z.to_nat i + 8)) as [Hlt8|]; [|lia].
Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma res_found : forall i b, (0 <= i < n)%Z -> NOB i -> nth_error buf (Z.to_nat i) = Some b -> bv_unsigned b = c ->
memchr_res A c n buf = (A + i)%Z.
Proof.
intros i b Hi HN Hn Hb. unfold memchr_res.
rewrite (find_byte_charact c _ (Z.to_nat i) b); [lia| | exact Hb|].
- rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia). exact Hn.
- intros j b' Hj Hn'. rewrite nth_error_firstn in Hn'. destruct (Nat.ltb j (Z.to_nat n)); [|discriminate].
exact (HN _ _ Hj Hn').
Qed.

#[using="Type"] Lemma res_none : NOB n -> memchr_res A c n buf = 0%Z.
Proof.
intros HN. unfold memchr_res. rewrite find_byte_None_intro; [reflexivity|].
intros j b Hn. rewrite nth_error_firstn in Hn. destruct (Nat.ltb_spec0 j (Z.to_nat n)); [|discriminate].
exact (HN j b ltac:(lia) Hn).
Qed.

#[using="w_22 w_23 w_24 w_25 CODE MI BUF OK MU WM"] Lemma memchr_tail : forall (k : nat) (i : Z) (x5 x12 x14 x15 x16 x17 : word),
Z.to_nat (n - i) = k -> (0 <= i < n)%Z -> NOB i ->
evt segs POST (ST (base + 0xa0) x5 (Z_to_bv 64 (A + i)) x12 (Z_to_bv 64 (n - i)) x14 x15 x16 x17).
Proof. clear - w_22 w_23 w_24 w_25 CODE MI BUF OK MU WM segs base.
induction k as [|k IH]; intros i x5 x12 x14 x15 x16 x17 Hk Hi HN; pose proof A_bound as AB; [lia|].
destruct (readable i Hi HN) as [b Hn]. pose proof (nth_error_lt _ _ _ Hn).
pose proof (u8ro_read segs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
zstep. zstep. if_cases K; zify_cond K.
-  zstep. rewrite <- (res_found i b Hi HN Hn K). finish.
- zstep. zstep. zstep. if_cases K0; zify_cond K0.
+ replace (n - i + -1)%Z with (n - (i + 1))%Z by lia. replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
apply (IH (i + 1)%Z); try lia. eapply NOB_S; eauto; lia.
+  zstep. zstep. rewrite <- res_none at 1. { finish. }
replace n with (i + 1)%Z by lia. eapply NOB_S; eauto; lia.
Qed.

#[using="w_22 w_23 w_24 w_25 CODE MI BUF OK MU WM"] Lemma memchr_tail_entry : forall (i : Z) (x5 x13 x14 x15 x16 x17 : word),
(0 <= i <= n)%Z -> NOB i ->
evt segs POST (ST (base + 0x98) x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 x15 x16 x17).
Proof. clear - w_22 w_23 w_24 w_25 CODE MI BUF OK MU WM segs base.
intros i x5 x13 x14 x15 x16 x17 Hi HN; pose proof A_bound as AB.
zstep. zstep. if_cases K; zify_cond K.
- zstep. zstep. rewrite <- res_none at 1. { finish. } replace n with i by lia. exact HN.
- apply (memchr_tail (Z.to_nat (n - i)) i); lia || assumption.
Qed.

#[using="w_22 w_23 w_24 w_25 CODE MI BUF OK MU WM"] Lemma memchr_words : forall (k : nat) (i : Z) (x5 x17 : word),
Z.to_nat (n - i) = k -> (0 <= i)%Z -> (i + 8 <= n)%Z -> ((A + i) mod 8 = 0)%Z -> NOB i ->
evt segs POST (ST (base + 0x74) x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS)
(Z_to_bv 64 (c * ONES)) (Z_to_bv 64 7) x17).
Proof. clear - w_22 w_23 w_24 w_25 CODE MI BUF OK MU WM segs base.
induction k as [k IH] using lt_wf_ind; intros i x5 x17 Hk Hi Hi8 Hal HN; pose proof A_bound as AB.
pose proof (readable8 i Hi Hi8 Hal HN) as HW.
pose proof (bytes_at_read segs m A buf i 8 BUF ltac:(lia) HW) as RD.
set (chunk := firstn 8 (skipn (Z.to_nat i) buf)) in RD.
assert (CL : length chunk = 8%nat). { subst chunk. rewrite firstn_length, skipn_length. lia. }
pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
pose proof (le_val_range _ (bytes_ok_xor _ c (bytes_ok_map chunk) ltac:(lia))) as XR. rewrite !length_map, CL in XR.
change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in XR.
do 6 zstep.
rewrite (load8_le_val chunk CL).
replace (Z.lxor (le_val (map bv_unsigned chunk)) (c * ONES)) with (le_val (map (fun b => Z.lxor b c) (map bv_unsigned chunk))).
2:{ change ONES with ONES64b. rewrite <- ones_8, <- CL, <- (length_map bv_unsigned). symmetry. apply le_val_xor_bcast; [apply bytes_ok_map| lia]. }
if_cases K; zify_cond K.
-
clear K. destruct (readable i ltac:(lia) HN) as [b Hn].
pose proof (u8ro_read segs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD1.
zstep. zstep. zstep. if_cases Kb; zify_cond Kb.
+ zstep. zstep. zstep. if_cases Kz; zify_cond Kz; [|exfalso; lia].
replace (n - i + -1)%Z with (n - (i + 1))%Z by lia. replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
apply (memchr_tail (Z.to_nat (n - (i + 1))) (i + 1)); try lia. eapply NOB_S; eauto; lia.
+ zstep. zstep. rewrite <- (res_found i b ltac:(lia) HN Hn Kb). finish.
- apply (haszero64_clang _ (bytes_ok_xor _ c (bytes_ok_map chunk) ltac:(lia)) ltac:(rewrite !length_map; exact CL)) in K.
rewrite In0_xor in K.

assert (HN8 : NOB (i + 8)).
{ intros j b Hj Hn. destruct (Nat.lt_ge_cases j (Z.to_nat i)) as [Hlt|Hge]. { exact (HN _ _ Hlt Hn). }
intros Hb. apply K. rewrite <- Hb. apply in_map. subst chunk.
apply nth_error_In with (n := (j - Z.to_nat i)%nat).
rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
rewrite nth_error_skipn, <- Hn. f_equal. lia. }
zstep. zstep. zstep. if_cases K8; zify_cond K8.
+ replace (A + i + 8)%Z with (A + (i + 8))%Z by lia. replace (n - i + -8)%Z with (n - (i + 8))%Z by lia.
apply (IH (Z.to_nat (n - (i + 8)))); try lia; try exact HN8. all: Z.div_mod_to_equations; lia.
+ replace (A + i + 8)%Z with (A + (i + 8))%Z by lia. replace (n - i + -8)%Z with (n - (i + 8))%Z by lia.
apply (memchr_tail_entry (i + 8)); try lia; exact HN8.
Qed.

#[using="w_22 w_23 w_24 w_25 hi_22 hi_24 lo_23 lo_25 G_10780 G_10790 CODE D_22 E_22 D_23 E_23 D_24 E_24 D_25 E_25 ANCH_23 ANCH_25 RNG_G_10790 ROM_G_10790 RNG_G_10780 ROM_G_10780 MI BUF OK MU WM"] Lemma memchr_mid : forall (i : Z) (x5 x13 x14 x15 x16 x17 : word),
(0 <= i <= n)%Z -> NOB i -> ((bv_unsigned x14 = 0)%Z <-> i = n) -> (i = n \/ (A + i) mod 8 = 0)%Z ->
evt segs POST (ST (base + 0x44) x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 x15 x16 x17).
Proof. clear - w_22 w_23 w_24 w_25 hi_22 hi_24 lo_23 lo_25 G_10780 G_10790 CODE D_22 E_22 D_23 E_23 D_24 E_24 D_25 E_25 ANCH_23 ANCH_25 RNG_G_10790 ROM_G_10790 RNG_G_10780 ROM_G_10780 MI BUF OK MU WM segs base.
intros i x5 x13 x14 x15 x16 x17 Hi HN H14 Hal; pose proof A_bound as AB.
zstep. if_cases K; zify_cond K.
-  apply H14 in K. subst i. zstep. zstep. rewrite <- res_none at 1; [finish| exact HN].
- assert (Hin : (i < n)%Z). { destruct (Z.eq_dec i n) as [E|]; [|lia]. exfalso. apply K. apply H14. exact E. }
destruct Hal as [|Hal]; [lia|].
destruct (readable i ltac:(lia) HN) as [b Hn].
pose proof (u8ro_read segs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
zstep. zstep. if_cases Kb; zify_cond Kb.
+ apply memchr_tail_entry; [lia| exact HN].
+ zstep. zstep. if_cases K8; zify_cond K8.
* apply memchr_tail_entry; [lia| exact HN].
* do 7 zstep.
apply (memchr_words (Z.to_nat (n - i)) i); try lia. exact HN.
Qed.

#[using="a1"] Lemma b2z_word_zero_iff : forall t, bv_unsigned (Z_to_bv 64 (Z.b2z t)) = 0%Z <-> t = false.
Proof. clear - a1. intros t. rewrite unsigned_lit by (destruct t; cbn; lia). destruct t; cbn; split; intros; first [congruence | lia]. Qed.

#[using="w_22 w_23 w_24 w_25 hi_22 hi_24 lo_23 lo_25 G_10780 G_10790 CODE D_22 E_22 D_23 E_23 D_24 E_24 D_25 E_25 ANCH_23 ANCH_25 RNG_G_10790 ROM_G_10790 RNG_G_10780 ROM_G_10780 MI BUF OK MU WM"] Lemma memchr_head : forall (k : nat) (i : Z) (x5 x13 x14 x17 : word),
Z.to_nat (n - i) = k -> (0 <= i < n)%Z -> NOB i -> ((A + i) mod 8 <> 0)%Z ->
evt segs POST (ST (base + 0x1c) x5 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14 (Z_to_bv 64 (A + i + 1)) (Z_to_bv 64 1) x17).
Proof. clear - w_22 w_23 w_24 w_25 hi_22 hi_24 lo_23 lo_25 G_10780 G_10790 CODE D_22 E_22 D_23 E_23 D_24 E_24 D_25 E_25 ANCH_23 ANCH_25 RNG_G_10790 ROM_G_10790 RNG_G_10780 ROM_G_10780 MI BUF OK MU WM segs base.
induction k as [|k IH]; intros i x5 x13 x14 x17 Hk Hi HN Hal; pose proof A_bound as AB; [lia|].
destruct (readable i Hi HN) as [b Hn]. pose proof (nth_error_lt _ _ _ Hn).
pose proof (u8ro_read segs m A buf i b _ BUF Hn ltac:(lia) eq_refl) as RD.
zstep. zstep. zstep. if_cases Kb; zify_cond Kb.
-  apply (memchr_tail (Z.to_nat (n - i)) i); try lia. exact HN.
- pose proof (NOB_S i b ltac:(lia) HN Hn Kb) as HN1.
zstep. zstep. zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
+ replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (n - i + -1)%Z with (n - (i + 1))%Z by lia.
apply (memchr_mid (i + 1)); try lia; try exact HN1.
* rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
* right. revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
+ zstep. zstep. if_cases K1; zify_cond K1.
* replace (A + i + 2)%Z with (A + (i + 1) + 1)%Z by lia.
replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (n - i + -1)%Z with (n - (i + 1))%Z by lia.
apply (IH (i + 1)%Z); try lia; try exact HN1. revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
* replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (n - i + -1)%Z with (n - (i + 1))%Z by lia.
apply (memchr_mid (i + 1)); try lia; try exact HN1. rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
Qed.

#[using="w_22 w_23 w_24 w_25 hi_22 hi_24 lo_23 lo_25 G_10780 G_10790 CODE D_22 E_22 D_23 E_23 D_24 E_24 D_25 E_25 ANCH_23 ANCH_25 RNG_G_10790 ROM_G_10790 RNG_G_10780 ROM_G_10780 MI BUF OK MU WM"] Lemma memchr_body :
evt segs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_24 w_25 hi_22 hi_24 lo_23 lo_25 G_10780 G_10790 CODE D_22 E_22 D_23 E_23 D_24 E_24 D_25 E_25 ANCH_23 ANCH_25 RNG_G_10790 ROM_G_10790 RNG_G_10780 ROM_G_10780 MI BUF OK MU WM segs base.
pose proof A_bound as AB. pose proof (zr_word a1) as R1. unfold inr64 in R1.
zstep. replace (Z.land (bv_unsigned a1) 255) with c.
2:{ change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. }
zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
-
eapply evt_eq.
2:{ apply (memchr_mid 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a5 a6 a7); try lia.
- apply NOB_0. - rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
- right. revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned. reflexivity.
- zstep. if_cases K0; zify_cond K0.
+
eapply evt_eq.
2:{ apply (memchr_mid 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a5 a6 a7); try lia.
- apply NOB_0. - rewrite b2z_word_zero_iff, Z.ltb_ge. lia. }
unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned. reflexivity.
+ zstep. zstep.
eapply evt_eq.
2:{ apply (memchr_head (Z.to_nat n) 0 t0 (Z_to_bv 64 (Z.land A 7)) (Z_to_bv 64 (Z.b2z (0 <? n)%Z)) a7); try lia.
- apply NOB_0. - revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
unfold mkR. rewrite Z_to_bv_plus0, Z.sub_0_r, Z_to_bv_bv_unsigned, Z.add_0_r. reflexivity.
Qed.
End Proofs.

#[using="w_22 w_23 w_24 w_25 hi_22 hi_24 lo_23 lo_25 G_10780 G_10790 CODE D_22 E_22 D_23 E_23 D_24 E_24 D_25 E_25 ANCH_23 ANCH_25 RNG_G_10790 ROM_G_10790 RNG_G_10780 ROM_G_10780"] Lemma memchr_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte),
bytes_at segs m (bv_unsigned a0) buf ->
memchr_ok (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf ->
mem_inv segs m ->
evt segs (memchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_24 w_25 hi_22 hi_24 lo_23 lo_25 G_10780 G_10790 CODE D_22 E_22 D_23 E_23 D_24 E_24 D_25 E_25 ANCH_23 ANCH_25 RNG_G_10790 ROM_G_10790 RNG_G_10780 ROM_G_10780 segs base. intros until buf. intros BUF OK MI. apply memchr_body; assumption. Qed.

End G.
End Mq8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg QgoP Q1jm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun Q9A7.

Import QVbl.Mq3.
Import QgoP Q1jm.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Local Ltac cur_mem_addr ::= g_cur_mem_addr. Local Ltac mkr__cur_mem_addr_3 := g_cur_mem_addr.

Definition memmove_code : list Z :=
[0x08b50663; 0x00a606b3; 0x00161713; 0x40d586b3; 0x40e00733; 0x04d77063; 0x00a5c6b3; 0x0076f693; 0x02b57c63; 0x06068663; 0x00050693; 0x00058713; 0x04060e63; 0x00c68633; 0x00074583; 0x00170713; 0x00168793; 0x00b68023; 0x00078693; 0xfec796e3; 0x03c0006f; 0xba9ff06f; 0x06068c63; 0x00060693; 0x02068663; 0x40d00633; 0xfff68713; 0x00e506b3; 0x00e585b3; 0x0005c703; 0x00160613; 0x00e68023; 0xfff68693; 0xfff58593; 0xfe0616e3; 0x00008067; 0x00757693; 0x0a068c63; 0x00150793; 0x00050813; 0xfe0606e3; 0xfff60613; 0x0005c883; 0x00158713; 0x00180693; 0x0077f293; 0x01180023; 0x00178793; 0x00070593; 0x00068813; 0xfc029ce3; 0x0880006f; 0x00c506b3; 0x0076f693; 0x04068063; 0x40c006b3; 0xfff60713; 0x00e50633; 0x00e58733; 0x00060793; 0xf8068ee3; 0x00074803; 0x01060023; 0x0077f813; 0x00168693; 0xfff78793; 0xfff60613; 0xfff70713; 0xfe0810e3; 0x40d00633; 0x00800693; 0xf4d660e3; 0xff858713; 0xff850793; 0x00700813; 0x00c706b3; 0x0006b883; 0xff860693; 0x00c78633; 0x01163023; 0x00068613; 0xfed864e3; 0xf19ff06f; 0x00050693; 0x00058713; 0x00800593; 0xecb66ce3; 0x00700593; 0x00073783; 0xff860613; 0x00f6b023; 0x00868693; 0x00870713; 0xfec5e6e3; 0xeb9ff06f]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base memmove_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 380.

Definition memcpy_post := Eval cbv beta delta [QVbl.Mq3.memcpy_post] in (QVbl.Mq3.memcpy_post segs).
Hypothesis memcpy_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq3.memcpy_spec segs (base + -1028)%Z) 3%nat in let T := gw_subst T (QVbl.Mq3.memcpy_post segs) memcpy_post in let T := gw_fold_pcs T base (-1028)%Z [0; 24; 72; 80; 96; 104; 116; 136; 164; 288; 300; 348; 380; 408; 428; 540; 576; 684; 824; 832; 908; 916; 960]%Z in exact T).

Definition memmove_entry := (base + 0x0)%Z.

Definition memmove_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rw_cells segs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src].

Definition memmove_stmt : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
bytes_at segs m (bv_unsigned a1) src ->
length src = Z.to_nat (bv_unsigned a2) ->
rw_cells segs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(bv_unsigned a2 < 2^63)%Z ->
mem_inv segs m ->
evt segs (memmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).

#[using="CODE BASE4 BASER memcpy_spec"] Lemma bytes_at_same : forall segs_ m a bs1 bs2, bytes_at segs_ m a bs1 -> bytes_at segs_ m a bs2 ->
length bs1 = length bs2 -> bs1 = bs2.
Proof.
intros segs_ m a bs1 bs2 (_ & _ & H1) (_ & _ & H2) L. apply nth_error_ext. intros i.
destruct (Nat.lt_ge_cases i (length bs1)).
- specialize (H1 i ltac:(lia)). specialize (H2 i ltac:(lia)). rewrite H1 in H2.
destruct (nth_error bs1 i) eqn:E1; destruct (nth_error bs2 i) eqn:E2; cbn in H2; try congruence.
all: exfalso; try (apply nth_error_None in E1; lia); apply nth_error_None in E2; lia.
- rewrite (proj2 (nth_error_None bs1 i)) by lia. rewrite (proj2 (nth_error_None bs2 i)) by lia. reflexivity.
Qed.

Section NoOverlap.
Local Open Scope Z_scope.
#[using="CODE BASE4 BASER memcpy_spec"] Lemma mod_cases : forall x M, 0 < M -> - M <= x < 2 * M ->
x mod M = x \/ x mod M = x + M \/ x mod M = x - M.
Proof. intros x M HM Hx. Z.div_mod_to_equations. assert (q = 0 \/ q = 1 \/ q = -1) by nia. lia. Qed.

#[using="CODE BASE4 BASER memcpy_spec"] Lemma nooverlap_test : forall S D n, 0 <= S -> S + n <= 2^64 -> 0 <= D -> D + n <= 2^64 -> 0 <= n < 2^63 -> D <> S ->
(S - (n + D) mod 18446744073709551616) mod 18446744073709551616 <= (0 - (n * 2) mod 18446744073709551616) mod 18446744073709551616 ->
S + n <= D \/ D + n <= S.
Proof.
intros S D n HS HSn HD HDn Hn NE.
pose proof (mod_cases (n + D) 18446744073709551616 ltac:(lia) ltac:(lia)) as C1.
pose proof (mod_cases (n * 2) 18446744073709551616 ltac:(lia) ltac:(lia)) as C2.
set (a := (n + D) mod 18446744073709551616) in *. set (b := (n * 2) mod 18446744073709551616) in *.
pose proof (Z.mod_pos_bound (n + D) 18446744073709551616 ltac:(lia)) as Ra. fold a in Ra.
pose proof (Z.mod_pos_bound (n * 2) 18446744073709551616 ltac:(lia)) as Rb. fold b in Rb.
pose proof (mod_cases (S - a) 18446744073709551616 ltac:(lia) ltac:(lia)) as C3.
pose proof (mod_cases (0 - b) 18446744073709551616 ltac:(lia) ltac:(lia)) as C4.
pose proof (Z.mod_pos_bound (S - a) 18446744073709551616 ltac:(lia)) as R3.
pose proof (Z.mod_pos_bound (0 - b) 18446744073709551616 ltac:(lia)) as R4.
clearbody a b. intros K. lia.
Qed.
End NoOverlap.

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src : list byte).
Notation S := (bv_unsigned a1).
Notation D := (bv_unsigned a0).
Notation n := (bv_unsigned a2).
Hypothesis LEN : length src = Z.to_nat n.
Hypothesis AB : (0 <= S /\ S + n <= 2^64 /\ 0 <= D /\ D + n <= 2^64 /\ 0 <= n < 2^63)%Z.

Notation POST := (memmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m).
Notation FI := (fwd_inv segs S D n src m).
Notation BI := (bwd_inv segs S D n src m).

Notation ST pc mm x5 x11 x12 x13 x14 x15 x16 x17 :=
(MS (mkR ra sp gp tp x5 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom segs)).

#[using="CODE BASE4 BASER memcpy_spec a0 a1 src LEN AB"] Lemma nlen : (0 <= n)%Z. Proof. lia. Qed.

#[using="CODE BASE4 BASER memcpy_spec LEN"] Lemma src_nth : forall i, (0 <= i < n)%Z -> exists b, nth_error src (Z.to_nat i) = Some b /\ firstn 1 (skipn (Z.to_nat i) src) = [b].
Proof.
intros i Hi. destruct (nth_error src (Z.to_nat i)) as [b|] eqn:E. 2:{ apply nth_error_None in E. rewrite LEN in E. lia. }
exists b. split; [reflexivity|]. apply nth_error_first1. exact E.
Qed.

#[using="CODE BASE4 BASER memcpy_spec LEN"] Lemma fwd_read1 : forall m1 bs P b, FI m1 bs P -> (0 <= P < n)%Z -> nth_error src (Z.to_nat P) = Some b ->
ov_read_bytes segs m1 (Z_to_bv 64 (S + P)) 1 = Some [b].
Proof.
intros m1 bs P b I HP Hb.
rewrite (fwd_read segs _ _ _ src m LEN m1 bs P 1 _ I ltac:(lia) ltac:(lia) ltac:(unfold wa; reflexivity)).
f_equal. apply nth_error_first1. exact Hb.
Qed.
#[using="CODE BASE4 BASER memcpy_spec LEN AB"] Lemma fwd_store1 : forall m1 bs P b, FI m1 bs P -> (D <= S)%Z -> (0 <= P < n)%Z -> nth_error src (Z.to_nat P) = Some b ->
store_ok segs m1 (Z_to_bv 64 (D + P)) 1 = true /\
FI (write_to_mem m1 (Z_to_bv 64 (D + P)) [b]) (upd_bytes bs (Z.to_nat P) [b]) (P + 1).
Proof.
intros m1 bs P b I DS HP Hb.
destruct (fwd_store segs _ _ _ src m LEN m1 bs P 1 [b] _ I DS ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(symmetry; apply nth_error_first1; exact Hb) ltac:(unfold wa; reflexivity)) as [SOK I'].
split; [exact SOK|]. replace (P + 1)%Z with (P + Z.of_nat 1)%Z by lia. exact I'.
Qed.
#[using="CODE BASE4 BASER memcpy_spec LEN"] Lemma fwd_read8 : forall m1 bs P w, FI m1 bs P -> (0 <= P)%Z -> (P + 8 <= n)%Z -> firstn 8 (skipn (Z.to_nat P) src) = w ->
ov_read_bytes segs m1 (Z_to_bv 64 (S + P)) 8 = Some w.
Proof.
intros m1 bs P w I HP HP8 Hw. rewrite <- Hw.
apply (fwd_read segs _ _ _ src m LEN m1 bs P 8 _ I); [lia | lia | unfold wa; reflexivity].
Qed.
#[using="CODE BASE4 BASER memcpy_spec LEN AB"] Lemma fwd_store8 : forall m1 bs P w, FI m1 bs P -> (D <= S)%Z -> (0 <= P)%Z -> (P + 8 <= n)%Z -> firstn 8 (skipn (Z.to_nat P) src) = w ->
store_ok segs m1 (Z_to_bv 64 (D + P)) 8 = true /\
FI (write_to_mem m1 (Z_to_bv 64 (D + P)) w) (upd_bytes bs (Z.to_nat P) w) (P + 8).
Proof.
intros m1 bs P w I DS HP HP8 Hw.
destruct (fwd_store segs _ _ _ src m LEN m1 bs P 8 w _ I DS ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (eq_sym Hw) ltac:(unfold wa; reflexivity)) as [SOK I'].
split; [exact SOK|]. replace (P + 8)%Z with (P + Z.of_nat 8)%Z by lia. exact I'.
Qed.
#[using="CODE BASE4 BASER memcpy_spec LEN"] Lemma bwd_read1 : forall m1 bs Q b, BI m1 bs Q -> (1 <= Q <= n)%Z -> nth_error src (Z.to_nat (Q - 1)) = Some b ->
ov_read_bytes segs m1 (Z_to_bv 64 (S + (Q - 1))) 1 = Some [b].
Proof.
intros m1 bs Q b I HQ Hb.
pose proof (bwd_read segs _ _ _ src m LEN m1 bs Q 1 (Z_to_bv 64 (S + (Q - 1))) I ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as R.
rewrite R. f_equal. replace (Q - Z.of_nat 1)%Z with (Q - 1)%Z by lia. apply nth_error_first1. exact Hb.
Qed.
#[using="CODE BASE4 BASER memcpy_spec LEN AB"] Lemma bwd_store1 : forall m1 bs Q b, BI m1 bs Q -> (S <= D)%Z -> (1 <= Q <= n)%Z -> nth_error src (Z.to_nat (Q - 1)) = Some b ->
store_ok segs m1 (Z_to_bv 64 (D + (Q - 1))) 1 = true /\
BI (write_to_mem m1 (Z_to_bv 64 (D + (Q - 1))) [b]) (upd_bytes bs (Z.to_nat (Q - 1)) [b]) (Q - 1).
Proof.
intros m1 bs Q b I SD HQ Hb.
destruct (bwd_store segs _ _ _ src m LEN m1 bs Q 1 [b] (Z_to_bv 64 (D + (Q - 1))) I SD ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(replace (Q - Z.of_nat 1)%Z with (Q - 1)%Z by lia; symmetry; apply nth_error_first1; exact Hb)
ltac:(unfold wa; f_equal; lia)) as [SOK I'].
split; [exact SOK|]. replace (Q - 1)%Z with (Q - Z.of_nat 1)%Z by lia. exact I'.
Qed.
#[using="CODE BASE4 BASER memcpy_spec LEN"] Lemma bwd_read8 : forall m1 bs Q w, BI m1 bs Q -> (8 <= Q <= n)%Z -> firstn 8 (skipn (Z.to_nat (Q - 8)) src) = w ->
ov_read_bytes segs m1 (Z_to_bv 64 (S + (Q - 8))) 8 = Some w.
Proof.
intros m1 bs Q w I HQ Hw. rewrite <- Hw. replace (Q - 8)%Z with (Q - Z.of_nat 8)%Z by lia.
apply (bwd_read segs _ _ _ src m LEN m1 bs Q 8 _ I); [lia | lia | unfold wa; reflexivity].
Qed.
#[using="CODE BASE4 BASER memcpy_spec LEN AB"] Lemma bwd_store8 : forall m1 bs Q w, BI m1 bs Q -> (S <= D)%Z -> (8 <= Q <= n)%Z -> firstn 8 (skipn (Z.to_nat (Q - 8)) src) = w ->
store_ok segs m1 (Z_to_bv 64 (D + (Q - 8))) 8 = true /\
BI (write_to_mem m1 (Z_to_bv 64 (D + (Q - 8))) w) (upd_bytes bs (Z.to_nat (Q - 8)) w) (Q - 8).
Proof.
intros m1 bs Q w I SD HQ Hw. replace (Q - 8)%Z with (Q - Z.of_nat 8)%Z by lia.
apply (bwd_store segs _ _ _ src m LEN m1 bs Q 8 w _ I SD); try lia. { symmetry. replace (Q - Z.of_nat 8)%Z with (Q - 8)%Z by lia. exact Hw. }
unfold wa; reflexivity.
Qed.

Ltac after_store I' :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?aa ?bb) _) =>
let m2 := fresh "m" in remember (write_to_mem mm aa bb) as m2 eqn:Heqm; clear Heqm;
repeat match goal with H : store_ok _ mm _ _ = true |- _ => clear H | H : ov_read_bytes _ mm _ _ = Some _ |- _ => clear H end;
try clear mm
end; rename I' into I.

#[using="CODE BASE4 BASER memcpy_spec LEN"] Lemma ret_fwd : forall m1 bs P x5 x11 x12 x13 x14 x15 x16 x17,
FI m1 bs P -> (n <= P)%Z -> evt segs POST (ST (base + 0x8c) m1 x5 x11 x12 x13 x14 x15 x16 x17).
Proof.
intros m1 bs P x5 x11 x12 x13 x14 x15 x16 x17 I HP.
destruct (fwd_done segs _ _ _ _ m LEN m1 bs P I HP) as (DST & MI & MU & WM).
zstep. finish2.
Qed.

#[using="CODE BASE4 BASER memcpy_spec LEN"] Lemma ret_bwd : forall m1 bs Q x5 x11 x12 x13 x14 x15 x16 x17,
BI m1 bs Q -> (Q <= 0)%Z -> evt segs POST (ST (base + 0x8c) m1 x5 x11 x12 x13 x14 x15 x16 x17).
Proof.
intros m1 bs Q x5 x11 x12 x13 x14 x15 x16 x17 I HQ.
destruct (bwd_done segs _ _ _ _ m LEN m1 bs Q I HQ) as (DST & MI & MU & WM).
zstep. finish2.
Qed.

Ltac fsb I Hnb DS :=
lazymatch type of I with fwd_inv _ _ _ _ _ _ ?m1 ?bs ?P =>
let SOK := fresh "SOK" in let I' := fresh "I" in
destruct (fwd_store1 m1 bs P _ I ltac:(lia) ltac:(lia) Hnb) as [SOK I'];
clear I; zstep; rewrite le1_zxb; after_store I'
end.
Ltac fsd I Hw DS :=
lazymatch type of I with fwd_inv _ _ _ _ _ _ ?m1 ?bs ?P =>
let SOK := fresh "SOK" in let I' := fresh "I" in
destruct (fwd_store8 m1 bs P _ I ltac:(lia) ltac:(lia) ltac:(lia) Hw) as [SOK I'];
clear I; zstep;
lazymatch goal with |- context [le8 (bv_extract 0 64 (le_bytes_to_word ?w))] =>
lazymatch goal with Lw : length w = 8%nat |- _ => rewrite (le8_ld w Lw) end end;
after_store I'
end.
Ltac bsb I Hnb SD :=
lazymatch type of I with bwd_inv _ _ _ _ _ _ ?m1 ?bs ?Q =>
let SOK := fresh "SOK" in let I' := fresh "I" in
destruct (bwd_store1 m1 bs Q _ I ltac:(lia) ltac:(lia) Hnb) as [SOK I'];
clear I; zstep; rewrite le1_zxb; after_store I'
end.
Ltac bsd I Hw SD :=
lazymatch type of I with bwd_inv _ _ _ _ _ _ ?m1 ?bs ?Q =>
let SOK := fresh "SOK" in let I' := fresh "I" in
destruct (bwd_store8 m1 bs Q _ I ltac:(lia) ltac:(lia) Hw) as [SOK I'];
clear I; zstep;
lazymatch goal with |- context [le8 (bv_extract 0 64 (le_bytes_to_word ?w))] =>
lazymatch goal with Lw : length w = 8%nat |- _ => rewrite (le8_ld w Lw) end end;
after_store I'
end.

#[using="CODE BASE4 BASER memcpy_spec LEN AB"] Lemma fbl : forall (k : nat) m1 bs (P : Z) x5 x11 x15 x16 x17,
FI m1 bs P -> (0 <= P < n)%Z -> Z.to_nat (n - P) = k -> (D < S)%Z ->
evt segs POST (ST (base + 0x38) m1 x5 x11 (Z_to_bv 64 (D + n)) (Z_to_bv 64 (D + P)) (Z_to_bv 64 (S + P)) x15 x16 x17).
Proof.
induction k as [|k IH]; intros m1 bs P x5 x11 x15 x16 x17 I HP Hk DS; [lia|].
destruct (src_nth P ltac:(lia)) as (b & Hnb & Hb). pose proof (byte_range8 b) as BR.
pose proof (fwd_read1 m1 bs P b I ltac:(lia) Hnb) as RD.
zstep. zstep. zstep.
fsb I Hnb DS.
zstep. zstep. if_cases K; zify_cond K.
- replace (D + P + 1)%Z with (D + (P + 1))%Z by lia. replace (S + P + 1)%Z with (S + (P + 1))%Z by lia.
eapply (IH _ _ (P + 1)%Z); [exact I | lia | lia | lia].
- zstep. eapply ret_fwd; [exact I | lia].
Qed.

#[using="CODE BASE4 BASER memcpy_spec LEN"] Lemma src_win8 : forall i, (0 <= i)%Z -> (i + 8 <= n)%Z ->
exists w, firstn 8 (skipn (Z.to_nat i) src) = w /\ length w = 8%nat.
Proof. intros i Hi Hn. eexists. split; [reflexivity|]. rewrite length_firstn, length_skipn, LEN. lia. Qed.

#[using="CODE BASE4 BASER memcpy_spec LEN AB"] Lemma fb : forall m1 bs (P : Z) x5 x11 x15 x16 x17,
FI m1 bs P -> (0 <= P <= n)%Z -> (D < S)%Z ->
evt segs POST (ST (base + 0x30) m1 x5 x11 (Z_to_bv 64 (n - P)) (Z_to_bv 64 (D + P)) (Z_to_bv 64 (S + P)) x15 x16 x17).
Proof.
intros m1 bs P x5 x11 x15 x16 x17 I HP DS.
zstep. if_cases K; zify_cond K.
- eapply ret_fwd; [exact I | lia].
- zstep. replace (D + P + (n - P))%Z with (D + n)%Z by lia.
eapply (fbl (Z.to_nat (n - P)) _ _ P); [exact I | lia | lia | lia].
Qed.

#[using="CODE BASE4 BASER memcpy_spec LEN AB"] Lemma fwl : forall (k : nat) m1 bs (P : Z) x5 x15 x16 x17,
FI m1 bs P -> (0 <= P)%Z -> (P + 8 <= n)%Z -> Z.to_nat (n - P) = k -> (D < S)%Z ->
evt segs POST (ST (base + 0x160) m1 x5 (Z_to_bv 64 7) (Z_to_bv 64 (n - P)) (Z_to_bv 64 (D + P)) (Z_to_bv 64 (S + P)) x15 x16 x17).
Proof.
induction k as [k IH] using lt_wf_ind; intros m1 bs P x5 x15 x16 x17 I HP HP8 Hk DS.
destruct (src_win8 P ltac:(lia) ltac:(lia)) as (w & Hw & Lw).
pose proof (fwd_read8 m1 bs P w I ltac:(lia) ltac:(lia) Hw) as RD.
zstep. zstep.
fsd I Hw DS.
zstep. zstep. zstep. if_cases K; zify_cond K.
- replace (D + P + 8)%Z with (D + (P + 8))%Z by lia. replace (S + P + 8)%Z with (S + (P + 8))%Z by lia.
replace (n - P + -8)%Z with (n - (P + 8))%Z by lia.
unshelve (eapply (IH (Z.to_nat (n - (P + 8))) _ _ _ (P + 8)%Z _ _ _ _ I)); lia.
- zstep. replace (D + P + 8)%Z with (D + (P + 8))%Z by lia. replace (S + P + 8)%Z with (S + (P + 8))%Z by lia.
replace (n - P + -8)%Z with (n - (P + 8))%Z by lia.
eapply (fb _ _ (P + 8)%Z); [exact I | lia | lia].
Qed.

#[using="CODE BASE4 BASER memcpy_spec LEN AB"] Lemma fw : forall m1 bs (P : Z) x5 x11 x15 x16 x17,
FI m1 bs P -> (0 <= P <= n)%Z -> (D < S)%Z ->
evt segs POST (ST (base + 0x154) m1 x5 x11 (Z_to_bv 64 (n - P)) (Z_to_bv 64 (D + P)) (Z_to_bv 64 (S + P)) x15 x16 x17).
Proof.
intros m1 bs P x5 x11 x15 x16 x17 I HP DS.
zstep. zstep. if_cases K; zify_cond K.
- eapply fb; [exact I | lia | lia].
- zstep. eapply (fwl (Z.to_nat (n - P)) _ _ P); [exact I | lia | lia | lia | lia].
Qed.

#[using="CODE BASE4 BASER memcpy_spec LEN AB"] Lemma fh : forall (k : nat) m1 bs (P : Z) x5 x13 x14 x17,
FI m1 bs P -> (0 <= P <= n)%Z -> Z.to_nat (n - P) = k -> (D < S)%Z ->
evt segs POST (ST (base + 0xa0) m1 x5 (Z_to_bv 64 (S + P)) (Z_to_bv 64 (n - P)) x13 x14 (Z_to_bv 64 (D + P + 1)) (Z_to_bv 64 (D + P)) x17).
Proof.
induction k as [|k IH]; intros m1 bs P x5 x13 x14 x17 I HP Hk DS.
- zstep. if_cases K; zify_cond K. 2:{ exfalso. lia. } eapply ret_fwd; [exact I | lia].
- zstep. if_cases K; zify_cond K. { eapply ret_fwd; [exact I | lia]. }
destruct (src_nth P ltac:(lia)) as (b & Hnb & Hb). pose proof (byte_range8 b) as BR.
pose proof (fwd_read1 m1 bs P b I ltac:(lia) Hnb) as RD.
zstep. zstep. zstep. zstep. zstep.
fsb I Hnb DS.
zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
+ replace (D + P + 1)%Z with (D + (P + 1))%Z by lia. replace (S + P + 1)%Z with (S + (P + 1))%Z by lia.
replace (n - P + -1)%Z with (n - (P + 1))%Z by lia. replace (D + P + 2)%Z with (D + (P + 1) + 1)%Z by lia.
eapply (IH _ _ (P + 1)%Z); [exact I | lia | lia | lia].
+ zstep. replace (D + P + 1)%Z with (D + (P + 1))%Z by lia. replace (S + P + 1)%Z with (S + (P + 1))%Z by lia.
replace (n - P + -1)%Z with (n - (P + 1))%Z by lia.
eapply (fw _ _ (P + 1)%Z); [exact I | lia | lia].
Qed.

#[using="CODE BASE4 BASER memcpy_spec a2 src LEN"] Lemma negc_word : forall q, Z_to_bv 64 ((0 - q) mod 18446744073709551616) = Z_to_bv 64 (18446744073709551616 - q).
Proof. intros q. apply Z_to_bv_eqm. Z.div_mod_to_equations. lia. Qed.

#[using="CODE BASE4 BASER memcpy_spec LEN AB"] Lemma bbl : forall (k : nat) m1 bs (q : Z) x5 x14 x15 x16 x17,
BI m1 bs q -> (1 <= q <= n)%Z -> Z.to_nat q = k -> (S < D)%Z ->
evt segs POST (ST (base + 0x74) m1 x5 (Z_to_bv 64 (S + (q - 1))) (Z_to_bv 64 (18446744073709551616 - q)) (Z_to_bv 64 (D + (q - 1))) x14 x15 x16 x17).
Proof.
induction k as [|k IH]; intros m1 bs q x5 x14 x15 x16 x17 I Hq Hk SD; [lia|].
destruct (src_nth (q - 1) ltac:(lia)) as (b & Hnb & _). pose proof (byte_range8 b) as BR.
pose proof (bwd_read1 m1 bs q b I ltac:(lia) Hnb) as RD.
zstep. zstep.
bsb I Hnb SD.
zstep. zstep. zstep. if_cases K; zify_cond K.
-
assert (Hq2 : (2 <= q)%Z). { destruct (Z.eq_dec q 1) as [->|]; [|lia]. exfalso. apply K. rewrite ?Z.mod_same; try reflexivity; lia. }
replace (S + (q - 1) + -1)%Z with (S + (q - 1 - 1))%Z by lia. replace (D + (q - 1) + -1)%Z with (D + (q - 1 - 1))%Z by lia.
replace (18446744073709551616 - q + 1)%Z with (18446744073709551616 - (q - 1))%Z by lia.
eapply (IH _ _ (q - 1)%Z); [exact I | lia | lia | lia].
- eapply ret_bwd; [exact I|].
destruct (Z.eq_dec q 1) as [->|NE]; [lia|]. exfalso. rewrite Z.mod_small in K by lia. lia.
Qed.

#[using="CODE BASE4 BASER memcpy_spec LEN AB"] Lemma bb2 : forall m1 bs (Q : Z) x5 x12 x14 x15 x16 x17,
BI m1 bs Q -> (0 <= Q <= n)%Z -> (S < D)%Z ->
evt segs POST (ST (base + 0x60) m1 x5 a1 x12 (Z_to_bv 64 Q) x14 x15 x16 x17).
Proof.
intros m1 bs Q x5 x12 x14 x15 x16 x17 I HQ SD.
zstep. if_cases K; zify_cond K.
- eapply ret_bwd; [exact I | lia].
- zstep. zstep. zstep. zstep.
replace (Z_to_bv 64 (0 - Q)) with (Z_to_bv 64 (18446744073709551616 - Q)) by (apply Z_to_bv_eqm; Z.div_mod_to_equations; lia).
replace (S + (Q + -1))%Z with (S + (Q - 1))%Z by lia. replace (D + (Q + -1))%Z with (D + (Q - 1))%Z by lia.
eapply (bbl (Z.to_nat Q) _ _ Q); [exact I | lia | lia | lia].
Qed.

#[using="CODE BASE4 BASER memcpy_spec LEN AB"] Lemma bb : forall m1 bs (Q : Z) x5 x13 x14 x15 x16 x17,
BI m1 bs Q -> (0 <= Q <= n)%Z -> (S < D)%Z ->
evt segs POST (ST (base + 0x5c) m1 x5 a1 (Z_to_bv 64 Q) x13 x14 x15 x16 x17).
Proof.
intros m1 bs Q x5 x13 x14 x15 x16 x17 I HQ SD. zstep. eapply bb2; [exact I | lia | lia].
Qed.

#[using="CODE BASE4 BASER memcpy_spec LEN AB"] Lemma bwl : forall (k : nat) m1 bs (Q : Z) x5 x13 x17,
BI m1 bs Q -> (8 <= Q <= n)%Z -> Z.to_nat Q = k -> (S < D)%Z ->
evt segs POST (ST (base + 0x12c) m1 x5 a1 (Z_to_bv 64 Q) x13 (Z_to_bv 64 (S + -8)) (Z_to_bv 64 (D + -8)) (Z_to_bv 64 7) x17).
Proof.
induction k as [k IH] using lt_wf_ind; intros m1 bs Q x5 x13 x17 I HQ Hk SD.
assert (HW : exists w, firstn 8 (skipn (Z.to_nat (Q - 8)) src) = w /\ length w = 8%nat).
{ eexists. split; [reflexivity|]. rewrite length_firstn, length_skipn, LEN. lia. }
destruct HW as (w & Hw & Lw).
pose proof (bwd_read8 m1 bs Q w I ltac:(lia) Hw) as RD.
zstep. zstep. zstep. zstep.
bsd I Hw SD.
zstep. zstep. if_cases K; zify_cond K.
- replace (Q + -8)%Z with (Q - 8)%Z by lia.
unshelve (eapply (IH (Z.to_nat (Q - 8)) _ _ _ (Q - 8)%Z _ _ _ I)); lia.
- zstep. replace (Q + -8)%Z with (Q - 8)%Z by lia. eapply (bb2 _ _ (Q - 8)%Z); [exact I | lia | lia].
Qed.

#[using="CODE BASE4 BASER memcpy_spec LEN AB"] Lemma bw : forall m1 bs (Q : Z) x5 x13 x14 x15 x16 x17,
BI m1 bs Q -> (0 <= Q <= n)%Z -> (S < D)%Z ->
evt segs POST (ST (base + 0x118) m1 x5 a1 (Z_to_bv 64 Q) x13 x14 x15 x16 x17).
Proof.
intros m1 bs Q x5 x13 x14 x15 x16 x17 I HQ SD.
zstep. zstep. if_cases K; zify_cond K.
- eapply bb; [exact I | lia | lia].
- zstep. zstep. zstep. eapply (bwl (Z.to_nat Q) _ _ Q); [exact I | lia | lia | lia].
Qed.

#[using="CODE BASE4 BASER memcpy_spec LEN AB"] Lemma bh : forall (k : nat) m1 bs (Q c3 : Z) x5 x16 x17,
BI m1 bs Q -> (0 <= Q <= n)%Z -> Z.to_nat Q = k -> (S < D)%Z -> c3 = (18446744073709551616 - Q)%Z ->
evt segs POST (ST (base + 0xf0) m1 x5 a1 (Z_to_bv 64 (D + (Q - 1))) (Z_to_bv 64 c3) (Z_to_bv 64 (S + (Q - 1)))
(Z_to_bv 64 (D + (Q - 1))) x16 x17).
Proof.
induction k as [|k IH]; intros m1 bs Q c3 x5 x16 x17 I HQ Hk SD Hc3.
- zstep. if_cases K; zify_cond K.
2:{ exfalso. apply K. subst c3. replace Q with 0%Z by lia. reflexivity. }
eapply ret_bwd; [exact I | lia].
- zstep. if_cases K; zify_cond K. { exfalso. subst c3. revert K. Z.div_mod_to_equations. lia. }
destruct (src_nth (Q - 1) ltac:(lia)) as (b & Hnb & _). pose proof (byte_range8 b) as BR.
pose proof (bwd_read1 m1 bs Q b I ltac:(lia) Hnb) as RD.
zstep.
bsb I Hnb SD.
zstep. zstep. zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
+ replace (D + (Q - 1) + -1)%Z with (D + (Q - 1 - 1))%Z by lia. replace (S + (Q - 1) + -1)%Z with (S + (Q - 1 - 1))%Z by lia.
eapply (IH _ _ (Q - 1)%Z (c3 + 1)%Z); [exact I | lia | lia | lia | lia].
+ zstep.
let v := reg_val 12%Z in replace v with (Z_to_bv 64 (Q - 1)) by (apply Z_to_bv_eqm; Z.div_mod_to_equations; lia).
eapply (bw _ _ (Q - 1)%Z); [exact I | lia | lia].
Qed.

#[using="CODE BASE4 BASER memcpy_spec LEN AB"] Lemma memmove_body : forall junk,
bytes_at segs m S src -> rw_cells segs m D [CB (Z.to_nat n) junk] -> mem_inv segs m ->
evt segs POST (ST (base + 0x0) m t0 a1 a2 a3 a4 a5 a6 a7).
Proof.
intros junk SRC DST MI.
pose proof (munch_refl [(D, D + n)]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
zstep. if_cases Keq; zify_cond Keq.
-
assert (Ejunk : junk = src).
{ pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as [DB _]. rewrite Keq in DB.
eapply (bytes_at_same segs m S); [exact DB | exact SRC | rewrite (rw_cells_CB_length _ _ _ _ _ DST), LEN; reflexivity]. }
subst junk. zstep. finish2.
- do 5 zstep. if_cases Kcpy; zify_cond Kcpy.
+
zstep. eapply evt_mono.
{ eapply memcpy_spec; [exact SRC | exact LEN | exact DST | | exact MI].
rewrite Z.shiftl_mul_pow2 in Kcpy by lia. change (2 ^ 1)%Z with 2%Z in Kcpy.
apply (nooverlap_test S D n); try lia; exact Kcpy. }
intros ms' PO. cbv beta delta [memcpy_post] in PO. destruct_exs PO. destruct PO as (E & MU' & WM' & MI' & DST' & _).
red. do 15 eexists. split; [exact E|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'| exact DST'].
+ do 3 zstep. if_cases Kdir; zify_cond Kdir.
*
pose proof (bwd_init segs _ _ _ src m LEN m junk DST SRC MI MU WM) as I.
zstep. if_cases Kal; zify_cond Kal.
-- do 3 zstep. if_cases Kal2; zify_cond Kal2.
++ eapply evt_eq. 2:{ eapply (bw _ _ n); [exact I | lia | lia]. }
unfold mkR. rewrite !Z_to_bv_lit_self. reflexivity.
++ do 5 zstep.
let v := reg_val 13%Z in replace v with (Z_to_bv 64 (18446744073709551616 - n)) by (apply Z_to_bv_eqm; Z.div_mod_to_equations; lia).
replace (D + (n + -1))%Z with (D + (n - 1))%Z by lia. replace (S + (n + -1))%Z with (S + (n - 1))%Z by lia.
eapply (bh (Z.to_nat n) _ _ n); [exact I | lia | lia | lia | lia].
-- eapply evt_eq. 2:{ eapply (bb _ _ n); [exact I | lia | lia]. }
unfold mkR. rewrite !Z_to_bv_lit_self. reflexivity.
*
pose proof (fwd_init segs _ _ _ src m LEN m junk DST SRC MI MU WM) as I.
zstep. if_cases Kal; zify_cond Kal.
-- do 2 zstep. if_cases Kal2; zify_cond Kal2.
++ do 2 zstep. eapply evt_eq. 2:{ eapply (fw _ _ 0%Z); [exact I | lia | lia]. }
unfold mkR. rewrite Z.sub_0_r, !Z.add_0_r, !Z_to_bv_lit_self. reflexivity.
++ do 2 zstep. eapply evt_eq. 2:{ eapply (fh (Z.to_nat n) _ _ 0%Z); [exact I | lia | lia | lia]. }
unfold mkR. rewrite Z.sub_0_r, !Z.add_0_r, !Z_to_bv_lit_self. reflexivity.
-- do 2 zstep. eapply evt_eq. 2:{ eapply (fb _ _ 0%Z); [exact I | lia | lia]. }
unfold mkR. rewrite Z.sub_0_r, !Z.add_0_r, !Z_to_bv_lit_self. reflexivity.
Qed.
End Proofs.

#[using="CODE BASE4 BASER memcpy_spec"] Lemma memmove_spec : memmove_stmt.
Proof.
unfold memmove_stmt. intros until junk. intros SRC LEN DST N63 MI.
eapply memmove_body; try eassumption.
pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
pose proof (bytes_at_bound _ _ _ _ SRC) as B2.
pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. lia.
Qed.

End G.
End Mq9.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1.
Import QZAi QqdR.
Import QnDM_c1.

Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.

Definition signbitl_code : list Z :=
[0x03f5d513; 0x00008067]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base signbitl_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 8.

#[using="CODE BASE4 BASER"] Lemma gw_all : True. Proof. exact I. Qed.

Definition signbitl_entry := (base + 0x0)%Z.

Definition signbitl_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom segs)
/\ munch [] m m /\ wmono segs m m /\ mem_inv segs m.

#[using="CODE"] Lemma signbitl_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
mem_inv segs m ->
evt segs (signbitl_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
(signbitl (bv_unsigned a0 + 2^64 * bv_unsigned a1)) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof. clear - CODE segs base.
intros until m. intros MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM. pose_word_ranges.
unfold signbitl. rewrite hi64_words by lia.
zstep. zstep. sf_finish.
Qed.

End G.
End Mqa.

Module Mqb.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.

Definition strlen_code (w_15 w_16 w_17 w_18 : Z) : list Z :=
[0x00757593; 0x00050613; 0x02058a63; 0x00054583; 0x06058c63; 0x00150613; 0x00050593; 0x00158693; 0x0076f693; 0x00068c63; 0x00064683; 0x00160613; 0x00158593; 0xfe0694e3; 0x0480006f; w_15; w_16; w_17; w_18; 0xff760593; 0xff860613; 0x00863783; 0x00860613; 0x40f68833; 0x00f867b3; 0x00e7f7b3; 0x00858593; 0xfee784e3; 0x00064683; 0x00160613; 0x00158593; 0xfe069ae3; 0x40a58533; 0x00008067; 0x40a50533; 0x00008067]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_15 w_16 w_17 w_18 : Z).
Variables (hi_15 hi_16 : bv 20).
Variables (lo_17 lo_18 : bv 12).
Variables (G_10780 G_10790 : Z).
Hypothesis CODE : code_at segs base (strlen_code w_15 w_16 w_17 w_18).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 144.
Hypothesis D_15 : decode_any (Z_to_bv 32 w_15) = Some (Auipc 11 hi_15, 4%Z).
Hypothesis E_15 : is_ecall (Z_to_bv 32 w_15) = false.
Hypothesis D_16 : decode_any (Z_to_bv 32 w_16) = Some (Auipc 14 hi_16, 4%Z).
Hypothesis E_16 : is_ecall (Z_to_bv 32 w_16) = false.
Hypothesis D_17 : decode_any (Z_to_bv 32 w_17) = Some (Load SZ8 true 13 11 lo_17, 4%Z).
Hypothesis E_17 : is_ecall (Z_to_bv 32 w_17) = false.
Hypothesis D_18 : decode_any (Z_to_bv 32 w_18) = Some (Load SZ8 true 14 14 lo_18, 4%Z).
Hypothesis E_18 : is_ecall (Z_to_bv 32 w_18) = false.
Hypothesis ANCH_17 : gw_anch (Z.shiftl (bv_signed hi_15) 12 + (base + 60) + bv_signed lo_17)%Z G_10790.
Hypothesis ANCH_18 : gw_anch (Z.shiftl (bv_signed hi_16) 12 + (base + 64) + bv_signed lo_18)%Z G_10780.
Hypothesis RNG_G_10790 : gw_br G_10790 8.
Hypothesis ROM_G_10790 : ro_bytes segs G_10790 (le8 (Z_to_bv 64 72340172838076672)).
Hypothesis RNG_G_10780 : gw_br G_10780 8.
Hypothesis ROM_G_10780 : ro_bytes segs G_10780 (le8 (Z_to_bv 64 9259542123273814144)).

#[using="CODE BASE4 BASER D_15 E_15 D_16 E_16 D_17 E_17 D_18 E_18 ANCH_17 ANCH_18 RNG_G_10790 ROM_G_10790 RNG_G_10780 ROM_G_10780"] Lemma gw_all : True. Proof. exact I. Qed.

Definition strlen_entry := (base + 0x0)%Z.

Definition strlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 : word) (str slack : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ bytes_at segs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str slack : list byte).
Hypothesis MI : mem_inv segs m.
Hypothesis STR : bytes_at segs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).
Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
Hypothesis PAD : ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z.
Let MU : munch [] m m := munch_refl [] m.
Let WM : wmono segs m m := wmono_refl segs m.

Notation A := (bv_unsigned a0).
Notation len := (Z.of_nat (length str)).
Notation full := (str ++ Z_to_bv 8 0 :: slack).
Notation POST := (strlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack m).

Notation ST pc x11 x12 x13 x14 x15 x16 :=
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom segs)).
Notation CMAGIC := 72340172838076672%Z.
Notation HIGHS := 9259542123273814144%Z.

#[using="a0"] Lemma full_length : length full = (length str + S (length slack))%nat.
Proof. clear - a0. rewrite length_app. cbn. lia. Qed.

#[using="segs m STR"] Lemma A_bound : (0 <= A /\ A + len + 1 + Z.of_nat (length slack) <= 2^64)%Z.
Proof. clear - segs m STR. pose proof (bytes_at_bound _ _ _ _ STR) as B. rewrite full_length in B. lia. Qed.

#[using="a0 NONUL"] Lemma full_nth_lt : forall i, (0 <= i < len)%Z ->
exists b, nth_error full (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z.
Proof. clear - a0 NONUL.
intros i Hi. destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E.
- exists b. split. { rewrite nth_error_app1 by lia. exact E. }
intros Hb. apply NONUL. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. }
apply bv_eq. rewrite Hb. reflexivity.
- apply nth_error_None in E. lia.
Qed.

#[using="a0"] Lemma full_nth_len : nth_error full (Z.to_nat len) = Some (Z_to_bv 8 0).
Proof. clear - a0. rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.

#[using="w_15 w_16 w_17 w_18 CODE MI STR NONUL MU WM"] Lemma strlen_tail : forall (k : nat) (i : Z) (a3 a4 a5 a6 : word),
(Z.to_nat (len - i) = k) -> (0 <= i <= len)%Z ->
evt segs POST (ST (base + 0x70) (Z_to_bv 64 (A + i - 1)) (Z_to_bv 64 (A + i)) a3 a4 a5 a6).
Proof. clear - w_15 w_16 w_17 w_18 CODE MI STR NONUL MU WM segs base.
induction k as [|k IH]; intros i a3 a4 a5 a6 Hk Hi; pose proof A_bound as AB.
- assert (Ei : i = len) by lia. subst i.
pose proof (u8ro_read segs m A full len _ _ STR full_nth_len ltac:(lia) eq_refl) as RD.
do 4 zstep. if_false. zstep. zstep.
replace (A + len - 1 + 1 - A)%Z with len by lia. finish.
- destruct (full_nth_lt i ltac:(lia)) as (b & Hn & Hb).
pose proof (u8ro_read segs m A full i b _ STR Hn ltac:(lia) eq_refl) as RD.
do 4 zstep. if_cases K; zify_cond K. 2:{ exfalso. exact (Hb K). }
replace (A + i - 1 + 1)%Z with (A + (i + 1) - 1)%Z by lia.
replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
apply (IH (i + 1)%Z); lia.
Qed.

#[using="w_15 w_16 w_17 w_18 CODE MI STR NONUL PAD MU WM"] Lemma strlen_words : forall (k : nat) (j : Z) (a5 a6 : word),
(Z.to_nat (len - j) = k) -> (0 <= j <= len)%Z -> ((A + j) mod 8 = 0)%Z ->
evt segs POST (ST (base + 0x54) (Z_to_bv 64 (A + j - 9)) (Z_to_bv 64 (A + j - 8)) (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS) a5 a6).
Proof. clear - w_15 w_16 w_17 w_18 CODE MI STR NONUL PAD MU WM segs base.
induction k as [k IH] using lt_wf_ind; intros j a5 a6 Hk Hj Hal; pose proof A_bound as AB.
assert (HW : (Z.to_nat j + 8 <= length full)%nat).
{ rewrite full_length. Z.div_mod_to_equations. lia. }
pose proof (bytes_at_read segs m A full j 8 STR ltac:(lia) HW) as RD.
set (chunk := firstn 8 (skipn (Z.to_nat j) full)) in RD.
assert (CL : length chunk = 8%nat). { subst chunk. rewrite firstn_length, skipn_length. lia. }
pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
do 7 zstep.
replace (A + j - 8 + 8)%Z with (A + j)%Z by lia.
replace (A + j - 9 + 8)%Z with (A + j - 1)%Z by lia.
rewrite (load8_le_val chunk CL).
if_cases K; zify_cond K.
-
apply (haszero64_clang _ (bytes_ok_map chunk) ltac:(rewrite length_map; exact CL)) in K.
rewrite In0_map_unsigned in K.
assert (Hj8 : (j + 8 <= len)%Z).
{ destruct (Z.lt_ge_cases len (j + 8)); [|assumption]. exfalso. apply K. subst chunk.
apply nth_error_In with (n := (Z.to_nat len - Z.to_nat j)%nat).
rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
rewrite nth_error_skipn, <- full_nth_len. f_equal. lia. }
replace (A + j - 1)%Z with (A + (j + 8) - 9)%Z by lia.
replace (Z_to_bv 64 (A + j)) with (Z_to_bv 64 (A + (j + 8) - 8)) by (f_equal; lia).
apply (IH (Z.to_nat (len - (j + 8)))); try lia. all: Z.div_mod_to_equations; lia.
-
apply (strlen_tail (Z.to_nat (len - j)) j); lia.
Qed.

#[using="w_15 w_16 w_17 w_18 hi_15 hi_16 lo_17 lo_18 G_10780 G_10790 CODE D_15 E_15 D_16 E_16 D_17 E_17 D_18 E_18 ANCH_17 ANCH_18 RNG_G_10790 ROM_G_10790 RNG_G_10780 ROM_G_10780 MI STR NONUL PAD MU WM"] Lemma strlen_wentry : forall (j : Z) (a1 a3 a4 a5 a6 : word),
(0 <= j <= len)%Z -> ((A + j) mod 8 = 0)%Z ->
evt segs POST (ST (base + 0x3c) a1 (Z_to_bv 64 (A + j)) a3 a4 a5 a6).
Proof. clear - w_15 w_16 w_17 w_18 hi_15 hi_16 lo_17 lo_18 G_10780 G_10790 CODE D_15 E_15 D_16 E_16 D_17 E_17 D_18 E_18 ANCH_17 ANCH_18 RNG_G_10790 ROM_G_10790 RNG_G_10780 ROM_G_10780 MI STR NONUL PAD MU WM segs base.
intros j a1 a3 a4 a5 a6 Hj Hal. pose proof A_bound as AB.
do 6 zstep.
replace (A + j + -9)%Z with (A + j - 9)%Z by lia.
replace (A + j + -8)%Z with (A + j - 8)%Z by lia.
apply (strlen_words (Z.to_nat (len - j)) j); lia.
Qed.

#[using="w_15 w_16 w_17 w_18 hi_15 hi_16 lo_17 lo_18 G_10780 G_10790 CODE D_15 E_15 D_16 E_16 D_17 E_17 D_18 E_18 ANCH_17 ANCH_18 RNG_G_10790 ROM_G_10790 RNG_G_10780 ROM_G_10780 MI STR NONUL PAD MU WM"] Lemma strlen_head : forall (k : nat) (i : Z) (a3 a4 a5 a6 : word),
(Z.to_nat (len - i) = k) -> (0 <= i < len)%Z ->
evt segs POST (ST (base + 0x1c) (Z_to_bv 64 (A + i)) (Z_to_bv 64 (A + i + 1)) a3 a4 a5 a6).
Proof. clear - w_15 w_16 w_17 w_18 hi_15 hi_16 lo_17 lo_18 G_10780 G_10790 CODE D_15 E_15 D_16 E_16 D_17 E_17 D_18 E_18 ANCH_17 ANCH_18 RNG_G_10790 ROM_G_10790 RNG_G_10780 ROM_G_10780 MI STR NONUL PAD MU WM segs base.
induction k as [|k IH]; intros i a3 a4 a5 a6 Hk Hi; pose proof A_bound as AB; [lia|].
do 3 zstep. if_cases Kal; zify_cond Kal.
- replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
apply strlen_wentry; [lia|]. revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
- destruct (Z.eq_dec (i + 1) len) as [E|NE].
+ pose proof (u8ro_read segs m A full len _ _ STR full_nth_len ltac:(lia) eq_refl) as RD.
do 4 zstep. if_false. do 3 zstep.
replace (A + i + 1 - A)%Z with len by lia. finish.
+ destruct (full_nth_lt (i + 1) ltac:(lia)) as (b & Hn & Hb).
pose proof (u8ro_read segs m A full (i + 1) b _ STR Hn ltac:(lia) eq_refl) as RD.
replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
do 4 zstep. if_cases K; zify_cond K. 2:{ exfalso. exact (Hb K). }
replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
apply (IH (i + 1)%Z); lia.
Qed.
End Proofs.

#[using="w_15 w_16 w_17 w_18 hi_15 hi_16 lo_17 lo_18 G_10780 G_10790 CODE D_15 E_15 D_16 E_16 D_17 E_17 D_18 E_18 ANCH_17 ANCH_18 RNG_G_10790 ROM_G_10790 RNG_G_10780 ROM_G_10780"] Lemma strlen_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte),
bytes_at segs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
~ In (Z_to_bv 8 0) str ->
((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
mem_inv segs m ->
evt segs (strlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof. clear - w_15 w_16 w_17 w_18 hi_15 hi_16 lo_17 lo_18 G_10780 G_10790 CODE D_15 E_15 D_16 E_16 D_17 E_17 D_18 E_18 ANCH_17 ANCH_18 RNG_G_10790 ROM_G_10790 RNG_G_10780 ROM_G_10780 segs base.
intros until slack. intros STR NONUL PAD MI.
pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM.
do 3 zstep. if_cases Kal; zify_cond Kal.
-
eapply evt_eq.
2:{ eapply (strlen_wentry _ _ _ _ _ _ _ _ _ a0) with (j := 0%Z); try eassumption; try lia.
revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
unfold mkR. rewrite Z_to_bv_plus0. reflexivity.
- destruct str as [|c str'] eqn:Es.
+
pose proof (u8ro_read segs m (bv_unsigned a0) _ 0 _ a0 STR eq_refl ltac:(lia) ltac:(symmetry; apply Z_to_bv_plus0)) as RD.
do 2 zstep. if_true. do 2 zstep.
replace (bv_unsigned a0 - bv_unsigned a0)%Z with 0%Z by lia. finish.
+ assert (Hc : bv_unsigned c <> 0%Z).
{ intros Hc. apply NONUL. left. apply bv_eq. rewrite Hc. reflexivity. }
pose proof (u8ro_read segs m (bv_unsigned a0) _ 0 _ a0 STR eq_refl ltac:(lia) ltac:(symmetry; apply Z_to_bv_plus0)) as RD.
do 2 zstep. if_cases K; zify_cond K. { exfalso. exact (Hc K). }
do 2 zstep.
eapply evt_eq.
2:{ eapply (strlen_head _ _ _ _ _ _ _ _ _ a0) with (i := 0%Z) (k := length (c :: str')); try eassumption; cbn [length]; lia. }
unfold mkR. rewrite Z.add_0_r, Z_to_bv_lit_self. reflexivity.
Qed.

End G.
End Mqb.

Module Mqc.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QnDM_c1.

Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Local Open Scope Z_scope.

Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenSF OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.

Definition trunctfdf2_code : list Z :=
[0xffffc637; 0x00159713; 0x01059693; 0x3ff6061b; 0x03175713; 0x00c70633; 0x7fd00793; 0x0106d693; 0x02c7ea63; 0x03c55713; 0x00469693; 0x00451793; 0x00100813; 0x00d76533; 0x0047d693; 0x03b81713; 0x00170793; 0x00160613; 0x04f6ec63; 0x00150513; 0x05c0006f; 0x00d56633; 0x02060863; 0x00008637; 0xfff6061b; 0x02c71263; 0x03c55513; 0x00469693; 0x00100613; 0x03361613; 0x00c56533; 0x00d56533; 0x7ff00613; 0x0380006f; 0x00004637; 0x3fe6079b; 0x04e7f463; 0x00000513; 0x7ff00613; 0x0200006f; 0x00e69663; 0x00157693; 0x00a68533; 0x03455693; 0xfff68713; 0x00a77533; 0x00c68633; 0x03f5d593; 0x03f59593; 0x03461613; 0x00b665b3; 0x00a5e533; 0xf2050553; 0x00008067; 0x00173793; 0xc016061b; 0x00c7c7b3; 0x40e78633; 0x07000813; 0x00c85863; 0x00000513; 0x00000613; 0xfc5ff06f; 0x00e038b3; 0x00e7c733; 0x08000793; 0x40c0083b; 0x03089893; 0x00e03733; 0x40c787bb; 0x010512b3; 0x0116e6b3; 0x02079793; 0x0207d893; 0xfc088313; 0x43f35793; 0x0057f7b3; 0x00034663; 0x01151833; 0x0180006f; 0x01069833; 0xfff8c893; 0x00155293; 0x0112d8b3; 0x01186833; 0x0107e7b3; 0x02061813; 0x00f038b3; 0x02085813; 0xfc080793; 0x01177733; 0x0007c663; 0x0106d533; 0x0180006f; 0x00c55533; 0x00169893; 0xfff84813; 0x01089833; 0x01056533; 0x00c6d633; 0x43f7d793; 0x03c55813; 0x00451513; 0x00c7f7b3; 0x00100613; 0x00455513; 0x03b61613; 0x00479793; 0x00e566b3; 0x00160713; 0x00f86533; 0x00e6e663; 0x00150513; 0x0100006f; 0x00c69663; 0x00157613; 0x00a60533; 0x03455613; 0x00c03633; 0x03461693; 0x00d54533; 0xed9ff06f]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base trunctfdf2_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 488.

Definition trunctfdf2_entry := (base + 0x0)%Z.

Open Scope bv_scope.

Import QZAa.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= g_step_fast.
Local Ltac zsimp ::= zsimp_fast.

Definition trunctfdf2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 10 (Z_to_bv 64 r) F) (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [] m m' /\ wmono segs m m' /\ mem_inv segs m'.

Ltac unfold_sfw := cbv beta delta [add64 sub64 shl64 not64 is_neg64 sra63 lt_s64 eqz64 nez64 zext32 lo64 hi64 wrap64
ONES64 M32 SIGN64 IMPLICIT_HI INF_HI HALF60 DQUIET].

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Hypothesis MI : mem_inv segs m.
Let MU : munch [] m m := munch_refl [] m.
Let WM : wmono segs m m := wmono_refl segs m.

Notation a_lo := (bv_unsigned a0). Notation a_hi := (bv_unsigned a1).
Notation POST r := (trunctfdf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m).

Notation ST pc x5 x6 x10 x12 x13 x14 x15 x16 x17 :=
(MS (mkR ra sp gp tp x5 x6 t2 s0 s1 x10 a1 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom segs)).

Lemma trunc_Lpack : forall x5 x6 x13 x14 x15 x16 x17 (dE dS r : Z),
(0 <= dE < 2^64)%Z -> (0 <= dS < 2^64)%Z ->
r = to_d_pack dE dS a_hi ->
evt segs (POST r) (ST (base + 0xbc) x5 x6 (Z_to_bv 64 dS) (Z_to_bv 64 dE) x13 x14 x15 x16 x17).
Proof using CODE BASE4 BASER MI.
intros until r. intros RdE RdS HR. subst r. unfold to_d_pack. unfold_sfw.
do 7 zstep. finish.
Qed.

Lemma trunc_LN : forall x5 x6 x13 x14 x15 x16 x17 (sig1 exp0 r : Z),
(0 <= sig1 < 2^64)%Z -> (0 <= exp0 < 2^64)%Z ->
r = (let '(dE, dS) := to_d_normD sig1 exp0 in to_d_pack dE dS a_hi) ->
evt segs (POST r) (ST (base + 0xac) x5 x6 (Z_to_bv 64 sig1) (Z_to_bv 64 exp0) x13 x14 x15 x16 x17).
Proof using CODE BASE4 BASER MI.
intros until r. intros Rs Re HR. subst r. unfold to_d_normD. unfold_sfw.
zstep. name_reg 13%Z carry.
zstep. model_reg 14%Z cm1 (Z.land (carry - 1) W64).
zstep. zstep. model_reg 12%Z dE (Z.land (carry + exp0) W64).
apply trunc_Lpack; [lia | zrange | reflexivity].
Qed.

Lemma trunc_L5 : forall x5 x6 x12 x13 x14 x15 x16 x17 (sig1 r : Z),
(0 <= sig1 < 2^64)%Z ->
r = (let '(dE, dS) := to_d_subD sig1 in to_d_pack dE dS a_hi) ->
evt segs (POST r) (ST (base + 0x1d4) x5 x6 (Z_to_bv 64 sig1) x12 x13 x14 x15 x16 x17).
Proof using CODE BASE4 BASER MI.
intros until r. intros Rs HR. subst r. unfold to_d_subD. unfold_sfw. rewrite b2z_Zb2z.
rewrite zb_negb_eqb0 by zrange_nonneg.
zstep. zstep. name_reg 12%Z carry.
zstep. zstep. zstep.
apply trunc_Lpack; [lia | zrange | reflexivity].
Qed.

Lemma trunc_L4 : forall x5 x6 x16 x17 (srLo shift sigHi1 sticky mM64 r : Z),
(0 <= srLo < 2^64)%Z -> (0 <= shift < 2^64)%Z -> (0 <= sigHi1 < 2^64)%Z -> (0 <= sticky < 2^64)%Z -> (0 <= mM64 < 2^64)%Z ->
r = (let '(dE, dS) := to_d_subC srLo sigHi1 shift mM64 sticky in to_d_pack dE dS a_hi) ->
evt segs (POST r) (ST (base + 0x18c) x5 x6 (Z_to_bv 64 srLo) (Z_to_bv 64 shift) (Z_to_bv 64 sigHi1) (Z_to_bv 64 sticky) (Z_to_bv 64 mM64) x16 x17).
Proof using CODE BASE4 BASER MI.
intros until r. intros R1 R2 R3 R4 R5 HR. subst r. unfold to_d_subC. unfold trunc_round. unfold_sfw.
rewrite (sra63_leb mM64) by lia.
zstep. name_as_by srHi0 (Z.shiftr sigHi1 (Z.land shift 63))
(change (inr64 (Z.shiftr sigHi1 (Z.land shift 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
zstep. rewrite (srai63_word mM64) by lia.
zstep. zstep. zstep. name_reg 15%Z srHi.
do 6 zstep. name_reg 13%Z roundBits.
zstep. name_reg 10%Z sig0.
zstep. if_cases Kr1; zify_cond Kr1; decide_tests_b.
-
zstep. if_cases Kr2; zify_cond Kr2; decide_tests_b.
+  eapply trunc_L5; [zrange | reflexivity].
+  zstep. zstep. model_reg 10%Z sig1 (Z.land (Z.land sig0 1 + sig0) W64).
eapply trunc_L5; [zrange | reflexivity].
-  zstep. model_reg 10%Z sig1 (Z.land (sig0 + 1) W64). zstep.
eapply trunc_L5; [zrange | reflexivity].
Qed.

Lemma trunc_L3 : forall x5 x6 x17 (slHi shift sigHi1 shNZ slLo r : Z),
(0 <= slHi < 2^64)%Z -> (0 <= shift < 2^64)%Z -> (0 <= sigHi1 < 2^64)%Z -> (0 <= shNZ < 2^64)%Z -> (0 <= slLo < 2^64)%Z ->
r = (let '(dE, dS) := to_d_subB a_lo sigHi1 shift shNZ slLo slHi in to_d_pack dE dS a_hi) ->
evt segs (POST r) (ST (base + 0x154) x5 x6 a0 (Z_to_bv 64 shift) (Z_to_bv 64 sigHi1) (Z_to_bv 64 shNZ) (Z_to_bv 64 slLo) (Z_to_bv 64 slHi) x17).
Proof using CODE BASE4 BASER MI.
intros until r. intros R1 R2 R3 R4 R5 HR. subst r. unfold to_d_subB. unfold_sfw. rewrite b2z_Zb2z.
pose_word_ranges.
zstep. name_reg 15%Z stickySrc.
rewrite (zb_negb_eqb0 stickySrc) by zrange_nonneg.
zstep. zstep. name_reg 17%Z sticky0.
zstep. name_reg 16%Z mm.
zstep. model_reg 15%Z mM64 (Z.land (mm - 64) W64).
zstep. name_reg 14%Z sticky.
zstep. if_cases K4; zify_cond K4; decide_tests_b.
-
zstep. name_as_by sr1 (Z.shiftr a_lo (Z.land shift 63))
(change (inr64 (Z.shiftr a_lo (Z.land shift 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
do 4 zstep. name_reg 10%Z srLo.
eapply trunc_L4; [zrange | zrange | zrange | zrange | zrange | reflexivity].
-
zstep.
name_as_by srLo (Z.shiftr sigHi1 (Z.land mm 63))
(change (inr64 (Z.shiftr sigHi1 (Z.land mm 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
zstep.
eapply trunc_L4; [zrange | zrange | zrange | zrange | zrange | reflexivity].
Qed.

Lemma trunc_L0c : forall x5 x6 x12 x15 x16 x17 (sigHi srcExp r : Z),
(0 <= sigHi < 2^64)%Z -> (0 <= srcExp < 2^64)%Z ->
r = (let '(dE, dS) := to_d_range a_lo sigHi srcExp in to_d_pack dE dS a_hi) ->
evt segs (POST r) (ST (base + 0x88) x5 x6 a0 x12 (Z_to_bv 64 sigHi) (Z_to_bv 64 srcExp) x15 x16 x17).
Proof using CODE BASE4 BASER MI.
intros until r. intros R1 R2 HR. subst r. unfold to_d_range. unfold_sfw. rewrite ?b2z_Zb2z.
pose_word_ranges.
do 3 zstep. if_cases K2; zify_cond K2; decide_tests_b.
-
zstep. rewrite (ltb1_eqb0 srcExp) by lia. name_reg 15%Z expZ.
zstep. zstep. name_reg 15%Z k.
zstep. model_reg 12%Z shift (Z.land (k - srcExp) W64).
zstep. zstep. if_cases K3; try rewrite bv_lts_lxor in K3; zify_cond K3; decide_tests_b.
+
unfold to_d_subA. unfold_sfw. rewrite ?b2z_Zb2z.
rewrite (zb_negb_eqb0 srcExp) by lia.
zstep. name_reg 17%Z expNZ.
zstep. name_reg 14%Z shNZ0. rewrite (zb_negb_eqb0 shNZ0) by zrange_nonneg.
zstep. zstep. rewrite Z_to_bv_swrap32. rewrite (sext32_land64 (0 - shift)).
name_as_by negsh (sext32 (0 - shift)) (apply sext32_range).
zstep. zstep. name_reg 14%Z shNZ.
zstep. rewrite Z_to_bv_swrap32. rewrite (sext32_land64 (128 - shift)).
name_as_by nW (sext32 (128 - shift)) (apply sext32_range).
zstep. zstep. name_reg 13%Z sigHi1.
zstep. zstep. name_reg 17%Z n.
zstep. model_reg 6%Z nM64 (Z.land (n - 64) W64).
rewrite (sra63_leb nM64) by lia.
zstep. rewrite (srai63_word nM64) by lia.
zstep. name_reg 15%Z slLo.
zstep. if_cases K4; zify_cond K4; decide_tests_b.
*
zstep. zstep. zstep. zstep.
name_as_by sr2 (Z.shiftr (Z.shiftr a_lo 1) (Z.land (Z.lxor n W64) 63))
(change (inr64 (Z.shiftr (Z.shiftr a_lo 1) (Z.land (Z.lxor n W64) 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
zstep. name_reg 16%Z slHi.
eapply trunc_L3; [zrange | zrange | zrange | zrange | zrange | reflexivity].
*
zstep. model_reg 16%Z slHi (Z.land (Z.shiftl a_lo (Z.land n 63)) W64). zstep.
eapply trunc_L3; [zrange | zrange | zrange | zrange | zrange | reflexivity].
+
do 3 zstep. apply trunc_Lpack; [lia | lia | reflexivity].
-
do 3 zstep. apply trunc_Lpack; [lia | lia | reflexivity].
Qed.

Lemma trunc_main : forall (x5 x6 x12 x13 x14 x15 x16 x17 : word) (r : Z),
r = f128_to_d (a_lo + 2^64 * a_hi) ->
evt segs (POST r) (ST (base + 0x0) x5 x6 a0 x12 x13 x14 x15 x16 x17).
Proof using CODE BASE4 BASER MI.
intros until r. intros HR. pose_word_ranges.
rewrite f128_to_d_split in HR by lia. subst r. unfold to_d_core. unfold_sfw.
do 5 zstep. name_reg 14%Z srcExp.
zstep. model_reg 12%Z candM1 (Z.land (srcExp + 18446744073709536255) W64).
zstep. zstep. name_reg 13%Z sigHi.
zstep. if_cases K0; zify_cond K0; decide_tests_b.
-
zstep. zstep. if_cases K1; zify_cond K1; decide_tests_b.
+
eapply trunc_L0c; [zrange | zrange | reflexivity].
+ do 3 zstep. if_cases K3; zify_cond K3; decide_tests_b.
*  eapply trunc_L0c; [zrange | zrange | reflexivity].
*  do 8 zstep. apply trunc_Lpack; [lia | zrange | reflexivity].
-
unfold to_d_normal. unfold trunc_round. unfold_sfw.
do 5 zstep. name_reg 10%Z sig0.
zstep. name_reg 13%Z roundBits.
do 3 zstep. model_reg 12%Z exp0 (Z.land (candM1 + 1) W64).
zstep. if_cases Kr1; zify_cond Kr1; decide_tests_b.
+
zstep. if_cases Kr2; zify_cond Kr2; decide_tests_b.
*  eapply trunc_LN; [zrange | zrange | reflexivity].
*  zstep. zstep. model_reg 10%Z sig1 (Z.land (Z.land sig0 1 + sig0) W64).
eapply trunc_LN; [zrange | zrange | reflexivity].
+  zstep. model_reg 10%Z sig1 (Z.land (sig0 + 1) W64). zstep.
eapply trunc_LN; [zrange | zrange | reflexivity].
Qed.
End Proofs.

#[using="CODE BASE4 BASER"] Lemma trunctfdf2_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
mem_inv segs m ->
evt segs (trunctfdf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
(f128_to_d (bv_unsigned a0 + 2^64 * bv_unsigned a1)) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof. intros until m. intros MI. eapply trunc_main; [exact MI | reflexivity]. Qed.

End G.
End Mqc.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq0.

Import ListNotations. Unset Keyed Unification.
Local Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenSF GwCallee.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.

Definition multf3_code : list Z :=
[0xfb010113; 0x04813423; 0x04913023; 0x03213c23; 0x03313823; 0x03413423; 0x03513023; 0x01613c23; 0x01713823; 0x01813423; 0x00058713; 0xfff00793; 0x00159593; 0x00169293; 0x00e6c333; 0xffff8e37; 0x00050e93; 0x0107d813; 0x0315d893; 0x0312d293; 0x03f35593; 0x001e0f1b; 0x03f59593; 0x01077333; 0x0106f3b3; 0x01e88fb3; 0x002e041b; 0x02035e13; 0x1e8fe263; 0x01e28fb3; 0x1dff7e63; 0x00000513; 0x00f61693; 0x03165713; 0x00f39393; 0x00010f37; 0x00100f93; 0x02031313; 0x020ed613; 0x020e9e93; 0x005882b3; 0xffffc8b7; 0x01ee6e33; 0x0203df13; 0x01ff9f93; 0x00776733; 0x0206d413; 0x02069693; 0x02035493; 0x020ed913; 0x0018839b; 0x01ff68b3; 0x02071713; 0x03c40f33; 0x0206df93; 0x029409b3; 0x0266ba33; 0x02c40ab3; 0x03240433; 0x03d6b6b3; 0x03c88b33; 0x02075b93; 0x03cf8c33; 0x029884b3; 0x02673333; 0x03288933; 0x02c888b3; 0x02cf8fb3; 0x03d73733; 0x015a0ab3; 0x03cb8e33; 0x02cb8633; 0x008f8433; 0x014abeb3; 0x00ea8733; 0x013c09b3; 0x01e88f33; 0x01f43fb3; 0x01573a33; 0x0189bab3; 0x01298933; 0x009e04b3; 0x02045b93; 0x02041413; 0x011f38b3; 0x006f0333; 0x014e8eb3; 0x013939b3; 0x00c90a33; 0x01c4be33; 0x020f9f93; 0x00d40633; 0x0204d693; 0x02049493; 0x01e33f33; 0x016888b3; 0x013a89b3; 0x012a3933; 0x00863433; 0x01fbefb3; 0x020a5a93; 0x020a1a13; 0x020e1e13; 0x01e888b3; 0x01d30eb3; 0x01298933; 0x01f70fb3; 0x00de6e33; 0x006eb6b3; 0x009e84b3; 0x00efb733; 0x02091913; 0x014f8a33; 0x00d888b3; 0x01d4b333; 0x01fa3eb3; 0x008a06b3; 0x012aef33; 0x01c888b3; 0x01d70733; 0x0146be33; 0x006888b3; 0x01e48f33; 0x009f3333; 0x00ef0733; 0x00688333; 0x01e73eb3; 0x01c708b3; 0x01d30333; 0x00e8b733; 0x00e30733; 0x00750533; 0x00f71313; 0x00a282b3; 0x08034a63; 0x03f8d513; 0x00171713; 0x00189893; 0x00a76733; 0x03f6d513; 0x00a8e8b3; 0x03f65513; 0x00169693; 0x00a6e6b3; 0x00161613; 0x00008537; 0xfff5051b; 0x06a2d863; 0x0800006f; 0x0017df93; 0x07fff437; 0x01f77f33; 0x02441413; 0x0c8f0263; 0x008f3433; 0x0c040263; 0x01f6f733; 0x07ffffb7; 0x024f9f93; 0x0df70263; 0x01f73fb3; 0x0c0f8263; 0x07fff6b7; 0x02469693; 0x00df4fb3; 0x01f56fb3; 0x100f9a63; 0x00e66633; 0x00061e63; 0x00000513; 0x1180006f; 0x00128293; 0x00008537; 0xfff5051b; 0x00a2cc63; 0x00000513; 0x07fff637; 0x02461613; 0x00c5e5b3; 0x2d00006f; 0x08505663; 0x00f8f533; 0x01077733; 0x03029293; 0x00e2e733; 0xfff00793; 0x03f79793; 0x28f68c63; 0x0006a793; 0x0017c793; 0x00b765b3; 0x28078a63; 0xfff00713; 0x03f71713; 0x00e6c6b3; 0x00d66633; 0x28061663; 0x00157613; 0x00c50633; 0x00a63533; 0x00a585b3; 0x0300006f; 0x00153413; 0xf40412e3; 0x00100593; 0x02f59593; 0x00b765b3; 0x2600006f; 0x00163f93; 0xf40f92e3; 0x00100513; 0x02f51513; 0x00a6e5b3; 0x00060513; 0x2440006f; 0x00100513; 0x405507b3; 0x07f00513; 0x14f56c63; 0x07f28513; 0x02051813; 0x02085813; 0xfc080e13; 0xfff84313; 0x140e4463; 0x010612b3; 0x00a61eb3; 0x43fe5393; 0x01d3feb3; 0x140e5a63; 0x00a71833; 0x0018de13; 0x006e5333; 0x00686833; 0x1440006f; 0x00d746b3; 0x00d666b3; 0x00069c63; 0x01e56533; 0xf00510e3; 0x0ffff5b7; 0x02359593; 0x1d40006f; 0x01e566b3; 0x0e068863; 0x00e666b3; 0x0e068463; 0x030f5693; 0x1e069463; 0x00133693; 0x00030463; 0x00030e93; 0x001ede13; 0x55555f37; 0x33333fb7; 0x0f0f1437; 0x010104b7; 0x01ceee33; 0x555f0e9b; 0x333f8f1b; 0xf0f40f9b; 0x1014841b; 0x002e5493; 0x009e6e33; 0x020e9493; 0x009e8eb3; 0x020f1493; 0x009f0f33; 0x020f9493; 0x009f8fb3; 0x02041493; 0x00940433; 0x004e5493; 0x009e6e33; 0x008e5493; 0x009e6e33; 0x010e5493; 0x009e6e33; 0x020e5493; 0x009e6e33; 0xfffe4e13; 0x001e5493; 0x01d4feb3; 0x00669693; 0x41de0e33; 0x01ee7eb3; 0x002e5e13; 0x01ee7e33; 0x01ce8e33; 0x004e5e93; 0x01de0e33; 0x01fe7e33; 0x028e0e33; 0x038e5e13; 0x00de66b3; 0xff168f13; 0x01e51e33; 0x020f1e93; 0x020edf93; 0xfc0f8413; 0x43f45e93; 0x10044e63; 0x01f51333; 0x1280006f; 0x00000513; 0x0d80006f; 0x00a692b3; 0x00165393; 0x0063d3b3; 0x0072e2b3; 0x00a61eb3; 0x43fe5393; 0x01d3feb3; 0xea0e4ae3; 0x01089833; 0x005ee333; 0x00a89533; 0x02079293; 0x00a3f3b3; 0x0202d513; 0xfc050e13; 0xfff54293; 0x020e4a63; 0x00a6deb3; 0x00603633; 0x00f6d6b3; 0x43fe5313; 0x00d376b3; 0x01d3e3b3; 0x040e5063; 0x00f8d533; 0x00171893; 0x005898b3; 0x01156533; 0x0300006f; 0x00f65633; 0x00169e93; 0x005e9eb3; 0x01d66eb3; 0x00603633; 0x00f6d6b3; 0x43fe5313; 0x00d376b3; 0x01d3e3b3; 0xfc0e44e3; 0x00a75533; 0x00d866b3; 0x00c3e633; 0x00f75733; 0x00e37733; 0xfff00793; 0x03f79793; 0xd6f698e3; 0x00163793; 0x00b765b3; 0xd6079ae3; 0x00150513; 0x00153613; 0x00c585b3; 0x04813403; 0x04013483; 0x03813903; 0x03013983; 0x02813a03; 0x02013a83; 0x01813b03; 0x01013b83; 0x00813c03; 0x05010113; 0x00008067; 0x00000513; 0x0280006f; 0x01e31333; 0xffffcf13; 0x00155513; 0x01e55533; 0x00a36333; 0x01cefeb3; 0x01000513; 0x40d50533; 0x02035e13; 0x03075713; 0xa80714e3; 0x0013b693; 0x00060713; 0x00038463; 0x00038713; 0x00175f13; 0x55555fb7; 0x33333437; 0x0f0f14b7; 0x01e76733; 0x555f8f1b; 0x33340f9b; 0xf0f4841b; 0x00275493; 0x00976733; 0x020f1493; 0x009f0f33; 0x020f9493; 0x009f8fb3; 0x02041493; 0x00940433; 0x00475493; 0x00976733; 0x00875493; 0x00976733; 0x01075493; 0x00976733; 0x02075493; 0x00976733; 0xfff74713; 0x00175493; 0x01e4ff33; 0x00669693; 0x41e70733; 0x01f77f33; 0x00275713; 0x01f77733; 0x01010fb7; 0x101f8f9b; 0x00ef0733; 0x00475f13; 0x01e70733; 0x020f9f13; 0x00877733; 0x01ef8f33; 0x03e70733; 0x03875713; 0x00d766b3; 0xff168713; 0x02071f13; 0x020f5f93; 0xfc0f8f13; 0x000f4663; 0x01f613b3; 0x0180006f; 0x00e393b3; 0xffffcf93; 0x00165413; 0x01f45fb3; 0x01f3e3b3; 0x00e61633; 0x43ff5713; 0x40d50533; 0x00c77633; 0x01050513; 0x985ff06f]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base multf3_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 1792.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= g_step_fast.
Local Ltac zsimp ::= zsimp_fast.

Definition multf3_entry := (base + 0x0)%Z.
Definition multf3_core_pc := (base + 0x80)%Z.
Definition multf3_mid_pc := (base + 0x20c)%Z.

#[using="CODE BASE4 BASER"] Lemma mulhu_shl32 : forall x y, 0 <= x -> 0 <= y ->
Z.shiftr (Z.land (Z.shiftl x 32) 18446744073709551615 * Z.land (Z.shiftl y 32) 18446744073709551615) 64
= Z.land (Z.land x 4294967295 * Z.land y 4294967295) 18446744073709551615.
Proof.
intros x y Hx Hy.
rewrite !land_W64. change 4294967295 with (2^32 - 1). rewrite !zb_land_mask by lia.
rewrite !Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^64) with (2^32 * 2^32) at 1 2.
rewrite !Zmult_mod_distr_r.
pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)). pose proof (Z.mod_pos_bound y (2^32) ltac:(lia)).
replace (x mod 2^32 * 2^32 * (y mod 2^32 * 2^32)) with ((x mod 2^32 * (y mod 2^32)) * 2^64) by lia.
rewrite Z.div_mul by lia. symmetry. apply Z.mod_small. nia.
Qed.

Definition multf3_mid (ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(aExp bExp aSigHi aSigLo bSigHi bSigLo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists es hh hl lh ll y5' t1 t2' x8 x9 a5' a6' s2' s3' s4' s5' s6' s7' s8' t3 t4 t5 t6,
(forall signHi scale, mul_core signHi aExp bExp aSigHi aSigLo bSigHi bSigLo scale = MC_tail signHi es hh hl lh ll scale)
/\ (0 <= es < 65536)%Z /\ (0 <= hh < 2^64)%Z /\ (0 <= hl < 2^64)%Z /\ (0 <= lh < 2^64)%Z /\ (0 <= ll < 2^64)%Z /\
y5' = Z_to_bv 64 es /\ a5' = Z_to_bv 64 18446744073709551615 /\ a6' = Z_to_bv 64 281474976710655 /\ t2' = Z_to_bv 64 (-16383) /\
ms' = MS (mkR ra sp gp tp y5' t1 t2' x8 x9
a0 a1 (Z_to_bv 64 ll) (Z_to_bv 64 lh) (Z_to_bv 64 hh) a5' a6' (Z_to_bv 64 hl)
s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x20c)) fc None m (seg_rom segs).

#[using="CODE BASE4 BASER"] Lemma multf3_core1 : forall (ra sp gp tp w1 w2 s0 s1 a0 a1 w4 a3 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 t5 t6 : word) (ea eb : Z)
(F : bvmap 5 word) fc (m : word -> option byte),
mem_inv segs m ->
(0 <= ea < 32768)%Z -> (0 <= eb < 32768)%Z ->
evt segs (multf3_mid ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
ea eb (bv_unsigned w1) (bv_unsigned w3) (bv_unsigned w2) (bv_unsigned w4) m)
(MS (mkR ra sp gp tp (Z_to_bv 64 eb) w1 w2 s0 s1 a0 a1 w4 a3 a4 (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 281474976710655) (Z_to_bv 64 ea)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (Z.shiftr (bv_unsigned w1) 32)) w3 t5 t6)
F (Z_to_bv 64 (base + 0x80)) fc None m (seg_rom segs)).
Proof.
intros until m. intros MI He1 He2.
pose_word_ranges.
set (aExp := ea) in *. set (bExp := eb) in *.
set (aSigHi := bv_unsigned w1) in *. set (aSigLo := bv_unsigned w3) in *. set (bSigHi := bv_unsigned w2) in *. set (bSigLo := bv_unsigned w4) in *.

do 1 zstep. model_reg 13 bLo15 (Z.land (Z.shiftl bSigLo 15) 18446744073709551615).
do 6 zstep. model_reg 12 A3 (Z.shiftr aSigLo 32).
do 2 zstep. model_reg 5 expSum (Z.land (aExp + bExp) 18446744073709551615).
do 2 zstep. model_reg 28 A1 (Z.lor (Z.shiftr aSigHi 32) 65536).
do 3 zstep. model_reg 14 bHi15 (Z.lor (Z.shiftr bSigLo 49) (Z.land (Z.shiftl bSigHi 15) 18446744073709551615)).
do 1 zstep. model_reg 8 B3 (Z.shiftr bLo15 32).
do 2 zstep. model_reg 9 A2 (Z.land aSigHi 4294967295).
do 1 zstep. model_reg 18 A4 (Z.land aSigLo 4294967295).
do 2 zstep. model_reg 17 B1 (Z.lor (Z.shiftr (Z.land (Z.shiftl bSigHi 15) 18446744073709551615) 32) 2147483648).
do 2 zstep. model_reg 30 p13 (Z.land (B3 * A1) 18446744073709551615).
do 1 zstep. model_reg 31 B4 (Z.land bLo15 4294967295).
do 1 zstep. model_reg 19 p23 (Z.land (B3 * A2) 18446744073709551615).
do 1 zstep. rewrite mulhu_shl32 by zrange_nonneg. change (Z.land bLo15 4294967295) with B4. change (Z.land aSigHi 4294967295) with A2.
model_reg 20 p24 (Z.land (B4 * A2) 18446744073709551615).
do 1 zstep. model_reg 21 p33 (Z.land (B3 * A3) 18446744073709551615).
do 1 zstep. model_reg 8 p43 (Z.land (B3 * A4) 18446744073709551615).
do 1 zstep. rewrite mulhu_shl32 by zrange_nonneg. change (Z.land bLo15 4294967295) with B4. change (Z.land aSigLo 4294967295) with A4.
model_reg 13 p44 (Z.land (B4 * A4) 18446744073709551615).
do 1 zstep. model_reg 22 p11 (Z.land (B1 * A1) 18446744073709551615).
do 1 zstep. model_reg 23 B2 (Z.land bHi15 4294967295).
do 1 zstep. model_reg 24 p14 (Z.land (B4 * A1) 18446744073709551615).
do 1 zstep. model_reg 9 p21 (Z.land (B1 * A2) 18446744073709551615).
do 1 zstep. rewrite mulhu_shl32 by zrange_nonneg. change (Z.land bHi15 4294967295) with B2. change (Z.land aSigHi 4294967295) with A2.
model_reg 6 p22 (Z.land (B2 * A2) 18446744073709551615).
do 1 zstep. model_reg 18 p41 (Z.land (B1 * A4) 18446744073709551615).
do 1 zstep. model_reg 17 p31 (Z.land (B1 * A3) 18446744073709551615).
do 1 zstep. model_reg 31 p34 (Z.land (B4 * A3) 18446744073709551615).
do 1 zstep. rewrite mulhu_shl32 by zrange_nonneg. change (Z.land bHi15 4294967295) with B2. change (Z.land aSigLo 4294967295) with A4.
model_reg 14 p42 (Z.land (B2 * A4) 18446744073709551615).
do 1 zstep. model_reg 21 s2a (Z.land (p24 + p33) 18446744073709551615).
do 1 zstep. model_reg 28 p12 (Z.land (B2 * A1) 18446744073709551615).
do 1 zstep. model_reg 12 p32 (Z.land (B2 * A3) 18446744073709551615).
do 1 zstep. model_reg 8 sum1 (Z.land (p34 + p43) 18446744073709551615).
do 1 zstep. model_reg 29 c2a (Z.b2z (s2a <? p24)).
do 1 zstep. model_reg 14 sum2 (Z.land (s2a + p42) 18446744073709551615).
do 1 zstep. model_reg 19 s3a (Z.land (p14 + p23) 18446744073709551615).
do 1 zstep. model_reg 30 s4a (Z.land (p31 + p13) 18446744073709551615).
do 1 zstep. model_reg 31 c1 (Z.b2z (sum1 <? p34)).
do 1 zstep. model_reg 20 c2b (Z.b2z (sum2 <? s2a)).
do 1 zstep. model_reg 21 c3a (Z.b2z (s3a <? p14)).
do 1 zstep. model_reg 18 s3b (Z.land (s3a + p41) 18446744073709551615).
do 1 zstep. model_reg 9 sum5 (Z.land (p12 + p21) 18446744073709551615).
do 1 zstep. model_reg 23 sum1Shr32 (Z.shiftr sum1 32).
do 1 zstep. model_reg 8 sum1Shl32 (Z.land (Z.shiftl sum1 32) 18446744073709551615).
do 1 zstep. model_reg 17 c4a (Z.b2z (s4a <? p31)).
do 1 zstep. model_reg 6 sum4 (Z.land (s4a + p22) 18446744073709551615).
do 1 zstep. model_reg 29 sum2Hi (Z.land (c2a + c2b) 18446744073709551615).
do 1 zstep. model_reg 19 c3b (Z.b2z (s3b <? s3a)).
do 1 zstep. model_reg 20 sum3 (Z.land (s3b + p32) 18446744073709551615).
do 1 zstep. model_reg 28 c5 (Z.b2z (sum5 <? p12)).
do 1 zstep. model_reg 31 c1Shl32 (Z.land (Z.shiftl c1 32) 18446744073709551615).
do 1 zstep. model_reg 12 lo_lo (Z.land (sum1Shl32 + p44) 18446744073709551615).
do 1 zstep. model_reg 13 sum5Shr32 (Z.shiftr sum5 32).
do 1 zstep. model_reg 9 sum5Shl32 (Z.land (Z.shiftl sum5 32) 18446744073709551615).
do 1 zstep. model_reg 30 c4b (Z.b2z (sum4 <? s4a)).
do 1 zstep. model_reg 17 hh1 (Z.land (c4a + p11) 18446744073709551615).
do 1 zstep. model_reg 19 c3ab (Z.land (c3a + c3b) 18446744073709551615).
do 1 zstep. model_reg 18 c3c (Z.b2z (sum3 <? s3b)).
do 1 zstep. model_reg 8 r0c (Z.b2z (lo_lo <? sum1Shl32)).
do 1 zstep. model_reg 31 sum1Mid (Z.lor sum1Shr32 c1Shl32).
do 1 zstep. model_reg 21 sum3Shr32 (Z.shiftr sum3 32).
do 1 zstep. model_reg 20 sum3Shl32 (Z.land (Z.shiftl sum3 32) 18446744073709551615).
do 1 zstep. model_reg 28 c5Shl32 (Z.land (Z.shiftl c5 32) 18446744073709551615).
do 1 zstep. model_reg 17 hh2 (Z.land (hh1 + c4b) 18446744073709551615).
do 1 zstep. model_reg 29 m1 (Z.land (sum4 + sum2Hi) 18446744073709551615).
do 1 zstep. model_reg 18 sum3Hi (Z.land (c3ab + c3c) 18446744073709551615).
do 1 zstep. model_reg 31 r1a (Z.land (sum2 + sum1Mid) 18446744073709551615).
do 1 zstep. model_reg 28 sum5MidHi (Z.lor c5Shl32 sum5Shr32).
do 1 zstep. model_reg 13 cm1 (Z.b2z (m1 <? sum4)).
do 1 zstep. model_reg 9 m2 (Z.land (m1 + sum5Shl32) 18446744073709551615).
do 1 zstep. model_reg 14 cr1a (Z.b2z (r1a <? sum2)).
do 1 zstep. model_reg 18 sum3HiShl32 (Z.land (Z.shiftl sum3Hi 32) 18446744073709551615).
do 1 zstep. model_reg 20 r1 (Z.land (r1a + sum3Shl32) 18446744073709551615).
do 1 zstep. model_reg 17 hh3 (Z.land (hh2 + cm1) 18446744073709551615).
do 1 zstep. model_reg 6 cm2 (Z.b2z (m2 <? m1)).
do 1 zstep. model_reg 29 cr1b (Z.b2z (r1 <? r1a)).
do 1 zstep. model_reg 13 lo_hi (Z.land (r1 + r0c) 18446744073709551615).
do 1 zstep. model_reg 30 sum3Mid (Z.lor sum3Shr32 sum3HiShl32).
do 1 zstep. model_reg 17 hh4 (Z.land (hh3 + sum5MidHi) 18446744073709551615).
do 1 zstep. model_reg 14 r1Hi (Z.land (cr1a + cr1b) 18446744073709551615).
do 1 zstep. model_reg 28 carry (Z.b2z (lo_hi <? r1)).
do 1 zstep. model_reg 17 hh5 (Z.land (hh4 + cm2) 18446744073709551615).
do 1 zstep. model_reg 30 m3 (Z.land (m2 + sum3Mid) 18446744073709551615).
do 1 zstep. model_reg 6 cm3 (Z.b2z (m3 <? m2)).
do 1 zstep. model_reg 14 m4 (Z.land (m3 + r1Hi) 18446744073709551615).
do 1 zstep. model_reg 6 hh6 (Z.land (hh5 + cm3) 18446744073709551615).
do 1 zstep. model_reg 29 cm4 (Z.b2z (m4 <? m3)).
do 1 zstep. model_reg 17 hi_lo (Z.land (m4 + carry) 18446744073709551615).
do 1 zstep. model_reg 6 hh7 (Z.land (hh6 + cm4) 18446744073709551615).
do 1 zstep. model_reg 14 cm5 (Z.b2z (hi_lo <? m4)).
do 1 zstep. model_reg 14 hi_hi (Z.land (hh7 + cm5) 18446744073709551615).

apply evt_done. unfold multf3_mid.
exists expSum, hi_hi, hi_lo, lo_hi, lo_lo.
repeat (lazymatch goal with |- ex _ => eexists end).
split.
{ intros sg sc. cbv delta [mul_core]. sf_vocab. fold_model_lets. cbv delta [MC_tail]. sf_vocab. reflexivity. }
split. { subst expSum aExp bExp. rewrite land_W64, Z.mod_small by lia. lia. }
split. { exact Rhi_hi. } split. { exact Rhi_lo. } split. { exact Rlo_hi. } split. { exact Rlo_lo. }
split. { reflexivity. } split. { reflexivity. } split. { reflexivity. } split. { reflexivity. }
reflexivity.
Time Qed.

End G.
