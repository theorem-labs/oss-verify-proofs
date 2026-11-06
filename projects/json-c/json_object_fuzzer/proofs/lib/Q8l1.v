(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q5Rg Qc3B QZAi QdBa QqdR QfYR QfcC Ql2m QnDM_c1 QDUx Q9Ay Q91D QCa8 QVbl QQRC QQLG Qy8Z Lib.CodeAt Lib.StepGen Lib.StepGenX Lib.StepGenX2 Lib.GwCallee Lib.GwApply Lib.GwFold.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qc3B.
Import QZAi.Mq1 QZAi QdBa QqdR QfYR QfcC Ql2m.
Import QnDM_c1 QDUx Q9Ay.
Import Q91D.
Import QCa8.
Import QVbl.
Import QQRC.
Import QVbl.Mq2.
Import QQLG.Mq3.
Import QQLG.Mq5.
Import QQLG.Mq1.
Import Qy8Z.Mq0.
Import QQRC.Mq1.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4.
Open Scope Z_scope.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition fmodlblk_code (w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 : Z) : list Z :=
[0xe00505d3; 0x0175d51b; 0x02959613; 0x0ff57693; 0x02965613; 0x02068a63; 0x0ff00513; 0x0ea69e63; 0x00000513; 0x01961613; 0x000086b7; 0xfff68693; 0x01f5d593; 0x03f59593; 0x03069693; 0x00b6e5b3; 0x00c5e5b3; 0x00008067; 0x00000513; 0x0e060c63; 0x00165693; 0x00d666b3; 0x0026d713; 0x00e6e6b3; 0x0046d713; 0x00e6e6b3; 0x02969713; 0x03175793; 0x00f6e6b3; 0x555557b7; 0x5557879b; 0x03975713; 0x00e6e6b3; 0xfff6c693; 0x0016d713; 0x00f77733; 0x333337b7; 0x3337879b; 0x40e686b3; 0x00f6f733; 0x0026d693; 0x00f6f6b3; 0x00d706b3; 0x0046d713; 0x00e686b3; 0x0f0f1737; 0xf0f70713; 0x00e6f6b3; 0x01010737; 0x10170713; 0x02e686b3; 0x00004737; 0xf8070713; 0x0186d69b; 0x40d70733; 0x01168693; 0x00d61633; 0x0006a693; 0xfff68693; 0x00c6f633; 0x00100793; 0x00970693; 0x03079793; 0x00f64633; 0x01f5d593; 0x03f59593; 0x03069693; 0x00b6e5b3; 0x00c5e5b3; 0x00008067; 0x00000513; 0x00004737; 0xf8070713; 0x00e686b3; 0x01961613; 0x01f5d593; 0x03f59593; 0x03069693; 0x00b6e5b3; 0x00c5e5b3; 0x00008067; 0x01f5d593; 0x03f59593; 0x03001693; 0x00b6e5b3; 0x00c5e5b3; 0x00008067; 0x03f6d693; 0x00159613; 0x01059593; 0x00f69693; 0x03165613; 0x00c6e633; 0x03061613; 0x0105d593; 0x00b665b3; 0x00008067; 0xfb010113; 0x04113423; 0x04813023; 0x02913c23; 0x03213823; 0x03313423; 0x03413023; 0x01513c23; 0x01613823; 0x01713423; 0x01813023; 0x00068993; 0x00060913; 0x00058413; 0x00050493; 0x00000513; w_113; 0x00050613; 0x00058693; 0x00090513; 0x00098593; w_118; 0x04051a63; 0x00048513; 0x00040593; 0x00090613; 0x00098693; w_124; 0x00050613; 0x00058693; w_127; 0x04813083; 0x04013403; 0x03813483; 0x03013903; 0x02813983; 0x02013a03; 0x01813a83; 0x01013b03; 0x00813b83; 0x00013c03; 0x05010113; 0x00008067; 0x00090513; 0x00098593; w_142; 0xfa0502e3; 0x03045b13; 0x00008537; 0x031b1593; 0x0315db93; 0xfff5051b; 0xf8ab86e3; 0xfff00513; 0x00155513; 0x00a47ab3; 0x00a9fa33; 0x00048513; 0x000a8593; 0x00090613; 0x000a0693; w_158; 0x02a04063; 0x00048513; 0x000a8593; 0x00090613; 0x000a0693; w_164; 0x10050863; 0x17c0006f; 0x00199993; 0x0319dc13; 0x0a0b8263; 0x00048993; 0x020c1a63; 0x7b800537; 0xf0050553; 0xd49ff0ef; 0x00050613; 0x00058693; 0x00090513; 0x000a0593; w_179; 0x00050913; 0x00058a13; 0x0305d513; 0xf8850c13; 0xfff00513; 0x01055513; 0x00aaf5b3; 0x00150613; 0x00aa7533; 0x00c5e5b3; 0x00c56533; 0x037c4063; 0x0840006f; 0x03f9d613; 0x00159593; 0x00c5e5b3; 0xfffb8b9b; 0x00199993; 0x077c5463; 0x40a58633; 0x0129b6b3; 0x40d60633; 0xfc064ee3; 0x412989b3; 0x013665b3; 0x06058663; 0x03f9d593; 0x00161613; 0x00b665b3; 0xfcdff06f; 0x7b800537; 0xf0050553; 0xcb1ff0ef; 0x00050613; 0x00058693; 0x00048513; 0x000a8593; w_217; 0x00050993; 0x00058a93; 0x0305d513; 0xf8850b93; 0xf60c14e3; 0xf35ff06f; 0x000c0b93; 0x40a58533; 0x0129b633; 0x40c50533; 0x02054463; 0x412989b3; 0x013565b3; 0x02059063; 0x00000513; w_233; 0x00048613; 0x00040693; w_236; 0xe4dff06f; 0x00058513; 0x03055613; 0x000085b7; 0x02061063; 0x03f9d613; 0x00151693; 0x00199993; 0x00c6e533; 0x0306d693; 0xfffb8b9b; 0xfe0684e3; 0x00bb75b3; 0xfff00693; 0x00010737; 0x0106d613; 0xfff70713; 0x03705463; 0x00ebf733; 0x00d9f4b3; 0x00b765b3; 0x03059593; 0x00c57533; 0x00b56433; 0x00048513; 0x00040593; 0xde5ff06f; 0x078b8793; 0x00d9f433; 0x00e7f733; 0x00b765b3; 0x03059593; 0x00c57533; 0x00b564b3; 0x03800537; 0xf0050553; 0xbbdff0ef; 0x00050613; 0x00058693; 0x00040513; 0x00048593; w_278; 0xda5ff06f; 0x00159593; 0x0015d593; 0x00008067; 0xfe010113; 0x00113c23; 0x00813823; 0x00913423; 0x01213023; 0x00060413; 0x00004637; 0x04c44a63; 0x03fff4b7; 0x02549493; 0x00000613; 0x00048693; w_295; 0x00008637; 0xfff6061b; 0x08c46863; 0x00000613; 0x00048693; w_301; 0x00050913; 0x0000c637; 0xffd6061b; 0x00058493; 0x00c46463; 0x00060413; 0xffff8537; 0x00250513; 0x0900006f; 0xffffc637; 0x0016061b; 0x06864463; 0x03900493; 0x03149493; 0x00000613; 0x00048693; w_318; 0xffff8637; 0x0746061b; 0x04866a63; 0x00000613; 0x00048693; w_324; 0x00050913; 0xffff4637; 0x0e86061b; 0x00058493; 0x00866463; 0x00060413; 0x00008537; 0xf1a50513; 0x0340006f; 0x00058493; 0x00050913; 0xffffc537; 0x00150513; 0x0200006f; 0x00058493; 0x00050913; 0x0180006f; 0x00058493; 0x00050913; 0x00004537; 0xf8d50513; 0x00a40433; w_347; w_348; w_349; 0x00050613; 0x03041413; 0x01059593; 0x0105d593; 0x00b465b3; 0x03fff537; 0x02451513; 0x00a586b3; 0x00090513; 0x00048593; w_360; 0x01813083; 0x01013403; 0x00813483; 0x00013903; 0x02010113; 0x00008067]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 : Z).
Variables (joff_113 joff_118 joff_124 joff_127 joff_142 joff_158 joff_164 joff_179 joff_217 joff_233 joff_236 joff_278 : bv 21).
Variables (e_fpclassifyl e_letf2 e_multf3 e_floatsitf e_divtf3 : Z).
Hypothesis CODE : code_at segs base (fmodlblk_code w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 1468.
Hypothesis D_113 : decode_any (Z_to_bv 32 w_113) = Some (Jal 1 joff_113, 4%Z).
Hypothesis E_113 : is_ecall (Z_to_bv 32 w_113) = false.
Hypothesis D_118 : decode_any (Z_to_bv 32 w_118) = Some (Jal 1 joff_118, 4%Z).
Hypothesis E_118 : is_ecall (Z_to_bv 32 w_118) = false.
Hypothesis D_124 : decode_any (Z_to_bv 32 w_124) = Some (Jal 1 joff_124, 4%Z).
Hypothesis E_124 : is_ecall (Z_to_bv 32 w_124) = false.
Hypothesis D_127 : decode_any (Z_to_bv 32 w_127) = Some (Jal 1 joff_127, 4%Z).
Hypothesis E_127 : is_ecall (Z_to_bv 32 w_127) = false.
Hypothesis D_142 : decode_any (Z_to_bv 32 w_142) = Some (Jal 1 joff_142, 4%Z).
Hypothesis E_142 : is_ecall (Z_to_bv 32 w_142) = false.
Hypothesis D_158 : decode_any (Z_to_bv 32 w_158) = Some (Jal 1 joff_158, 4%Z).
Hypothesis E_158 : is_ecall (Z_to_bv 32 w_158) = false.
Hypothesis D_164 : decode_any (Z_to_bv 32 w_164) = Some (Jal 1 joff_164, 4%Z).
Hypothesis E_164 : is_ecall (Z_to_bv 32 w_164) = false.
Hypothesis D_179 : decode_any (Z_to_bv 32 w_179) = Some (Jal 1 joff_179, 4%Z).
Hypothesis E_179 : is_ecall (Z_to_bv 32 w_179) = false.
Hypothesis D_217 : decode_any (Z_to_bv 32 w_217) = Some (Jal 1 joff_217, 4%Z).
Hypothesis E_217 : is_ecall (Z_to_bv 32 w_217) = false.
Hypothesis D_233 : decode_any (Z_to_bv 32 w_233) = Some (Jal 1 joff_233, 4%Z).
Hypothesis E_233 : is_ecall (Z_to_bv 32 w_233) = false.
Hypothesis D_236 : decode_any (Z_to_bv 32 w_236) = Some (Jal 1 joff_236, 4%Z).
Hypothesis E_236 : is_ecall (Z_to_bv 32 w_236) = false.
Hypothesis D_278 : decode_any (Z_to_bv 32 w_278) = Some (Jal 1 joff_278, 4%Z).
Hypothesis E_278 : is_ecall (Z_to_bv 32 w_278) = false.
Hypothesis LINK_113 : gw_anch (base + 452 + bv_signed joff_113)%Z (e_floatsitf + 0)%Z.
Hypothesis LINK_118 : gw_anch (base + 472 + bv_signed joff_118)%Z (e_letf2 + 0)%Z.
Hypothesis LINK_124 : gw_anch (base + 496 + bv_signed joff_124)%Z (e_multf3 + 0)%Z.
Hypothesis LINK_127 : gw_anch (base + 508 + bv_signed joff_127)%Z (e_divtf3 + 0)%Z.
Hypothesis LINK_142 : gw_anch (base + 568 + bv_signed joff_142)%Z (e_fpclassifyl + 0)%Z.
Hypothesis LINK_158 : gw_anch (base + 632 + bv_signed joff_158)%Z (e_letf2 + 0)%Z.
Hypothesis LINK_164 : gw_anch (base + 656 + bv_signed joff_164)%Z (e_letf2 + 0)%Z.
Hypothesis LINK_179 : gw_anch (base + 716 + bv_signed joff_179)%Z (e_multf3 + 0)%Z.
Hypothesis LINK_217 : gw_anch (base + 868 + bv_signed joff_217)%Z (e_multf3 + 0)%Z.
Hypothesis LINK_233 : gw_anch (base + 932 + bv_signed joff_233)%Z (e_floatsitf + 0)%Z.
Hypothesis LINK_236 : gw_anch (base + 944 + bv_signed joff_236)%Z (e_multf3 + 0)%Z.
Hypothesis LINK_278 : gw_anch (base + 1112 + bv_signed joff_278)%Z (e_multf3 + 0)%Z.

Local Definition gw_tbl_0 := tt.

Definition fixunstfsi_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.fixunstfsi_post segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.fixunstfsi_post segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@Qy8Z.Mq0.fixunstfsi_post segs) fixunstfsi_post gw_tbl_0).
Definition floatsitf_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.floatsitf_post segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.floatsitf_post segs) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@Qy8Z.Mq0.floatsitf_post segs) floatsitf_post gw_tbl_1).
Definition floatunsitf_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.floatunsitf_post segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.floatunsitf_post segs) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@Qy8Z.Mq0.floatunsitf_post segs) floatunsitf_post gw_tbl_2).
Definition extenddftf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.extenddftf2_post segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.extenddftf2_post segs) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@Qy8Z.Mq0.extenddftf2_post segs) extenddftf2_post gw_tbl_3).
Definition addtf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.addtf3_post segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.addtf3_post segs) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@Qy8Z.Mq0.addtf3_post segs) addtf3_post gw_tbl_4).
Definition multf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.multf3_post segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.multf3_post segs) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@Qy8Z.Mq0.multf3_post segs) multf3_post gw_tbl_5).
Definition multf3_stmt : ltac:(gw_rebind_ty (@Qy8Z.Mq0.multf3_stmt segs e_multf3) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.multf3_stmt segs e_multf3) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@Qy8Z.Mq0.multf3_stmt segs e_multf3) multf3_stmt gw_tbl_6).
Definition divtf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.divtf3_post segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.divtf3_post segs) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@Qy8Z.Mq0.divtf3_post segs) divtf3_post gw_tbl_7).
Definition divtf3_stmt : ltac:(gw_rebind_ty (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt gw_tbl_8).
Definition letf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.letf2_post segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.letf2_post segs) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@Qy8Z.Mq0.letf2_post segs) letf2_post gw_tbl_9).
Definition frexpl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.frexpl_post segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.frexpl_post segs) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@Qy8Z.Mq0.frexpl_post segs) frexpl_post gw_tbl_10).
Definition signbitl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.signbitl_post segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.signbitl_post segs) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@Qy8Z.Mq0.signbitl_post segs) signbitl_post gw_tbl_11).
Definition fpclassifyl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.fpclassifyl_post segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.fpclassifyl_post segs) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@Qy8Z.Mq0.fpclassifyl_post segs) fpclassifyl_post gw_tbl_12).
Definition leaf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.leaf2_post segs) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.leaf2_post segs) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@Qy8Z.Mq0.leaf2_post segs) leaf2_post gw_tbl_13).
Definition leaf1_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.leaf1_post segs) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.leaf1_post segs) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@Qy8Z.Mq0.leaf1_post segs) leaf1_post gw_tbl_14).
Definition call2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.call2_post segs) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.call2_post segs) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@Qy8Z.Mq0.call2_post segs) call2_post gw_tbl_15).

Hypothesis divtf3_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQRC.divtf3_spec segs e_divtf3) 9%nat in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_16))) in exact T).

Hypothesis fpclassifyl_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQLG.Mq5.gw_all) (@QQLG.Mq5.fpclassifyl_spec) e_fpclassifyl)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_16))) in exact T).  Arguments fpclassifyl_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope.
Hypothesis letf2_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq2.letf2_spec segs e_letf2) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in let T := gw_subst T (@QVbl.Mq2.letf2_post segs) letf2_post in exact T).  Arguments letf2_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope.
Hypothesis floatsitf_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.Mq3.floatsitf_spec segs e_floatsitf) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).  Arguments floatsitf_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope.
Hypothesis multf3_spec : gw_hyp ltac:(let T := gw_callee_type0 (QCa8.multf3_spec segs e_multf3) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).

Definition letf2_callv : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.letf2_callv) constr:(gw_tbl_16)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.letf2_callv)).
Definition floatsitf_callv : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.floatsitf_callv) constr:(gw_tbl_16)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.floatsitf_callv)).
Definition multf3_callq : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.multf3_callq) constr:(gw_tbl_16)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.multf3_callq)).
Definition divtf3_callq : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.divtf3_callq) constr:(gw_tbl_16)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.divtf3_callq)).
Ltac norm_rsegs :=
idtac.

Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.
Ltac mlia2 := rewrite ?land_W64 in *; Z.div_mod_to_equations; lia.
Ltac brs K := if_cases K; rewrite ?bv_lts_0_lit, ?bv_lts_lit in K by lia;
repeat first [apply (proj1 (Bool.negb_true_iff _)) in K | apply (proj1 (Bool.negb_false_iff _)) in K];
first [apply Z.ltb_lt in K | apply Z.ltb_ge in K | idtac]; try (exfalso; lia).
Ltac fixw :=
try match goal with |- context [bv_swrap 32 (?x + ?k)] =>
lazymatch isZcst k with true => idtac end;
first [ assert_succeeds (assert (2^63 <= k)%Z by lia);
let k' := eval vm_compute in (k - 2^64)%Z in rewrite (swrap32_shift x k k') by reflexivity
| idtac ] end;
try match goal with |- context [bv_swrap 32 (?x - ?k)] =>
lazymatch isZcst k with true => idtac end;
first [ assert_succeeds (assert (2^63 <= k)%Z by lia);
let k' := eval vm_compute in (2^64 - k)%Z in rewrite (swrap32_shift_sub x k k') by reflexivity
| idtac ] end;
try rewrite swrap32_land64_add by lia; try rewrite swrap32_land64_small by lia; try rewrite swrap32_small by lia.

Notation F_divtf3_main__divtf3_spec := divtf3_spec (only parsing).

#[using="e_fpclassifyl e_letf2 e_multf3 e_floatsitf e_divtf3 CODE BASE4 BASER D_113 E_113 D_118 E_118 D_124 E_124 D_127 E_127 D_142 E_142 D_158 E_158 D_164 E_164 D_179 E_179 D_217 E_217 D_233 E_233 D_236 E_236 D_278 E_278 LINK_113 LINK_118 LINK_124 LINK_127 LINK_142 LINK_158 LINK_164 LINK_179 LINK_217 LINK_233 LINK_236 LINK_278 divtf3_spec fpclassifyl_spec letf2_spec floatsitf_spec multf3_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_113 joff_118 joff_124 joff_127 joff_142 joff_158 joff_164 joff_179 joff_217 joff_233 joff_236 joff_278 e_fpclassifyl e_letf2 e_multf3 e_floatsitf e_divtf3 CODE BASE4 BASER D_113 E_113 D_118 E_118 D_124 E_124 D_127 E_127 D_142 E_142 D_158 E_158 D_164 E_164 D_179 E_179 D_217 E_217 D_233 E_233 D_236 E_236 D_278 E_278 LINK_113 LINK_118 LINK_124 LINK_127 LINK_142 LINK_158 LINK_164 LINK_179 LINK_217 LINK_233 LINK_236 LINK_278 divtf3_spec fpclassifyl_spec letf2_spec floatsitf_spec multf3_spec.

Definition FMODL : Z := (base + 0x184).
Definition RFMODL_DEPTH : Z := 192.

Ltac lit_loads :=
repeat match goal with
| |- context [sx32 (Z_to_bv 64 ?c)] =>
lazymatch isZcst c with true => idtac end;
let c' := eval vm_compute in (bv_swrap 32 (c mod 2^64))%Z in
let c'' := eval vm_compute in (c' mod 2^64)%Z in
replace (sx32 (Z_to_bv 64 c)) with (Z_to_bv 64 c'') by (unfold sx32; apply Z_to_bv_eqm; vm_compute; reflexivity)
| |- context [zx32 (Z_to_bv 64 ?c)] =>
lazymatch isZcst c with true => idtac end;
let c' := eval vm_compute in ((c mod 2^64) mod 2^32)%Z in
replace (zx32 (Z_to_bv 64 c)) with (Z_to_bv 64 c') by (unfold zx32; apply Z_to_bv_eqm; vm_compute; reflexivity)
end.

Definition extsf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom segs)
/\ munch [] m m /\ wmono segs m m /\ mem_inv segs m.

#[using="w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 CODE"] Lemma extendsftf2_2p120 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
mem_inv segs m ->
evt segs (extsf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (bvmap_set 10 (Z_to_bv 64 18446744071486570496) F) fc C_2P120 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 10 (Z_to_bv 64 18446744071486570496) F) (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof. clear - w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 CODE segs base.
intros until m. intros MI.
zs. lit_loads. zs. zs. zs. zs. zs.
(if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ exfalso; lia | ]); try (exfalso; clear - K1 w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 CODE segs base; cbv in K1; lia).
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia); [ | exfalso; lia ]); try (exfalso; clear - K2 w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 CODE segs base; cbv in K2; lia).
do 11 zs.
apply evt_done. unfold extsf_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl | hyp].
Qed.

#[using="w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 CODE"] Lemma extendsftf2_2pm120 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
mem_inv segs m ->
evt segs (extsf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (bvmap_set 10 (Z_to_bv 64 18446744069473304576) F) fc C_2PM120 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 10 (Z_to_bv 64 18446744069473304576) F) (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof. clear - w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 CODE segs base.
intros until m. intros MI.
zs. lit_loads. zs. zs. zs. zs. zs.
(if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ exfalso; lia | ]); try (exfalso; clear - K1 w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 CODE segs base; cbv in K1; lia).
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia); [ | exfalso; lia ]); try (exfalso; clear - K2 w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 CODE segs base; cbv in K2; lia).
do 11 zs.
apply evt_done. unfold extsf_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl | hyp].
Qed.

#[using="Type"] Lemma m_fpclassifyl_canon : forall y, fpclassifyl (lo64 y + 2^64 * hi64 y) = m_fpclassifyl y.
Proof.
intros y. unfold fpclassifyl, m_fpclassifyl. change (lo64 y + 2^64 * hi64 y)%Z with (canon y).
rewrite lo64_canon, hi64_canon. unfold nz. reflexivity.
Qed.

Definition rfmodl_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(q - RFMODL_DEPTH, q)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' (q - RFMODL_DEPTH) q
/\ (forall k : bv 5, bv_unsigned k <> 10%Z -> reg_get F' k = reg_get F k).

Definition rfmodl_stmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X Y r : Z),
stk segs m (q - RFMODL_DEPTH) q -> mem_inv segs m ->
(4096 <= q - RFMODL_DEPTH)%Z -> (q < 2^63)%Z ->
m_fmodl X Y = Some r ->
evt segs (rfmodl_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FMODL) fc None m (seg_rom segs)).

Section Fmodl.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (X Y r : Z).
Hypothesis SPLO : (4096 <= q - RFMODL_DEPTH)%Z.
Hypothesis SPHI : (q < 2^63)%Z.
Hypothesis HM : m_fmodl X Y = Some r.

Notation POST := (rfmodl_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m0).
Notation SPv := (Z_to_bv 64 (q + -80)).
Definition frame : list cell := [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition finv (m : word -> option byte) : Prop :=
mem_inv segs m /\ munch [(q - RFMODL_DEPTH, q)]%Z m0 m /\ wmono segs m0 m
/\ rw_cells segs m (q + -80) frame /\ stk segs m (q - RFMODL_DEPTH) (q + -80).
Ltac dest_finv H := destruct H as (MI & MU & WM & FR & ST); unfold frame in FR; unfold RFMODL_DEPTH in MU, ST.
Ltac mk_finv := unfold finv, frame, RFMODL_DEPTH; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|hyp].

Definition Fok (F' : bvmap 5 word) : Prop := forall k : bv 5, bv_unsigned k <> 10%Z -> reg_get F' k = reg_get F k.
#[using="Type"] Lemma Fok_refl : Fok F. Proof. clear - ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r SPLO SPHI HM. first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPHI | gw_hide SPHI | idtac]; first [clear HM | gw_hide HM | idtac]. intros k _. reflexivity. Qed.
#[using="Type"] Lemma Fok_set10 : forall F' v, Fok F' -> Fok (bvmap_set 10 v F').
Proof. clear - ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r SPLO SPHI HM. first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPHI | gw_hide SPHI | idtac]; first [clear HM | gw_hide HM | idtac]. intros F' v H k Hk. rewrite reg_get_set_other by (intros E; apply Hk; rewrite <- E; reflexivity). apply H. exact Hk. Qed.

Definition exv : Z := Z.land (Z.shiftr (hi64 X) 48) 0x7fff.
Definition eyv : Z := Z.land (Z.shiftr (hi64 Y) 48) 0x7fff.
Definition sxv : Z := Z.land (Z.shiftr (hi64 X) 48) 0x8000.

#[using="w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 CODE"] Lemma L_ret : forall m (x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word) F' x1,
finv m -> Fok F' ->
evt segs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 (base + 0x200)) fc None m (seg_rom segs)).
Proof. clear - w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 CODE segs base ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r SPLO SPHI HM. try gw_hide SPLO; first [clear SPHI | gw_hide SPHI | idtac]; first [clear HM | gw_hide HM | idtac].
intros until x1. intros FI FOK. dest_finv FI. unfold RFMODL_DEPTH in SPLO.
do 12 zs.
release_frame FR ST q.
apply evt_done. unfold rfmodl_post, RFMODL_DEPTH. repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST | exact FOK].
Qed.

Definition DS : divtf3_stmt := F_divtf3_main__divtf3_spec.
#[using="Type"] Lemma stk_lower : forall m lo lo' hi, stk segs m lo hi -> (lo <= lo' <= hi)%Z -> stk segs m lo' hi.
Proof. clear - segs ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r SPLO SPHI HM. first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPHI | gw_hide SPHI | idtac]; first [clear HM | gw_hide HM | idtac]. intros m lo lo' hi ST H. exact (proj2 (stk_split _ _ _ _ _ ST H)). Qed.

Tactic Notation "call_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 192)%Z (q + -80)%Z |- _ =>
let ST1 := fresh "ST1" in let ST2 := fresh "ST2" in
destruct (stk_split _ _ _ (q + -80 - K)%Z _ ST ltac:(lia)) as [ST1 ST2]; clear ST;
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -80 - K)%Z (q + -80)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1 STn ltac:(lia)) as ST; clear ST1 STn end
end.

#[using="w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_124 joff_127 e_multf3 e_divtf3 CODE BASE4 BASER D_124 E_124 D_127 E_127 LINK_124 LINK_127 divtf3_spec multf3_spec SPLO SPHI"] Lemma L_nan : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word) F' x1,
finv m -> Fok F' -> r = f128_div (f128_mul X Y) (f128_mul X Y) ->
evt segs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 (base + 0x1e0)) fc None m (seg_rom segs)).
Proof. clear - w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_124 joff_127 e_multf3 e_divtf3 CODE BASE4 BASER D_124 E_124 D_127 E_127 LINK_124 LINK_127 divtf3_spec multf3_spec SPLO SPHI segs base ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r HM. first [clear HM | gw_hide HM | idtac].
intros until x1. intros FI FOK Hr. dest_finv FI. unfold RFMODL_DEPTH in SPLO.
zs. zs. zs. zs.
zs. call_split 80%Z (eapply multf3_callq; [hyp | hyp | lia]).
zs. zs.
zs. call_split 112%Z (eapply (divtf3_callq DS); [hyp | hyp | lia]).
rewrite <- Hr. apply L_ret; [mk_finv | exact FOK].
Qed.

#[using="w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_233 joff_236 e_multf3 e_floatsitf CODE BASE4 BASER D_233 E_233 D_236 E_236 LINK_233 LINK_236 floatsitf_spec multf3_spec SPLO SPHI"] Lemma L_zero : forall m (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word) F' x1,
finv m -> Fok F' -> r = f128_mul (f128_of_i32 0) X ->
evt segs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 (base + 0x3a4)) fc None m (seg_rom segs)).
Proof. clear - w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_233 joff_236 e_multf3 e_floatsitf CODE BASE4 BASER D_233 E_233 D_236 E_236 LINK_233 LINK_236 floatsitf_spec multf3_spec SPLO SPHI segs base ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r HM. first [clear HM | gw_hide HM | idtac].
intros until x1. intros FI FOK Hr. dest_finv FI. unfold RFMODL_DEPTH in SPLO.
zs. callw (eapply floatsitf_callv with (v := 0%Z) (i := 0%Z); [hyp | lia | reflexivity]).
zs. zs.
zs. call_split 80%Z (eapply multf3_callq; [hyp | hyp | lia]).
zs. rewrite <- Hr. apply L_ret; [mk_finv | exact FOK].
Qed.

#[using="w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 CODE"] Lemma L_retx : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word) F' x1 lo hi,
finv m -> Fok F' -> Z_to_bv 64 lo = Z_to_bv 64 (lo64 r) -> Z_to_bv 64 hi = Z_to_bv 64 (hi64 r) ->
evt segs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 (base + 0x414)) fc None m (seg_rom segs)).
Proof. clear - w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 CODE segs base ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r SPLO SPHI HM. try gw_hide SPLO; first [clear SPHI | gw_hide SPHI | idtac]; first [clear HM | gw_hide HM | idtac].
intros until hi. intros FI FOK Hlo Hhi. pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO.
zs. zs. zs. rewrite Hlo, Hhi. apply L_ret; [exact FI | exact FOK].
Qed.

#[using="Type"] Lemma sxv_cases : sxv = 0%Z \/ sxv = 32768%Z.
Proof. clear - ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r SPLO SPHI HM. first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPHI | gw_hide SPHI | idtac]; first [clear HM | gw_hide HM | idtac]. unfold sxv. change 32768%Z with (2^15)%Z. rewrite land_pow2_bit by lia. destruct (Z.testbit _ _); [right|left]; reflexivity. Qed.
#[using="Type"] Lemma sext_field : forall e, Z.land (Z.lor (Z.land e 65535) sxv) 65535 = Z.land (Z.lor e sxv) 65535.
Proof. clear - ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r SPLO SPHI HM. first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPHI | gw_hide SPHI | idtac]; first [clear HM | gw_hide HM | idtac].
intros e. rewrite !zb_land_lor_distr_l, <- Z.land_assoc, Z.land_diag. reflexivity.
Qed.
#[using="Type"] Lemma exv_range : (0 <= exv < 32768)%Z.
Proof. clear - ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r SPLO SPHI HM. first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPHI | gw_hide SPHI | idtac]; first [clear HM | gw_hide HM | idtac]. unfold exv. rewrite Z.land_comm. change 32768%Z with (2^15)%Z. apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.land_lt_pow2; [cbn; lia|]. apply Z.shiftr_nonneg. pose proof (hi64_range X). lia. Qed.
#[using="Type"] Lemma eyv_range : (0 <= eyv < 32768)%Z.
Proof. clear - ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r SPLO SPHI HM. first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPHI | gw_hide SPHI | idtac]; first [clear HM | gw_hide HM | idtac]. unfold eyv. rewrite Z.land_comm. change 32768%Z with (2^15)%Z. apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.land_lt_pow2; [cbn; lia|]. apply Z.shiftr_nonneg. pose proof (hi64_range Y). lia. Qed.
#[using="Type"] Lemma shr48X : Z.shiftr (hi64 X) 48 = (hi64 X / 2^48)%Z. Proof. clear - ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r SPLO SPHI HM. first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPHI | gw_hide SPHI | idtac]; first [clear HM | gw_hide HM | idtac]. apply Z.shiftr_div_pow2. lia. Qed.

#[using="Type"] Lemma land_M_16 : forall e, Z.land (Z.land e 18446744073709551615) 65535 = Z.land e 65535.
Proof. clear - ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r SPLO SPHI HM. first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPHI | gw_hide SPHI | idtac]; first [clear HM | gw_hide HM | idtac]. intros. rewrite <- Z.land_assoc. reflexivity. Qed.

#[using="Type"] Lemma pack_bridge : forall xhi xlo E, (0 <= xlo < 2^64)%Z ->
Z_to_bv 64 (Z.lor (Z.land xhi 281474976710655) (Z.land (Z.shiftl (Z.lor (Z.land E 65535) sxv) 48) 18446744073709551615))
= Z_to_bv 64 (hi64 (mk128 (Z.lor (Z.land xhi 281474976710655) (Z.shiftl (Z.land (Z.lor E sxv) 65535) 48)) xlo)).
Proof. clear - ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r SPLO SPHI HM. first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPHI | gw_hide SPHI | idtac]; first [clear HM | gw_hide HM | idtac].
intros xhi xlo E Hxlo. rewrite Z.lor_comm. rewrite (proj1 (pack_eq xhi xlo _ Hxlo)). rewrite sext_field. reflexivity.
Qed.
#[using="Type"] Lemma pack_bridge_lo : forall xhi xlo E, (0 <= xlo < 2^64)%Z ->
Z_to_bv 64 xlo = Z_to_bv 64 (lo64 (mk128 (Z.lor (Z.land xhi 281474976710655) (Z.shiftl (Z.land (Z.lor E sxv) 65535) 48)) xlo)).
Proof. clear - ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r SPLO SPHI HM. first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPHI | gw_hide SPHI | idtac]; first [clear HM | gw_hide HM | idtac]. intros xhi xlo E Hxlo. exact (proj2 (pack_eq xhi xlo _ Hxlo)). Qed.

#[using="w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_278 e_multf3 CODE BASE4 BASER D_278 E_278 LINK_278 multf3_spec SPLO SPHI"] Lemma L_scale : forall m (x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x20 x21 x24 x28 x29 x30 x31 : word) F' x1
(xhi xlo ex : Z),
finv m -> Fok F' ->
(0 <= xhi < 2^64)%Z -> (0 <= xlo < 2^64)%Z -> (-2^20 <= ex < 2^20)%Z ->
fmodl_scale sxv (xhi, xlo, ex) = r ->
evt segs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 xhi) (Z_to_bv 64 32768) x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 xlo) x20 x21 (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 (base + 0x3e4)) fc None m (seg_rom segs)).
Proof. clear - w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_278 e_multf3 CODE BASE4 BASER D_278 E_278 LINK_278 multf3_spec SPLO SPHI segs base ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r HM. first [clear HM | gw_hide HM | idtac].
intros until ex. intros FI FOK Rh Rl Re HS.
pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO. pose proof (hi64_range X) as RHX.
pose proof sxv_cases as SX. unfold sxv in SX.
unfold fmodl_scale in HS.
zs. zs. zs. zs. zs. zs. brs K1.
-
replace (ex <=? 0) with true in HS by (symmetry; apply Z.leb_le; lia).
do 7 zs. rewrite ?land_M_16. change (Z.land (Z.shiftr (hi64 X) 48) 32768) with sxv. rewrite (pack_bridge xhi xlo (ex + 120)) by lia.
rewrite (land_W64 xlo), (Z.mod_small xlo) by lia.
zs. zs. zs. callw (eapply extendsftf2_2pm120; hyp).
zs. zs. zs. zs. rewrite (pack_bridge_lo xhi xlo (ex + 120)) by lia.
zs. call_split 80%Z (eapply multf3_callq; [hyp | hyp | lia]).
zs. rewrite HS. apply L_ret; [mk_finv | apply Fok_set10; exact FOK].
- replace (ex <=? 0) with false in HS by (symmetry; apply Z.leb_gt; lia).
do 6 zs. rewrite ?land_M_16. change (Z.land (Z.shiftr (hi64 X) 48) 32768) with sxv. rewrite (pack_bridge xhi xlo ex) by lia.
rewrite (land_W64 xlo), (Z.mod_small xlo) by lia.
eapply L_retx; [exact FI | exact FOK | rewrite <- HS; apply pack_bridge_lo; lia | rewrite <- HS; reflexivity].
Qed.

#[using="w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_278 e_multf3 CODE BASE4 BASER D_278 E_278 LINK_278 multf3_spec SPLO SPHI"] Lemma L_L2 : forall (n : nat) m (x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x20 x21 x24 x28 x29 x30 x31 : word) F' x1
(xhi xlo ex : Z) st',
finv m -> Fok F' ->
(0 <= xhi < 2^48)%Z -> (0 <= xlo < 2^64)%Z -> (-2^20 + Z.of_nat n <= ex < 2^20)%Z ->
fmodl_norm_loop n (fmodl_norm_body (xhi, xlo, ex)) = Some st' -> fmodl_scale sxv st' = r ->
evt segs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 xhi) (Z_to_bv 64 32768) x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 xlo) x20 x21 (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 (base + 0x3c8)) fc None m (seg_rom segs)).
Proof. clear - w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_278 e_multf3 CODE BASE4 BASER D_278 E_278 LINK_278 multf3_spec SPLO SPHI segs base ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r HM. first [clear HM | gw_hide HM | idtac].
induction n as [|n IH]; intros until st'; intros FI FOK Rh Rl Re HL HS; [discriminate HL|].
pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO. pose proof (hi64_range X) as RHX.
unfold fmodl_norm_body in HL. rewrite fmodl_norm_loop_step in HL.
zs. zs. zs. zs. zs. zs. fixw. zs.

set (b := Z.shiftr xlo 63) in *. assert (Rb : (0 <= b <= 1)%Z) by (subst b; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
assert (E1 : Z.land (Z.shiftl xhi 1) 18446744073709551615 = (xhi * 2)%Z) by (rewrite land_W64, Z.shiftl_mul_pow2 by lia; apply Z.mod_small; lia).
rewrite !E1 in *.
assert (E2 : Z.lor (xhi * 2) b = (b + xhi * 2)%Z) by (rewrite Z.lor_comm; change (xhi * 2)%Z with (xhi * 2^1)%Z; apply lor_low_high; lia).
rewrite !E2 in *.
assert (E3 : u64 (2 * xhi + b) = (b + xhi * 2)%Z) by (unfold u64; rewrite Z.mod_small by lia; lia).
rewrite !E3 in HL.
assert (E4 : Z.shiftr (b + xhi * 2) 48 = Z.shiftr (xhi * 2) 48) by (rewrite !Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
rewrite E4 in HL.
assert (R5 : (0 <= Z.shiftr (xhi * 2) 48 < 2^16)%Z) by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
assert (E6 : Z.land (Z.shiftl xlo 1) 18446744073709551615 = u64 (2 * xlo)) by (unfold u64; rewrite land_W64, Z.shiftl_mul_pow2 by lia; f_equal; lia).
rewrite ?E6 in *. pose proof (Z.mod_pos_bound (2 * xlo) (2^64) ltac:(lia)) as R6. unfold u64 in *.
replace (Z_to_bv 64 (Z.shiftl xlo 1)) with (Z_to_bv 64 ((2 * xlo) mod 2^64)%Z) by (apply Z_to_bv_eqm; rewrite Z.shiftl_mul_pow2, Z.mod_mod by lia; f_equal; lia).
replace (ex + -1)%Z with (ex - 1)%Z by lia.
(if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)); rewrite ?Z.shiftr_div_pow2 in K2 by lia.
-
replace (Z.shiftr (xhi * 2) 48 =? 0) with true in HL by (symmetry; apply Z.eqb_eq; rewrite Z.shiftr_div_pow2 by lia; lia).
eapply (IH m); [exact FI | exact FOK | | | | exact HL | exact HS]; lia.
- replace (Z.shiftr (xhi * 2) 48 =? 0) with false in HL by (symmetry; apply Z.eqb_neq; rewrite Z.shiftr_div_pow2 by lia; lia).
injection HL as <-.
eapply L_scale; [exact FI | exact FOK | lia | lia | lia | exact HS].
Qed.

#[using="w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_278 e_multf3 CODE BASE4 BASER D_278 E_278 LINK_278 multf3_spec SPLO SPHI"] Lemma L_K2 : forall m (x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x24 x28 x29 x30 x31 : word) F' x1
(xhi xlo ex : Z),
finv m -> Fok F' ->
(0 <= xhi < 2^64)%Z -> (0 <= xlo < 2^64)%Z -> (-2^19 <= ex < 2^19)%Z ->
fmodl_K2 sxv (xhi, xlo, ex) = Some r ->
evt segs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 xhi) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 xlo) x20 x21 (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 (base + 0x3bc)) fc None m (seg_rom segs)).
Proof. clear - w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_278 e_multf3 CODE BASE4 BASER D_278 E_278 LINK_278 multf3_spec SPLO SPHI segs base ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r HM. first [clear HM | gw_hide HM | idtac].
intros until ex. intros FI FOK Rh Rl Re HK.
pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO. pose proof (hi64_range X) as RHX.
unfold fmodl_K2 in HK. change 130%nat with (S 129) in HK. rewrite fmodl_norm_loop_step in HK.
pose proof (shr48_range xhi Rh) as R48.
rewrite Z.shiftr_div_pow2 in R48 by lia.
zs. zs. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia)); rewrite ?Z.shiftr_div_pow2 in K1 by lia.
- replace (Z.shiftr xhi 48 =? 0) with false in HK by (symmetry; apply Z.eqb_neq; rewrite Z.shiftr_div_pow2 by lia; lia). injection HK as HS.
eapply L_scale; [exact FI | exact FOK | lia | lia | lia | exact HS].
- replace (Z.shiftr xhi 48 =? 0) with true in HK by (symmetry; apply Z.eqb_eq; rewrite Z.shiftr_div_pow2 by lia; lia).
destruct (fmodl_norm_loop 129 _) as [st'|] eqn:HL; [|discriminate HK]. injection HK as HS.
eapply L_L2; [exact FI | exact FOK | | exact Rl | | exact HL | exact HS].
+ Z.div_mod_to_equations. lia.
+ lia.
Qed.

#[using="w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_233 joff_236 joff_278 e_multf3 e_floatsitf CODE BASE4 BASER D_233 E_233 D_236 E_236 D_278 E_278 LINK_233 LINK_236 LINK_278 floatsitf_spec multf3_spec SPLO SPHI"] Lemma L_fin : forall m (x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x21 x24 x28 x29 x30 x31 : word) F' x1
(xhi xlo yhi ylo ex : Z),
finv m -> Fok F' ->
(0 <= xhi < 2^64)%Z -> (0 <= xlo < 2^64)%Z -> (0 <= yhi < 2^64)%Z -> (0 <= ylo < 2^64)%Z -> (-2^19 <= ex < 2^19)%Z ->
fmodl_K1 X yhi ylo sxv (inl (xhi, xlo, ex)) = Some r ->
evt segs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 yhi) (Z_to_bv 64 xhi) x12 x13 x14 x15 x16 x17
(Z_to_bv 64 ylo) (Z_to_bv 64 xlo) x20 x21 (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 (base + 0x384)) fc None m (seg_rom segs)).
Proof. clear - w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_233 joff_236 joff_278 e_multf3 e_floatsitf CODE BASE4 BASER D_233 E_233 D_236 E_236 D_278 E_278 LINK_233 LINK_236 LINK_278 floatsitf_spec multf3_spec SPLO SPHI segs base ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r HM. first [clear HM | gw_hide HM | idtac].
intros until ex. intros FI FOK Rxh Rxl Ryh Ryl Re HK.
pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO. pose proof (hi64_range X) as RHX.
unfold fmodl_K1, fmodl_fin in HK.
destruct (sbb_bridge xhi xlo yhi ylo Rxh Rxl Ryh Ryl) as (B1 & B2 & B3 & B4). cbv zeta in B1, B2, B3.
set (hi' := if xlo <? ylo then u64 (u64 (xhi - yhi) - 1) else u64 (xhi - yhi)) in *.
zs. zs. zs. rewrite B2.
rewrite (shr63_eqb hi') in HK by lia.
zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia)).
-
replace (hi' <? 2^63) with false in HK by (symmetry; apply Z.ltb_ge; lia).
zs. eapply L_K2; [exact FI | exact FOK | lia | lia | lia | exact HK].
- replace (hi' <? 2^63) with true in HK by (symmetry; apply Z.ltb_lt; lia).
zs. zs. rewrite <- B4. pose proof (Z.mod_pos_bound (xlo - ylo) (2^64) ltac:(lia)) as Rlo. unfold u64 in HK, Rlo |- *.
assert (RL : (0 <= Z.lor hi' ((xlo - ylo) mod 2^64) < 2^64)%Z) by (apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.lor_lt_pow2; lia).
change 18446744073709551616%Z with (2^64)%Z in *.
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)); rewrite ?land_W64 in K2; rewrite ?(Z.mod_small (Z.lor _ _) (2^64)) in K2 by lia; change 18446744073709551616%Z with (2^64)%Z in K2.
+ replace (Z.lor hi' ((xlo - ylo) mod 2 ^ 64) =? 0) with false in HK by (symmetry; apply Z.eqb_neq; exact K2).
rewrite <- (Z_to_bv_mod64 (xlo - ylo)).
eapply L_K2; [exact FI | exact FOK | lia | lia | lia | exact HK].
+ replace (Z.lor hi' ((xlo - ylo) mod 2 ^ 64) =? 0) with true in HK by (symmetry; apply Z.eqb_eq; exact K2).
injection HK as Hr. zs. eapply L_zero; [exact FI | exact FOK | symmetry; exact Hr].
Qed.

#[using="Type"] Lemma dbl_bridge : forall h b, (0 <= h < 2^64)%Z -> (0 <= b <= 1)%Z ->
Z.lor (Z.land (Z.shiftl h 1) 18446744073709551615) b = u64 (2 * h + b).
Proof. clear - ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r SPLO SPHI HM. first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPHI | gw_hide SPHI | idtac]; first [clear HM | gw_hide HM | idtac].
intros h b Hh Hb. rewrite land_W64, Z.shiftl_mul_pow2 by lia. unfold u64.
replace ((h * 2^1) mod 2^64)%Z with ((h mod 2^63) * 2^1)%Z by (Z.div_mod_to_equations; lia).
rewrite Z.lor_comm, lor_low_high by (try lia; Z.div_mod_to_equations; lia).
Z.div_mod_to_equations; lia.
Qed.
#[using="Type"] Lemma shr63_b : forall l, (0 <= l < 2^64)%Z -> (0 <= Z.shiftr l 63 <= 1)%Z.
Proof. clear - ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r SPLO SPHI HM. first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPHI | gw_hide SPHI | idtac]; first [clear HM | gw_hide HM | idtac]. intros l Hl. rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations; lia. Qed.
#[using="Type"] Lemma u64_range : forall v, (0 <= u64 v < 2^64)%Z.
Proof. clear - ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r SPLO SPHI HM. first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPHI | gw_hide SPHI | idtac]; first [clear HM | gw_hide HM | idtac]. intros. unfold u64. apply Z.mod_pos_bound. lia. Qed.
#[using="Type"] Lemma zbv_shl1 : forall v, Z_to_bv 64 (Z.shiftl v 1) = Z_to_bv 64 (u64 (2 * v)).
Proof. clear - ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r SPLO SPHI HM. first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPHI | gw_hide SPHI | idtac]; first [clear HM | gw_hide HM | idtac]. intros. rewrite zbv_u64, Z.shiftl_mul_pow2 by lia. f_equal. lia. Qed.

#[using="w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_233 joff_236 joff_278 e_multf3 e_floatsitf CODE BASE4 BASER D_233 E_233 D_236 E_236 D_278 E_278 LINK_233 LINK_236 LINK_278 floatsitf_spec multf3_spec SPLO SPHI"] Lemma L_L1 : forall (yhi ylo ey : Z) (n : nat) m (x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31 : word) F' x1
(xhi xlo ex : Z) res,
finv m -> Fok F' ->
(0 <= xhi < 2^64)%Z -> (0 <= xlo < 2^64)%Z -> (0 <= yhi < 2^64)%Z -> (0 <= ylo < 2^64)%Z ->
(-2^18 <= ey)%Z -> (ey < ex < 2^18)%Z ->
fmodl_sub_loop (S n) X yhi ylo ey (xhi, xlo, ex) = Some res -> fmodl_K1 X yhi ylo sxv res = Some r ->
evt segs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 yhi) (Z_to_bv 64 xhi) x12 x13 x14 x15 x16 x17
(Z_to_bv 64 ylo) (Z_to_bv 64 xlo) x20 x21 (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) (Z_to_bv 64 ey) s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 (base + 0x31c)) fc None m (seg_rom segs)).
Proof. clear - w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_233 joff_236 joff_278 e_multf3 e_floatsitf CODE BASE4 BASER D_233 E_233 D_236 E_236 D_278 E_278 LINK_233 LINK_236 LINK_278 floatsitf_spec multf3_spec SPLO SPHI segs base ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r HM. first [clear HM | gw_hide HM | idtac].
intros yhi ylo ey. induction n as [|n IH]; intros until res; intros FI FOK Rxh Rxl Ryh Ryl Rey Rex HL HK.
all: pose proof FI as FI'; dest_finv FI'; unfold RFMODL_DEPTH in SPLO; pose proof (hi64_range X) as RHX.
all: rewrite fmodl_sub_loop_step in HL; replace (ey <? ex) with true in HL by (symmetry; apply Z.ltb_lt; lia).
all: unfold fmodl_sub_body in HL.
all: destruct (sbb_bridge xhi xlo yhi ylo Rxh Rxl Ryh Ryl) as (B1 & B2 & B3 & B4); cbv zeta in B1, B2, B3.
all: set (hi' := if xlo <? ylo then u64 (u64 (xhi - yhi) - 1) else u64 (xhi - yhi)) in *.
all: rewrite (shr63_eqb hi') in HL by lia.
all: pose proof (shr63_b xlo Rxl) as Rb; pose proof (u64_range (xlo - ylo)) as Rlo; pose proof (shr63_b (u64 (xlo - ylo)) Rlo) as Rb2.
all: zs; zs; zs; rewrite B2; zs; (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia)).

- replace (hi' <? 2^63) with false in HL by (symmetry; apply Z.ltb_ge; lia). cbn [fmodl_sub_loop] in HL. discriminate HL.
- replace (hi' <? 2^63) with true in HL by (symmetry; apply Z.ltb_lt; lia).
zs. rewrite <- (Z_to_bv_mod64 (xlo - ylo)). change ((xlo - ylo) mod 2^64)%Z with (u64 (xlo - ylo)).
assert (RL : (0 <= Z.lor hi' (u64 (xlo - ylo)) < 2^64)%Z) by (apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.lor_lt_pow2; lia).
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)); rewrite ?land_W64 in K2; rewrite ?(Z.mod_small (Z.lor _ _) (2^64)) in K2 by lia; change 18446744073709551616%Z with (2^64)%Z in K2.
+ replace (Z.lor hi' (u64 (xlo - ylo)) =? 0) with true in HL by (symmetry; apply Z.eqb_eq; exact K2).
injection HL as <-. cbn [fmodl_K1] in HK. injection HK as Hr.
zs. eapply L_zero; [exact FI | exact FOK | symmetry; exact Hr].
+ replace (Z.lor hi' (u64 (xlo - ylo)) =? 0) with false in HL by (symmetry; apply Z.eqb_neq; exact K2).
cbn [fmodl_sub_loop] in HL. discriminate HL.
-
replace (hi' <? 2^63) with false in HL by (symmetry; apply Z.ltb_ge; lia).
zs. zs. zs. rewrite (dbl_bridge xhi (Z.shiftr xlo 63)) by lia.
zs. fixw. zs. rewrite zbv_shl1. zs. brs K3.
*
rewrite fmodl_sub_loop_step in HL. replace (ey <? ex - 1) with false in HL by (symmetry; apply Z.ltb_ge; lia).
injection HL as <-. zs. replace (ex - 1)%Z with ey in HK by lia.
eapply L_fin; [exact FI | exact FOK | apply u64_range | apply u64_range | lia | lia | lia | exact HK].
* eapply IH; [exact FI | exact FOK | apply u64_range | apply u64_range | lia | lia | lia | lia | exact HL | exact HK].
- replace (hi' <? 2^63) with true in HL by (symmetry; apply Z.ltb_lt; lia).
zs. rewrite <- (Z_to_bv_mod64 (xlo - ylo)). change ((xlo - ylo) mod 2^64)%Z with (u64 (xlo - ylo)).
assert (RL : (0 <= Z.lor hi' (u64 (xlo - ylo)) < 2^64)%Z) by (apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.lor_lt_pow2; lia).
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)); rewrite ?land_W64 in K2; rewrite ?(Z.mod_small (Z.lor _ _) (2^64)) in K2 by lia; change 18446744073709551616%Z with (2^64)%Z in K2.
+ replace (Z.lor hi' (u64 (xlo - ylo)) =? 0) with true in HL by (symmetry; apply Z.eqb_eq; exact K2).
injection HL as <-. cbn [fmodl_K1] in HK. injection HK as Hr.
zs. eapply L_zero; [exact FI | exact FOK | symmetry; exact Hr].
+ replace (Z.lor hi' (u64 (xlo - ylo)) =? 0) with false in HL by (symmetry; apply Z.eqb_neq; exact K2).
zs. zs. zs. rewrite (dbl_bridge hi' (Z.shiftr (u64 (xlo - ylo)) 63)) by lia. zs.
zs. fixw. zs. rewrite zbv_shl1. zs. brs K3.
*
rewrite fmodl_sub_loop_step in HL. replace (ey <? ex - 1) with false in HL by (symmetry; apply Z.ltb_ge; lia).
injection HL as <-. zs. replace (ex - 1)%Z with ey in HK by lia.
eapply L_fin; [exact FI | exact FOK | apply u64_range | apply u64_range | lia | lia | lia | exact HK].
* eapply IH; [exact FI | exact FOK | apply u64_range | apply u64_range | lia | lia | lia | lia | exact HL | exact HK].
Qed.

#[using="Type"] Lemma ex_field : forall v, (0 <= v < 2^16)%Z -> Z.shiftr (Z.land (Z.shiftl v 49) 18446744073709551615) 49 = Z.land v 32767.
Proof. clear - ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r SPLO SPHI HM. first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPHI | gw_hide SPHI | idtac]; first [clear HM | gw_hide HM | idtac].
intros v Hv. apply Z.bits_inj'. intros i Hi.
rewrite Z.shiftr_spec, Z.land_spec, Z.land_spec by lia.
change 18446744073709551615%Z with (Z.ones 64). change 32767%Z with (Z.ones 15).
destruct (Z.lt_ge_cases i 15).
- rewrite Z.shiftl_spec, !Z.ones_spec_low by lia. rewrite !Bool.andb_true_r. f_equal. lia.
- rewrite (Z.ones_spec_high 64), (Z.ones_spec_high 15) by lia. now rewrite !Bool.andb_false_r.
Qed.
#[using="Type"] Lemma mant_or_range : forall h, (0 <= Z.lor (Z.land h 281474976710655) 281474976710656 < 2^64)%Z.
Proof. clear - ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r SPLO SPHI HM. first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPHI | gw_hide SPHI | idtac]; first [clear HM | gw_hide HM | idtac].
intros h. pose proof (land48_range h) as R. change 0x0000ffffffffffff%Z with 281474976710655%Z in R.
change 281474976710656%Z with (1 * 2^48)%Z. rewrite lor_low_high by lia. lia.
Qed.

#[using="w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_233 joff_236 joff_278 e_multf3 e_floatsitf CODE BASE4 BASER D_233 E_233 D_236 E_236 D_278 E_278 LINK_233 LINK_236 LINK_278 floatsitf_spec multf3_spec SPLO SPHI"] Lemma L_setup : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) F' x1
(uxh uxl uyh uyl ex ey : Z),
finv m -> Fok F' ->
(0 <= uxh < 2^64)%Z -> (0 <= uxl < 2^64)%Z -> (0 <= uyh < 2^64)%Z -> (0 <= uyl < 2^64)%Z ->
(-2^18 <= ey < 2^18)%Z -> (-2^18 <= ex < 2^18)%Z ->
match fmodl_sub_loop (S (Z.to_nat (ex - ey))) X (Z.lor (Z.land uyh 0x0000ffffffffffff) (2^48)) uyl ey
(Z.lor (Z.land uxh 0x0000ffffffffffff) (2^48), uxl, ex) with
| Some res => fmodl_K1 X (Z.lor (Z.land uyh 0x0000ffffffffffff) (2^48)) uyl sxv res
| None => None end = Some r ->
evt segs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 uyl) (Z_to_bv 64 uxl) (Z_to_bv 64 uyh) (Z_to_bv 64 uxh) (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) (Z_to_bv 64 ey) s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 (base + 0x2e0)) fc None m (seg_rom segs)).
Proof. clear - w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_233 joff_236 joff_278 e_multf3 e_floatsitf CODE BASE4 BASER D_233 E_233 D_236 E_236 D_278 E_278 LINK_233 LINK_236 LINK_278 floatsitf_spec multf3_spec SPLO SPHI segs base ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r HM. first [clear HM | gw_hide HM | idtac].
intros until ey. intros FI FOK R1 R2 R3 R4 R5 R6 HK.
pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO. pose proof (hi64_range X) as RHX.
pose proof (mant_or_range uxh) as Q1. pose proof (mant_or_range uyh) as Q2.
change (2^48)%Z with 281474976710656%Z in HK. change 0x0000ffffffffffff%Z with 281474976710655%Z in HK.
do 7 zs. rewrite ?land_W64, ?(Z.mod_small (Z.lor _ _) (2^64)) by lia.
zs. brs K1.
-
destruct (fmodl_sub_loop _ _ _ _ _ _) as [res|] eqn:HL; [|discriminate HK].
eapply L_L1; [exact FI | exact FOK | lia | lia | lia | lia | lia | lia | exact HL | exact HK].
- zs. rewrite fmodl_sub_loop_step in HK. replace (ey <? ex) with false in HK by (symmetry; apply Z.ltb_ge; lia).
eapply L_fin; [exact FI | exact FOK | lia | lia | lia | lia | lia | exact HK].
Qed.

Definition UX : Z := mk128 (Z.land (hi64 X) 0x7fffffffffffffff) (lo64 X).
Definition UY : Z := mk128 (Z.land (hi64 Y) 0x7fffffffffffffff) (lo64 Y).
#[using="Type"] Lemma UX_words : lo64 UX = lo64 X /\ hi64 UX = Z.land (hi64 X) 0x7fffffffffffffff.
Proof. clear - ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r SPLO SPHI HM. first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPHI | gw_hide SPHI | idtac]; first [clear HM | gw_hide HM | idtac]. unfold UX. pose proof (lo64_range X). pose proof (land63_range (hi64 X) (hi64_range X)). rewrite lo64_mk128, hi64_mk128 by lia. split; reflexivity. Qed.
#[using="Type"] Lemma UY_words : lo64 UY = lo64 Y /\ hi64 UY = Z.land (hi64 Y) 0x7fffffffffffffff.
Proof. clear - ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r SPLO SPHI HM. first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPHI | gw_hide SPHI | idtac]; first [clear HM | gw_hide HM | idtac]. unfold UY. pose proof (lo64_range Y). pose proof (land63_range (hi64 Y) (hi64_range Y)). rewrite lo64_mk128, hi64_mk128 by lia. split; reflexivity. Qed.

Definition K_normy (ux ex uy ey : Z) : option Z :=
(let xhi := Z.lor (Z.land (hi64 ux) 0x0000ffffffffffff) (2^48) in
let yhi := Z.lor (Z.land (hi64 uy) 0x0000ffffffffffff) (2^48) in
match fmodl_sub_loop (S (Z.to_nat (ex - ey))) X yhi (lo64 uy) ey (xhi, lo64 ux, ex) with
| Some res => fmodl_K1 X yhi (lo64 uy) sxv res
| None => None end)%Z.

#[using="w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_179 joff_233 joff_236 joff_278 e_multf3 e_floatsitf CODE BASE4 BASER D_179 E_179 D_233 E_233 D_236 E_236 D_278 E_278 LINK_179 LINK_233 LINK_236 LINK_278 floatsitf_spec multf3_spec SPLO SPHI"] Lemma L_normy : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) F' x1 (ux ex : Z) (wl wh : word),
finv m -> Fok F' -> (-2^18 <= ex < 2^18)%Z ->
K_normy ux ex (f128_mul UY C_2P120) (Z.shiftr (hi64 (f128_mul UY C_2P120)) 48 - 120)%Z = Some r ->
wl = Z_to_bv 64 (lo64 ux) -> wh = Z_to_bv 64 (hi64 ux) ->
evt segs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (lo64 UY)) wl (Z_to_bv 64 (hi64 UY)) wh (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) (Z_to_bv 64 0) s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 (base + 0x2b0)) fc None m (seg_rom segs)).
Proof. clear - w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_179 joff_233 joff_236 joff_278 e_multf3 e_floatsitf CODE BASE4 BASER D_179 E_179 D_233 E_233 D_236 E_236 D_278 E_278 LINK_179 LINK_233 LINK_236 LINK_278 floatsitf_spec multf3_spec SPLO SPHI segs base ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r HM. first [clear HM | gw_hide HM | idtac].
intros until wh. intros FI FOK Re HK -> ->.
pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO. pose proof (hi64_range X) as RHX.
pose proof (lo64_range UY) as R1. pose proof (hi64_range UY) as R2. pose proof (lo64_range ux) as R3. pose proof (hi64_range ux) as R4.
zs. zs. zs. callw (eapply extendsftf2_2p120; hyp).
zs. zs. zs. zs.
zs. call_split 80%Z (eapply multf3_callq; [hyp | hyp | lia]).
set (uy' := f128_mul UY C_2P120) in *. pose proof (lo64_range uy') as R5. pose proof (hi64_range uy') as R6.
pose proof (shr48_range (hi64 uy') R6) as R7.
zs. zs. zs. zs.
unfold K_normy in HK.
eapply L_setup; [mk_finv | apply Fok_set10; exact FOK | lia | lia | lia | lia | | lia | exact HK].
rewrite Z.shiftr_div_pow2 in R7 |- * by lia. lia.
Qed.

#[using="w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_179 joff_217 joff_233 joff_236 joff_278 e_multf3 e_floatsitf CODE BASE4 BASER D_179 E_179 D_217 E_217 D_233 E_233 D_236 E_236 D_278 E_278 LINK_179 LINK_217 LINK_233 LINK_236 LINK_278 floatsitf_spec multf3_spec SPLO SPHI"] Lemma L_norm : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31 : word) F' x1,
finv m -> Fok F' ->
(let '(ux, ex) := (if exv =? 0 then (f128_mul UX C_2P120, Z.shiftr (hi64 (f128_mul UX C_2P120)) 48 - 120) else (UX, exv))%Z in
let '(uy, ey) := (if eyv =? 0 then (f128_mul UY C_2P120, Z.shiftr (hi64 (f128_mul UY C_2P120)) 48 - 120) else (UY, eyv))%Z in
K_normy ux ex uy ey) = Some r ->
evt segs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 (Z.land (hi64 Y) 0x7fffffffffffffff)) (Z_to_bv 64 (Z.land (hi64 X) 0x7fffffffffffffff))
(Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 exv) x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 (base + 0x29c)) fc None m (seg_rom segs)).
Proof. clear - w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_179 joff_217 joff_233 joff_236 joff_278 e_multf3 e_floatsitf CODE BASE4 BASER D_179 E_179 D_217 E_217 D_233 E_233 D_236 E_236 D_278 E_278 LINK_179 LINK_217 LINK_233 LINK_236 LINK_278 floatsitf_spec multf3_spec SPLO SPHI segs base ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r HM. first [clear HM | gw_hide HM | idtac].
intros until x1. intros FI FOK HK.
pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO.
pose proof (hi64_range X) as RHX. pose proof (lo64_range X) as RLX. pose proof (hi64_range Y) as RHY. pose proof (lo64_range Y) as RLY.
pose proof exv_range as REX. pose proof eyv_range as REY.
pose proof (land63_range (hi64 X) RHX) as R63X. pose proof (land63_range (hi64 Y) RHY) as R63Y.
destruct UX_words as [EUXl EUXh]. destruct UY_words as [EUYl EUYh].
zs. zs. rewrite (fpc_exp_field (hi64 Y)) by lia. change (Z.land (Z.shiftr (hi64 Y) 48) 32767) with eyv.
zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia)).
-
replace (exv =? 0) with true in HK by (symmetry; apply Z.eqb_eq; lia).
zs. zs. zs. callw (eapply extendsftf2_2p120; hyp).
zs. zs. rewrite <- EUXl, <- EUXh. zs. zs.
zs. call_split 80%Z (eapply multf3_callq; [hyp | hyp | lia]).
rewrite EUXl.
set (ux' := f128_mul UX C_2P120) in *. pose proof (lo64_range ux') as R5. pose proof (hi64_range ux') as R6.
pose proof (shr48_range (hi64 ux') R6) as R7. rewrite Z.shiftr_div_pow2 in R7 by lia.
zs. zs. zs. zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+
replace (eyv =? 0) with false in HK by (symmetry; apply Z.eqb_neq; lia). cbv beta iota zeta in HK. unfold K_normy in HK.
rewrite EUYl, EUYh in HK.
eapply L_setup; [mk_finv | apply Fok_set10; exact FOK | lia | lia | lia | lia | lia | | exact HK].
rewrite Z.shiftr_div_pow2 by lia. lia.
+ replace (eyv =? 0) with true in HK by (symmetry; apply Z.eqb_eq; lia). cbv beta iota zeta in HK.
zs. rewrite <- EUYl, <- EUYh, K2. eapply L_normy; [mk_finv | apply Fok_set10; exact FOK | | exact HK | reflexivity | reflexivity].
rewrite Z.shiftr_div_pow2 by lia. lia.
- replace (exv =? 0) with false in HK by (symmetry; apply Z.eqb_neq; lia). cbv beta iota zeta in HK.
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ replace (eyv =? 0) with false in HK by (symmetry; apply Z.eqb_neq; lia). cbv beta iota zeta in HK. unfold K_normy in HK.
rewrite EUXl, EUXh, EUYl, EUYh in HK.
eapply L_setup; [exact FI | exact FOK | lia | lia | lia | lia | lia | lia | exact HK].
+ replace (eyv =? 0) with true in HK by (symmetry; apply Z.eqb_eq; lia). cbv beta iota zeta in HK.
rewrite <- EUYl, <- EUYh, K2. eapply L_normy; [exact FI | exact FOK | lia | exact HK | rewrite EUXl; reflexivity | rewrite EUXh; reflexivity].
Qed.

Definition K_norm : option Z :=
(let '(ux, ex) := (if exv =? 0 then (f128_mul UX C_2P120, Z.shiftr (hi64 (f128_mul UX C_2P120)) 48 - 120) else (UX, exv))%Z in
let '(uy, ey) := (if eyv =? 0 then (f128_mul UY C_2P120, Z.shiftr (hi64 (f128_mul UY C_2P120)) 48 - 120) else (UY, eyv))%Z in
K_normy ux ex uy ey).
Definition K_cmp : option Z :=
if f128_le UX UY <=? 0 then (if f128_le UX UY =? 0 then Some (f128_mul (f128_of_i32 0) X) else Some X) else K_norm.

#[using="w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_124 joff_127 joff_158 joff_164 joff_179 joff_217 joff_233 joff_236 joff_278 e_letf2 e_multf3 e_floatsitf e_divtf3 CODE BASE4 BASER D_124 E_124 D_127 E_127 D_158 E_158 D_164 E_164 D_179 E_179 D_217 E_217 D_233 E_233 D_236 E_236 D_278 E_278 LINK_124 LINK_127 LINK_158 LINK_164 LINK_179 LINK_217 LINK_233 LINK_236 LINK_278 divtf3_spec letf2_spec floatsitf_spec multf3_spec SPLO SPHI"] Lemma L_cmp : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) x1,
finv m ->
(if exv =? 32767 then Some (f128_div (f128_mul X Y) (f128_mul X Y)) else K_cmp) = Some r ->
evt segs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x240)) fc None m (seg_rom segs)).
Proof. clear - w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_124 joff_127 joff_158 joff_164 joff_179 joff_217 joff_233 joff_236 joff_278 e_letf2 e_multf3 e_floatsitf e_divtf3 CODE BASE4 BASER D_124 E_124 D_127 E_127 D_158 E_158 D_164 E_164 D_179 E_179 D_217 E_217 D_233 E_233 D_236 E_236 D_278 E_278 LINK_124 LINK_127 LINK_158 LINK_164 LINK_179 LINK_217 LINK_233 LINK_236 LINK_278 divtf3_spec letf2_spec floatsitf_spec multf3_spec SPLO SPHI segs base ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r HM. first [clear HM | gw_hide HM | idtac].
intros until x1. intros FI HK.
pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO.
pose proof (hi64_range X) as RHX. pose proof (lo64_range X) as RLX. pose proof (hi64_range Y) as RHY. pose proof (lo64_range Y) as RLY.
pose proof (shr48_range (hi64 X) RHX) as R48.
pose proof (land63_range (hi64 X) RHX) as R63X. pose proof (land63_range (hi64 Y) RHY) as R63Y.
destruct UX_words as [EUXl EUXh]. destruct UY_words as [EUYl EUYh].
pose proof exv_range as REX.
zs. zs. zs. zs. try rewrite (ex_field (Z.shiftr (hi64 X) 48)) by lia. change (Z.land (Z.shiftr (hi64 X) 48) 32767) with exv.
zs. fixw. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia)).
- replace (exv =? 32767) with true in HK by (symmetry; apply Z.eqb_eq; lia). injection HK as Hr.
eapply L_nan; [exact FI | apply Fok_refl | symmetry; exact Hr].
- replace (exv =? 32767) with false in HK by (symmetry; apply Z.eqb_neq; lia). unfold K_cmp in HK.
pose proof (f128_le_range UX UY) as RLE.
zs. zs. zs. zs. zs. zs. zs. zs.
rewrite <- EUXl, <- EUXh, <- EUYl, <- EUYh.
zs. callw (eapply letf2_callv; hyp).
zs. brs K2.
+ replace (f128_le UX UY <=? 0) with false in HK by (symmetry; apply Z.leb_gt; lia).
rewrite EUXl, EUXh, EUYl, EUYh. eapply L_norm; [mk_finv | apply Fok_refl | exact HK].
+ replace (f128_le UX UY <=? 0) with true in HK by (symmetry; apply Z.leb_le; lia).
zs. zs. zs. zs. zs. callw (eapply letf2_callv; hyp).
zs. (if_cases K3; zify_cond K3; try (rewrite ?signed_of_Z in K3 by lia)).
* replace (f128_le UX UY =? 0) with true in HK by (symmetry; apply Z.eqb_eq; clear - K3 RLE w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_124 joff_127 joff_158 joff_164 joff_179 joff_217 joff_233 joff_236 joff_278 e_letf2 e_multf3 e_floatsitf e_divtf3 CODE BASE4 BASER D_124 E_124 D_127 E_127 D_158 E_158 D_164 E_164 D_179 E_179 D_217 E_217 D_233 E_233 D_236 E_236 D_278 E_278 LINK_124 LINK_127 LINK_158 LINK_164 LINK_179 LINK_217 LINK_233 LINK_236 LINK_278 divtf3_spec letf2_spec floatsitf_spec multf3_spec segs base; mlia2). injection HK as Hr.
rewrite EUXl. replace (Z_to_bv 64 (f128_le UX UY)) with (Z_to_bv 64 0) by (f_equal; clear - K3 RLE w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_124 joff_127 joff_158 joff_164 joff_179 joff_217 joff_233 joff_236 joff_278 e_letf2 e_multf3 e_floatsitf e_divtf3 CODE BASE4 BASER D_124 E_124 D_127 E_127 D_158 E_158 D_164 E_164 D_179 E_179 D_217 E_217 D_233 E_233 D_236 E_236 D_278 E_278 LINK_124 LINK_127 LINK_158 LINK_164 LINK_179 LINK_217 LINK_233 LINK_236 LINK_278 divtf3_spec letf2_spec floatsitf_spec multf3_spec segs base; mlia2).
eapply L_zero; [mk_finv | apply Fok_refl | symmetry; exact Hr].
* replace (f128_le UX UY =? 0) with false in HK by (symmetry; apply Z.eqb_neq; clear - K3 RLE w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_124 joff_127 joff_158 joff_164 joff_179 joff_217 joff_233 joff_236 joff_278 e_letf2 e_multf3 e_floatsitf e_divtf3 CODE BASE4 BASER D_124 E_124 D_127 E_127 D_158 E_158 D_164 E_164 D_179 E_179 D_217 E_217 D_233 E_233 D_236 E_236 D_278 E_278 LINK_124 LINK_127 LINK_158 LINK_164 LINK_179 LINK_217 LINK_233 LINK_236 LINK_278 divtf3_spec letf2_spec floatsitf_spec multf3_spec segs base; mlia2). injection HK as Hr.
zs. rewrite EUXl. eapply L_retx; [mk_finv | apply Fok_refl | rewrite Hr; reflexivity | rewrite Hr; reflexivity].
Qed.

#[using="w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_113 joff_118 joff_124 joff_127 joff_142 joff_158 joff_164 joff_179 joff_217 joff_233 joff_236 joff_278 e_fpclassifyl e_letf2 e_multf3 e_floatsitf e_divtf3 CODE BASE4 BASER D_113 E_113 D_118 E_118 D_124 E_124 D_127 E_127 D_142 E_142 D_158 E_158 D_164 E_164 D_179 E_179 D_217 E_217 D_233 E_233 D_236 E_236 D_278 E_278 LINK_113 LINK_118 LINK_124 LINK_127 LINK_142 LINK_158 LINK_164 LINK_179 LINK_217 LINK_233 LINK_236 LINK_278 divtf3_spec fpclassifyl_spec letf2_spec floatsitf_spec multf3_spec SPLO SPHI HM"] Lemma L_entry : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
stk segs m0 (q - RFMODL_DEPTH) q -> mem_inv segs m0 ->
evt segs POST
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FMODL) fc None m0 (seg_rom segs)).
Proof. clear - w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_113 joff_118 joff_124 joff_127 joff_142 joff_158 joff_164 joff_179 joff_217 joff_233 joff_236 joff_278 e_fpclassifyl e_letf2 e_multf3 e_floatsitf e_divtf3 CODE BASE4 BASER D_113 E_113 D_118 E_118 D_124 E_124 D_127 E_127 D_142 E_142 D_158 E_158 D_164 E_164 D_179 E_179 D_217 E_217 D_233 E_233 D_236 E_236 D_278 E_278 LINK_113 LINK_118 LINK_124 LINK_127 LINK_142 LINK_158 LINK_164 LINK_179 LINK_217 LINK_233 LINK_236 LINK_278 divtf3_spec fpclassifyl_spec letf2_spec floatsitf_spec multf3_spec SPLO SPHI HM segs ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 X Y r.
intros until t6. intros ST MI.
pose proof (munch_refl [(q - RFMODL_DEPTH, q)]%Z m0) as MU. pose proof (wmono_refl segs m0) as WM.
unfold RFMODL_DEPTH in ST, MU, SPLO. unfold FMODL.
pose proof (hi64_range X) as RHX. pose proof (lo64_range X) as RLX. pose proof (hi64_range Y) as RHY. pose proof (lo64_range Y) as RLY.
pose proof HM as HK. rewrite m_fmodl_split in HK. cbv zeta in HK.
change (Z.land (Z.shiftr (hi64 X) 48) 32767) with exv in HK. change (Z.land (Z.shiftr (hi64 Y) 48) 32767) with eyv in HK.
change (Z.land (Z.shiftr (hi64 X) 48) 32768) with sxv in HK.
fold UX UY in HK.
zs. carve_frame 80%nat ST.
do 15 zs.
zs. callw (eapply floatsitf_callv with (v := 0%Z) (i := 0%Z); [hyp | lia | reflexivity]).
set (t00 := f128_of_i32 0) in *. pose proof (lo64_range t00) as RT1. pose proof (hi64_range t00) as RT2.
pose proof (f128_le_range Y t00) as RLE.
zs. zs. zs. zs. zs. callw (eapply letf2_callv; hyp).
zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia)).
-
replace (f128_le Y t00 =? 0) with false in HK by (symmetry; apply Z.eqb_neq; clear - K1 RLE w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_113 joff_118 joff_124 joff_127 joff_142 joff_158 joff_164 joff_179 joff_217 joff_233 joff_236 joff_278 e_fpclassifyl e_letf2 e_multf3 e_floatsitf e_divtf3 CODE BASE4 BASER D_113 E_113 D_118 E_118 D_124 E_124 D_127 E_127 D_142 E_142 D_158 E_158 D_164 E_164 D_179 E_179 D_217 E_217 D_233 E_233 D_236 E_236 D_278 E_278 LINK_113 LINK_118 LINK_124 LINK_127 LINK_142 LINK_158 LINK_164 LINK_179 LINK_217 LINK_233 LINK_236 LINK_278 divtf3_spec fpclassifyl_spec letf2_spec floatsitf_spec multf3_spec segs; mlia2). cbn [orb] in HK.
zs. zs. zs. callw (eapply fpclassifyl_spec; eassumption). norm_rsegs.
rewrite !ulit_lo64, !ulit_hi64, m_fpclassifyl_canon.
assert (RC : (0 <= m_fpclassifyl Y <= 4)%Z) by (clear; unfold m_fpclassifyl; repeat (destruct (_ : bool)); lia).
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ replace (m_fpclassifyl Y =? 0) with true in HK by (symmetry; apply Z.eqb_eq; clear - K2 RC w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_113 joff_118 joff_124 joff_127 joff_142 joff_158 joff_164 joff_179 joff_217 joff_233 joff_236 joff_278 e_fpclassifyl e_letf2 e_multf3 e_floatsitf e_divtf3 CODE BASE4 BASER D_113 E_113 D_118 E_118 D_124 E_124 D_127 E_127 D_142 E_142 D_158 E_158 D_164 E_164 D_179 E_179 D_217 E_217 D_233 E_233 D_236 E_236 D_278 E_278 LINK_113 LINK_118 LINK_124 LINK_127 LINK_142 LINK_158 LINK_164 LINK_179 LINK_217 LINK_233 LINK_236 LINK_278 divtf3_spec fpclassifyl_spec letf2_spec floatsitf_spec multf3_spec segs; mlia2). cbn [orb] in HK. injection HK as Hr.
eapply L_nan; [mk_finv | apply Fok_refl | symmetry; exact Hr].
+ replace (m_fpclassifyl Y =? 0) with false in HK by (symmetry; apply Z.eqb_neq; clear - K2 RC w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_113 joff_118 joff_124 joff_127 joff_142 joff_158 joff_164 joff_179 joff_217 joff_233 joff_236 joff_278 e_fpclassifyl e_letf2 e_multf3 e_floatsitf e_divtf3 CODE BASE4 BASER D_113 E_113 D_118 E_118 D_124 E_124 D_127 E_127 D_142 E_142 D_158 E_158 D_164 E_164 D_179 E_179 D_217 E_217 D_233 E_233 D_236 E_236 D_278 E_278 LINK_113 LINK_118 LINK_124 LINK_127 LINK_142 LINK_158 LINK_164 LINK_179 LINK_217 LINK_233 LINK_236 LINK_278 divtf3_spec fpclassifyl_spec letf2_spec floatsitf_spec multf3_spec segs; mlia2). cbn [orb] in HK.
eapply L_cmp; [mk_finv | exact HK].
- replace (f128_le Y t00 =? 0) with true in HK by (symmetry; apply Z.eqb_eq; clear - K1 RLE w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_113 joff_118 joff_124 joff_127 joff_142 joff_158 joff_164 joff_179 joff_217 joff_233 joff_236 joff_278 e_fpclassifyl e_letf2 e_multf3 e_floatsitf e_divtf3 CODE BASE4 BASER D_113 E_113 D_118 E_118 D_124 E_124 D_127 E_127 D_142 E_142 D_158 E_158 D_164 E_164 D_179 E_179 D_217 E_217 D_233 E_233 D_236 E_236 D_278 E_278 LINK_113 LINK_118 LINK_124 LINK_127 LINK_142 LINK_158 LINK_164 LINK_179 LINK_217 LINK_233 LINK_236 LINK_278 divtf3_spec fpclassifyl_spec letf2_spec floatsitf_spec multf3_spec segs; mlia2). cbn [orb] in HK. injection HK as Hr.
eapply L_nan; [mk_finv | apply Fok_refl | symmetry; exact Hr].
Qed.
End Fmodl.

#[using="w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_113 joff_118 joff_124 joff_127 joff_142 joff_158 joff_164 joff_179 joff_217 joff_233 joff_236 joff_278 e_fpclassifyl e_letf2 e_multf3 e_floatsitf e_divtf3 CODE BASE4 BASER D_113 E_113 D_118 E_118 D_124 E_124 D_127 E_127 D_142 E_142 D_158 E_158 D_164 E_164 D_179 E_179 D_217 E_217 D_233 E_233 D_236 E_236 D_278 E_278 LINK_113 LINK_118 LINK_124 LINK_127 LINK_142 LINK_158 LINK_164 LINK_179 LINK_217 LINK_233 LINK_236 LINK_278 divtf3_spec fpclassifyl_spec letf2_spec floatsitf_spec multf3_spec"] Lemma rfmodl_spec : rfmodl_stmt.
Proof. clear - w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 joff_113 joff_118 joff_124 joff_127 joff_142 joff_158 joff_164 joff_179 joff_217 joff_233 joff_236 joff_278 e_fpclassifyl e_letf2 e_multf3 e_floatsitf e_divtf3 CODE BASE4 BASER D_113 E_113 D_118 E_118 D_124 E_124 D_127 E_127 D_142 E_142 D_158 E_158 D_164 E_164 D_179 E_179 D_217 E_217 D_233 E_233 D_236 E_236 D_278 E_278 LINK_113 LINK_118 LINK_124 LINK_127 LINK_142 LINK_158 LINK_164 LINK_179 LINK_217 LINK_233 LINK_236 LINK_278 divtf3_spec fpclassifyl_spec letf2_spec floatsitf_spec multf3_spec.
unfold rfmodl_stmt. intros. eapply L_entry; eassumption.
Qed.

End G.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1 QWxq_c1 QYTG G.T_shp G.T_pe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.
Import QZAi.Mq1 Ql2m.Mq3 QZAi QqdR QYTG.Mq2.
Import QnDM_c1.
Import QVbl.Mq4.
Import QVbl.Mq3.
Import QQLG.Mq7.
Import Q91D.Mq2.
Import QQRC.Mq0.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_shp.F_fmt_fp.
Import Q91D.Mq3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.

Import ListNotations.
Import QlEo_c1.Mq0.Exc. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition printf_core_code (w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 : Z) : list Z :=
[0xde010113; 0x20113c23; 0x20813823; 0x20913423; 0x21213023; 0x1f313c23; 0x1f413823; 0x1f513423; 0x1f613023; 0x1d713c23; 0x1d813823; 0x1d913423; 0x1da13023; 0x1bb13c23; 0x04e13023; 0x02d13c23; 0x04c13423; 0x00058a93; 0x00050a13; 0x04013c23; 0x00000993; 0x00000d13; w_22; 0x800004b7; 0x000135b7; w_25; 0x0cccd537; 0x06c13023; 0x00063603; 0xffff06b7; 0x1ac13823; 0xccccd637; 0xfff4849b; 0x8895859b; 0x04b13823; 0xccc5051b; 0x06a13423; 0xfff6869b; 0x02d13823; 0xccd6051b; 0x02a13423; 0x02500413; 0x0080006f; 0x0a0b0063; 0x4134853b; 0x000d059b; 0x3cb540e3; 0x000a8b93; 0x000ac503; 0x013d09bb; 0x3a050ee3; 0x000b8a93; 0x00050a63; 0x00850c63; 0x001ac503; 0x001a8a93; 0xfe051ae3; 0x000a8513; 0x0300006f; 0x000a8513; 0x000a8593; 0x0015c603; 0x00861e63; 0x0025c603; 0x00258a93; 0x00150513; 0x000a8593; 0xfe8604e3; 0x0080006f; 0x00058a93; 0x41750d33; 0x4134893b; 0x35a94ce3; 0x000d0b1b; 0xf80a02e3; 0x000a4503; 0x02057513; 0xf6051ce3; 0x000b8513; 0x000b0593; 0x000a0613; w_81; 0xf65ff06f; 0x001ac583; 0x001a8613; 0xfd058693; 0xfff00513; 0x00900713; 0x02d76863; 0x002ac703; 0x02400793; 0x00100813; 0x05013283; 0x02f71263; 0x003ac583; 0x003a8613; 0x00100513; 0x04a13c23; 0x00068513; 0x00c0006f; 0x00100813; 0x05013283; 0xfe058693; 0x01f00713; 0x06d76e63; 0x00d816bb; 0x0056f733; 0x02000893; 0x00000c13; 0x02070663; 0x00160713; 0x00070613; 0x00074583; 0xfe058713; 0x0186ec33; 0x01177a63; 0x00e816bb; 0x0056f7b3; 0x00160713; 0xfe0790e3; 0x02a00693; 0x04d59263; 0x00164583; 0xfd058593; 0x00900693; 0x0ab6e263; 0x00264683; 0x02400713; 0x08e69c63; 0x0c0a0c63; 0x00459593; 0x03813683; 0x00b685b3; 0x0005ab03; 0x0dc0006f; 0x00000c13; 0x02a00693; 0xfcd582e3; 0xfd058593; 0x00000b13; 0x00900693; 0x0cb6ee63; 0x00060693; 0x0380006f; 0x00a00313; 0x026b063b; 0x0005871b; 0x0016c803; 0x009647b3; 0x00b608bb; 0x00e7b5b3; 0x40b002bb; 0x00168613; 0xfd080593; 0x0112eb33; 0x00060693; 0x0665f263; 0x06813603; 0xfd6674e3; 0x0016c583; 0x00168693; 0xfd058593; 0xfff00b13; 0x00a00613; 0xfec5e2e3; 0x1e50006f; 0x05813583; 0x320598e3; 0x00160613; 0x020a0263; 0x04813703; 0x00073583; 0x00858693; 0x00d73023; 0x0005ab03; 0x04013c23; 0x040b5863; 0x0400006f; 0x04013c23; 0x00000b13; 0x0400006f; 0x02e7fe63; 0x1a10006f; 0x00000b13; 0x00259593; 0x04013683; 0x00b685b3; 0x00a00693; 0x00d5a023; 0x00360613; 0x00100593; 0x04b13c23; 0x000b5863; 0x000025b7; 0x00bc6c33; 0x41600b3b; 0x00064583; 0x02e00693; 0x04d59863; 0x00164583; 0x02a00693; 0x04d59e63; 0x00264583; 0xfd058593; 0x00900693; 0xfc600793; 0x03a00813; 0x00800893; 0x0ab6e263; 0x00364683; 0x02400713; 0x08e69c63; 0x0c0a0a63; 0x00459593; 0x03813683; 0x00b685b3; 0x0005ac83; 0x0d80006f; 0x00000293; 0xfff00c93; 0xfc600793; 0x03a00813; 0x00800893; 0x0cc0006f; 0x00160613; 0xfd058593; 0x00100293; 0x00900693; 0x00800893; 0x00000c93; 0x06b6ec63; 0x00a00813; 0x0340006f; 0x030c86bb; 0x0005871b; 0x0096c7b3; 0x00e7b733; 0x00b685bb; 0x40e006bb; 0x00b6ecb3; 0x00164583; 0x00160693; 0xfd058593; 0x00068613; 0x0305fe63; 0x06813683; 0xfd96f6e3; 0xfff00c93; 0xfe1ff06f; 0x05813583; 0x1e0592e3; 0x00260613; 0x020a0663; 0x04813703; 0x00073583; 0x00858693; 0x00d73023; 0x0005ac83; 0x0380006f; 0x00068613; 0xfc600793; 0x03a00813; 0x0300006f; 0x00000c93; 0x0200006f; 0x00000c93; 0x00259593; 0x04013683; 0x00b685b3; 0x00a00693; 0x00d5a023; 0x00460613; 0x000ca593; 0x0015c293; 0x00000593; 0x00060a93; 0x000ac603; 0xf8560693; 0x16f6eae3; 0x00058d93; 0x030585b3; w_281; w_282; 0x00b685b3; 0x00b605b3; 0xfbf5c583; 0xfff58613; 0x001a8a93; 0xfd1668e3; 0x01b00613; 0x02c58863; 0x140580e3; 0x02054c63; 0x0e0a0663; 0x00451513; 0x03813583; 0x00a58533; 0x00053583; 0x00853503; 0x06b13823; 0x06a13c23; 0x02c0006f; 0x10055ae3; 0x00000d13; 0x020a1063; 0xbedff06f; 0x080a08e3; 0x07010513; 0x04813603; 0x00028d13; 0x159000ef; 0x000d0293; 0x000a4503; 0x02057513; 0x0e0518e3; 0xfffac803; 0x01b03533; 0x00f87593; 0xffd58593; 0x0015b593; 0x00b57533; 0x00050463; 0x0d387813; 0x032c1513; 0x03013583; 0x00bc7d33; 0x00055463; 0x000d0c13; 0xfbf80513; 0x03700593; 0x0aa5e063; 0x00251513; w_332; w_333; 0x00b50533; 0x00052503; 0x00b50533; 0x00050067; 0x000ca513; 0x00a2f533; 0x72051463; 0x07013583; 0x07813603; 0x000a0513; 0x000b0693; 0x000c8713; 0x000c0793; 0x000d8893; 0x2c9000ef; 0x00050d13; 0xb2055ce3; 0x6fc0006f; 0x00000d13; 0x00251513; 0x04013603; 0x00a60533; 0x00b52023; 0xb1dff06f; 0x07013503; 0x2c054a63; w_360; 0x034c1613; w_362; 0x00a00713; 0x2e064063; 0x001c7613; 0x00c13c23; 0x00161613; 0x00c588b3; 0x2d80006f; 0x00013c23; w_371; w_372; 0x00a13023; 0x0b010593; 0x3700006f; 0x07013b83; 0x020b9063; w_378; w_379; 0x0140006f; w_381; 0x00052503; w_383; 0x00050b93; 0x000c8593; 0x009ce463; 0x00048593; 0x000b8513; w_389; 0x00ab85b3; 0x000cd663; 0x0005c603; 0x64061a63; 0x00013c23; w_395; w_396; 0x00c13023; 0x000d0c13; 0x30c0006f; 0x07013503; 0x0b010b93; 0x02050263; 0x0b010593; 0x00757613; 0xfff58b93; 0x03060613; 0x00355513; 0xfec58fa3; 0x000b8593; 0xfe0514e3; 0x008c7513; w_412; w_413; 0x00b13023; 0x00050863; 0x0b010513; 0x41750533; 0x5b955a63; 0x00013c23; 0x26c0006f; 0x0ffdf513; 0x00000d13; 0x00700593; 0xa0a5e8e3; 0x00251513; w_426; w_427; 0x00b50533; 0x00052503; 0x00b50533; 0x00050067; 0x00000d13; 0x07013503; 0x01353023; 0x9e5ff06f; 0x00013c23; 0x07013503; w_438; w_439; 0x00a00713; 0x1b80006f; 0x07013503; 0x02050063; 0x08a12823; 0x08012a23; 0x09010913; 0x07213823; 0xfff00c93; 0x0b00006f; 0x07013503; 0x00013c23; 0x0aa107a3; w_453; w_454; 0x00a13023; 0x00100c93; 0x0b010593; 0x0af10b93; 0x000d0c13; 0x21c0006f; 0x01000513; 0x01956463; 0x01000c93; 0x008c6c13; 0x07800813; 0x07013503; w_467; w_468; 0x04050463; 0x02087593; 0x0b010b93; 0x00f57613; w_473; w_474; 0x00c68633; 0x00064603; 0x00455513; 0x00b66633; 0xfecb8fa3; 0xfffb8b93; 0xfc051ee3; 0x008c7513; 0x0c051263; 0x00e13023; 0x00013c23; 0x1640006f; 0x00e13023; 0x00013c23; 0x0b010b93; 0x1540006f; 0x440c8263; 0x07013903; 0x00000b93; 0x00090d13; 0x000d2583; 0x02058263; 0x08c10513; 0x739010ef; 0x60054663; 0x417c85b3; 0x00a5e863; 0x00ab8bb3; 0x004d0d13; 0xfd9beee3; 0x01fbd513; 0x48051863; 0x02000593; 0x000a0513; 0x000b0613; 0x000b8693; 0x000c0713; 0x764000ef; 0x400b8463; 0x00000c93; 0x00c0006f; 0x00490913; 0x3f7cfc63; 0x00092583; 0x3e058863; 0x08c10513; 0x6dd010ef; 0x00ac8cb3; 0x3f9be063; 0x00050593; 0x000a4503; 0x02057513; 0xfc051ae3; 0x08c10513; 0x000a0613; w_530; 0xfc5ff06f; 0x00485513; w_533; w_534; 0x00a58533; 0x00a13023; 0x00200513; 0x00a13c23; 0x0900006f; 0x40a00533; 0x00100593; 0x00b13c23; w_543; 0x06a13823; w_545; 0x00a00713; 0x0100006f; 0x00158893; 0x00100593; 0x00b13c23; 0x02813783; 0x06300813; 0x02e56e63; 0x0b010593; 0x00050613; 0x02079513; 0x00a78533; 0x02a63533; 0x00355513; 0x02e506b3; 0x40d606bb; 0x0306e693; 0xfff58b93; 0xfed58fa3; 0x000b8593; 0xfcc86ae3; 0x0080006f; 0x0b010b93; 0x01113023; 0x00050a63; 0x03056513; 0xfffb8593; 0xfeab8fa3; 0x00058b93; 0x000ca513; 0x00a2f533; 0x36051a63; 0x00028663; 0x03013503; 0x00ac7c33; 0x07013503; 0x00051a63; 0x000c9863; 0x0b010b93; 0x000b8593; 0x0240006f; 0x00153513; 0x0b010593; 0x417585b3; 0x00a58533; 0x00acc463; 0x000c8513; 0x0b010593; 0x00050c93; 0x000c8c9b; 0x41758533; 0x00050593; 0x00a13823; 0x00acc463; 0x000c8593; 0x00058c9b; 0x01813503; 0x40a4853b; 0x31954463; 0x00058d93; 0x01813503; 0x00b5053b; 0x000b0d13; 0x02a13023; 0x01654463; 0x02013d03; 0x2fa94463; 0x00012537; 0x00ac7933; 0x01213423; 0x08091263; 0x02013503; 0x07655e63; 0x02013503; 0x40ad0c3b; 0x10000913; 0x000c0613; 0x012c6463; 0x10000613; 0x0b010513; 0x02000593; w_627; 0x032c6a63; 0x0ff00913; 0x00c0006f; 0xf00c0c1b; 0x03897263; 0x000a4503; 0x02057513; 0xfe0518e3; 0x0b010513; 0x10000593; 0x000a0613; w_639; 0xfddff06f; 0x000a4503; 0x02057513; 0x00813903; 0x00051a63; 0x0b010513; 0x000c0593; 0x000a0613; w_648; 0x000a4503; 0x02057513; 0x00051a63; 0x00013503; 0x01813583; 0x000a0613; w_655; 0x00010537; 0x08a91263; 0x02013503; 0x07655e63; 0x02013503; 0x40ad0c3b; 0x10000913; 0x000c0613; 0x012c6463; 0x10000613; 0x0b010513; 0x03000593; w_668; 0x032c6a63; 0x0ff00913; 0x00c0006f; 0xf00c0c1b; 0x03897263; 0x000a4503; 0x02057513; 0xfe0518e3; 0x0b010513; 0x10000593; 0x000a0613; w_680; 0xfddff06f; 0x000a4503; 0x02057513; 0x00813903; 0x00051a63; 0x0b010513; 0x000c0593; 0x000a0613; w_689; 0x01012503; 0x09955063; 0x00090c93; 0x01013503; 0x40ad8c3b; 0x10000913; 0x000c0613; 0x012c6463; 0x10000613; 0x0b010513; 0x03000593; w_701; 0x032c6a63; 0x0ff00913; 0x00c0006f; 0xf00c0c1b; 0x03897263; 0x000a4503; 0x02057513; 0xfe0518e3; 0x0b010513; 0x10000593; 0x000a0613; w_713; 0xfddff06f; 0x000a4503; 0x02057513; 0x000c8913; 0x00051a63; 0x0b010513; 0x000c0593; 0x000a0613; w_722; 0x000a4503; 0x02057513; 0x00051a63; 0x000b8513; 0x01013583; 0x000a0613; w_729; 0x00002537; 0xd4a91263; 0x02013503; 0xd3655e63; 0x02013503; 0x40ad0b3b; 0x10000913; 0x000b0613; 0x012b6463; 0x10000613; 0x0b010513; 0x02000593; w_742; 0x032b6a63; 0x0ff00913; 0x00c0006f; 0xf00b0b1b; 0x03697263; 0x000a4503; 0x02057513; 0xfe0518e3; 0x0b010513; 0x10000593; 0x000a0613; w_754; 0xfddff06f; 0x000a4503; 0x02057513; 0xcc051c63; 0x0b010513; 0x000b0593; 0x000a0613; w_762; 0xcc4ff06f; 0x02000593; 0x000a0513; 0x000b0613; 0x00000693; 0x000c0713; 0x360000ef; 0x00000b93; 0x00002537; 0x00ac4733; 0x000b8b9b; 0x02000593; 0x000a0513; 0x000b0613; 0x000b8693; 0x33c000ef; 0x016bc463; 0x000b8b13; 0x000b0d13; 0xc78ff06f; 0x00013c23; 0x00150c9b; 0xcb9ff06f; 0x00000d13; 0x07013503; 0x01352023; 0xc5cff06f; 0x00000d13; 0x07013503; 0x01351023; 0xc4cff06f; 0x00000d13; 0x07013503; 0x01350023; 0xc3cff06f; w_798; 0x04b00593; 0x1540006f; 0x140a1c63; 0x05813503; 0x0c050663; 0x04013403; 0x00442583; 0x0c058463; 0x03813903; 0x01090513; 0x04813483; 0x00048613; 0x184000ef; 0x00842583; 0x0a058a63; 0x02090513; 0x00048613; 0x170000ef; 0x00c42583; 0x0a058463; 0x03090513; 0x00048613; 0x15c000ef; 0x01042583; 0x08058e63; 0x04090513; 0x00048613; 0x148000ef; 0x01442583; 0x08058863; 0x05090513; 0x00048613; 0x134000ef; 0x01842583; 0x08058263; 0x06090513; 0x00048613; 0x120000ef; 0x01c42583; 0x06058c63; 0x07090513; 0x00048613; 0x10c000ef; 0x02042583; 0x06058663; 0x08090513; 0x00048613; 0x0f8000ef; 0x02442583; 0x06058063; 0x09090513; 0x00048613; 0x0e4000ef; 0x00100993; 0x0880006f; 0x00000993; 0x0800006f; 0x00100513; 0x0400006f; 0x00200513; 0x0380006f; 0x00300513; 0x0300006f; 0x00400513; 0x0280006f; 0x00500513; 0x0200006f; 0x00600513; 0x0180006f; 0x00700513; 0x0100006f; 0x00800513; 0x0080006f; 0x00900513; 0xff650593; 0x00251513; 0x00a40533; 0x00052603; 0x00061c63; 0x00158593; 0x00450513; 0xfe0598e3; 0x00100993; 0x0140006f; w_883; 0x01600593; 0x00b52023; 0xfff00993; 0x06013503; 0x00053503; 0x1b013583; 0x04b51263; 0x00098513; 0x21813083; 0x21013403; 0x20813483; 0x20013903; 0x1f813983; 0x1f013a03; 0x1e813a83; 0x1e013b03; 0x1d813b83; 0x1d013c03; 0x1c813c83; 0x1c013d03; 0x1b813d83; 0x22010113; 0x00008067; w_907]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 : Z).
Variables (got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_fwritex : Z).
Hypothesis CODE : code_at segs base (printf_core_code w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 3632.

Local Definition gw_tbl_0 := tt.

Definition wfile : ltac:(gw_rebind_ty (@QQLG.Mq7.wfile segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QQLG.Mq7.wfile segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@Q91D.Mq2.wfile segs) wfile (gw_ent (@QQLG.Mq7.wfile segs) wfile gw_tbl_0)).
Definition ssp_cells : ltac:(gw_rebind_ty (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_1).
Definition va_area : ltac:(gw_rebind_ty (@Q91D.Mq3.va_area segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q91D.Mq3.va_area segs) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@Q91D.Mq3.va_area segs) va_area gw_tbl_2).

Notation parg := G.T_printf.parg.
Notation PA_s := G.T_printf.PA_s.
Notation PA_i := G.T_printf.PA_i.
Notation PA_u := G.T_printf.PA_u.
Notation PA_g := G.T_printf.PA_g.
Notation PA_li := G.T_printf.PA_li.
Notation PA_lu := G.T_printf.PA_lu.

#[using="got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex CODE BASE4 BASER"] Lemma gw_all : True. Proof. exact I. Qed.

Notation mem := (word -> option byte).

Definition OUT_DEPTH : Z := 1024.
Definition PC_DEPTH : Z := 5184.
Definition VF_DEPTH : Z := 5552.

Section Sink.
Context {St : Type}.
Variables (Fp B BS : Z).
Variable SINK : mem -> St -> Prop.
Variable TOPOK : Z -> Prop.
Variable OUT : list Z -> M St unit.
Variable OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z.

Definition SR : list (Z * Z) := [(Fp, Fp + 232); (B, B + BS)].

Definition sink_frame_stmt : Prop :=
forall (W : list (Z * Z)) (m m' : mem) (st : St),
SINK m st -> munch W m m' -> wmono segs m m' ->
Forall (fun iv => snd iv <= Fp \/ Fp + 232 <= fst iv) W ->
Forall (fun iv => snd iv <= B \/ B + BS <= fst iv) W ->
SINK m' st.

Definition sink_flags_stmt : Prop :=
forall m st, SINK m st -> exists fl : byte, rw_cells segs m Fp [CB 1 [fl]] /\ Z.land (bv_unsigned fl) 32 = 0.

Definition topok_stmt : Prop := forall a b, a <= b -> TOPOK b -> TOPOK a.

Definition out_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(S : Z) (bs : list Z) (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch ((lo, bv_unsigned sp) :: SR) m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp)
/\ SINK m' st'
/\ ssp_cells m' canary
/\ bytes_at segs m' S (zb bs).

Definition out_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (bs : list Z) (lo : Z) (canary : word),
SINK m st ->
bytes_at segs m (bv_unsigned a0) (zb bs) ->
Forall (fun c => 0 <= c < 256) bs -> zlength bs < 2^31 ->
a1 = Z_to_bv 64 (zlength bs) ->
a2 = Z_to_bv 64 Fp ->
stk segs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - OUT_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp < 2^63) -> TOPOK (bv_unsigned sp) ->
ssp_cells m canary ->
mem_inv segs m ->
(Fp + 232 <= lo \/ bv_unsigned sp <= Fp) -> (B + BS <= lo \/ bv_unsigned sp <= B) ->
(bv_unsigned a0 + zlength bs <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
(bv_unsigned a0 + zlength bs <= Fp \/ Fp + 232 <= bv_unsigned a0) ->
(bv_unsigned a0 + zlength bs <= B \/ B + BS <= bv_unsigned a0) ->
implM segs (OUT bs) st
(out_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) bs lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_fwritex + 0x0)) fc None m (seg_rom segs)).

Definition fpcall_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(lo : Z) (canary : word) (m : mem) : Z -> St -> machine_state -> Prop :=
fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom segs)
/\ munch ((lo, bv_unsigned sp) :: SR) m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk segs m' lo (bv_unsigned sp)
/\ SINK m' st'
/\ ssp_cells m' canary.

Definition fpcall_stmt (c : Z * Z * Z * Z * Z) : Prop :=
let '(y, w, p, fl, t) := c in
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word),
SINK m st ->
y = bv_unsigned a1 + 2^64 * bv_unsigned a2 ->
a0 = Z_to_bv 64 Fp -> a3 = Z_to_bv 64 w -> a4 = Z_to_bv 64 p -> a5 = Z_to_bv 64 fl -> a6 = Z_to_bv 64 t ->
bv_unsigned a7 <> 5 ->
(-2^31 <= w <= 1) -> (-2^31 <= p < 2^20) -> (0 <= fl < 2^32) -> (0 <= t < 256) -> Z.lor t 32 <> 97 ->
stk segs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FMT_FP_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp < 2^63) -> TOPOK (bv_unsigned sp) ->
ssp_cells m canary ->
mem_inv segs m -> frm0 fc ->
(Fp + 232 <= lo \/ bv_unsigned sp <= Fp) -> (B + BS <= lo \/ bv_unsigned sp <= B) ->
implM segs (OUTFP y w p fl t) st
(fpcall_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 4152)) fc None m (seg_rom segs)).

Definition arg_ok (m : mem) (lo sp ap : Z) (slot : word) (a : parg) : Prop :=
match a with
| PA_s s => exists slack : list byte,
bytes_at segs m (bv_unsigned slot) (zb s ++ Z_to_bv 8 0 :: slack)
/\ Forall (fun c => 0 < c < 256) s
/\ ((- (bv_unsigned slot + zlength s + 1)) mod 8 <= zlength slack)
/\ 0 < bv_unsigned slot
/\ (bv_unsigned slot + zlength s + 1 + zlength slack <= lo \/ sp <= bv_unsigned slot)
/\ (bv_unsigned slot + zlength s + 1 + zlength slack <= Fp \/ Fp + 232 <= bv_unsigned slot)
/\ (bv_unsigned slot + zlength s + 1 + zlength slack <= B \/ B + BS <= bv_unsigned slot)
/\ (bv_unsigned slot + zlength s + 1 + zlength slack <= ap \/ ap + 8 <= bv_unsigned slot)
| PA_i i => -2^31 <= i < 2^31 /\ bv_unsigned slot mod 2^32 = i mod 2^32
| PA_u u => 0 <= u < 2^32 /\ bv_unsigned slot mod 2^32 = u
| PA_g d => bv_unsigned slot = d
| PA_li i => -2^63 <= i < 2^63 /\ bv_unsigned slot = i mod 2^64
| PA_lu u => 0 <= u < 2^64 /\ bv_unsigned slot = u
end.
Fixpoint args_ok (m : mem) (lo sp ap : Z) (slots : list word) (args : list parg) : Prop :=
match args with
| [] => True
| a :: args' => match slots with
| [] => False
| w :: slots' => arg_ok m lo sp ap w a /\ args_ok m lo sp ap slots' args'
end
end.

Definition printf_core_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(AP lo : Z) (canary : word) (m : mem) : Z -> St -> machine_state -> Prop :=
fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (apv : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom segs)
/\ munch ((lo, bv_unsigned sp) :: (AP, AP + 8) :: SR) m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk segs m' lo (bv_unsigned sp)
/\ SINK m' st'
/\ ssp_cells m' canary
/\ rw_cells segs m' AP [C8 apv]
/\ (0 <= r <= INT_MAX).

Definition printf_core_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word)
(fmt : list Z) (VA i : Z) (slots : list word) (args : list parg),
SINK m st ->
bytes_at segs m (bv_unsigned a1) (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt ->
a0 = Z_to_bv 64 Fp ->
rw_cells segs m (bv_unsigned a2) [C8 (Z_to_bv 64 (VA + 8 * i))] ->
va_area m VA slots -> 0 <= i -> args_ok m lo (bv_unsigned sp) (bv_unsigned a2) (skipn (Z.to_nat i) slots) args ->
Forall fpcall_stmt (fp_calls (length fmt) fmt args) ->
stk segs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PC_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp < 2^63) -> TOPOK (bv_unsigned sp) ->
ssp_cells m canary -> mem_inv segs m -> frm0 fc ->

(bv_unsigned a1 + zlength fmt <= STATIC_SPLIT) -> (0 <= BS) ->
(((got_ssp + 8)%Z <= Fp /\ Fp + 232 <= ssp_guard) \/ (bv_unsigned a2 + 8 <= Fp /\ Fp + 232 <= VA)) ->
(((ssp_guard + 8)%Z <= B /\ B + BS <= lo) \/ (bv_unsigned a2 + 8 <= B /\ B + BS <= VA)) ->
(bv_unsigned sp <= bv_unsigned a2) -> (bv_unsigned a2 + 8 <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
implM segs (printf_model OUT OUTFP fmt args) st
(printf_core_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (bv_unsigned a2) lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
End Sink.

Definition printf_core1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(lo, bv_unsigned sp)] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp)
/\ ssp_cells m' canary.

Definition printf_core1_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (canary : word) (fmt : list Z),
bytes_at segs m (bv_unsigned a1) (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt ->
pass1_ok fmt = true ->
a0 = Z_to_bv 64 0 ->
stk segs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PC_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp < 2^63) ->
ssp_cells m canary -> mem_inv segs m ->
(bv_unsigned a1 + zlength fmt <= STATIC_SPLIT) ->
(bv_unsigned sp <= bv_unsigned a2) -> (bv_unsigned a2 + 8 <= 2^64) ->
evt segs (printf_core1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).

Section SnSink.

Variables (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (frest : list cell) (B TOP : Z).
Definition SN_CAP : Z := 80.

Definition SINK_sn (m : mem) (o : list Z) : Prop :=
exists junk : list byte,
wfile m Fp fl0 j1 j2 lbfw B (zb o) junk
/\ rw_cells segs m (Fp + 148) frest /\ Z.of_nat (cells_size frest) = 84
/\ zlength o + zlength junk = SN_CAP
/\ (B + SN_CAP <= Fp \/ Fp + 232 <= B)
/\ TOP <= Fp /\ TOP <= B.
Definition TOPOK_sn (sp : Z) : Prop := sp <= TOP.

Definition OUT_sn (bs : list Z) : M (list Z) unit :=
o <- mget ;; if zlength o + zlength bs <=? SN_CAP then mput (o ++ bs) else munr.

Definition OUTFP_sn (y w p fl t : Z) : M (list Z) Z :=
o <- mget ;;
match fmt_fp o y w p fl t with
| Some (o1, r) => if zlength o1 <=? SN_CAP then (mput o1 ;;; mret r) else munr
| None => munr
end.
End SnSink.

Definition TOPOK_none (sp : Z) : Prop := True.

End G.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Q9A7.Mq1 Q5Rg.
Import QQRC.Mq0.

Import ListNotations. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation shp := G.T_shp.shp.
Notation S8 := G.T_shp.S8.
Notation S4 := G.T_shp.S4.
Notation SB4 := G.T_shp.SB4.
Definition shp_size (s : shp) : nat := match s with S8 => 8 | _ => 4 end%nat.
Fixpoint shp_sum (pat : list shp) : nat := match pat with [] => 0 | s :: pat' => shp_size s + shp_sum pat' end%nat.
Fixpoint shape_cells (pat : list shp) (bs : list byte) : list cell :=
match pat with
| [] => []
| s :: pat' =>
match s with
| S8 => C8 (le_bytes_to_word (firstn 8 bs)) :: shape_cells pat' (skipn 8 bs)
| S4 => C4 (le_bytes_to_word (firstn 4 bs)) :: shape_cells pat' (skipn 4 bs)
| SB4 => CB 4 (firstn 4 bs) :: shape_cells pat' (skipn 4 bs)
end
end.

Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
pose proof (bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.
Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
intros bs HL. unfold le4, le_bytes_to_word.
pose proof (bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z in HR.
rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

Lemma shape_wf : forall pat bs, length bs = shp_sum pat -> cells_wf (shape_cells pat bs).
Proof.
induction pat as [|s pat IH]; intros bs HL; cbn; [exact I|].
destruct s; cbn in HL |- *; (split; [try exact I; rewrite length_firstn; lia | apply IH; rewrite length_skipn; lia]).
Qed.
Lemma shape_bytes : forall pat bs, length bs = shp_sum pat -> cells_bytes (shape_cells pat bs) = bs.
Proof.
induction pat as [|s pat IH]; intros bs HL; cbn in HL |- *.
- destruct bs; [reflexivity | cbn in HL; lia].
- destruct s; cbn [shp_size] in HL; cbn [cells_bytes cbytes];
[rewrite le8_of_bytes by (rewrite length_firstn; lia) | rewrite le4_of_bytes by (rewrite length_firstn; lia) |];
rewrite IH by (rewrite length_skipn; lia); apply firstn_skipn.
Qed.
Lemma shape_size : forall pat bs, cells_size (shape_cells pat bs) = shp_sum pat.
Proof. induction pat as [|s pat IH]; intros bs; cbn; [reflexivity|]. destruct s; cbn; rewrite IH; reflexivity. Qed.

Lemma rw_cells_reshape : forall segs_ m A cs cs',
rw_cells segs_ m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
rw_cells segs_ m A cs'.
Proof.
intros segs_ m A cs cs' [[Hwf Hb] Hw] Hwf' Hb' Hs'. split; [split; [exact Hwf'|]|].
- rewrite Hb'. exact Hb.
- rewrite Hs'. exact Hw.
Qed.

Lemma rw_cells_shape : forall segs_ m A n bs pat,
rw_cells segs_ m A [CB n bs] -> shp_sum pat = n -> rw_cells segs_ m A (shape_cells pat bs).
Proof.
intros segs_ m A n bs pat H Hs. pose proof H as H0. destruct H0 as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [HL _].
apply (rw_cells_reshape segs_ m A [CB n bs]); [exact H | apply shape_wf; lia | | cbn; rewrite shape_size; lia].
cbn [cells_bytes cbytes]. rewrite app_nil_r. apply shape_bytes. lia.
Qed.

Definition FILE_PAT : list shp :=
[S4; SB4; S8; S8; S8; S8; S8; S8; S8; S8; S8; S8; S8; S8; S8; S8; S4; S4; S8; S4; S4; S4; SB4; S8; S8; S8; S8; S8; S8; S8; S8; S8; S8].

Lemma file_cells_of_junk : forall segs_ m A junk, rw_cells segs_ m A [CB 232 junk] ->
exists (fl : word) (p0 : list byte) (w8 w16 c24 c32 c40 c48 c56 c64 c72 c80 w88 c96 c104 c112 fd pp c128 md lk lbf : word)
(p1 : list byte) (c152 c160 c168 c176 c184 c192 c200 c208 c216 c224 : word),
rw_cells segs_ m A [C4 fl; CB 4 p0; C8 w8; C8 w16; C8 c24; C8 c32; C8 c40; C8 c48; C8 c56; C8 c64; C8 c72; C8 c80;
C8 w88; C8 c96; C8 c104; C8 c112; C4 fd; C4 pp; C8 c128; C4 md; C4 lk; C4 lbf; CB 4 p1;
C8 c152; C8 c160; C8 c168; C8 c176; C8 c184; C8 c192; C8 c200; C8 c208; C8 c216; C8 c224]
/\ length p0 = 4%nat /\ length p1 = 4%nat.
Proof.
intros segs_ m A junk H. pose proof H as H0. destruct H0 as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [HL _].
pose proof (rw_cells_shape segs_ m A 232 junk FILE_PAT H eq_refl) as H'. cbn [shape_cells FILE_PAT] in H'.
repeat (eexists; []). split; [exact H'|]. split; rewrite length_firstn, ?length_skipn; lia.
Qed.

Lemma file_cells_zero : forall segs_ m A, rw_cells segs_ m A [CB 232 (repeat (Z_to_bv 8 0) 232)] ->
rw_cells segs_ m A [C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4);
C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
intros segs_ m A H. apply (rw_cells_reshape segs_ m A _ _ H); [cbn; repeat split; reflexivity | vm_compute; reflexivity | reflexivity].
Qed.

Section G.

Local Definition gw_tbl_0 := tt.

#[using="Type"] Lemma gw_all : True. Proof. exact I. Qed.

End G.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg.
Import QZAi.Mq1 QZAi QfYR QfcC.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y.
Import QVbl.Mq3.
Import QQLG.Mq8.
Import Qy8Z.Mq0.
Export QQRC.Mq3.

Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.

Definition rtext (T : Z) (txt pre post : list Z) : Prop :=
txt = pre ++ 0%Z :: post /\ Forall (fun c => 0 < c < 256)%Z pre /\ Forall (fun c => 0 <= c < 256)%Z txt /\
((T + zlength txt) mod 8 = 0)%Z /\ (zlength txt <= 256)%Z.

Lemma zbytes_app : forall a b, zbytes (a ++ b) = zbytes a ++ zbytes b.
Proof. intros. unfold zbytes. apply map_app. Qed.
Lemma zbytes_length : forall a, length (zbytes a) = length a.
Proof. intros. unfold zbytes. apply length_map. Qed.
Lemma zbytes_skipn : forall k a, zbytes (skipn k a) = skipn k (zbytes a).
Proof. intros. unfold zbytes. rewrite skipn_map. reflexivity. Qed.
Lemma nonul_pos : forall l, Forall (fun c => 0 < c < 256)%Z l -> ~ In (Z_to_bv 8 0) (zbytes l).
Proof.
intros l H IN. unfold zbytes in IN. apply in_map_iff in IN. destruct IN as [c [E INc]].
pose proof (proj1 (Forall_forall _ _) H c INc) as X. cbv beta in X.
pose proof (f_equal bv_unsigned E) as E2. rewrite !Qy5Y.unsigned_lit8 in E2 by lia. lia.
Qed.
Lemma Forall_skipn' : forall {A} (P : A -> Prop) k l, Forall P l -> Forall P (skipn k l).
Proof. intros A P k l H. rewrite <- (firstn_skipn k l) in H. apply Forall_app in H. tauto. Qed.
Lemma skipn_hd : forall (l : list byte) k b, nth_error l k = Some b -> skipn k l = b :: skipn (S k) l.
Proof.
induction l as [|x l IH]; intros k b H; [destruct k; discriminate H|].
destruct k as [|k]; cbn in H |- *; [injection H as ->; reflexivity|]. exact (IH k b H).
Qed.
Lemma hd_eq : forall (l : list byte) b, nth_error l 0 = Some b -> l = b :: skipn 1 l.
Proof. intros [|x l] b H; [discriminate H|]. cbn in H |- *. injection H as ->. reflexivity. Qed.

Definition sread_len (off p : Z) : Z := if (off <? p)%Z then 1 else 0.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_71 w_72 w_98 : Z).
Variables (STRING_READ : Z).
Variables (e_memcpy e_memchr : Z).
Hypothesis CODE : code_at segs base (shgetc_code w_71 w_72 w_98).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 544.

Local Definition gw_tbl_0 := tt.

Definition memcpy_post : ltac:(gw_rebind_ty (@QVbl.Mq3.memcpy_post segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QVbl.Mq3.memcpy_post segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@QVbl.Mq3.memcpy_post segs) memcpy_post gw_tbl_0).
Definition memchr_post : ltac:(gw_rebind_ty (@QQLG.Mq8.memchr_post segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QQLG.Mq8.memchr_post segs) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QQLG.Mq8.memchr_post segs) memchr_post gw_tbl_1).
Definition ss_cells : ltac:(gw_rebind_ty (@QQRC.Mq3.ss_cells STRING_READ) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ss_cells STRING_READ) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@QQRC.Mq3.ss_cells STRING_READ) ss_cells gw_tbl_2).

Hypothesis memcpy_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq3.memcpy_spec segs e_memcpy) 3%nat in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_3))) in exact T).  Arguments memcpy_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_list_scope _%_list_scope.

Hypothesis memchr_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQLG.Mq8.gw_all) (@QQLG.Mq8.memchr_spec) e_memchr)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_3))) in exact T).  Arguments memchr_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_list_scope.

Notation F_memchr__memchr_post := memchr_post (only parsing).
Notation F_memchr__memchr_spec := memchr_spec (only parsing).
Notation F_memcpy__memcpy_post := memcpy_post (only parsing).
Notation F_memcpy__memcpy_spec := memcpy_spec (only parsing).

#[using="STRING_READ e_memcpy e_memchr CODE BASE4 BASER memcpy_spec memchr_spec"] Lemma gw_all : True. Proof. exact I. Qed.

#[using="Type"] Lemma rw_cells_CB1 : forall m A bs, rw_cells segs m A [CB 1 bs] -> exists b, rw_cells segs m A [CB 1 [b]].
Proof. clear - segs.
intros m A bs H. pose proof H as H'. destruct H as [[[W _] _] _]. cbn in W.
destruct bs as [|b [|]]; try discriminate W. exists b. exact H'.
Qed.
#[using="Type"] Lemma rw_cells_CB0 : forall m A cs, rw_cells segs m A cs -> rw_cells segs m A (CB 0 [] :: cs).
Proof. clear - segs. intros m A cs [[W B] R]. split; [split|]; [split; [reflexivity | exact W] | exact B | exact R]. Qed.
#[using="Type"] Lemma rw_cells_unCB0 : forall m A cs, rw_cells segs m A (CB 0 [] :: cs) -> rw_cells segs m A cs.
Proof. clear - segs. intros m A cs [[[_ W] B] R]. split; [split|]; [exact W | exact B | exact R]. Qed.

Definition memchr_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A C N : Z) (buf : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (memchr_res A C N buf)) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ bytes_at segs m' A buf.
#[using="memchr_spec"] Lemma memchr_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (A C N : Z) (buf : list byte),
bytes_at segs m A buf -> memchr_ok A C N buf -> (0 <= C < 256)%Z -> (0 <= N < 2^64)%Z -> (A < 2^64)%Z -> mem_inv segs m ->
evt segs (memchr_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A C N buf m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_memchr + 0x0)) fc None m (seg_rom segs)).
Proof. clear - memchr_spec segs e_memchr.
intros until buf. intros BA OK HC HN HA MI. pose proof (bytes_at_bound _ _ _ _ BA) as B.
assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
assert (EC : (bv_unsigned (Z_to_bv 64 C) mod 256 = C)%Z) by (rewrite unsigned_lit by lia; apply Z.mod_small; lia).
assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
eapply evt_mono. { eapply F_memchr__memchr_spec with (buf := buf); rewrite ?EA, ?EC, ?EN; [exact BA | exact OK | exact MI]. }
intros ms' P. unfold F_memchr__memchr_post in P. rewrite EA, EC, EN in P. exact P.
Qed.

Definition memcpy_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Dst Src N : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(Dst, Dst + N)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rw_cells segs m' Dst [CB (Z.to_nat N) src]
/\ bytes_at segs m' Src src.
#[using="memcpy_spec"] Lemma memcpy_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (Dst Src N : Z) (src junk : list byte),
bytes_at segs m Src src -> length src = Z.to_nat N -> rw_cells segs m Dst [CB (Z.to_nat N) junk] ->
(Src + N <= Dst \/ Dst + N <= Src)%Z -> (0 <= N)%Z -> (Src + N < 2^64)%Z -> (Dst + N < 2^64)%Z -> mem_inv segs m ->
evt segs (memcpy_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_memcpy + 0x0)) fc None m (seg_rom segs)).
Proof. clear - memcpy_spec segs e_memcpy.
intros until junk. intros BA LEN DC SEP HN HS HD MI.
pose proof (bytes_at_bound _ _ _ _ BA) as B1. pose proof (rw_cells_bound _ _ _ _ DC) as B2. cbn [cells_size csize] in B2.
assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
eapply evt_mono. { eapply F_memcpy__memcpy_spec with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact BA | exact LEN | exact DC | exact SEP | exact MI]. }
intros ms' P. unfold F_memcpy__memcpy_post in P. rewrite ED, ES, EN in P. exact P.
Qed.

Definition sread_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp T D p off : Z) (txt : list Z) (dj : byte) (mode : word) (shend : Z) (shl shc : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sread_len off p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(q - 64, q); (Fp, Fp + 232); (D, D + 1)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' (q - 64) (q)
/\ rw_cells segs m' Fp (ss_cells T (T + off + sread_len off p) (T + p) mode (T + p) shend shl shc)
/\ rw_cells segs m' D [CB 1 [if (off <? p)%Z then Z_to_bv 8 (znth txt off) else dj]]
/\ bytes_at segs m' T (zbytes txt).

Definition sread_stmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T D p off rpos rend shend : Z) (txt pre post : list Z) (dj : byte) (mode shl shc : word),
rw_cells segs m Fp (ss_cells T rpos rend mode (T + off) shend shl shc) ->
rtext T txt pre post -> p = zlength pre -> (0 <= off <= p)%Z ->
bytes_at segs m T (zbytes txt) -> rw_cells segs m D [CB 1 [dj]] ->
(4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
(D + 1 <= Fp \/ Fp + 232 <= D)%Z -> (D + 1 <= T \/ T + zlength txt <= D)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
stk segs m (q - 64) (q) -> (4096 <= q)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
(q <= D)%Z -> (D + 1 <= 2^63)%Z -> (T + zlength txt <= q - 64 \/ q <= T)%Z ->
(0 <= q)%Z -> (q < 2^63)%Z ->
mem_inv segs m ->
evt segs (sread_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T D p off txt dj mode shend shl shc m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 D) (Z_to_bv 64 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 STRING_READ) fc None m (seg_rom segs)).

End G.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg.
Import QZAi.Mq1.
Import QnDM_c1.
Import QVbl.Mq4.
Import QVbl.Mq3.
Import QQLG.Mq7.
Import QQRC.Mq0.

Import Qfw3_c1.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition sn_write_code (w_22 w_34 : Z) : list Z :=
[0xfc010113; 0x02113c23; 0x02813823; 0x02913423; 0x03213023; 0x01313c23; 0x01413823; 0x01513423; 0x00060413; 0x00058913; 0x00050493; 0x09853a83; 0x02853503; 0x0384b583; 0x008ab983; 0x40b50533; 0x00098a13; 0x00a9e463; 0x00050a13; 0x000ab503; 0x020a0263; 0x000a0613; w_22; 0x000ab503; 0x008ab583; 0x01450533; 0x414589b3; 0x00aab023; 0x013ab423; 0x0089e463; 0x00040993; 0x02098463; 0x00090593; 0x00098613; w_34; 0x000ab503; 0x008ab583; 0x01350533; 0x413585b3; 0x00aab023; 0x00bab423; 0x00050023; 0x0584b503; 0x02a4b423; 0x02a4bc23; 0x00040513; 0x03813083; 0x03013403; 0x02813483; 0x02013903; 0x01813983; 0x01013a03; 0x00813a83; 0x04010113; 0x00008067]%Z.

Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_3 := mem_after_store_fast.
Local Ltac lia ::= lia3. Local Ltac mkr__lia_4 := lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.
Ltac br K := brf K; try (exfalso; lia).
Ltac if_lit :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
end. Ltac mkr__if_lit_6 := lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
end.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma le1_zero : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. reflexivity. Qed.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_22 w_34 : Z).
Variables (joff_22 : bv 21).
Variables (e_memcpy : Z).
Hypothesis CODE : code_at segs base (sn_write_code w_22 w_34).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 220.
Hypothesis D_22 : decode_any (Z_to_bv 32 w_22) = Some (Jal 1 joff_22, 4%Z).
Hypothesis E_22 : is_ecall (Z_to_bv 32 w_22) = false.
Hypothesis LINK_22 : gw_anch (base + 88 + bv_signed joff_22)%Z (e_memcpy + 0)%Z.

Local Definition gw_tbl_0 := tt.

Definition memcpy_post : ltac:(gw_rebind_ty (@QVbl.Mq3.memcpy_post segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QVbl.Mq3.memcpy_post segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@QQLG.Mq7.memcpy_post segs) memcpy_post (gw_ent (@QVbl.Mq3.memcpy_post segs) memcpy_post gw_tbl_0)).

Hypothesis memcpy_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq3.memcpy_spec segs e_memcpy) 3%nat in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_1))) in exact T).

#[using="e_memcpy CODE BASE4 BASER D_22 E_22 LINK_22 memcpy_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac transport_chunks segs_ m a bs ::= transport_chunks_fast segs_ m a bs.
Local Ltac footprint_after_store segs_ m a bs ::= footprint_after_store_fast segs_ m a bs.
Local Ltac transport_after_call segs_ m m' MU WM ::= transport_after_call_fast segs_ m m' MU WM.
#[using="Type"] Lemma rw_CB_length : forall m A n (bs : list byte), rw_cells segs m A [CB n bs] -> length bs = n.
Proof. clear - segs. intros m A n bs [[[H _] _] _]. exact H. Qed.

Definition memcpy_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Dst Src N : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(Dst, Dst + N)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rw_cells segs m' Dst [CB (Z.to_nat N) src]
/\ bytes_at segs m' Src src.
#[using="memcpy_spec"] Lemma memcpy_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (Dst Src N : Z) (src junk : list byte),
bytes_at segs m Src src -> length src = Z.to_nat N -> rw_cells segs m Dst [CB (Z.to_nat N) junk] ->
(Src + N <= Dst \/ Dst + N <= Src)%Z -> (0 <= N < 2^64)%Z -> (0 <= Src < 2^64)%Z -> (0 <= Dst < 2^64)%Z -> mem_inv segs m ->
evt segs (memcpy_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_memcpy + 0x0)) fc None m (seg_rom segs)).
Proof. clear - memcpy_spec segs e_memcpy.
intros until junk. intros BA LEN DC SEP HN HS HD MI.
assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
eapply evt_mono. { eapply memcpy_spec with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact BA | exact LEN | exact DC | exact SEP | exact MI]. }
intros ms' P. unfold memcpy_post, memcpy_postv in *. rewrite ED, ES, EN in P. exact P.
Qed.

Definition sn_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp CK D n B bufp : Z) (o : list Z) (dn : nat) (junk : list byte) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m m'
/\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' (bv_unsigned sp - 64) (bv_unsigned sp)
/\ rw_cells segs m' CK [C8 (Z_to_bv 64 (D + zlength o)); C8 (Z_to_bv 64 (n - zlength o))]
/\ rw_cells segs m' D [CB dn (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junk)]
/\ rw_cells segs m' (Fp + 40) [C8 (Z_to_bv 64 bufp)]
/\ rw_cells segs m' (Fp + 56) [C8 (Z_to_bv 64 bufp)]
/\ bytes_at segs m' B (zb o).

#[using="w_22 w_34 joff_22 e_memcpy CODE BASE4 BASER D_22 E_22 LINK_22 memcpy_spec"] Lemma sn_write_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : mem) (Fp CK D n B bufp : Z) (o : list Z) (dn : nat) (junk : list byte),
a0 = Z_to_bv 64 Fp -> a2 = Z_to_bv 64 0 ->
rw_cells segs m (Fp + 40) [C8 (Z_to_bv 64 (B + zlength o))] ->
rw_cells segs m (Fp + 56) [C8 (Z_to_bv 64 B)] ->
rw_cells segs m (Fp + 88) [C8 (Z_to_bv 64 bufp)] ->
rw_cells segs m (Fp + 152) [C8 (Z_to_bv 64 CK)] ->
rw_cells segs m CK [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 n)] ->
bytes_at segs m B (zb o) ->
rw_cells segs m D [CB dn junk] -> (length o < dn)%nat -> (zlength o <= n < 2^63)%Z -> (0 <= bufp < 2^64)%Z -> (B + zlength o < 2^63)%Z ->
stk segs m (bv_unsigned sp - 64) (bv_unsigned sp) -> (64 <= bv_unsigned sp)%Z -> mem_inv segs m ->

(B + zlength o <= D \/ D + Z.of_nat dn <= B)%Z ->
(CK + 16 <= D \/ D + Z.of_nat dn <= CK)%Z ->
(Fp + 160 <= D \/ D + Z.of_nat dn <= Fp + 40)%Z ->
(D + Z.of_nat dn <= bv_unsigned sp - 64 \/ bv_unsigned sp <= D)%Z ->
(bv_unsigned sp <= CK)%Z -> (bv_unsigned sp <= Fp)%Z -> (bv_unsigned sp <= B)%Z ->
(CK + 16 <= Fp + 40 \/ Fp + 160 <= CK)%Z ->
(B + zlength o <= CK \/ CK + 16 <= B)%Z -> (B + zlength o <= Fp + 40 \/ Fp + 160 <= B)%Z ->
evt segs (sn_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp CK D n B bufp o dn junk m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof. clear - w_22 w_34 joff_22 e_memcpy CODE BASE4 BASER D_22 E_22 LINK_22 memcpy_spec segs base.
intros until junk. intros -> -> WPOS WBASE BUF COOKIE CKC SRC DST ROOM Hn Hbufp BHI ST SPLO MI D1 D2 D3 D4 S1 S2 S3 S4 S5 S6.
pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
pose proof (rw_cells_bound _ _ _ _ CKC) as CB_. cbn [cells_size csize Nat.add] in CB_.
pose proof (rw_cells_bound _ _ _ _ COOKIE) as FB. cbn [cells_size csize Nat.add] in FB.
pose proof (bytes_at_bound _ _ _ _ SRC) as BB. pose proof (zb_length o) as LZ. rewrite LZ in BB. unfold zlength in *.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m) as MU.
pose proof (wmono_refl segs m) as WM.
pose_word_ranges.
carve_frame 64%nat ST.
do 15 zs.
zs. replace (B + Z.of_nat (length o) - B)%Z with (Z.of_nat (length o)) by lia.
zs. zs. brf K1; [exfalso; lia|]. zs. zs. zs. brf K2.
-
assert (O0 : length o = 0%nat) by lia. destruct o as [|c o']; [|cbn in O0; lia]. cbn [length Z.of_nat] in *.
zs. brf K3; [exfalso; lia|]. zs. zs. if_lit.
pose proof (rw_CB_length _ _ _ _ DST) as LJ.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as DA. clear DST.
pose proof (u8arr_store_ok segs _ _ _ 0%Z (Z_to_bv 64 D) DA ltac:(rewrite LJ; lia) ltac:(f_equal; lia)) as SOK.
zs. rewrite le1_zero. replace (Z_to_bv 64 D) with (wa (D + 0)) by (unfold wa; f_equal; lia).
pose proof (u8arr_write segs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJ; lia)) as DA2. clear DA. store_done.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DST. rewrite upd_length, LJ in DST.
zs. zs. zs. zs.
do 9 zs.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold sn_write_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; rewrite ?Z.add_0_r; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
split. { cbn [zlength length Z.of_nat]. rewrite Z.add_0_r, Z.sub_0_r. match goal with H : rw_cells _ _ CK _ |- _ => exact H end. }
split. { cbn [zb map app length skipn]. rewrite upd_firstn_skipn in DST by (rewrite LJ; lia). cbn [firstn app] in DST. exact DST. }
split; [assumption|]. split; [assumption|]. assumption.
-
pose proof (rw_CB_length _ _ _ _ DST) as LJ.
apply (rw_cells_split_CB segs _ _ [] dn _ [] [length o; dn - length o]%nat) in DST; [ | cbn; lia ].
cbn [mk_CB_cells app] in DST.
apply (proj1 (rw_cells_app segs _ _ [_] _)) in DST. destruct DST as [DSTa DSTb]. cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
zs. zs.
eapply evt_cut.
{ eapply memcpy_callv with (src := zb o) (junk := firstn (length o) junk);
[ exact SRC | rewrite LZ; lia | rewrite Nat2Z.id; exact DSTa | lia | lia | lia | lia | exact MI ]. }
cbv beta. intros ms' P. unfold memcpy_postv in P.
destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & DSTa' & SRC').
lazymatch type of MUc with munch _ ?mm _ => transport_after_call segs mm m' MUc WMc; clear MUc WMc; try clear MI end.
(try g_ret_pc).
zs. zs. zs. zs. zs. zs.
zs. brf K3; [exfalso; lia|]. zs. zs. if_lit.
pose proof (rw_CB_length _ _ _ _ DSTb) as LJb.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DSTb) as DA. clear DSTb.
pose proof (u8arr_store_ok segs _ _ _ 0%Z (Z_to_bv 64 (D + Z.of_nat (length o))) DA ltac:(rewrite LJb; lia) ltac:(f_equal; lia)) as SOK.
zs. rewrite le1_zero. replace (Z_to_bv 64 (D + Z.of_nat (length o))) with (wa (D + Z.of_nat (length o) + 0)) by (unfold wa; f_equal; lia).
pose proof (u8arr_write segs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJb; lia)) as DA2. clear DA. store_done.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DSTb. rewrite upd_length, LJb in DSTb.
zs. zs. zs. zs.
do 9 zs.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold sn_write_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; rewrite ?Z.add_0_r; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split. { unfold zlength. match goal with H : rw_cells _ _ CK _ |- _ => exact H end. }
split.
{ match goal with Ha : rw_cells _ ?mm D [CB _ ?l1], Hb : rw_cells _ ?mm (D + _)%Z [CB _ ?l2] |- _ =>
assert (J : rw_cells segs mm D ([] ++ [CB (length o) l1; CB (dn - length o) l2] ++ []));
[ cbn [app]; apply (proj2 (rw_cells_app segs _ _ [_] _)); split; [rewrite Nat2Z.id in Ha; exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r; exact Hb
| apply rw_cells_merge in J; cbn [cells_size cells_bytes csize cbytes app] in J; rewrite app_nil_r in J ] end.
replace (length o + (dn - length o + 0))%nat with dn in J by lia.
rewrite upd_firstn_skipn in J by (rewrite length_firstn, length_skipn, LJ; lia). change (Z.to_nat 0) with 0%nat in J. rewrite firstn_O, app_nil_l in J.
rewrite skipn_firstn_comm, skipn_skipn in J. replace (1 + length o)%nat with (S (length o)) in J by lia.
rewrite firstn_all2 in J by (rewrite length_skipn, LJ; lia). first [exact J | let t := type of J in idtac "J:" t; match goal with |- ?g => idtac g end; fail]. }
split; [assumption|]. split; [assumption|]. assumption.
Qed.

End G.
End Mq4.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Q2qa QytA Q4J3 QPjm QJE4 QWTl QUZl Q7S0 Q8QT QDXD QkTt Q6q3 G.GwFamMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.

Import Q2qa.Mq1 QytA Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 Qy5Y.Mq6 QPjm.Mq3 QJE4.Mq0 QJE4.Mq1 QWTl.Mq1.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QkTt.Mq4.
Import Qy8Z.Mq9.
Import QQRC.Mq5.
Import Qy8Z.Mq2.
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

Definition errno_loc_code : list Z :=
[0x00020513; 0xf5c50513; 0x00008067]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rerrno_loc_entry rvm_wait_entry : Z).
Variables (w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 : Z).
Variables (hi_7 hi_10 hi_14 : bv 20).
Variables (lo_8 lo_12 lo_15 : bv 12).
Variables (joff_30 joff_98 joff_120 joff_173 joff_175 joff_181 : bv 21).
Variables (e_197bc e_24f80 : Z).
Hypothesis CODE : code_at segs base (alloc_meta_code w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 728.
Let rmmap_entry := (rvm_wait_entry + 4)%Z.
Let rmprotect_entry := (rvm_wait_entry + 240)%Z.
Hypothesis D_7 : decode_any (Z_to_bv 32 w_7) = Some (Auipc 10 hi_7, 4%Z).
Hypothesis E_7 : is_ecall (Z_to_bv 32 w_7) = false.
Hypothesis D_8 : decode_any (Z_to_bv 32 w_8) = Some (Load SZ8 true 18 10 lo_8, 4%Z).
Hypothesis E_8 : is_ecall (Z_to_bv 32 w_8) = false.
Hypothesis D_10 : decode_any (Z_to_bv 32 w_10) = Some (Auipc 11 hi_10, 4%Z).
Hypothesis E_10 : is_ecall (Z_to_bv 32 w_10) = false.
Hypothesis D_12 : decode_any (Z_to_bv 32 w_12) = Some (OpImm ALU_ADD 19 11 lo_12, 4%Z).
Hypothesis E_12 : is_ecall (Z_to_bv 32 w_12) = false.
Hypothesis D_14 : decode_any (Z_to_bv 32 w_14) = Some (Auipc 11 hi_14, 4%Z).
Hypothesis E_14 : is_ecall (Z_to_bv 32 w_14) = false.
Hypothesis D_15 : decode_any (Z_to_bv 32 w_15) = Some (OpImm ALU_ADD 8 11 lo_15, 4%Z).
Hypothesis E_15 : is_ecall (Z_to_bv 32 w_15) = false.
Hypothesis D_30 : decode_any (Z_to_bv 32 w_30) = Some (Jal 1 joff_30, 4%Z).
Hypothesis E_30 : is_ecall (Z_to_bv 32 w_30) = false.
Hypothesis D_98 : decode_any (Z_to_bv 32 w_98) = Some (Jal 1 joff_98, 4%Z).
Hypothesis E_98 : is_ecall (Z_to_bv 32 w_98) = false.
Hypothesis D_120 : decode_any (Z_to_bv 32 w_120) = Some (Jal 1 joff_120, 4%Z).
Hypothesis E_120 : is_ecall (Z_to_bv 32 w_120) = false.
Hypothesis D_173 : decode_any (Z_to_bv 32 w_173) = Some (Jal 1 joff_173, 4%Z).
Hypothesis E_173 : is_ecall (Z_to_bv 32 w_173) = false.
Hypothesis D_175 : decode_any (Z_to_bv 32 w_175) = Some (Jal 1 joff_175, 4%Z).
Hypothesis E_175 : is_ecall (Z_to_bv 32 w_175) = false.
Hypothesis D_181 : decode_any (Z_to_bv 32 w_181) = Some (Jal 1 joff_181, 4%Z).
Hypothesis E_181 : is_ecall (Z_to_bv 32 w_181) = false.
Hypothesis ANCH_8 : gw_anch (Z.shiftl (bv_signed hi_7) 12 + (base + 28) + bv_signed lo_8)%Z RGOT_SSP.
Hypothesis ANCH_12 : gw_anch (Z.shiftl (bv_signed hi_10) 12 + (base + 40) + bv_signed lo_12)%Z (RATP + 131960).
Hypothesis ANCH_15 : gw_anch (Z.shiftl (bv_signed hi_14) 12 + (base + 56) + bv_signed lo_15)%Z (RATP + 131728).
Hypothesis LINK_30 : gw_anch (base + 120 + bv_signed joff_30)%Z (e_24f80 + 0)%Z.
Hypothesis LINK_98 : gw_anch (base + 392 + bv_signed joff_98)%Z (rmmap_entry + 0)%Z.
Hypothesis LINK_120 : gw_anch (base + 480 + bv_signed joff_120)%Z (rmmap_entry + 0)%Z.
Hypothesis LINK_173 : gw_anch (base + 692 + bv_signed joff_173)%Z (rmprotect_entry + 0)%Z.
Hypothesis LINK_175 : gw_anch (base + 700 + bv_signed joff_175)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_181 : gw_anch (base + 724 + bv_signed joff_181)%Z (e_197bc + 0)%Z.
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
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis AL_rerrno_loc_entry : gw_al rerrno_loc_entry 4.
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition ram_fp : ltac:(gw_rebind_ty (@QQRC.Mq5.ram_fp RATP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QQRC.Mq5.ram_fp RATP) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QQRC.Mq5.ram_fp RATP) (@ram_fp) gw_tbl_0).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QQRC.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq9.rpres_except segs) (@rpres_except) gw_tbl_1)))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@Qy8Z.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq9.rarea_rep segs) (@rarea_rep) gw_tbl_2))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@Qy8Z.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq9.rmrep_areas segs) (@rmrep_areas) gw_tbl_3))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@Qy8Z.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_4))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@Qy8Z.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_5))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@Qy8Z.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq9.rgroup_rep segs) (@rgroup_rep) gw_tbl_6))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@Qy8Z.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq9.rmrep_groups segs) (@rmrep_groups) gw_tbl_7))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@Qy8Z.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq9.rshadow_rep segs) (@rshadow_rep) gw_tbl_8))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@Qy8Z.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq9.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_9))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@Qy8Z.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_10))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@Qy8Z.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_11))))))).
Definition ram_ret_post : ltac:(gw_rebind_ty (@QQRC.Mq5.ram_ret_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QQRC.Mq5.ram_ret_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@QQRC.Mq5.ram_ret_post segs RATP RGOT_SSP ref_reserved RC__) (@ram_ret_post) gw_tbl_12).
Definition ram_frame : ltac:(gw_rebind_ty (@QQRC.Mq5.ram_frame RC__) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QQRC.Mq5.ram_frame RC__) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@QQRC.Mq5.ram_frame RC__) (@ram_frame) gw_tbl_13).
Definition rrepfoot : ltac:(gw_rebind_ty (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) constr:(gw_tbl_14)).
Notation gw_tbl_15 := (gw_ent (@Qy8Z.Mq2.rrepfoot RATP RGOT_SSP) (@rrepfoot) (gw_ent (@QkTt.Mq4.rrepfoot RATP RGOT_SSP) (@rrepfoot) (gw_ent (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) (@rrepfoot) gw_tbl_14))).

Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).
Definition rreserved_disjoint : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint)).
Definition rarea_lr_lo : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_lr_lo) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_lr_lo)).
Definition rarea_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_conc) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_conc)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rpres_except_trans : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_trans) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_trans)).
Definition rpres_except_mono : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_mono) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_mono)).

Definition rmrep_transport_unowned : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_transport_unowned) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_transport_unowned)).
Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rpres_except_of_munch_cov : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rpres_except_of_munch_cov) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rpres_except_of_munch_cov)).
Definition rmrep_ctx_frameW : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_ctx_frameW) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_ctx_frameW)).

Definition ram_fp_stack : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq5.ram_fp_stack) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq5.ram_fp_stack)).
Definition ram_fp_ctx : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq5.ram_fp_ctx) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq5.ram_fp_ctx)).
Definition ram_fp_region : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq5.ram_fp_region) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq5.ram_fp_region)).
Definition ram_fp_area : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq5.ram_fp_area) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq5.ram_fp_area)).
Definition ram_fp_same : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq5.ram_fp_same) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq5.ram_fp_same)).
Definition ram_b0 : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq5.ram_b0) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq5.ram_b0)).

Definition rrw_cells_of_zeros : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mq2.rrw_cells_of_zeros) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mq2.rrw_cells_of_zeros)).
Definition rmrep_set_area_next : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mq2.rmrep_set_area_next) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mq2.rmrep_set_area_next)).
Definition rmrep_new_area : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mq2.rmrep_new_area) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mq2.rmrep_new_area)).
Definition rfresh_page_avoids : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mq2.rfresh_page_avoids) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mq2.rfresh_page_avoids)).

#[using="RGOT_SSP rerrno_loc_entry e_197bc rmmap_entry rmprotect_entry e_24f80 RATP RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry CODE BASE4 BASER D_7 E_7 D_8 E_8 D_10 E_10 D_12 E_12 D_14 E_14 D_15 E_15 D_30 E_30 D_98 E_98 D_120 E_120 D_173 E_173 D_175 E_175 D_181 E_181 ANCH_8 ANCH_12 ANCH_15 LINK_30 LINK_98 LINK_120 LINK_173 LINK_175 LINK_181 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rmmap_entry rmprotect_entry"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := first [clear - hs segs base w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 hi_7 hi_10 hi_14 lo_8 lo_12 lo_15 joff_30 joff_98 joff_120 joff_173 joff_175 joff_181 RGOT_SSP rerrno_loc_entry e_197bc rmmap_entry rmprotect_entry e_24f80 RATP RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry CODE BASE4 BASER D_7 E_7 D_8 E_8 D_10 E_10 D_12 E_12 D_14 E_14 D_15 E_15 D_30 E_30 D_98 E_98 D_120 E_120 D_173 E_173 D_175 E_175 D_181 E_181 ANCH_8 ANCH_12 ANCH_15 LINK_30 LINK_98 LINK_120 LINK_173 LINK_175 LINK_181 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ | clear - hs segs base w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 hi_7 hi_10 hi_14 lo_8 lo_12 lo_15 joff_30 joff_98 joff_120 joff_173 joff_175 joff_181 RGOT_SSP rerrno_loc_entry e_197bc rmmap_entry rmprotect_entry e_24f80 RATP RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry CODE BASE4 BASER D_7 E_7 D_8 E_8 D_10 E_10 D_12 E_12 D_14 E_14 D_15 E_15 D_30 E_30 D_98 E_98 D_120 E_120 D_173 E_173 D_175 E_175 D_181 E_181 ANCH_8 ANCH_12 ANCH_15 LINK_30 LINK_98 LINK_120 LINK_173 LINK_175 LINK_181 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay].

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmmap_entry rmprotect_entry"] Lemma ram_carve2 : forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m0 m : word -> option byte) (junk : list byte) (lo : Z) (st0 st : mstate) (p : aptr) (r : region),
rmrep st m -> mem_inv segs m -> s_regions st = s_regions st0 ->
(s_regions st) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
pgal (snd p) -> lr_lo r <= r_base r + snd p ->
(s_areas st) !! p = None -> (forall k, 0 <= k < NSLOTS -> (s_metas st) !! (aadd p (AREA_HDR + META_SIZE * k)) = None) ->
0 <= c_secret (ctx st) < 2^64 ->
rw_cells segs m (conc st p) [C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0)] ->
rw_cells segs m (conc st p + 24) [CB 4072 (zeros 4072)] ->
rpres_except (ram_fp st0 lo (bv_unsigned sp)) m0 m -> wmono segs m0 m ->
rw_cells segs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk segs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
let stC := upd_ctx (set_meta_area_tail (Some p)) st in
let stD := set_areas (<[p := mkArea (c_secret (ctx st)) None NSLOTS]> (s_areas stC)) stC in
evt segs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
(am_took stD (aadd p AREA_HDR) 100) (Z_to_bv 64 (conc st p + 24)))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st p)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x244)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmmap_entry rmprotect_entry segs base RATP. gw_expose_fam RATP.
intros until r. intros MR MI ER0 Hr NK S0 S1 SAL SLR ANone FRESH SEC HDR0 REST PE0 WM0 FR ST LO LOLE stC stD.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR as (WF & (C1 & _) & _). pose proof WF as (Hres & WR & DJ & WA & WG).
pose proof (conc_region' st p r Hr) as Cp.
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). unfold alloc_ceiling in RBC.
pose proof (lr_lo_ge r) as LRG. pose proof (round_up_pg_ge (r_len r)) as RU.
unfold ctx_head_cells in C1.
(gw_expose_fam RATP; unfold alloc_ceiling in *).

assert (PD : conc st p + 4096 <= RDATA_LO \/ RIMG_HI <= conc st p) by lia.
assert (PB : 0 <= conc st p /\ conc st p + 4096 <= lo) by lia.
clear RBAL RL0 RB0 RF DR1 DR23 DR2 LRG RU Hres DJ WA WG.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); ((RATP + 131968), (RATP + 132896)); (conc st p, conc st p + 4096)]%Z m) as MU.
pose proof (wmono_refl segs m) as WM. gw_expose_fam RATP.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [((RATP + 132032), (RATP + 132040))]%Z mX) as MUc; pose proof (wmono_refl segs mX) as WMc end.
gw_expose_fam RATP.
st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRC : rmrep stC mX) end.
{ eapply (rmrep_ctx_frameW st stC _ _ _ MR MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia.
- left. (gw_expose_fam RATP; unfold ctx_head_cells). cbn [ctx stC upd_ctx s_ctx set_meta_area_tail c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
unfold pw at 4. cbn [oconc]. change (conc stC p) with (conc st p). gw_exact C1.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia. }
clear MUc WMc.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(conc st p, conc st p + 4096)]%Z mX) as MUp; pose proof (wmono_refl segs mX) as WMp end.

st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRC3 : rmrep stC mX) end.
{ eapply rmrep_transport_unowned; [gw_exact MRC | gw_exact MUp | gw_exact WMp |].
intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. eapply (rfresh_page_avoids stC _ p r a MRC); try assumption. }
clear MUp WMp MRC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRD : rmrep stD mX) end.
{ unfold stD. eapply (rmrep_new_area stC _ p r (c_secret (ctx st))); try first [gw_exact MRC3 | gw_exact Hr | gw_exact NK | gw_exact S0 | gw_exact S1 | gw_exact SLR | gw_exact ANone | gw_exact FRESH | idtac].
- gw_exact SAL.
- change (conc stC p) with (conc st p). gw_exact HDR0.
- intros k Hk. change (conc stC p) with (conc st p). rewrite meta_cells_meta0.
destruct REST as [[_ B] W]. cbn [cells_bytes cbytes cells_size csize Nat.add] in B, W. rewrite app_nil_r in B.
replace (conc st p + AREA_HDR + META_SIZE * k) with ((conc st p + 24) + 40 * k) by (unfold AREA_HDR, META_SIZE; lia).
eapply (rrw_cells_of_zeros _ (conc st p + 24) 4072 (40 * k)); [gw_exact B| gw_exact W| cbn; tauto| reflexivity| lia| cbn [cells_size csize Nat.add]; unfold NSLOTS in Hk; lia].
- change (conc stC p) with (conc st p).
destruct REST as [[_ B] W]. cbn [cells_bytes cbytes cells_size csize Nat.add] in B, W. rewrite app_nil_r in B.
replace (conc st p + 4064) with ((conc st p + 24) + 4040) by lia.
eapply (rrw_cells_of_zeros _ (conc st p + 24) 4072 4040); [gw_exact B| gw_exact W| cbn; split; [reflexivity| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| lia| cbn [cells_size csize Nat.add]; lia]. }
clear MRC3 HDR0 REST.
assert (MSq : meta_slot stD (aadd p AREA_HDR)).
{ exists p, (mkArea (c_secret (ctx st)) None NSLOTS), 0. split; [| split; [unfold NSLOTS; lia| unfold AREA_HDR, META_SIZE; rewrite Z.mul_0_r, Z.add_0_r; reflexivity]].
unfold stD. cbn [s_areas set_areas]. rewrite lookup_insert_eq. reflexivity. }
assert (CQ : conc st p + 24 = conc stD (aadd p AREA_HDR)).
{ change (conc stD (aadd p AREA_HDR)) with (conc st (aadd p AREA_HDR)). rewrite (conc_aadd st p AREA_HDR) by (rewrite Hr; eauto). reflexivity. }
rewrite CQ. change (Z_to_bv 64 (RATP + 131696)) with (Z_to_bv 64 (RATP + 131696)). change (Z_to_bv 64 (RATP + 131960)) with (Z_to_bv 64 (RATP + 131960)).
eapply evt_mono.
{ eapply (ram_b0 sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo 100 stD (aadd p AREA_HDR));
[gw_exact MRD | assumption | gw_exact MSq | lia | | | unfold alloc_ceiling; lia | lia].
- lazymatch goal with H : rw_cells segs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
- lazymatch goal with H : stk segs ?mX lo _ |- _ => exact H end. }
intros ms' RP. unfold ram_ret_post in RP |- *.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
do 15 eexists. split; [reflexivity|].
split.
{ eapply rpres_except_trans; [gw_exact PE0|].
apply (rpres_except_of_munch_cov (ram_fp st0 lo (bv_unsigned sp))) in MU; [|gw_exact WM|].
- eapply rpres_except_trans; [gw_exact MU|]. eapply rpres_except_mono; [gw_exact PE'|]. intros a Ha.
apply (proj1 (ram_fp_same st0 stD lo _ a ltac:(rewrite <- ER0; reflexivity))). gw_exact Ha.
- cbn [ivs_covered]. split; [|split; [|split; [|exact I]]].
+ intros x Hx. apply ram_fp_stack. lia.
+ intros x Hx. apply ram_fp_ctx. gw_expose_fam RATP. lia.
+ intros x Hx. eapply (ram_fp_region st0 lo _ x (fst p) r); [rewrite <- ER0; gw_exact Hr| gw_exact NK|].
pose proof (lr_lo_ge r). lia. }

split; [eapply wmono_trans; [gw_exact WM0| gw_exact WM']|]. split; [gw_exact MI'|]. split; [gw_exact ST'|]. gw_exact MR'.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmmap_entry rmprotect_entry"] Lemma ram_carve_walk : forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (p : aptr) (r : region),
rmrep st m -> mem_inv segs m ->
(s_regions st) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
pgal (snd p) -> lr_lo r <= r_base r + snd p ->
(s_areas st) !! p = None -> (forall k, 0 <= k < NSLOTS -> (s_metas st) !! (aadd p (AREA_HDR + META_SIZE * k)) = None) ->
(forall tl, c_meta_area_tail (ctx st) = Some tl -> is_Some ((s_areas st) !! tl)) ->
1 <= c_avail_meta_area_count (ctx st) < 2^64 -> 0 <= c_secret (ctx st) < 2^64 ->
bytes_at segs m (conc st p) (zeros 4096) -> wr_at segs m (conc st p) 4096 ->
rw_cells segs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk segs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
evt segs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo (carve_st st p) m
(am_took (carve_st st p) (aadd p AREA_HDR) 100) (Z_to_bv 64 (conc st p + 24)))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st p)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x218)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmmap_entry rmprotect_entry segs base RATP. gw_expose_fam RATP.
intros until r. intros MR MI Hr NK S0 S1 SAL SLR ANone FRESH TL CNT SEC ZB ZW FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR as (WF & (C1 & _) & _ & AR & _). pose proof WF as (Hres & WR & DJ & WA & WG).
pose proof (conc_region' st p r Hr) as Cp.
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). unfold alloc_ceiling in RBC.
pose proof (lr_lo_ge r) as LRG. pose proof (round_up_pg_ge (r_len r)) as RU.
unfold ctx_head_cells in C1.

assert (HDR0 : rw_cells segs m (conc st p) [C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0)]).
{ rewrite <- (Z.add_0_r (conc st p)). eapply (rrw_cells_of_zeros m (conc st p) 4096 0); [gw_exact ZB| gw_exact ZW| cbn; tauto| reflexivity| lia| cbn; lia]. }
assert (REST : rw_cells segs m (conc st p + 24) [CB 4072 (zeros 4072)]).
{ eapply (rrw_cells_of_zeros m (conc st p) 4096 24); [gw_exact ZB| gw_exact ZW| cbn [cells_wf]; split; [first [reflexivity | apply zeros_length]| exact I] | cbn [cells_bytes cbytes cells_size csize Nat.add]; rewrite app_nil_r; reflexivity| lia| cbn; lia]. }
clear ZB ZW.
(gw_expose_fam RATP; unfold alloc_ceiling in *).
assert (PD : conc st p + 4096 <= RDATA_LO \/ RIMG_HI <= conc st p) by lia.
assert (PB : 0 <= conc st p /\ conc st p + 4096 <= lo) by lia.
clear RBAL RL0 RF DR1 DR23 DR2 RU.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); ((RATP + 131968), (RATP + 132896)); (conc st p, conc st p + 4096)]%Z m) as MU0.
pose proof (wmono_refl segs m) as WM0. gw_expose_fam RATP.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [((RATP + 132008), (RATP + 132016)); ((RATP + 132040), (RATP + 132048))]%Z mX) as MUc; pose proof (wmono_refl segs mX) as WMc end.
gw_expose_fam RATP.

st1. st1. st1. st1. st1. st1. st1.
set (st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : rmrep st1 mX) end.
{ eapply (rmrep_ctx_frameW st st1 _ _ _ MR MUc WMc); try reflexivity.
- intros lo' hi' [E|[E|[]]]; inversion E; subst; gw_expose_fam RATP; lia.
- left. (gw_expose_fam RATP; unfold ctx_head_cells). cbn [ctx st1 upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
unfold pw at 5. cbn [oconc]. change (conc st1 (aadd p 4096)) with (conc st (aadd p 4096)).
rewrite (conc_aadd st p 4096) by (rewrite Hr; eauto). unfold wz at 6 7.
lazymatch goal with H : rw_cells segs ?mX (RATP + 131968) _ |- _ => exact H end.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; gw_expose_fam RATP; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; gw_expose_fam RATP; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; gw_expose_fam RATP; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; gw_expose_fam RATP; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; gw_expose_fam RATP; lia. }
clear MUc WMc.

st1.
destruct (c_meta_area_tail (ctx st)) as [tl|] eqn:HT.
-
destruct (TL tl eq_refl) as [ar Har].
destruct (rarea_conc st tl ar WF Har) as (rt & Hrt & Ct & St0 & St1 & StL & NKt & RBt & RBAt & RBCt). unfold alloc_ceiling in RBCt.
pose proof (rarea_lr_lo st tl ar rt WF Har Hrt) as LRt.
destruct (WR _ _ Hrt) as (_ & _ & _ & _ & RFt). destruct (rreserved_disjoint _ _ RFt) as (DT1 & _ & DT23 & DT2).
assert (TD : conc st tl + 4096 <= RDATA_LO \/ RIMG_HI <= conc st tl) by lia.
assert (TB : 0 < conc st tl /\ conc st tl + 4096 <= lo) by lia.
assert (TP : conc st tl + 4096 <= conc st p \/ conc st p + 4096 <= conc st tl).
{ destruct (N.eq_dec (fst tl) (fst p)) as [E|NE].
- rewrite E, Hr in Hrt. assert (rt = r) by congruence. subst rt.
assert (NEo : snd tl <> snd p) by (intros E2; assert (tl = p) by (destruct tl, p; cbn in *; congruence); subst tl; rewrite ANone in Har; discriminate).
unfold pgal in SAL. clear - Ct Cp NEo SAL StL E RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmmap_entry rmprotect_entry segs base RATP. Z.div_mod_to_equations. lia.
- destruct (DJ _ _ _ _ Hrt Hr NE); lia. }
clear RBAt StL RFt DT1 DT23 DT2 St0 St1 LRt RBt RBCt DJ WA WG.
unfold pw. cbn [oconc]. unfold wz.
assert (CF : bv_eqb (Z_to_bv 64 (conc st tl)) (Z_to_bv 64 0) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
rewrite CF. clear CF.
pose proof MR1 as (_ & _ & _ & AR1 & _). destruct (AR1 tl ar Har) as (ARh & _ & _). clear AR1.
change (conc st1 tl) with (conc st tl) in ARh.
apply (munch_grow2 _ (conc st tl, conc st tl + 4096)) in MU0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(conc st tl + 8, conc st tl + 16)]%Z mX) as MUa; pose proof (wmono_refl segs mX) as WMa end.

st1. st1.
set (st2 := set_areas (<[tl := mkArea (a_check ar) (Some p) (a_nslots ar)]> (s_areas st1)) st1).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR2 : rmrep st2 mX) end.
{ eapply (rmrep_set_area_next st1 _ _ tl ar p MR1 Har); [cbn; rewrite Hr; eauto| gw_exact MUa| gw_exact WMa|].
change (conc st1 tl) with (conc st tl). change (conc st1 p) with (conc st p). unfold wz at 2. gw_exact ARh. }
clear MUa WMa ARh MR1.
rewrite (carve_st_some st p tl ar HT Har ANone). cbv zeta. fold st1. fold st2.
change (Z_to_bv 64 (RATP + 131696)) with (Z_to_bv 64 (RATP + 131696)). change (Z_to_bv 64 (RATP + 131960)) with (Z_to_bv 64 (RATP + 131960)).
eapply evt_mono.
{ eapply (ram_carve2 sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc m _ junk lo st st2 p r);
first [gw_exact MR2 | reflexivity | gw_exact Hr | gw_exact NK | gw_exact S0 | gw_exact S1 | gw_exact SAL | gw_exact SLR | gw_exact FRESH | gw_exact SEC | gw_exact WM0 | idtac].
- lazymatch goal with H : mem_inv segs ?mX |- _ => exact H end.
- cbn [s_areas set_areas upd_ctx st2 st1]. rewrite lookup_insert_ne; [gw_exact ANone|]. intros ->. rewrite ANone in Har; discriminate.
- lazymatch goal with H : rw_cells segs ?mX (conc st p) _ |- _ => exact H end.
- lazymatch goal with H : rw_cells segs ?mX (conc st p + 24) _ |- _ => exact H end.
- apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU0; [gw_exact MU0|gw_exact WM0|].
cbn [ivs_covered]. split; [|split; [|split; [|split; [|exact I]]]].
+ intros x Hx. apply ram_fp_stack. lia.
+ intros x Hx. eapply ram_fp_area; [gw_exact MR| gw_exact Har| lia].
+ intros x Hx. apply ram_fp_ctx. gw_expose_fam RATP. lia.
+ intros x Hx. eapply (ram_fp_region st lo _ x (fst p) r); [gw_exact Hr| gw_exact NK| lia].
- lazymatch goal with H : rw_cells segs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
- lazymatch goal with H : stk segs ?mX lo _ |- _ => exact H end.
- unfold alloc_ceiling; lia.
- lia. }
intros ms' RP. gw_exact RP.
-
unfold pw. cbn [oconc]. unfold wz.
change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [((RATP + 132024), (RATP + 132032))]%Z mX) as MUc; pose proof (wmono_refl segs mX) as WMc end.
gw_expose_fam RATP.

st1.
set (st2 := upd_ctx (set_meta_area_head (Some p)) st1).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR2 : rmrep st2 mX) end.
{ eapply (rmrep_ctx_frameW st1 st2 _ _ _ MR1 MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia.
- left. (gw_expose_fam RATP; unfold ctx_head_cells). cbn [ctx st2 st1 upd_ctx s_ctx set_meta_area_head set_avail_meta_areas set_avail_meta_area_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
rewrite HT. unfold pw. cbn [oconc]. change (conc st2 ?q) with (conc st q). change (conc st2 p) with (conc st p).
rewrite (conc_aadd st p 4096) by (rewrite Hr; eauto). unfold wz.
lazymatch goal with H : rw_cells segs ?mX (RATP + 131968) _ |- _ => exact H end.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia. }
clear MUc WMc MR1.
rewrite (carve_st_none st p HT ANone). cbv zeta. fold st1. fold st2.
change (Z_to_bv 64 (RATP + 131696)) with (Z_to_bv 64 (RATP + 131696)). change (Z_to_bv 64 (RATP + 131960)) with (Z_to_bv 64 (RATP + 131960)).
eapply evt_mono.
{ eapply (ram_carve2 sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc m _ junk lo st st2 p r);
first [gw_exact MR2 | reflexivity | gw_exact Hr | gw_exact NK | gw_exact S0 | gw_exact S1 | gw_exact SAL | gw_exact SLR | gw_exact ANone | gw_exact FRESH | gw_exact SEC | gw_exact WM0 | idtac].
- lazymatch goal with H : mem_inv segs ?mX |- _ => exact H end.
- lazymatch goal with H : rw_cells segs ?mX (conc st p) _ |- _ => exact H end.
- lazymatch goal with H : rw_cells segs ?mX (conc st p + 24) _ |- _ => exact H end.
- apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU0; [gw_exact MU0|gw_exact WM0|].
cbn [ivs_covered]. split; [|split; [|split; [|exact I]]].
+ intros x Hx. apply ram_fp_stack. lia.
+ intros x Hx. apply ram_fp_ctx. gw_expose_fam RATP. lia.
+ intros x Hx. eapply (ram_fp_region st lo _ x (fst p) r); [gw_exact Hr| gw_exact NK| lia].
- lazymatch goal with H : rw_cells segs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
- lazymatch goal with H : stk segs ?mX lo _ |- _ => exact H end.
- unfold alloc_ceiling; lia.
- lia. }
intros ms' RP. gw_exact RP.
Qed.

End RC__1.

End G.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.

Import Q2qa.Mq1 QytA Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 QJE4.Mq3 Qy5Y.Mq6 QPjm.Mq3 QJE4.Mq0 QWTl.Mq2.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QkTt.Mq4.
Import Qy8Z.Mq9.
Import QQRC.Mq9.
Import QQRC.Mq5.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope bv_scope.
Open Scope Z_scope.

Definition errno_loc_code : list Z :=
[0x00020513; 0xf5c50513; 0x00008067]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rerrno_loc_entry rvm_wait_entry : Z).
Variables (w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 : Z).
Variables (hi_7 hi_10 hi_14 : bv 20).
Variables (lo_8 lo_12 lo_15 : bv 12).
Variables (joff_30 joff_98 joff_120 joff_173 joff_175 joff_181 : bv 21).
Variables (e_197bc e_24f80 : Z).
Hypothesis CODE : code_at segs base (alloc_meta_code w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 728.
Let rmmap_entry := (rvm_wait_entry + 4)%Z.
Let rmprotect_entry := (rvm_wait_entry + 240)%Z.
Hypothesis D_7 : decode_any (Z_to_bv 32 w_7) = Some (Auipc 10 hi_7, 4%Z).
Hypothesis E_7 : is_ecall (Z_to_bv 32 w_7) = false.
Hypothesis D_8 : decode_any (Z_to_bv 32 w_8) = Some (Load SZ8 true 18 10 lo_8, 4%Z).
Hypothesis E_8 : is_ecall (Z_to_bv 32 w_8) = false.
Hypothesis D_10 : decode_any (Z_to_bv 32 w_10) = Some (Auipc 11 hi_10, 4%Z).
Hypothesis E_10 : is_ecall (Z_to_bv 32 w_10) = false.
Hypothesis D_12 : decode_any (Z_to_bv 32 w_12) = Some (OpImm ALU_ADD 19 11 lo_12, 4%Z).
Hypothesis E_12 : is_ecall (Z_to_bv 32 w_12) = false.
Hypothesis D_14 : decode_any (Z_to_bv 32 w_14) = Some (Auipc 11 hi_14, 4%Z).
Hypothesis E_14 : is_ecall (Z_to_bv 32 w_14) = false.
Hypothesis D_15 : decode_any (Z_to_bv 32 w_15) = Some (OpImm ALU_ADD 8 11 lo_15, 4%Z).
Hypothesis E_15 : is_ecall (Z_to_bv 32 w_15) = false.
Hypothesis D_30 : decode_any (Z_to_bv 32 w_30) = Some (Jal 1 joff_30, 4%Z).
Hypothesis E_30 : is_ecall (Z_to_bv 32 w_30) = false.
Hypothesis D_98 : decode_any (Z_to_bv 32 w_98) = Some (Jal 1 joff_98, 4%Z).
Hypothesis E_98 : is_ecall (Z_to_bv 32 w_98) = false.
Hypothesis D_120 : decode_any (Z_to_bv 32 w_120) = Some (Jal 1 joff_120, 4%Z).
Hypothesis E_120 : is_ecall (Z_to_bv 32 w_120) = false.
Hypothesis D_173 : decode_any (Z_to_bv 32 w_173) = Some (Jal 1 joff_173, 4%Z).
Hypothesis E_173 : is_ecall (Z_to_bv 32 w_173) = false.
Hypothesis D_175 : decode_any (Z_to_bv 32 w_175) = Some (Jal 1 joff_175, 4%Z).
Hypothesis E_175 : is_ecall (Z_to_bv 32 w_175) = false.
Hypothesis D_181 : decode_any (Z_to_bv 32 w_181) = Some (Jal 1 joff_181, 4%Z).
Hypothesis E_181 : is_ecall (Z_to_bv 32 w_181) = false.
Hypothesis ANCH_8 : gw_anch (Z.shiftl (bv_signed hi_7) 12 + (base + 28) + bv_signed lo_8)%Z RGOT_SSP.
Hypothesis ANCH_12 : gw_anch (Z.shiftl (bv_signed hi_10) 12 + (base + 40) + bv_signed lo_12)%Z (RATP + 131960).
Hypothesis ANCH_15 : gw_anch (Z.shiftl (bv_signed hi_14) 12 + (base + 56) + bv_signed lo_15)%Z (RATP + 131728).
Hypothesis LINK_30 : gw_anch (base + 120 + bv_signed joff_30)%Z (e_24f80 + 0)%Z.
Hypothesis LINK_98 : gw_anch (base + 392 + bv_signed joff_98)%Z (rmmap_entry + 0)%Z.
Hypothesis LINK_120 : gw_anch (base + 480 + bv_signed joff_120)%Z (rmmap_entry + 0)%Z.
Hypothesis LINK_173 : gw_anch (base + 692 + bv_signed joff_173)%Z (rmprotect_entry + 0)%Z.
Hypothesis LINK_175 : gw_anch (base + 700 + bv_signed joff_175)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_181 : gw_anch (base + 724 + bv_signed joff_181)%Z (e_197bc + 0)%Z.
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
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis AL_rerrno_loc_entry : gw_al rerrno_loc_entry 4.
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition ram_fp : ltac:(gw_rebind_ty (@QQRC.Mq5.ram_fp RATP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QQRC.Mq5.ram_fp RATP) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QQRC.Mq5.ram_fp RATP) (@ram_fp) gw_tbl_0).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QQRC.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq9.rarea_rep segs) (@rarea_rep) gw_tbl_1))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QQRC.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq9.rmrep_areas segs) (@rmrep_areas) gw_tbl_2))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QQRC.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_3))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QQRC.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_4))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QQRC.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq9.rgroup_rep segs) (@rgroup_rep) gw_tbl_5))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QQRC.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq9.rmrep_groups segs) (@rmrep_groups) gw_tbl_6))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QQRC.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq9.rshadow_rep segs) (@rshadow_rep) gw_tbl_7))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QQRC.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq9.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_8))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QQRC.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_9))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QQRC.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_10))))))).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@QQRC.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QQRC.Mq9.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq9.rpres_except segs) (@rpres_except) gw_tbl_11))))).
Definition ram_ret_post : ltac:(gw_rebind_ty (@QQRC.Mq5.ram_ret_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QQRC.Mq5.ram_ret_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@QQRC.Mq5.ram_ret_post segs RATP RGOT_SSP ref_reserved RC__) (@ram_ret_post) gw_tbl_12).
Definition ram_frame : ltac:(gw_rebind_ty (@QQRC.Mq5.ram_frame RC__) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QQRC.Mq5.ram_frame RC__) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@QQRC.Mq5.ram_frame RC__) (@ram_frame) gw_tbl_13).

Hypothesis rconc_meta_inj : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQRC.Mq9.gw_all) (@QQRC.Mq9.rconc_meta_inj) (base + -984)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_14))) in let T := gw_fold_pcs T base (-984)%Z [0; 356; 740; 896; 936]%Z in exact T).

Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rpres_except_trans : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_trans) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_trans)).
Definition rpres_except_mono : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_mono) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_mono)).

Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmeta_slot_bounds : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmeta_slot_bounds) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmeta_slot_bounds)).
Definition rpres_except_of_munch_cov : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rpres_except_of_munch_cov) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rpres_except_of_munch_cov)).
Definition rmrep_ctx_frameW : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_ctx_frameW) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_ctx_frameW)).

Definition ram_fp_stack : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq5.ram_fp_stack) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq5.ram_fp_stack)).
Definition ram_fp_ctx : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq5.ram_fp_ctx) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq5.ram_fp_ctx)).
Definition ram_fp_meta : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq5.ram_fp_meta) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq5.ram_fp_meta)).
Definition ram_fp_same : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq5.ram_fp_same) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq5.ram_fp_same)).
Definition ram_tail : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq5.ram_tail) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq5.ram_tail)).
Definition ram_b0 : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq5.ram_b0) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq5.ram_b0)).

Ltac rmeta_open cq MUq WMq :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(cq, cq + 40)]%Z mX) as MUq;
pose proof (wmono_refl segs mX) as WMq end.
Ltac rmeta_chunk MR MSq CH :=
pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
rewrite ?get_meta_rec_put_same in CH;
rewrite ?conc_put_meta, ?pw_put_meta in CH;
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta_word meta0
m_set_prev m_set_next m_set_mem m_set_avail m_set_freed Z.mul Z.add] in CH;
rewrite ?meta_word_meta0 in CH; unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.
Ltac rmeta_close2 MRold MSq MUq WMq CH st' MRnew E1 E2 :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRnew : rmrep st' mX)
by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
eapply rw_cells_congr; [ | | | exact CH];
[ unfold meta_cells; unfold pw; cbn [oconc m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen m_set_prev m_set_next];
unfold wz; rewrite ?E1, ?E2; cbn [oconc]; reflexivity
| reflexivity | cbn; tauto]);
clear MUq WMq CH end.
#[using="RGOT_SSP rerrno_loc_entry e_197bc rmmap_entry rmprotect_entry e_24f80 RATP RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry CODE BASE4 BASER D_7 E_7 D_8 E_8 D_10 E_10 D_12 E_12 D_14 E_14 D_15 E_15 D_30 E_30 D_98 E_98 D_120 E_120 D_173 E_173 D_175 E_175 D_181 E_181 ANCH_8 ANCH_12 ANCH_15 LINK_30 LINK_98 LINK_120 LINK_173 LINK_175 LINK_181 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rmmap_entry rmprotect_entry rconc_meta_inj"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ctx_cells_cbn :=
cbn [ctx set_head upd_ctx s_ctx set_free_meta_head set_avail_meta set_avail_meta_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
Section RC__1.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rconc_meta_inj rmmap_entry rmprotect_entry"] Lemma ram_deq : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (h nx pv : aptr),
rmrep st m -> mem_inv segs m ->
c_free_meta_head (ctx st) = Some h -> meta_slot st h ->
m_next (get_meta_rec st h) = Some nx -> m_prev (get_meta_rec st h) = Some pv ->
meta_slot st nx -> meta_slot st pv -> (nx = h <-> pv = h) ->
rw_cells segs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk segs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
evt segs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m (dequeue LFree h st) (Z_to_bv 64 (conc st h)))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0xb4)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rconc_meta_inj rmmap_entry rmprotect_entry segs base RATP. gw_expose_fam RATP.
intros until pv. intros MR MI FMH MSh HN HP MSn MSp SELF FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m h MR MSh) as (HB0 & HB1 & HB2 & _).
pose proof (rmeta_slot_bounds st m nx MR MSn) as (NB0 & NB1 & NB2 & _).
pose proof (rmeta_slot_bounds st m pv MR MSp) as (PB0 & PB1 & PB2 & _).
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite FMH in C1.
(gw_expose_fam RATP; unfold alloc_ceiling in *).
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (conc st h, conc st h + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40); ((RATP + 131968), (RATP + 132896))]%Z m) as MU.
pose proof (wmono_refl segs m) as WM.

unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
st1. st1.
assert (CF : bv_eqb (Z_to_bv 64 (conc st h)) (Z_to_bv 64 0) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
rewrite CF; clear CF.

rmeta_chunk MR MSh CH. rewrite HN, HP in CH. cbn [oconc] in CH.
st1. clear CH.

st1. if_cases K; zify_cond K.
-
assert (Enx : nx = h).
{ rewrite ?unsigned_lit in K by lia. exact (rconc_meta_inj st m h nx MR MSh MSn ltac:(first [gw_exact K | symmetry; gw_exact K])). }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [((RATP + 131984), (RATP + 131992))]%Z mX) as MUc; pose proof (wmono_refl segs mX) as WMc end.
gw_expose_fam RATP.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : rmrep (set_head LFree None st) mX) end.
{ eapply (rmrep_ctx_frameW st _ _ _ _ MR MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst. gw_expose_fam RATP. lia.
- left. (gw_expose_fam RATP; unfold ctx_head_cells). ctx_cells_cbn. unfold pw at 1. cbn [oconc]. unfold pw. unfold wz at 4.
lazymatch goal with H : rw_cells segs ?mX (RATP + 131968) _ |- _ => exact H end.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. gw_expose_fam RATP. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. gw_expose_fam RATP. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. gw_expose_fam RATP. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. gw_expose_fam RATP. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. gw_expose_fam RATP. lia. }
clear MUc WMc C1.
st1.
assert (EQ : dequeue LFree h st = upd_meta h clr_links (set_head LFree None st)).
{ rewrite dequeue_mid. unfold deq_mid. rewrite HN, <- Enx, optr_eqb_refl. reflexivity. }
rewrite EQ.
change (conc st h) with (conc (set_head LFree None st) h). change (Z_to_bv 64 (RATP + 131696)) with (Z_to_bv 64 (RATP + 131696)).
eapply evt_mono.
{ eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo (set_head LFree None st) h);
[gw_exact MR1 | | apply meta_slot_same_areas with st; [reflexivity| gw_exact MSh] | | | unfold alloc_ceiling; lia | lia].
- lazymatch goal with H : mem_inv segs ?mX |- _ => exact H end.
- lazymatch goal with H : rw_cells segs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
- lazymatch goal with H : stk segs ?mX lo _ |- _ => exact H end. }
intros ms' RP. unfold ram_ret_post in RP |- *.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
do 15 eexists. split; [reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|gw_exact WM|].
- eapply rpres_except_trans; [gw_exact MU|]. eapply rpres_except_mono; [gw_exact PE'|]. intros a Ha. apply (proj1 (ram_fp_same st _ lo _ a eq_refl)). gw_exact Ha.
- cbn [ivs_covered]. repeat split; intros x Hx.
+ apply ram_fp_stack. lia.
+ eapply ram_fp_meta; [gw_exact MR | gw_exact MSh | lia].
+ eapply ram_fp_meta; [gw_exact MR | gw_exact MSp | lia].
+ eapply ram_fp_meta; [gw_exact MR | gw_exact MSn | lia].
+ apply ram_fp_ctx. gw_expose_fam RATP. lia. }
split; [eapply wmono_trans; [gw_exact WM| gw_exact WM']|]. split; [gw_exact MI'|]. split; [gw_exact ST'|]. gw_exact MR'.
-
assert (NEn : nx <> h) by (intros ->; apply K; reflexivity).
assert (NEp : pv <> h) by (intros E; apply NEn; apply (proj2 SELF); gw_exact E).

rmeta_chunk MR MSh CH. rewrite HN, HP in CH. cbn [oconc] in CH.
st1. clear CH.

rmeta_open (conc st pv) MUp WMp.
rmeta_chunk MR MSp CH.
st1.
rmeta_close2 MR MSp MUp WMp CH (put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) MR1 HP HN.
set (st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) in MR1.
assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; gw_exact MSh).
assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; gw_exact MSn).

rmeta_chunk MR1 MSh1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; gw_exact E).
rewrite HN, HP in CH. cbn [oconc] in CH.
st1. st1. clear CH.

rmeta_open (conc st nx) MUn WMn.
rmeta_chunk MR1 MSn1 CH.
st1.
rmeta_close2 MR1 MSn1 MUn WMn CH (put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) MR2 HP HN.
set (st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) in MR2.
assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; gw_exact MSh1).

st1. st1.
rewrite bv_eqb_refl. cbn [negb]. cbv iota.

rmeta_chunk MR2 MSh2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; gw_exact E).
unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; gw_exact E).
rewrite HN, HP in CH. cbn [oconc] in CH.
st1. clear CH.

clear C1. pose proof MR2 as (_ & (C1 & _) & _). (gw_expose_fam RATP; unfold ctx_head_cells in C1).
replace (c_free_meta_head (ctx st2)) with (Some h) in C1 by (symmetry; gw_exact FMH).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [((RATP + 131984), (RATP + 131992))]%Z mX) as MUc; pose proof (wmono_refl segs mX) as WMc end.
gw_expose_fam RATP.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR3 : rmrep (set_head LFree (Some nx) st2) mX) end.
{ eapply (rmrep_ctx_frameW st2 _ _ _ _ MR2 MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst. gw_expose_fam RATP. lia.
- left. (gw_expose_fam RATP; unfold ctx_head_cells). ctx_cells_cbn. unfold pw at 1. cbn [oconc]. change (conc (set_head LFree (Some nx) st2) nx) with (conc st nx).
unfold pw. unfold wz at 4.
lazymatch goal with H : rw_cells segs ?mX (RATP + 131968) _ |- _ => exact H end.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. gw_expose_fam RATP. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. gw_expose_fam RATP. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. gw_expose_fam RATP. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. gw_expose_fam RATP. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. gw_expose_fam RATP. lia. }
clear MUc WMc C1.

st1.
assert (EQ : dequeue LFree h st = upd_meta h clr_links (set_head LFree (Some nx) st2)).
{ rewrite dequeue_mid. unfold deq_mid. rewrite HN, HP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx h NEn). cbn [negb get_head].
rewrite !upd_meta_put. fold st1. fold st2. rewrite ctx_put_meta. unfold st1. rewrite ctx_put_meta. rewrite FMH, optr_eqb_refl. reflexivity. }
rewrite EQ.
change (conc st h) with (conc (set_head LFree (Some nx) st2) h). change (Z_to_bv 64 (RATP + 131696)) with (Z_to_bv 64 (RATP + 131696)).
eapply evt_mono.
{ eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo (set_head LFree (Some nx) st2) h);
[gw_exact MR3 | | apply meta_slot_same_areas with st; [reflexivity| gw_exact MSh] | | | unfold alloc_ceiling; lia | lia].
- lazymatch goal with H : mem_inv segs ?mX |- _ => exact H end.
- lazymatch goal with H : rw_cells segs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
- lazymatch goal with H : stk segs ?mX lo _ |- _ => exact H end. }
intros ms' RP. unfold ram_ret_post in RP |- *.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
do 15 eexists. split; [reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|gw_exact WM|].
- eapply rpres_except_trans; [gw_exact MU|]. eapply rpres_except_mono; [gw_exact PE'|]. intros a Ha. apply (proj1 (ram_fp_same st _ lo _ a eq_refl)). gw_exact Ha.
- cbn [ivs_covered]. repeat split; intros x Hx.
+ apply ram_fp_stack. lia.
+ eapply ram_fp_meta; [gw_exact MR | gw_exact MSh | lia].
+ eapply ram_fp_meta; [gw_exact MR | gw_exact MSp | lia].
+ eapply ram_fp_meta; [gw_exact MR | gw_exact MSn | lia].
+ apply ram_fp_ctx. gw_expose_fam RATP. lia. }
split; [eapply wmono_trans; [gw_exact WM| gw_exact WM']|]. split; [gw_exact MI'|]. split; [gw_exact ST'|]. gw_exact MR'.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmmap_entry rmprotect_entry"] Lemma ram_take_walk : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (q : aptr),
rmrep st m -> mem_inv segs m ->
c_free_meta_head (ctx st) = None -> c_avail_meta_count (ctx st) <> 0 -> 0 <= c_avail_meta_count (ctx st) < 2^64 ->
c_avail_meta (ctx st) = Some q -> meta_slot st q ->
rw_cells segs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk segs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
evt segs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m
(am_took st q (c_avail_meta_count (ctx st) - 1)) (Z_to_bv 64 (conc st q)))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0xb4)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmmap_entry rmprotect_entry segs base RATP. gw_expose_fam RATP.
intros until q. intros MR MI FMH CNT CR AVM MSq FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m q MR MSq) as (QB0 & QB1 & QB2 & _).
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite FMH, AVM in C1.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
(gw_expose_fam RATP; unfold alloc_ceiling in *).

st1. st1.
rewrite bv_eqb_refl. cbv iota.
st1. st1.
assert (CF : bv_eqb (Z_to_bv 64 (c_avail_meta_count (ctx st))) (Z_to_bv 64 0) = false)
by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; gw_exact CNT).
rewrite CF; clear CF.
st1. st1. st1. rewrite ?(unsigned_lit (c_avail_meta_count (ctx st))) by lia.
replace (c_avail_meta_count (ctx st) + -1) with (c_avail_meta_count (ctx st) - 1) by lia.
change (Z_to_bv 64 (RATP + 131696)) with (Z_to_bv 64 (RATP + 131696)). change (Z_to_bv 64 (RATP + 131960)) with (Z_to_bv 64 (RATP + 131960)).
eapply (ram_b0 sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc m junk lo _ st q);
[gw_exact MR | gw_exact MI | gw_exact MSq | lia | gw_exact FR | gw_exact ST | unfold alloc_ceiling; lia | lia].
Qed.

#[using="rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE rmmap_entry rmprotect_entry"] Lemma ram_disp0 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate),
rmrep st m -> c_free_meta_head (ctx st) = None -> c_avail_meta_count (ctx st) = 0 ->
evt segs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x108)) fc None m (seg_rom segs))
(MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0xb4)) fc None m (seg_rom segs)).
Proof. clear - rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE rmmap_entry rmprotect_entry segs base RATP. gw_expose_fam RATP.
intros until st. intros MR FMH CNT.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite FMH, CNT in C1.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1. gw_expose_fam RATP.
st1. st1. rewrite bv_eqb_refl. cbv iota.
st1. st1. rewrite bv_eqb_refl. cbv iota.
apply evt_done. reflexivity.
Qed.

End RC__1.

End G.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.

Import QVbl.Mq3.
Import Q2qa.Mq1 QytA Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 Qy5Y.Mq6 QPjm.Mq3 QJE4.Mq0 QJE4.Mq1 QWTl.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QkTt.Mq4.
Import Qy8Z.Mq9.
Import QQRC.Mq5.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope bv_scope.
Open Scope Z_scope.

Definition errno_loc_code : list Z :=
[0x00020513; 0xf5c50513; 0x00008067]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rerrno_loc_entry rvm_wait_entry : Z).
Variables (w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 : Z).
Variables (hi_7 hi_10 hi_14 : bv 20).
Variables (lo_8 lo_12 lo_15 : bv 12).
Variables (joff_30 joff_98 joff_120 joff_173 joff_175 joff_181 : bv 21).
Variables (e_197bc e_24f80 : Z).
Hypothesis CODE : code_at segs base (alloc_meta_code w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 728.
Let rmmap_entry := (rvm_wait_entry + 4)%Z.
Let rmprotect_entry := (rvm_wait_entry + 240)%Z.
Hypothesis D_7 : decode_any (Z_to_bv 32 w_7) = Some (Auipc 10 hi_7, 4%Z).
Hypothesis E_7 : is_ecall (Z_to_bv 32 w_7) = false.
Hypothesis D_8 : decode_any (Z_to_bv 32 w_8) = Some (Load SZ8 true 18 10 lo_8, 4%Z).
Hypothesis E_8 : is_ecall (Z_to_bv 32 w_8) = false.
Hypothesis D_10 : decode_any (Z_to_bv 32 w_10) = Some (Auipc 11 hi_10, 4%Z).
Hypothesis E_10 : is_ecall (Z_to_bv 32 w_10) = false.
Hypothesis D_12 : decode_any (Z_to_bv 32 w_12) = Some (OpImm ALU_ADD 19 11 lo_12, 4%Z).
Hypothesis E_12 : is_ecall (Z_to_bv 32 w_12) = false.
Hypothesis D_14 : decode_any (Z_to_bv 32 w_14) = Some (Auipc 11 hi_14, 4%Z).
Hypothesis E_14 : is_ecall (Z_to_bv 32 w_14) = false.
Hypothesis D_15 : decode_any (Z_to_bv 32 w_15) = Some (OpImm ALU_ADD 8 11 lo_15, 4%Z).
Hypothesis E_15 : is_ecall (Z_to_bv 32 w_15) = false.
Hypothesis D_30 : decode_any (Z_to_bv 32 w_30) = Some (Jal 1 joff_30, 4%Z).
Hypothesis E_30 : is_ecall (Z_to_bv 32 w_30) = false.
Hypothesis D_98 : decode_any (Z_to_bv 32 w_98) = Some (Jal 1 joff_98, 4%Z).
Hypothesis E_98 : is_ecall (Z_to_bv 32 w_98) = false.
Hypothesis D_120 : decode_any (Z_to_bv 32 w_120) = Some (Jal 1 joff_120, 4%Z).
Hypothesis E_120 : is_ecall (Z_to_bv 32 w_120) = false.
Hypothesis D_173 : decode_any (Z_to_bv 32 w_173) = Some (Jal 1 joff_173, 4%Z).
Hypothesis E_173 : is_ecall (Z_to_bv 32 w_173) = false.
Hypothesis D_175 : decode_any (Z_to_bv 32 w_175) = Some (Jal 1 joff_175, 4%Z).
Hypothesis E_175 : is_ecall (Z_to_bv 32 w_175) = false.
Hypothesis D_181 : decode_any (Z_to_bv 32 w_181) = Some (Jal 1 joff_181, 4%Z).
Hypothesis E_181 : is_ecall (Z_to_bv 32 w_181) = false.
Hypothesis ANCH_8 : gw_anch (Z.shiftl (bv_signed hi_7) 12 + (base + 28) + bv_signed lo_8)%Z RGOT_SSP.
Hypothesis ANCH_12 : gw_anch (Z.shiftl (bv_signed hi_10) 12 + (base + 40) + bv_signed lo_12)%Z (RATP + 131960).
Hypothesis ANCH_15 : gw_anch (Z.shiftl (bv_signed hi_14) 12 + (base + 56) + bv_signed lo_15)%Z (RATP + 131728).
Hypothesis LINK_30 : gw_anch (base + 120 + bv_signed joff_30)%Z (e_24f80 + 0)%Z.
Hypothesis LINK_98 : gw_anch (base + 392 + bv_signed joff_98)%Z (rmmap_entry + 0)%Z.
Hypothesis LINK_120 : gw_anch (base + 480 + bv_signed joff_120)%Z (rmmap_entry + 0)%Z.
Hypothesis LINK_173 : gw_anch (base + 692 + bv_signed joff_173)%Z (rmprotect_entry + 0)%Z.
Hypothesis LINK_175 : gw_anch (base + 700 + bv_signed joff_175)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_181 : gw_anch (base + 724 + bv_signed joff_181)%Z (e_197bc + 0)%Z.
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
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis AL_rerrno_loc_entry : gw_al rerrno_loc_entry 4.
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition memcpy_post : ltac:(gw_rebind_ty (@QVbl.Mq3.memcpy_post segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QVbl.Mq3.memcpy_post segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QVbl.Mq3.memcpy_post segs) (@memcpy_post) gw_tbl_0).
Definition rauxv_ok : ltac:(gw_rebind_ty (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QCa8.Mq5.rauxv_ok segs RATP RC__) (@rauxv_ok) gw_tbl_1).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QQRC.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq9.rarea_rep segs) (@rarea_rep) gw_tbl_2)))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QQRC.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq9.rmrep_areas segs) (@rmrep_areas) gw_tbl_3)))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QQRC.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_4)))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QQRC.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_5)))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QQRC.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq9.rgroup_rep segs) (@rgroup_rep) gw_tbl_6)))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QQRC.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq9.rmrep_groups segs) (@rmrep_groups) gw_tbl_7)))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QQRC.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq9.rshadow_rep segs) (@rshadow_rep) gw_tbl_8)))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QQRC.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq9.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_9)))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QQRC.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_10)))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@QQRC.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_11)))))).
Definition ram_frame : ltac:(gw_rebind_ty (@QQRC.Mq5.ram_frame RC__) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QQRC.Mq5.ram_frame RC__) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@QQRC.Mq5.ram_frame RC__) (@ram_frame) gw_tbl_12).

Hypothesis memcpy_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq3.memcpy_spec segs e_24f80) 3%nat in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_13))) in exact T).

Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).
Definition rmrep_transport_high : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_transport_high) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_transport_high)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmrep_ctx_frameW : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_ctx_frameW) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_ctx_frameW)).

#[using="RGOT_SSP rerrno_loc_entry e_197bc rmmap_entry rmprotect_entry e_24f80 RATP RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry CODE BASE4 BASER D_7 E_7 D_8 E_8 D_10 E_10 D_12 E_12 D_14 E_14 D_15 E_15 D_30 E_30 D_98 E_98 D_120 E_120 D_173 E_173 D_175 E_175 D_181 E_181 ANCH_8 ANCH_12 ANCH_15 LINK_30 LINK_98 LINK_120 LINK_173 LINK_175 LINK_181 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rmmap_entry rmprotect_entry memcpy_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

#[using="rvm_wait_entry memcpy_spec rmmap_entry rmprotect_entry"] Lemma rmemcpy_callZ3 : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (D S n : Z) (src junk : list byte),
bytes_at segs m S src -> length src = Z.to_nat n ->
rw_cells segs m D [CB (Z.to_nat n) junk] ->
0 <= D -> D + n <= 2^64 -> 0 <= S -> S + n <= 2^64 -> 0 < n ->
(S + n <= D \/ D + n <= S) ->
mem_inv segs m ->
evt segs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(D, D + n)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rw_cells segs m' D [CB (Z.to_nat n) src])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_24f80 + 0x0)) fc None m (seg_rom segs)).
Proof. clear - rvm_wait_entry memcpy_spec rmmap_entry rmprotect_entry segs e_24f80.
intros until junk. intros SRC LEN DST D0 D1 S0 S1 N0 SEP MI.
assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
assert (EN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
eapply evt_mono.
{ eapply (memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n)); rewrite ?ED, ?ES, ?EN;
[gw_exact SRC | gw_exact LEN | gw_exact DST | gw_exact SEP | gw_exact MI]. }
intros ms' P. unfold memcpy_post in P. rewrite !ED, !EN in P.
destruct P as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m' & -> & MU & WM & MI' & DST' & _).
do 15 eexists. split; [reflexivity|]. auto.
Qed.

#[using="rvm_wait_entry rmmap_entry rmprotect_entry"] Lemma ru64s_read : forall m A ws (i : Z) w a,
bytes_at segs m A (u64s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 8 * i) ->
ov_read_bytes segs m a 8 = Some (le8 w).
Proof. clear - rvm_wait_entry rmmap_entry rmprotect_entry segs.
intros m A ws i w a Hb Hn Hi ->.
destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
rewrite (bytes_at_ov_read segs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

#[using="rvm_wait_entry rmmap_entry rmprotect_entry"] Lemma rrw_cells_app_split : forall m A cs1 cs2,
rw_cells segs m A (cs1 ++ cs2) -> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof. clear - rvm_wait_entry rmmap_entry rmprotect_entry segs.
intros m A cs1 cs2 H. split; [eapply rw_cells_prefix; gw_exact H|].
destruct H as [[WF B] W].
apply cells_wf_app in WF. destruct WF as [WF1 WF2].
rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [_ B2]. rewrite cells_bytes_length in B2 by gw_exact WF1.
split; [split; [gw_exact WF2 | gw_exact B2] |].
rewrite cells_size_app in W. eapply wr_at_sub; [gw_exact W | lia | lia].
Qed.

#[using="rvm_wait_entry rmmap_entry rmprotect_entry"] Lemma rrw_cells_app_join : forall m A cs1 cs2,
rw_cells segs m A cs1 -> rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells segs m A (cs1 ++ cs2).
Proof. clear - rvm_wait_entry rmmap_entry rmprotect_entry segs.
intros m A cs1 cs2 [[WF1 B1] W1] [[WF2 B2] W2]. split; [split|].
- apply cells_wf_app. split; assumption.
- rewrite cells_bytes_app. apply bytes_at_app. split; [gw_exact B1|]. rewrite cells_bytes_length by gw_exact WF1. gw_exact B2.
- rewrite cells_size_app. destruct W1 as (H0 & H1 & X1). destruct W2 as (H2 & H3 & X2). split; [lia|]. split; [lia|].
intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))).
+ apply X1. lia.
+ replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply X2. lia.
Qed.

Definition ram_entry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists x1 t0 t1 t2 s1x s4x a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' junk,
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xb4)) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp); ((RATP + 131968), (RATP + 131984))]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rw_cells segs m' (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)
/\ stk segs m' lo (bv_unsigned sp + -64)
/\ rmrep (am_init_st st) m'.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 hi_7 hi_10 hi_14 lo_8 lo_12 lo_15 joff_30 e_24f80 CODE BASE4 BASER D_7 E_7 D_8 E_8 D_10 E_10 D_12 E_12 D_14 E_14 D_15 E_15 D_30 E_30 ANCH_8 ANCH_12 ANCH_15 LINK_30 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved memcpy_spec rmmap_entry rmprotect_entry"] Lemma ram_entry : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (lo : Z) (st : mstate),
rmrep st m -> mem_inv segs m -> rauxv_ok m (bv_unsigned sp) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
(c_init_done (ctx st) = 0 \/ c_init_done (ctx st) = 1) -> s_secret st = rc_secret -> 0 <= c_secret (ctx st) < 2^64 ->
evt segs (ram_entry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 hi_7 hi_10 hi_14 lo_8 lo_12 lo_15 joff_30 e_24f80 CODE BASE4 BASER D_7 E_7 D_8 E_8 D_10 E_10 D_12 E_12 D_14 E_14 D_15 E_15 D_30 E_30 ANCH_8 ANCH_12 ANCH_15 LINK_30 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved memcpy_spec rmmap_entry rmprotect_entry segs base RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros until st. intros MR MI AUX ST LO LOLE INIT SEC0 SECR.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR as (WF & (C1 & _) & (_ & _ & PGS & G4 & G5) & _). unfold ctx_head_cells in C1.
(gw_expose_fam RATP; gw_expose_fam RGOT_SSP; unfold alloc_ceiling in *). unfold wz in G4.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); ((RATP + 131968), (RATP + 131984))]%Z m) as MU.
pose proof (wmono_refl segs m) as WM. gw_expose_fam RATP.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MUh.
destruct AUX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & AVC & AVL & RND & AB & BAV & AVH & BR & RH & X3 & X4 & X5 & X16 & X6 & X11 & X12 & X23 & XR & AV8).
gw_expose_fam RATP.

st1. carve_frame 64%nat ST. st1. st1. st1. st1. st1. st1.

st1. st1. st1. st1. st1. st1.

st1. rewrite sx32_wz by lia. st1. st1.

st1.
lazymatch goal with H : rw_cells segs _ (bv_unsigned sp + -64) (CB 8 ?j :: _) |- _ => set (junk8 := j) in H; clearbody junk8 end.
destruct INIT as [I0|I1].
2:{
rewrite I1. change (negb (bv_eqb (wz 1) (Z_to_bv 64 0))) with true. cbv iota.
st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.
apply evt_done. (gw_expose_fam RATP; unfold ram_entry_post). do 20 eexists. split; [reflexivity|].
split; [gw_exact MU|]. split; [gw_exact WM|]. split; [assumption|]. split; [gw_exact FR|]. split; [gw_exact ST|].
unfold am_init_st. rewrite I1. cbn [Z.eqb Pos.eqb].
eapply rmrep_transport_high; [gw_exact MR| gw_exact MUh| gw_exact WM|]. intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia. }

rewrite I0. change (negb (bv_eqb (wz 0) (Z_to_bv 64 0))) with false. cbv iota.

st1. st1. st1. st1. st1. st1. st1. st1. st1.

Ltac skip_iter i key HB :=
let RD := fresh "RD" in
st1;
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (ru64s_read mX _ _ i (wz key) (wa (_ + 8 * i)) HB eq_refl ltac:(lia) eq_refl) as RD end;
st1; try clear RD;
st1; change (bv_eqb (wz key) (Z_to_bv 64 25)) with false; cbv iota;
st1; change (negb (bv_eqb (wz key) (Z_to_bv 64 0))) with true; cbv iota;
st1.
skip_iter 0 3 AVL.
skip_iter 2 4 AVL. skip_iter 4 5 AVL. skip_iter 6 16 AVL. skip_iter 8 6 AVL.
skip_iter 10 11 AVL. skip_iter 12 12 AVL. skip_iter 14 23 AVL.

st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (ru64s_read mX _ _ 16 (wz 25) (wa (_ + 8 * 16)) AVL eq_refl ltac:(lia) eq_refl) as RD end.
st1. try clear RD.
st1. change (bv_eqb (wz 25) (Z_to_bv 64 25)) with true. cbv iota.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (ru64s_read mX _ _ 17 (wz rnd) (wa (_ + 8 * 17)) AVL eq_refl ltac:(lia) eq_refl) as RD end.
st1. try clear RD. st1. st1. st1.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?rest) =>
destruct (rrw_cells_app_split mX _ [c1] rest FR) as [FRm FRc];
cbn [cells_size csize Nat.add] in FRc;
replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) in FRc by lia;
apply (rw_cells_merge segs mX _ [] [c1] []) in FRm; cbn [cells_size csize Nat.add cells_bytes cbytes app] in FRm;
rewrite app_nil_r in FRm; clear FR
end end.

st1.
call rmemcpy_callZ3.
1:{ gw_exact RND. } 1:{ reflexivity. } 1:{ gw_exact FRm. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
1:{ lazymatch goal with H : mem_inv segs ?mX |- mem_inv segs ?mX => exact H end. }
lazymatch goal with H : rw_cells segs ?mX (bv_unsigned sp + -64) [CB _ (le8 (wz rc_secret))] |- _ => rename H into DST end.

st1. st1.

st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (ru64s_read mX _ _ 18 (wz 0) (wa (_ + 8 * 18)) AVL eq_refl ltac:(lia) eq_refl) as RD end.
st1. try clear RD.
st1. change (bv_eqb (wz 0) (Z_to_bv 64 25)) with false. cbv iota.
st1. change (negb (bv_eqb (wz 0) (Z_to_bv 64 0))) with false. cbv iota.

lazymatch type of DST with rw_cells _ ?mX _ _ =>
assert (DST8 : rw_cells segs mX (bv_unsigned sp + -64) [C8 (wz rc_secret)])
by (destruct DST as [[_ B] W]; cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B;
split; [split; [cbn; tauto| cbn [cells_bytes cbytes app]; rewrite app_nil_r; gw_exact B]| gw_exact W]);
clear DST end.
st1.

st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRX : rmrep st mX) by (eapply rmrep_transport_high; [gw_exact MR| gw_exact MUh| gw_exact WM|]; intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia);
pose proof (munch_refl [((RATP + 131968), (RATP + 131984))]%Z mX) as MUc; pose proof (wmono_refl segs mX) as WMc end.
clear MUh. gw_expose_fam RATP.

st1. st1.
set (stI := upd_ctx (fun c => set_init_done 1 (set_secret rc_secret c)) st).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRI : rmrep stI mX) end.
{ eapply (rmrep_ctx_frameW st stI _ _ _ MRX MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia.
- left. (gw_expose_fam RATP; unfold ctx_head_cells). cbn [ctx stI upd_ctx s_ctx set_init_done set_secret c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
change (pw stI ?q) with (pw st q). unfold wz at 2.
lazymatch goal with H : rw_cells segs ?mX (RATP + 131968) _ |- _ => exact H end.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia. }
clear MUc WMc MRX.

st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
lazymatch goal with Hm : rw_cells segs mX (bv_unsigned sp + -64) ?csm, Hc : rw_cells segs mX (bv_unsigned sp + -56) ?csc |- _ =>
pose proof (rrw_cells_app_join mX _ csm csc Hm ltac:(cbn [cells_size csize Nat.add]; replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) by lia; gw_exact Hc)) as J2;
cbn [app] in J2; clear Hm Hc;
lazymatch type of J2 with rw_cells _ _ _ (?c1 :: ?rest) =>
apply (rw_cells_merge segs mX _ [] [c1] rest) in J2; cbn [cells_size csize Nat.add cells_bytes cbytes app] in J2; rewrite app_nil_r in J2 end
end end.
apply evt_done. (gw_expose_fam RATP; unfold ram_entry_post). do 20 eexists. split; [reflexivity|].
split; [gw_exact MU|]. split; [gw_exact WM|]. split; [assumption|]. split; [gw_exact J2|]. split; [gw_exact ST|].
unfold am_init_st. rewrite I0, SEC0. cbn [Z.eqb]. gw_exact MRI.
Qed.

End RC__1.

End G.
End Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq QGeV QLsg QXxF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QDUx.Mq8 Q9Ay.Mqa QXxF.Mq3 QDUx.Mq9.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QCa8.Mq4.
Import QDXD.Mq2.
Import QkTt.Mq3.
Import QDXD.Mq1.
Import QkTt.Mq5.
Import Qy8Z.Mq7.
Import Qy8Z.Mq1.
Import Qy8Z.Mq8.
Import QQRC.Mq8.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope Z_scope.

Definition errno_loc_code : list Z :=
[0x00020513; 0xf5c50513; 0x00008067]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rerrno_loc_entry rvm_wait_entry rlock_entry runlock_entry : Z).
Variables (w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 : Z).
Variables (hi_26 hi_40 hi_43 hi_57 hi_85 hi_125 hi_128 hi_147 hi_216 : bv 20).
Variables (lo_27 lo_41 lo_44 lo_59 lo_90 lo_126 lo_129 lo_148 lo_217 : bv 12).
Variables (joff_11 joff_37 joff_45 joff_130 joff_149 joff_152 joff_203 joff_218 : bv 21).
Hypothesis CODE : code_at segs base (malloc_code w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 880.
Let ralloc_slot_entry := (base + 880)%Z.
Let rmmap_entry := (rvm_wait_entry + 4)%Z.
Let rmunmap_entry := (rvm_wait_entry + 524)%Z.
Hypothesis D_11 : decode_any (Z_to_bv 32 w_11) = Some (Jal 1 joff_11, 4%Z).
Hypothesis E_11 : is_ecall (Z_to_bv 32 w_11) = false.
Hypothesis D_26 : decode_any (Z_to_bv 32 w_26) = Some (Auipc 11 hi_26, 4%Z).
Hypothesis E_26 : is_ecall (Z_to_bv 32 w_26) = false.
Hypothesis D_27 : decode_any (Z_to_bv 32 w_27) = Some (OpImm ALU_ADD 9 11 lo_27, 4%Z).
Hypothesis E_27 : is_ecall (Z_to_bv 32 w_27) = false.
Hypothesis D_37 : decode_any (Z_to_bv 32 w_37) = Some (Jal 1 joff_37, 4%Z).
Hypothesis E_37 : is_ecall (Z_to_bv 32 w_37) = false.
Hypothesis D_40 : decode_any (Z_to_bv 32 w_40) = Some (Auipc 10 hi_40, 4%Z).
Hypothesis E_40 : is_ecall (Z_to_bv 32 w_40) = false.
Hypothesis D_41 : decode_any (Z_to_bv 32 w_41) = Some (Load SZ1 false 10 10 lo_41, 4%Z).
Hypothesis E_41 : is_ecall (Z_to_bv 32 w_41) = false.
Hypothesis D_43 : decode_any (Z_to_bv 32 w_43) = Some (Auipc 10 hi_43, 4%Z).
Hypothesis E_43 : is_ecall (Z_to_bv 32 w_43) = false.
Hypothesis D_44 : decode_any (Z_to_bv 32 w_44) = Some (OpImm ALU_ADD 10 10 lo_44, 4%Z).
Hypothesis E_44 : is_ecall (Z_to_bv 32 w_44) = false.
Hypothesis D_45 : decode_any (Z_to_bv 32 w_45) = Some (Jal 1 joff_45, 4%Z).
Hypothesis E_45 : is_ecall (Z_to_bv 32 w_45) = false.
Hypothesis D_57 : decode_any (Z_to_bv 32 w_57) = Some (Auipc 12 hi_57, 4%Z).
Hypothesis E_57 : is_ecall (Z_to_bv 32 w_57) = false.
Hypothesis D_59 : decode_any (Z_to_bv 32 w_59) = Some (OpImm ALU_ADD 19 12 lo_59, 4%Z).
Hypothesis E_59 : is_ecall (Z_to_bv 32 w_59) = false.
Hypothesis D_85 : decode_any (Z_to_bv 32 w_85) = Some (Auipc 12 hi_85, 4%Z).
Hypothesis E_85 : is_ecall (Z_to_bv 32 w_85) = false.
Hypothesis D_90 : decode_any (Z_to_bv 32 w_90) = Some (OpImm ALU_ADD 11 12 lo_90, 4%Z).
Hypothesis E_90 : is_ecall (Z_to_bv 32 w_90) = false.
Hypothesis D_125 : decode_any (Z_to_bv 32 w_125) = Some (Auipc 10 hi_125, 4%Z).
Hypothesis E_125 : is_ecall (Z_to_bv 32 w_125) = false.
Hypothesis D_126 : decode_any (Z_to_bv 32 w_126) = Some (Load SZ1 false 10 10 lo_126, 4%Z).
Hypothesis E_126 : is_ecall (Z_to_bv 32 w_126) = false.
Hypothesis D_128 : decode_any (Z_to_bv 32 w_128) = Some (Auipc 10 hi_128, 4%Z).
Hypothesis E_128 : is_ecall (Z_to_bv 32 w_128) = false.
Hypothesis D_129 : decode_any (Z_to_bv 32 w_129) = Some (OpImm ALU_ADD 10 10 lo_129, 4%Z).
Hypothesis E_129 : is_ecall (Z_to_bv 32 w_129) = false.
Hypothesis D_130 : decode_any (Z_to_bv 32 w_130) = Some (Jal 1 joff_130, 4%Z).
Hypothesis E_130 : is_ecall (Z_to_bv 32 w_130) = false.
Hypothesis D_147 : decode_any (Z_to_bv 32 w_147) = Some (Auipc 10 hi_147, 4%Z).
Hypothesis E_147 : is_ecall (Z_to_bv 32 w_147) = false.
Hypothesis D_148 : decode_any (Z_to_bv 32 w_148) = Some (OpImm ALU_ADD 10 10 lo_148, 4%Z).
Hypothesis E_148 : is_ecall (Z_to_bv 32 w_148) = false.
Hypothesis D_149 : decode_any (Z_to_bv 32 w_149) = Some (Jal 1 joff_149, 4%Z).
Hypothesis E_149 : is_ecall (Z_to_bv 32 w_149) = false.
Hypothesis D_152 : decode_any (Z_to_bv 32 w_152) = Some (Jal 1 joff_152, 4%Z).
Hypothesis E_152 : is_ecall (Z_to_bv 32 w_152) = false.
Hypothesis D_203 : decode_any (Z_to_bv 32 w_203) = Some (Jal 1 joff_203, 4%Z).
Hypothesis E_203 : is_ecall (Z_to_bv 32 w_203) = false.
Hypothesis D_216 : decode_any (Z_to_bv 32 w_216) = Some (Auipc 10 hi_216, 4%Z).
Hypothesis E_216 : is_ecall (Z_to_bv 32 w_216) = false.
Hypothesis D_217 : decode_any (Z_to_bv 32 w_217) = Some (OpImm ALU_ADD 10 10 lo_217, 4%Z).
Hypothesis E_217 : is_ecall (Z_to_bv 32 w_217) = false.
Hypothesis D_218 : decode_any (Z_to_bv 32 w_218) = Some (Jal 1 joff_218, 4%Z).
Hypothesis E_218 : is_ecall (Z_to_bv 32 w_218) = false.
Hypothesis ANCH_27 : gw_anch (Z.shiftl (bv_signed hi_26) 12 + (base + 104) + bv_signed lo_27)%Z (RATP + 131960).
Hypothesis ANCH_41 : gw_anch (Z.shiftl (bv_signed hi_40) 12 + (base + 160) + bv_signed lo_41)%Z (RATP + 131731).
Hypothesis ANCH_44 : gw_anch (Z.shiftl (bv_signed hi_43) 12 + (base + 172) + bv_signed lo_44)%Z (RATP + 131960).
Hypothesis ANCH_59 : gw_anch (Z.shiftl (bv_signed hi_57) 12 + (base + 228) + bv_signed lo_59)%Z RDEBRUIJN.
Hypothesis ANCH_90 : gw_anch (Z.shiftl (bv_signed hi_85) 12 + (base + 340) + bv_signed lo_90)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_126 : gw_anch (Z.shiftl (bv_signed hi_125) 12 + (base + 500) + bv_signed lo_126)%Z (RATP + 131731).
Hypothesis ANCH_129 : gw_anch (Z.shiftl (bv_signed hi_128) 12 + (base + 512) + bv_signed lo_129)%Z (RATP + 131960).
Hypothesis ANCH_148 : gw_anch (Z.shiftl (bv_signed hi_147) 12 + (base + 588) + bv_signed lo_148)%Z (RATP + 131960).
Hypothesis ANCH_217 : gw_anch (Z.shiftl (bv_signed hi_216) 12 + (base + 864) + bv_signed lo_217)%Z (RATP + 131960).
Hypothesis LINK_11 : gw_anch (base + 44 + bv_signed joff_11)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_37 : gw_anch (base + 148 + bv_signed joff_37)%Z (rmmap_entry + 0)%Z.
Hypothesis LINK_45 : gw_anch (base + 180 + bv_signed joff_45)%Z (rlock_entry + 0)%Z.
Hypothesis LINK_130 : gw_anch (base + 520 + bv_signed joff_130)%Z (rlock_entry + 0)%Z.
Hypothesis LINK_149 : gw_anch (base + 596 + bv_signed joff_149)%Z (runlock_entry + 0)%Z.
Hypothesis LINK_152 : gw_anch (base + 608 + bv_signed joff_152)%Z (rmunmap_entry + 0)%Z.
Hypothesis LINK_203 : gw_anch (base + 812 + bv_signed joff_203)%Z (runlock_entry + 0)%Z.
Hypothesis LINK_218 : gw_anch (base + 872 + bv_signed joff_218)%Z (runlock_entry + 0)%Z.
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
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis AL_rerrno_loc_entry : gw_al rerrno_loc_entry 4.
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis AL_rlock_entry : gw_al rlock_entry 4.
Hypothesis AL_runlock_entry : gw_al runlock_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition runlock_post : ltac:(gw_rebind_ty (@QCa8.Mq4.runlock_post segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QCa8.Mq4.runlock_post segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@Qy8Z.Mq7.runlock_post segs) (@runlock_post) (gw_ent (@QCa8.Mq4.runlock_post segs) (@runlock_post) gw_tbl_0)).
Definition rauxv_ok : ltac:(gw_rebind_ty (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QQRC.Mq8.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@Qy8Z.Mq1.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QDXD.Mq1.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QCa8.Mq5.rauxv_ok segs RATP RC__) (@rauxv_ok) gw_tbl_1)))).
Definition ralloc_fp : ltac:(gw_rebind_ty (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QQRC.Mq8.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@Qy8Z.Mq1.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QkTt.Mq5.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QCa8.Mq5.ralloc_fp RATP) (@ralloc_fp) gw_tbl_2)))).
Definition rmalloc_fp : ltac:(gw_rebind_ty (@QkTt.Mq5.rmalloc_fp RATP RC__) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@QkTt.Mq5.rmalloc_fp RATP RC__) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QQRC.Mq8.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@Qy8Z.Mq1.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QkTt.Mq5.rmalloc_fp RATP RC__) (@rmalloc_fp) gw_tbl_3))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QQRC.Mq8.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq7.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_4)))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QQRC.Mq8.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq7.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_5)))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QQRC.Mq8.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq7.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_6)))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QQRC.Mq8.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq7.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_7)))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QQRC.Mq8.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq7.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_8)))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QQRC.Mq8.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq7.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_9)))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QQRC.Mq8.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq7.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_10)))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@QQRC.Mq8.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq7.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_11)))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@QQRC.Mq8.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq7.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_12)))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@QQRC.Mq8.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq7.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_13)))))))))).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_14)).
Notation gw_tbl_15 := (gw_ent (@QQRC.Mq8.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq7.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq3.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) gw_tbl_14)))))))).
Definition ras_post : ltac:(gw_rebind_ty (@Qy8Z.Mq1.ras_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@Qy8Z.Mq1.ras_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_15)).
Notation gw_tbl_16 := (gw_ent (@Qy8Z.Mq1.ras_post segs RATP RGOT_SSP ref_reserved RC__) (@ras_post) gw_tbl_15).
Definition rimplT : ltac:(gw_rebind_ty (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_16)).
#[global] Arguments rimplT {R}%_type_scope o t s Q%_function_scope ms.
Notation gw_tbl_17 := (gw_ent (@QQRC.Mq8.rimplT segs RC__) (@rimplT) (gw_ent (@Qy8Z.Mq1.rimplT segs RC__) (@rimplT) (gw_ent (@Qy8Z.Mq7.rimplT segs RC__) (@rimplT) (gw_ent (@QkTt.Mq3.rimplT segs RC__) (@rimplT) (gw_ent (@QCa8.Mq5.rimplT segs RC__) (@rimplT) gw_tbl_16))))).
Definition ralloc_slot_stmt : ltac:(gw_rebind_ty (@Qy8Z.Mq1.ralloc_slot_stmt segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@Qy8Z.Mq1.ralloc_slot_stmt segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) constr:(gw_tbl_17)).
Notation gw_tbl_18 := (gw_ent (@Qy8Z.Mq1.ralloc_slot_stmt segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) (@ralloc_slot_stmt) gw_tbl_17).
Definition renf_hyp : ltac:(gw_rebind_ty (@QQRC.Mq8.renf_hyp segs base RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QQRC.Mq8.renf_hyp segs base RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_18)).
#[global] Arguments renf_hyp {R}%_type_scope K%_function_scope o m0 st s Q%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope s0v%_bv_scope s1v%_bv_scope s2v%_bv_scope s3v%_bv_scope s4v%_bv_scope F fc%_bv_scope n%_Z_scope lo%_Z_scope.
Notation gw_tbl_19 := (gw_ent (@QQRC.Mq8.renf_hyp segs base RATP RGOT_SSP ref_reserved RC__) (@renf_hyp) gw_tbl_18).
Definition rfail_hyp : ltac:(gw_rebind_ty (@QQRC.Mq8.rfail_hyp segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QQRC.Mq8.rfail_hyp segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_19)).
#[global] Arguments rfail_hyp {R}%_type_scope K%_function_scope o m0 st s Q%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope s0v%_bv_scope s1v%_bv_scope s2v%_bv_scope s3v%_bv_scope s4v%_bv_scope F fc%_bv_scope lo%_Z_scope.
Notation gw_tbl_20 := (gw_ent (@QQRC.Mq8.rfail_hyp segs RATP RGOT_SSP ref_reserved RC__) (@rfail_hyp) gw_tbl_19).

Hypothesis runlock_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QCa8.Mq4.gw_all) (@QCa8.Mq4.runlock_spec) (base + -1984)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_20))) in let T := gw_fold_pcs T base (-1984)%Z [0; 244]%Z in exact T).

Definition rmrep_meta_set_avail : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_set_avail) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_set_avail)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rauxv_ok_weaken : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rauxv_ok_weaken) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rauxv_ok_weaken)).
Definition rauxv_ok_frame : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rauxv_ok_frame) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rauxv_ok_frame)).
Definition rpres_except_trans : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_trans) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_trans)).
Definition rpres_except_mono : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_mono) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_mono)).
Ltac riprefixT := apply rimplT_from_evt.

Definition rpres_except_munch_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq1.rpres_except_munch_frame) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq1.rpres_except_munch_frame)).

Definition rmeta_chunk_facts : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rmeta_chunk_facts) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rmeta_chunk_facts)).
Definition rregion_facts : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rregion_facts) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rregion_facts)).
Definition rmalloc_fp_mono : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rmalloc_fp_mono) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rmalloc_fp_mono)).
Definition rfast_slot_ok : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rfast_slot_ok) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rfast_slot_ok)).
Notation RMFACTS := (@MFACTS_g ref_reserved).

Definition rdbi_range : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mq8.rdbi_range) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mq8.rdbi_range)).
Definition rdebruijn_read : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mq8.rdebruijn_read) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mq8.rdebruijn_read)).

Definition rframe_after_call : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq8.rframe_after_call) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq8.rframe_after_call)).
Definition rmalloc_fp_sp_mono : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq8.rmalloc_fp_sp_mono) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq8.rmalloc_fp_sp_mono)).
Definition rmalloc_fp_st_mono : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq8.rmalloc_fp_st_mono) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq8.rmalloc_fp_st_mono)).
Definition rauxv_ok_malloc_fp : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq8.rauxv_ok_malloc_fp) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq8.rauxv_ok_malloc_fp)).

#[using="RDEBRUIJN rerrno_loc_entry rmmap_entry rmunmap_entry rlock_entry runlock_entry RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry CODE BASE4 BASER D_11 E_11 D_26 E_26 D_27 E_27 D_37 E_37 D_40 E_40 D_41 E_41 D_43 E_43 D_44 E_44 D_45 E_45 D_57 E_57 D_59 E_59 D_85 E_85 D_90 E_90 D_125 E_125 D_126 E_126 D_128 E_128 D_129 E_129 D_130 E_130 D_147 E_147 D_148 E_148 D_149 E_149 D_152 E_152 D_203 E_203 D_216 E_216 D_217 E_217 D_218 E_218 ANCH_27 ANCH_41 ANCH_44 ANCH_59 ANCH_90 ANCH_126 ANCH_129 ANCH_148 ANCH_217 LINK_11 LINK_37 LINK_45 LINK_130 LINK_149 LINK_152 LINK_203 LINK_218 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry AL_rlock_entry AL_runlock_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ ralloc_slot_entry rmmap_entry rmunmap_entry runlock_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := first [clear - hs segs base w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 hi_26 hi_40 hi_43 hi_57 hi_85 hi_125 hi_128 hi_147 hi_216 lo_27 lo_41 lo_44 lo_59 lo_90 lo_126 lo_129 lo_148 lo_217 joff_11 joff_37 joff_45 joff_130 joff_149 joff_152 joff_203 joff_218 RDEBRUIJN rerrno_loc_entry rmmap_entry rmunmap_entry rlock_entry runlock_entry RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry CODE BASE4 BASER D_11 E_11 D_26 E_26 D_27 E_27 D_37 E_37 D_40 E_40 D_41 E_41 D_43 E_43 D_44 E_44 D_45 E_45 D_57 E_57 D_59 E_59 D_85 E_85 D_90 E_90 D_125 E_125 D_126 E_126 D_128 E_128 D_129 E_129 D_130 E_130 D_147 E_147 D_148 E_148 D_149 E_149 D_152 E_152 D_203 E_203 D_216 E_216 D_217 E_217 D_218 E_218 ANCH_27 ANCH_41 ANCH_44 ANCH_59 ANCH_90 ANCH_126 ANCH_129 ANCH_148 ANCH_217 LINK_11 LINK_37 LINK_45 LINK_130 LINK_149 LINK_152 LINK_203 LINK_218 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry AL_rlock_entry AL_runlock_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ ralloc_slot_entry runlock_spec | clear - hs segs base w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 hi_26 hi_40 hi_43 hi_57 hi_85 hi_125 hi_128 hi_147 hi_216 lo_27 lo_41 lo_44 lo_59 lo_90 lo_126 lo_129 lo_148 lo_217 joff_11 joff_37 joff_45 joff_130 joff_149 joff_152 joff_203 joff_218 RDEBRUIJN rerrno_loc_entry rmmap_entry rmunmap_entry rlock_entry runlock_entry RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry CODE BASE4 BASER D_11 E_11 D_26 E_26 D_27 E_27 D_37 E_37 D_40 E_40 D_41 E_41 D_43 E_43 D_44 E_44 D_45 E_45 D_57 E_57 D_59 E_59 D_85 E_85 D_90 E_90 D_125 E_125 D_126 E_126 D_128 E_128 D_129 E_129 D_130 E_130 D_147 E_147 D_148 E_148 D_149 E_149 D_152 E_152 D_203 E_203 D_216 E_216 D_217 E_217 D_218 E_218 ANCH_27 ANCH_41 ANCH_44 ANCH_59 ANCH_90 ANCH_126 ANCH_129 ANCH_148 ANCH_217 LINK_11 LINK_37 LINK_45 LINK_130 LINK_149 LINK_152 LINK_203 LINK_218 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry AL_rlock_entry AL_runlock_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay ralloc_slot_entry runlock_spec].

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Section RC__1.

Definition rcoarse_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' : word) (F : bvmap 5 word) (fc : bv 32)
(m : mem) (st : mstate) (n sc' : Z) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3,
ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 (RATP + 131960)) a0 a1 a2 a3 a4 a5 a6 a7
(pw st (active st sc')) (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 sc') s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x2c8)) fc None m (seg_rom segs)
/\ a0 = wz (sxv (match active st sc' with Some g => m_avail (get_meta_rec st g) | None => 0 end)).

Section COARSE.
Variables (st : mstate) (LB : list block) (m1 : mem) (t : N).
Let st1 := set_tick t st.
Hypothesis MF : RMFACTS st LB.
Hypothesis MR : rmrep st1 m1.
Hypothesis MI : mem_inv segs m1.

#[using="segs base RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 ROM_reservedZ LAY_ref_reserved ralloc_slot_entry rmmap_entry rmunmap_entry LB m1 MF MR"] Lemma ractive_ptr_facts sc g : active st sc = Some g -> 0 < conc st1 g /\ conc st1 g + 40 <= alloc_ceiling /\ meta_slot st1 g
/\ (exists b, m_mem (get_meta_rec st g) = Some b)
/\ 0 <= m_avail (get_meta_rec st g) < 2^32 /\ 0 <= m_freed (get_meta_rec st g) < 2^32
/\ 0 <= m_last_idx (get_meta_rec st g) + 32 * m_freeable (get_meta_rec st g) + 64 * m_sizeclass (get_meta_rec st g) + 4096 * m_maplen (get_meta_rec st g) < 2^64.
Proof. clear - segs base RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 ROM_reservedZ LAY_ref_reserved ralloc_slot_entry rmmap_entry rmunmap_entry LB m1 MF MR sc g st t st1 MI. first [clear MI | gw_hide MI | idtac]; try gw_hide st1; first [clear t | gw_hide t | idtac]; try gw_hide st.
intros ACT.
pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
destruct (FA sc g ACT) as (SC48 & GSC & NN).
destruct (m_mem (get_meta_rec st g)) as [b|] eqn:Hm; [|congruence].
pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
specialize (FG g b Hm). cbv zeta in FG. destruct FG as (MSL & AV & FR & LI & FB & SC & ML & _).
pose proof (rmeta_chunk_facts st1 m1 g MR MSL) as (_ & G0 & GC & _).
split; [gw_exact G0|]. split; [gw_exact GC|]. split; [gw_exact MSL|]. split; [exists b; reflexivity|]. split; [gw_exact AV|]. split; [gw_exact FR|].
pose proof (mf_maplen _ _ MF g b Hm) as MP. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MP. lia.
Qed.

#[using="RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 CODE LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 ROM_reservedZ LAY_ref_reserved ralloc_slot_entry rmmap_entry rmunmap_entry RC__ LB MF MR"] Lemma rcoarse_walk : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' : word) F fc (n sc : Z),
0 <= sc < 48 -> (sc < 32 -> 0 <= Z.lor sc 1 < 48) ->
evt segs (rcoarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n (coarse_sc st sc))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 (RATP + 131960)) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x20c)) fc None m1 (seg_rom segs)).
Proof. clear - RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 CODE LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 ROM_reservedZ LAY_ref_reserved ralloc_slot_entry rmmap_entry rmunmap_entry RC__ LB MF MR segs base RATP RDEBRUIJN st m1 t st1 MI. gw_expose_fam RATP; gw_expose_fam RDEBRUIJN. first [clear MI | gw_hide MI | idtac]; try gw_hide st1; first [clear t | gw_hide t | idtac]; try gw_hide m1; try gw_hide st.
intros until sc. intros SC48 SC1.
pose proof MR as (WF & (CXH & CXA & CXU & _) & (ML & NL & _) & _).
pose proof (mf_usage _ _ MF) as FU. change (fact_usage (strip st)) with (fact_usage st) in FU.
(gw_expose_fam RATP; gw_expose_fam RDEBRUIJN). unfold alloc_ceiling in *.

step. rewrite sextw_small by lia. step. rewrite (unsigned_lit sc), (Z.shiftl_mul_pow2 sc) by lia. change (2 ^ 3) with 8. step.
pose proof (actives_nth st1 sc ltac:(lia)) as NTH. change (active st1 sc) with (active st sc) in NTH.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_read segs mc _ (actives st1) sc _ (wa ((RATP + 132048) + 8 * sc)) CXA NTH ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
step.

assert (J40 : forall (a0' a1' a2' a3' : word) (sc' : Z), 0 <= sc' < 48 ->
evt segs (rcoarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n sc')
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 (RATP + 131960)) a0' a1' a2' a3' a4 a5 a6 a7
(pw st1 (active st sc')) (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 sc') s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x2b8)) fc None m1 (seg_rom segs))).
{ intros a0' a1' a2' a3' sc' SC'.
destruct (active st sc') as [g|] eqn:ACT'.
- destruct (ractive_ptr_facts sc' g ACT') as (G0 & GC & MSL & _ & AV & FR & MW). unfold alloc_ceiling in GC.
pose proof (rmeta_chunk_facts st1 m1 g MR MSL) as (MM & _).
change (get_meta_rec st1 g) with (get_meta_rec st g) in MM. unfold meta_cells, meta_word in MM.
unfold pw. cbn [oconc]. set (gw := wz (conc st1 g)) in *.
assert (HG : bv_unsigned gw = conc st1 g) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM.
step. if_cases K; zify_cond K. { exfalso. rewrite HG in K. lia. }
step. rewrite (sx32_wz_sxv (m_avail (get_meta_rec st g))) by lia. step.
apply evt_done. unfold rcoarse_post. change (active st1 sc') with (active st sc'). rewrite ACT'. do 4 eexists. split; [subst gw; reflexivity| reflexivity].
- unfold pw. cbn [oconc].
step. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K by lia. lia. }
step.
apply evt_done. unfold rcoarse_post. change (active st1 sc') with (active st sc'). rewrite ACT'. do 4 eexists. split; [reflexivity| reflexivity]. }

assert (J4c : forall (a0' a1' a2' a3' : word) (sc' : Z), active st sc' = None ->
evt segs (rcoarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n sc')
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 (RATP + 131960)) a0' a1' a2' a3' a4 a5 a6 a7
(Z_to_bv 64 0) (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 sc') s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x2c4)) fc None m1 (seg_rom segs))).
{ intros a0' a1' a2' a3' sc' ACT'. step.
apply evt_done. unfold rcoarse_post. change (active st1 sc') with (active st sc'). rewrite ACT'. do 4 eexists. split; [reflexivity| reflexivity]. }

assert (J2c : forall (a1' a2' a3' s4' : word) (sc' : Z), 0 <= sc' < 48 ->
evt segs (rcoarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n sc')
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 (RATP + 131960)) (Z_to_bv 64 sc') a1' a2' a3' a4 a5 a6 a7
(Z_to_bv 64 0) (Z_to_bv 64 RDEBRUIJN) s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x2a4)) fc None m1 (seg_rom segs))).
{ intros a1' a2' a3' s4' sc' SC'.
step. rewrite sextw_small by lia. step. rewrite (unsigned_lit sc'), (Z.shiftl_mul_pow2 sc') by lia. change (2 ^ 3) with 8. step.
pose proof (actives_nth st1 sc' ltac:(lia)) as NTH'. change (active st1 sc') with (active st sc') in NTH'.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_read segs mc _ (actives st1) sc' _ (wa ((RATP + 132048) + 8 * sc')) CXA NTH' ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD' end.
step. step. apply J40. gw_exact SC'. }

step.
destruct (active st sc) as [g|] eqn:ACT.
-
destruct (ractive_ptr_facts sc g ACT) as (G0 & GC & _). unfold alloc_ceiling in GC.
unfold pw. cbn [oconc].
if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }
clear K1.
replace (coarse_sc st sc) with sc by (unfold coarse_sc; rewrite ACT; reflexivity).
change (wz (conc st1 g)) with (pw st1 (Some g)). rewrite <- ACT. apply J40. gw_exact SC48.
-
unfold pw. cbn [oconc].
if_cases K1; zify_cond K1. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }
clear K1.
assert (CS : forall b : bool, (4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0) = b ->
coarse_sc st sc = if b then
(let usage1 := usage st (Z.lor sc 1) in
let usage1 := match active st (Z.lor sc 1) with
| None => usage1 + 3
| Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st (Z.lor sc 1))) in
if (m_avail ar =? 0) && (m_freed ar =? 0) then usage1 + 3 else usage1
end in
if usage1 <=? 12 then Z.lor sc 1 else sc) else sc).
{ intros b Hb. unfold coarse_sc. rewrite ACT, Hb. reflexivity. }

step. step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit sc) in K2 by lia.
+
rewrite (CS false) by (subst sc; reflexivity).
change (wz 0) with (pw st1 None). rewrite <- ACT. apply J40. gw_exact SC48.
+
step. step. step. if_cases K3; zify_cond K3; rewrite (swrap32_small (sc + -4)), land_ones64 in K3 by lia.
*
rewrite (CS false). 2:{ destruct (Z.lt_ge_cases sc 4); [replace (4 <=? sc) with false by (symmetry; apply Z.leb_gt; lia); reflexivity|].
replace (sc <? 32) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia). destruct (4 <=? sc); reflexivity. }
change (wz 0) with (pw st1 None). rewrite <- ACT. apply J40. gw_exact SC48.
* assert (SC432 : 4 <= sc < 32) by (Z.div_mod_to_equations; lia). clear K3. rename K2 into NE6.

step. step. if_cases K4; zify_cond K4; rewrite ?(unsigned_lit sc) in K4 by lia.
--
rewrite (CS false).
2:{ replace (4 <=? sc) with true by (symmetry; apply Z.leb_le; lia). replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
replace (sc =? 6) with false by (symmetry; apply Z.eqb_neq; lia).
destruct (Z.even sc) eqn:EV; [|reflexivity]. exfalso. apply K4. apply (proj2 (land_1_even sc)). gw_exact EV. }
step. step. apply J4c. gw_exact ACT.
-- pose proof (proj1 (land_1_even sc) K4) as EV.

pose proof (usages_nth st1 sc ltac:(lia)) as NTHU. change (usage st1 sc) with (usage st sc) in NTHU.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_read segs mc _ (usages st1) sc _ (wa ((RATP + 132432) + 8 * sc)) CXU NTHU ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDU end.
step. pose proof (FU sc) as FUsc.
step. if_cases K6; zify_cond K6; rewrite ?wz_unsigned in K6 by lia.
**
assert (COND : (4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0) = true).
{ replace (4 <=? sc) with true by (symmetry; apply Z.leb_le; lia).
replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
replace (sc =? 6) with false by (symmetry; apply Z.eqb_neq; lia).
rewrite EV. replace (usage st sc =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
specialize (SC1 ltac:(lia)). set (sc1 := Z.lor sc 1) in *.

step. rewrite (unsigned_lit sc) by lia. fold sc1.
step. rewrite sextw_small by lia. step. rewrite (unsigned_lit sc1), (Z.shiftl_mul_pow2 sc1) by lia. change (2 ^ 3) with 8. step.
pose proof (actives_nth st1 sc1 ltac:(lia)) as NTH1. change (active st1 sc1) with (active st sc1) in NTH1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_read segs mc _ (actives st1) sc1 _ (wa ((RATP + 132048) + 8 * sc1)) CXA NTH1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD1 end.
step.
pose proof (usages_nth st1 sc1 ltac:(lia)) as NTHU1. change (usage st1 sc1) with (usage st sc1) in NTHU1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_read segs mc _ (usages st1) sc1 _ (wa ((RATP + 132432) + 8 * sc1)) CXU NTHU1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDU1 end.
step. pose proof (FU sc1) as FU1.

set (u1 := match active st sc1 with
| None => usage st sc1 + 3
| Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st sc1)) in
if (m_avail ar =? 0) && (m_freed ar =? 0) then usage st sc1 + 3 else usage st sc1 end).
assert (U1 : 0 <= u1 < 2^61).
{ unfold u1. destruct (active st sc1); [match goal with |- context [if ?c then _ else _] => destruct c end|]; lia. }
assert (CS1 : coarse_sc st sc = if u1 <=? 12 then sc1 else sc).
{ rewrite (CS true COND). reflexivity. }
clear CS.
assert (J20 : forall (a2' a3' : word),
evt segs (rcoarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n (coarse_sc st sc))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 (RATP + 131960)) (Z_to_bv 64 sc1) (wz u1) a2' a3' a4 a5 a6 a7
(Z_to_bv 64 0) (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x298)) fc None m1 (seg_rom segs))).
{ intros a2' a3'. step. step. if_cases K9; zify_cond K9; rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia.
-
rewrite CS1. replace (u1 <=? 12) with true by (symmetry; apply Z.leb_le; lia). apply J2c. gw_exact SC1.
-
step. rewrite CS1. replace (u1 <=? 12) with false by (symmetry; apply Z.leb_gt; lia). apply J2c. gw_exact SC48. }
change (Z_to_bv 64 0) with (wz 0).
destruct (active st sc1) as [g1|] eqn:ACT1.
+++
destruct (ractive_ptr_facts sc1 g1 ACT1) as (G10 & G1C & MSL1 & _ & AV1 & FR1 & MW1). unfold alloc_ceiling in G1C.
pose proof (rmeta_chunk_facts st1 m1 g1 MR MSL1) as (MM1 & _).
change (get_meta_rec st1 g1) with (get_meta_rec st g1) in MM1. unfold meta_cells, meta_word in MM1.
unfold pw. cbn [oconc]. set (gw := wz (conc st1 g1)) in *.
assert (HG : bv_unsigned gw = conc st1 g1) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM1.
step. if_cases K7; zify_cond K7. { exfalso. rewrite HG in K7. lia. } clear K7.
cbn [default from_option id] in u1.

step. rewrite (sx32_wz_sxv (m_avail (get_meta_rec st g1))) by lia.
pose proof (sxv_range (m_avail (get_meta_rec st g1))) as RA1.
step. if_cases K8; zify_cond K8; rewrite ?wz_unsigned in K8 by lia.
***
assert (NA : m_avail (get_meta_rec st g1) <> 0) by (intros E; rewrite E in K8; apply K8; reflexivity).
replace (wz (usage st sc1)) with (wz u1).
2:{ unfold u1. replace (m_avail (get_meta_rec st g1) =? 0) with false by (symmetry; apply Z.eqb_neq; gw_exact NA). reflexivity. }
apply J20.
*** apply (proj1 (sxv_zero (m_avail (get_meta_rec st g1)) ltac:(lia))) in K8.

step. rewrite (sx32_wz_sxv (m_freed (get_meta_rec st g1))) by lia.
pose proof (sxv_range (m_freed (get_meta_rec st g1))) as RF1.
step. if_cases K9; zify_cond K9; rewrite ?wz_unsigned in K9 by lia.
---- assert (NF : m_freed (get_meta_rec st g1) <> 0) by (intros E; rewrite E in K9; apply K9; reflexivity).
replace (wz (usage st sc1)) with (wz u1).
2:{ unfold u1. rewrite K8. replace (m_freed (get_meta_rec st g1) =? 0) with false by (symmetry; apply Z.eqb_neq; gw_exact NF). reflexivity. }
apply J20.
---- apply (proj1 (sxv_zero (m_freed (get_meta_rec st g1)) ltac:(lia))) in K9.

step. rewrite (wz_unsigned (usage st sc1)) by lia.
replace (Z_to_bv 64 (usage st sc1 + 3)) with (wz u1).
2:{ unfold u1. rewrite K8, K9. reflexivity. }
apply J20.
+++
unfold pw. cbn [oconc].
step. if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K7 by lia. lia. } clear K7.
step. rewrite (wz_unsigned (usage st sc1)) by lia.
replace (Z_to_bv 64 (usage st sc1 + 3)) with (wz u1) by first [reflexivity | (cbn; lia)].
apply J20.
**
rewrite (CS false).
2:{ replace (4 <=? sc) with true by (symmetry; apply Z.leb_le; lia). replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
replace (sc =? 6) with false by (symmetry; apply Z.eqb_neq; lia). rewrite EV.
replace (usage st sc =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
step. step. apply J4c. gw_exact ACT.
Qed.
End COARSE.
End RC__1.

Ltac mem_after_store ::=
lazymatch goal with
| |- evt ?segs_ ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs_ m A ?cs0 |- _ =>
split_for_access H segs_ m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs_ m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs_ m |- _ =>
apply (mem_inv_store_cbytes segs_ m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs_ m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs_ m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs_ m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs_ m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
let E := fresh "EQ" m' in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:E;
clear HB; try rename H' into H
end
end
end.
Section RC__2.

#[using="base rvm_wait_entry ralloc_slot_entry rmmap_entry rmunmap_entry"] Lemma mul_srliw27_sxv k : 0 <= k < 32 ->
bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 (bv_unsigned (wz (sxv (2 ^ k))) * rDB32)))) 27) = rdbi k.
Proof. clear - base rvm_wait_entry ralloc_slot_entry rmmap_entry rmunmap_entry k.
intros Hk. unfold rdbi. rewrite (wz_unsigned (sxv (2 ^ k))) by apply sxv_range.
rewrite unsigned_lit_wrap. change (bv_wrap 32 ((sxv (2 ^ k) * rDB32) mod 2 ^ 64)) with (((sxv (2 ^ k) * rDB32) mod 2^64) mod 2^32).
rewrite (mod_mod_pow2 _ 32 64) by lia. rewrite <- Z.mul_mod_idemp_l, sxv_mod32, Z.mul_mod_idemp_l by lia.
rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.mod_pos_bound (2 ^ k * rDB32) (2^32) ltac:(lia)).
apply swrap32_small. Z.div_mod_to_equations. nia.
Qed.

Definition rfc_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' nw gw s4v : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (G avail k : Z) (prev next memw : word) (freed mword : Z) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3 m3,
ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 (RATP + 131960)) a0 a1 a2 a3 a4 a5 a6 a7
gw (wz k) s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x324)) fc None m3 (seg_rom segs)
/\ m3 = write_to_mem m (wa (G + 24)) (le4 (wz (avail - 2 ^ k)))
/\ munch [(G + 24, G + 28)]%Z m m3 /\ wmono segs m m3 /\ mem_inv segs m3
/\ rw_cells segs m3 (bv_unsigned gw) [C8 prev; C8 next; C8 memw; C4 (wz (avail - 2 ^ k)); C4 (wz freed); C8 (wz mword)].

#[using="rvm_wait_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 CODE RNG_RATP RNG_RDEBRUIJN ROM_RDEBRUIJN ralloc_slot_entry rmmap_entry rmunmap_entry"] Lemma rfast_walk : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw gw prev next memw : word) F fc m
(G avail k freed mword : Z),
bv_unsigned gw = G ->
rw_cells segs m (bv_unsigned gw) [C8 prev; C8 next; C8 memw; C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
mem_inv segs m -> (G + 40 <= 0x10000 \/ RIMG_HI <= G) ->
0 < avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= mword < 2^64 ->
0 <= k < 32 -> lowbit avail = 2 ^ k ->
evt segs (rfc_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' nw gw s4v F fc m G avail k prev next memw freed mword)
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 (RATP + 131960)) (wz (sxv avail)) a1 a2 a3 a4 a5 a6 a7
gw (Z_to_bv 64 RDEBRUIJN) s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x2c8)) fc None m (seg_rom segs)).
Proof. clear - rvm_wait_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 CODE RNG_RATP RNG_RDEBRUIJN ROM_RDEBRUIJN ralloc_slot_entry rmmap_entry rmunmap_entry segs base RATP RDEBRUIJN RIMG_HI. gw_expose_fam RATP; gw_expose_fam RDEBRUIJN.
intros until mword. intros HG MM MI GRES AV FRr MW HK LB.
pose proof (munch_refl [(G + 24, G + 28)]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (bv_unsigned_in_range _ gw) as GWR. change (bv_modulus 64) with (2^64) in GWR.
(gw_expose_fam RATP; gw_expose_fam RDEBRUIJN).
assert (P2 : 0 < 2 ^ k <= avail).
{ destruct (lowbit_nonzero avail ltac:(lia)) as (k' & Hk' & E & L). rewrite LB in E.
apply Z.pow_inj_r in E; [|lia|lia|lia]. subst k'. split; [apply Z.pow_pos_nonneg; lia| gw_exact L]. }
assert (P32 : 2 ^ k < 2 ^ 32) by (apply Z.pow_lt_mono_r; lia).
pose proof (sxv_range avail) as RA. pose proof (sxv_range (2 ^ k)) as RK.

step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv avail)))). rewrite (negw_and_lowbit avail) by lia. rewrite LB.

step. if_cases K0; zify_cond K0.
{ exfalso. rewrite ?wz_unsigned in K0 by assumption. pose proof (proj1 (sxv_zero (2 ^ k) ltac:(lia)) K0). lia. }
clear K0.

step. step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv avail)))). rewrite (negw_and_lowbit avail) by lia. rewrite LB.
step. step. change 125613361 with rDB32.
step. rewrite (mul_srliw27_sxv k) by lia.
pose proof (rdbi_range k) as DR.

step. rewrite ?(unsigned_lit (rdbi k)) by lia.
lazymatch goal with HI : mem_inv segs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; gw_expose_fam RDEBRUIJN end.
step. rewrite ?zxb_b8 by lia. clear DBR.

step. rewrite (wz_unsigned (sxv avail)), (wz_unsigned (sxv (2 ^ k))) by assumption.
rewrite (swrap_word (sxv avail - sxv (2 ^ k))).

step.
lazymatch goal with H : rw_cells segs ?mc (bv_unsigned gw) ?cs |- evt _ _ (MS _ _ _ _ _ ?mc' _) =>
apply (rw_cells_congr segs mc (bv_unsigned gw) cs
[C8 prev; C8 next; C8 memw; C4 (wz (avail - 2 ^ k)); C4 (wz freed); C8 (wz mword)]) in H;
[| cbn [cells_bytes cbytes]; rewrite (le4_avail_sub avail (2 ^ k)) by lia; reflexivity | reflexivity | cbn; tauto ]
end.

step.
apply evt_done. unfold rfc_post.
do 4 eexists.
lazymatch goal with E : ?mx = write_to_mem m _ _ |- _ => exists mx end.
split; [reflexivity|].
split. { lazymatch goal with E : ?mx = write_to_mem m _ _ |- _ => rewrite E end.
f_equal; [unfold wa; f_equal; lia | cbn [cbytes]; apply le4_avail_sub; lia]. }
split; [gw_exact MU|]. split; [gw_exact WM|]. split; [assumption|]. assumption.
Qed.
End RC__2.

Ltac mem_after_store ::=
lazymatch goal with
| |- evt ?segs_ ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs_ m A ?cs0 |- _ =>
split_for_access H segs_ m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs_ m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs_ m |- _ =>
apply (mem_inv_store_cbytes segs_ m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs_ m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs_ m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs_ m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs_ m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
clear Heqm; clear HB; try clear m; try rename H' into H
end
end
end.
Section RC__3.

#[using="rvm_wait_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 CODE ralloc_slot_entry rmmap_entry rmunmap_entry"] Lemma rcore0_walk : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw : word) F fc (m : mem),
evt segs (fun ms' => exists a1', ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 (RATP + 131960)) (wz (sxv 0)) a1' a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x300)) fc None m (seg_rom segs))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 (RATP + 131960)) (wz (sxv 0)) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x2c8)) fc None m (seg_rom segs)).
Proof. clear - rvm_wait_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 CODE ralloc_slot_entry rmmap_entry rmunmap_entry segs base RATP. gw_expose_fam RATP.
intros.
step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv 0)))). rewrite (negw_and_lowbit 0) by lia. rewrite lowbit_0.
step. if_cases KZ; zify_cond KZ. 2:{ exfalso. apply KZ. reflexivity. }
apply evt_done. eexists. reflexivity.
Qed.

Section FASTCORE.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> QUZl.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
(Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Hypothesis HENF : renf_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
Hypothesis MF : RMFACTS st LB.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 48.
Hypothesis N0 : 0 <= n.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RDEBRUIJN ROM_reservedZ LAY_ref_reserved ralloc_slot_entry rmmap_entry rmunmap_entry LB HENF MF TP CLO LO N0 NT BL"] Lemma rfast_core_implT :
forall (m1 : mem) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word) (sc : Z) (g : aptr),
let mr := get_meta_rec st g in
let mask := m_avail mr in
let first := lowbit mask in
rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 -> mem_inv segs m1 ->
stk segs m1 lo (bv_unsigned sp + -48) ->
rw_cells segs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells segs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m1 ->
active st sc = Some g -> 0 < mask -> n + 4 <= 16 * size_class sc ->
rimplT o (K (upd_meta g (m_set_avail (mask - first)) st1) (Some (g, ctz32 first))) s Q
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 (RATP + 131960)) (wz (sxv mask)) a1 a2 a3 a4 a5 a6 a7
(pw st1 (Some g)) (Z_to_bv 64 RDEBRUIJN) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x2c8)) fc None m1 (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RDEBRUIJN ROM_reservedZ LAY_ref_reserved ralloc_slot_entry rmmap_entry rmunmap_entry LB HENF MF TP CLO LO N0 NT BL segs base RATP RDEBRUIJN R K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo t st1. gw_expose_fam RATP; gw_expose_fam RDEBRUIJN. try gw_hide st1; try gw_hide t; first [clear lo | gw_hide lo | idtac]; try gw_hide n; try gw_hide fc; try gw_hide F; first [clear s4v | gw_hide s4v | idtac]; first [clear s3v | gw_hide s3v | idtac]; first [clear s2v | gw_hide s2v | idtac]; first [clear s1v | gw_hide s1v | idtac]; first [clear s0v | gw_hide s0v | idtac]; try gw_hide s11; try gw_hide s10; try gw_hide s9; try gw_hide s8; try gw_hide s7; try gw_hide s6; try gw_hide s5; try gw_hide tp; try gw_hide gp; try gw_hide sp; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; try gw_hide s; try gw_hide st; first [clear m0 | gw_hide m0 | idtac]; first [clear o | gw_hide o | idtac]; first [clear K | gw_hide K | idtac].
intros until g. intros mr mask first MR TK UA MI ST FR ERR AUX PE ACT AV NFIT.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold alloc_ceiling in CLO.

pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
destruct (FA sc g ACT) as (SC48 & GSC & _). change (get_meta_rec st g) with mr in GSC.
pose proof (mf_gmeta _ _ MF) as FG0.
assert (AVr : 0 <= mask < 2^32 /\ 0 <= m_freed mr < 2^32 /\ 0 <= m_last_idx mr < 32 /\ 0 <= m_freeable mr < 2 /\ 0 <= m_sizeclass mr < 64 /\ 0 <= m_maplen mr < 2^19).
{ change (fact_gmeta (strip st)) with (fact_gmeta st) in FG0.
destruct (m_mem mr) as [b|] eqn:Hm.
- specialize (FG0 g b Hm). change (get_meta_rec st g) with mr in FG0. cbv zeta in FG0.
destruct FG0 as (_ & A1 & A2 & A3 & A4 & A5 & A6 & _). subst mask. clear - A1 A2 A3 A4 A5 A6 GSC SC48 RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RDEBRUIJN ROM_reservedZ LAY_ref_reserved ralloc_slot_entry rmmap_entry rmunmap_entry segs base RATP RDEBRUIJN. lia.
- exfalso. destruct (FA sc g ACT) as (_ & _ & NN). apply NN. gw_exact Hm. }
destruct AVr as (AVr & FRr & LIr & FBr & SCr & MPr).
destruct (lowbit_facts mask ltac:(lia)) as (k & K32 & LBK). fold first in LBK.
assert (P2k : 0 < 2 ^ k <= mask).
{ split; [apply Z.pow_pos_nonneg; lia|]. destruct (lowbit_pow2 mask AV) as (k' & _ & E' & LE'). unfold first, lowbit in LBK.
rewrite LBK in E'. rewrite E'. gw_exact LE'. }
destruct (rfast_slot_ok st LB sc n g k t MF ACT AV ltac:(lia) LBK N0 NFIT) as (b & r & SO & SPANFP & _ & Hmem & Hr).
fold mr st1 in SO. change (get_meta_rec st g) with mr in Hmem.
pose proof (mf_ctx _ _ MF) as FC. change (fact_ctx (strip st)) with (fact_ctx st) in FC. destruct FC as (CTR & SEC & INI & _).

assert (MSL : meta_slot st1 g) by (exact (so_mslot _ _ _ _ _ _ SO)).
pose proof (rmeta_chunk_facts st1 m1 g MR MSL) as (MM & G0 & GC & GI1 & GI2 & GDJ & (rid0 & r0 & Hr0 & Hk0 & GR0 & GR1)). unfold alloc_ceiling in GC.
set (G := conc st1 g) in *.
change (get_meta_rec st1 g) with mr in MM. unfold meta_cells in MM. fold mask in MM. unfold meta_word in MM.

riprefixT.
eapply evt_mono.
{ eapply (rfast_walk sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' (Z_to_bv 64 n) (pw st1 (Some g))
(pw st1 (m_prev mr)) (pw st1 (m_next mr)) (pw st1 (m_mem mr)) F fc m1 G mask k (m_freed mr)
(m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)).
all: lazymatch goal with
| |- rw_cells _ _ (bv_unsigned (pw _ _)) _ => unfold pw; cbn [oconc]; fold G; rewrite (wz_unsigned G) by lia; gw_exact MM
| |- mem_inv _ _ => gw_exact MI
| |- bv_unsigned (pw _ _) = _ => unfold pw; cbn [oconc]; fold G; apply wz_unsigned; lia
| |- _ => idtac end.
all: try lia. all: try assumption. }
intros ms' PO. cbv beta in PO. unfold rfc_post in PO.
destruct PO as (v0 & v1 & v2 & v3 & m3 & -> & E3 & MU & WM & MI' & MM').

pose proof (ctz32_pow2 k ltac:(lia)) as CTZ.
replace (ctz32 first) with k by (rewrite LBK; symmetry; gw_exact CTZ).
replace (mask - first) with (mask - 2 ^ k) by (rewrite LBK; reflexivity).
set (st2 := upd_meta g (m_set_avail (mask - 2 ^ k)) st1) in *.
change (pw st1 (Some g)) with (pw st2 (Some g)).
assert (RB0 : forall rid r1, (s_regions st1) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= alloc_ceiling).
{ intros rid r1 H1. pose proof (rregion_facts st1 m1 rid r1 MR H1) as (X1 & _ & X2 & _). unfold alloc_ceiling in X2. lia. }
assert (RB : forall rid r1, (s_regions st1) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= 2^64).
{ intros rid r1 H1. pose proof (RB0 rid r1 H1). lia. }
eapply (HENF st2 g b r k m3 s errv).
-  rewrite E3. unfold st2. apply rmrep_meta_set_avail; [gw_exact MR| gw_exact MSL| lia].
- apply ticks_ok_upd_meta. gw_exact TK.
- eapply unk_agree_munch; [| gw_exact MU | |].
+ eapply unk_agree_ext; [gw_exact UA| reflexivity| intros; reflexivity| reflexivity].
+ intros rid r1 H1 K1. change (s_regions st2) with (s_regions st1) in H1.
pose proof (GDJ rid r1 H1 K1). pose proof (RB0 rid r1 H1). cbn. lia.
+ intros rid r1 H1. exact (RB rid r1 H1).
- gw_exact MI'.
- eapply stk_transport; [gw_exact ST| gw_exact MU| gw_exact WM|]. cbn. lia.
- eapply rw_cells_transport; [gw_exact FR| gw_exact MU| gw_exact WM|]. cbn. lia.
- eapply rw_cells_transport; [gw_exact ERR| gw_exact MU| gw_exact WM|]. subst tp. gw_expose_fam RATP. rewrite unsigned_lit by lia. cbn. lia.
- eapply rauxv_ok_frame; [gw_exact AUX| gw_exact MU| gw_exact WM|].
gw_expose_fam RATP. constructor; [cbn; lia|]. constructor.
- eapply rpres_except_munch_frame; [| gw_exact MU| gw_exact WM|].
+ eapply rpres_except_mono; [gw_exact PE|]. intros a Ha. eapply rmalloc_fp_mono; [|gw_exact Ha].
intros rid r1 H1. exists r1. repeat split; auto. lia.
+ intros x Hx NC. cbn. split; [|exact I].
intros HX. apply NC. left. right. right. right. exists rid0, r0. split; [gw_exact Hr0|]. split; [gw_exact Hk0|]. lia.
- intros a Ha. right. right. left. apply SPANFP.
replace (get_stride (get_meta_rec st2 g)) with (get_stride mr) in Ha; [gw_exact Ha|].
unfold st2. rewrite get_meta_rec_upd_same. reflexivity.
- gw_exact CTR.
- gw_exact SO.
- intros [X|X]; [exfalso; lia|]. exfalso. change (s_regions st1) with (s_regions st) in Hr. rewrite X in Hr. rewrite lookup_empty in Hr. discriminate.
- apply mrel_same; reflexivity.
- gw_exact BL.
- reflexivity.
- reflexivity.
- reflexivity.
Qed.
End FASTCORE.

Section ASCALL.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> QUZl.M R) (bail : QUZl.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
(Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis HENF : renf_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
Hypothesis HFAIL : rfail_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc lo.
Hypothesis MF : RMFACTS st LB.
Hypothesis MR0 : rmrep st m0.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 48 - RAS_STACK 0.
Hypothesis N0 : 0 <= n < 2^32.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry runlock_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 hi_216 lo_217 joff_218 CODE BASE4 BASER D_216 E_216 D_217 E_217 D_218 E_218 ANCH_217 LINK_218 RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved runlock_spec ralloc_slot_entry rmmap_entry rmunmap_entry as_inv RAS HENF HFAIL MR0 TP CLO LO NT BL"] Lemma ras_call_implT :
forall (m1 : mem) (errv : word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2r t3 t4 t5 t6 ra' : word) (sc : Z),
as_pre st st1 sc n FUEL ->
rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 -> mem_inv segs m1 ->
stk segs m1 lo (bv_unsigned sp + -48) ->
rw_cells segs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells segs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m1 ->
0 <= sc < 48 ->
rimplT o (alloc_slot full_lay FUEL st1 sc n
(fun st2 idx => if idx <? 0 then K st2 None
else match active st2 sc with
| Some gp => K st2 (Some (gp, idx))
| None => SVis (EUndef UBadPtr) (fun _ => bail)
end) bail) s Q
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 (RATP + 131960)) a0 a1 a2 a3 a4 a5 a6 a7
s2r (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x300)) fc None m1 (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry runlock_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 hi_216 lo_217 joff_218 CODE BASE4 BASER D_216 E_216 D_217 E_217 D_218 E_218 ANCH_217 LINK_218 RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved runlock_spec ralloc_slot_entry rmmap_entry rmunmap_entry as_inv RAS HENF HFAIL MR0 TP CLO LO NT BL segs base RATP RDEBRUIJN R K bail o m0 st LB s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo t as_pre MF N0 st1. gw_expose_fam RATP; gw_expose_fam RDEBRUIJN. try gw_hide st1; first [clear N0 | gw_hide N0 | idtac]; first [clear MF | gw_hide MF | idtac]; try gw_hide as_pre; first [clear t | gw_hide t | idtac]; try gw_hide lo; first [clear n | gw_hide n | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear s4v | gw_hide s4v | idtac]; first [clear s3v | gw_hide s3v | idtac]; first [clear s2v | gw_hide s2v | idtac]; first [clear s1v | gw_hide s1v | idtac]; first [clear s0v | gw_hide s0v | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; try gw_hide tp; first [clear gp | gw_hide gp | idtac]; try gw_hide sp; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear LB | gw_hide LB | idtac]; try gw_hide st; try gw_hide m0; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear K | gw_hide K | idtac].
intros until sc. intros PRE MR TK UA MI ST FR ERR AUX PE SC48.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold alloc_ceiling in CLO. pose proof (RAS_STACK_ge sc) as ASG. pose proof (RAS_STACK_mono 0 sc ltac:(lia)) as ASM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m1) as MU. pose proof (wmono_refl segs m1) as WM.
assert (RB0 : forall rid r1, (s_regions st1) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= alloc_ceiling).
{ intros rid r1 H1. pose proof (rregion_facts st1 m1 rid r1 MR H1) as (X1 & _ & X2 & _). unfold alloc_ceiling in X2. lia. }
subst tp. gw_expose_fam RATP. rewrite unsigned_lit in ERR by lia.
(gw_expose_fam RATP; gw_expose_fam RDEBRUIJN).
riprefixT.

step. rewrite sextw_small by lia. step. step.

step. apply evt_done.
eapply (RAS FUEL) with (st0 := st) (lo := lo).
all: lazymatch goal with
| |- as_pre _ _ _ _ _ => try gw_exact PRE
| |- rmrep _ _ => try gw_exact MR
| |- ticks_ok _ => try gw_exact TK
| |- unk_agree _ _ _ => try gw_exact UA
| |- brk_link_ps _ _ => try gw_exact BL
| |- rauxv_ok _ _ => try (rewrite unsigned_lit by lia; eapply rauxv_ok_weaken; [gw_exact AUX| unfold alloc_ceiling; lia])
| |- stk _ _ _ _ => try (rewrite unsigned_lit by lia; gw_exact ST)
| |- mem_inv _ _ => try assumption
| |- rw_cells _ _ _ [C4 _] => try (rewrite unsigned_lit by lia; gw_exact ERR)
| |- _ => idtac
end.
all: try (rewrite ?unsigned_lit by lia; unfold alloc_ceiling; lia).
all: try reflexivity.

intros st2 idx s' ms' PO.
destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & MR' & TK' & UA' & PE' & MREL & BL' & PSM & PSF & PSO & INV' & CTR' & RES).
try g_ret_pc_any.
rewrite ?unsigned_lit in ST', AUX', PE', RES by lia.

pose proof (rframe_after_call st st2 lo _ m0 m1 m' m' _ _ MR0 MR' PE' FR ltac:(lia) ltac:(unfold alloc_ceiling; lia)) as FR'.
assert (AUX2' : rauxv_ok m' (bv_unsigned sp)) by (eapply (rauxv_ok_malloc_fp st st2 lo _ m0 m' m1 m'); [gw_exact MR0| gw_exact MR'| gw_exact AUX| gw_exact PE'| unfold alloc_ceiling; lia| lia]).
assert (PE2 : rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m').
{ eapply rpres_except_trans; [| eapply rpres_except_mono; [gw_exact PE'|]; intros a Ha; eapply rmalloc_fp_sp_mono; [|gw_exact Ha]; lia].
eapply rpres_except_mono; [gw_exact PE|]. intros a Ha. eapply rmalloc_fp_st_mono; [gw_exact MREL|].
eapply rmalloc_fp_mono; [|gw_exact Ha]. intros rid r1 H1. exists r1. repeat split; auto. lia. }
assert (MREL2 : mrel st st2) by (eapply mrel_trans; [|gw_exact MREL]; apply mrel_same; reflexivity).
pose proof MR' as (_ & (CXH' & CXA' & _) & (ML' & _) & _). gw_expose_fam RATP. gw_expose_fam RATP.
clear MU WM PE AUX.
destruct RES as [[-> E12] | (IDX0 & g & b & r & ACT2 & SO & SPANFP & EXPO)].
-
change (-1 <? 0) with true. cbv iota.
riprefixT.
step. if_cases KB; zify_cond KB. 2:{ exfalso. lia. }
clear KB.
step. step.

step.
eapply evt_cut.
{ eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| gw_exact ML']. }
intros ms'' ->.
try g_ret_pc_any.

step. step. step. step. step. step. step. step. step. step.
release_frame FR' ST' (bv_unsigned sp).
apply evt_done. eapply (HFAIL st2 m' s' errv').
all: try assumption.
-
replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite ACT2.
pose proof SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0' NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
riprefixT.
step. if_cases KB; zify_cond KB. { exfalso. rewrite ?unsigned_lit in KB by lia. lia. }
clear KB.
step. step. rewrite (unsigned_lit sc), (Z.shiftl_mul_pow2 sc) by lia. change (2 ^ 3) with 8. step.
pose proof (actives_nth st2 sc ltac:(lia)) as NTH. rewrite ACT2 in NTH.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_read segs mc _ (actives st2) sc (pw st2 (Some g)) (wa ((RATP + 132048) + 8 * sc)) CXA' NTH ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
step.
apply evt_done.
change (Z_to_bv 64 idx) with (wz idx).
eapply (HENF st2 g b r idx m' s' errv').
all: try assumption.
+ intros a Ha. eapply rmalloc_fp_sp_mono; [|apply SPANFP; gw_exact Ha]. lia.
+ intros [X|X]; [exfalso; unfold MMAP_THRESHOLD in *; lia|]. apply EXPO. gw_exact X.
Qed.
End ASCALL.

Section SMALL.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> QUZl.M R) (bail : QUZl.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
(Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis HENF : renf_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
Hypothesis HFAIL : rfail_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc lo.
Hypothesis MF : RMFACTS st LB.
Hypothesis MR0 : rmrep st m0.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 48 - RAS_STACK 0.
Hypothesis N0 : 0 <= n < 2^32.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry runlock_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 hi_216 lo_217 joff_218 CODE BASE4 BASER D_216 E_216 D_217 E_217 D_218 E_218 ANCH_217 LINK_218 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RDEBRUIJN ROM_reservedZ LAY_ref_reserved runlock_spec ralloc_slot_entry rmmap_entry rmunmap_entry LB as_inv RAS HENF HFAIL MF MR0 TP CLO LO N0 NT BL"] Lemma rmalloc_small_implT :
forall (m1 : mem) (errv : word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2r t3 t4 t5 t6 ra' : word) (sc : Z),
sc = size_to_class n -> 0 <= sc < 48 -> n + 4 <= 16 * size_class sc ->
(forall sc', 0 <= sc' < 48 -> n + 4 <= 16 * size_class sc' -> as_pre st st1 sc' n FUEL) ->
rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 -> mem_inv segs m1 ->
stk segs m1 lo (bv_unsigned sp + -48) ->
rw_cells segs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells segs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m1 ->
rimplT o (malloc_small_ctrl full_lay st1 n K bail) s Q
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 (RATP + 131960)) a0 a1 a2 a3 a4 a5 a6 a7
s2r (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x20c)) fc None m1 (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry runlock_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 hi_216 lo_217 joff_218 CODE BASE4 BASER D_216 E_216 D_217 E_217 D_218 E_218 ANCH_217 LINK_218 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RDEBRUIJN ROM_reservedZ LAY_ref_reserved runlock_spec ralloc_slot_entry rmmap_entry rmunmap_entry LB as_inv RAS HENF HFAIL MF MR0 TP CLO LO N0 NT BL segs base RATP RDEBRUIJN R K bail o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo t as_pre st1. gw_expose_fam RATP; gw_expose_fam RDEBRUIJN. try gw_hide st1; first [clear as_pre | gw_hide as_pre | idtac]; try gw_hide t; first [clear lo | gw_hide lo | idtac]; try gw_hide n; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear s4v | gw_hide s4v | idtac]; first [clear s3v | gw_hide s3v | idtac]; first [clear s2v | gw_hide s2v | idtac]; first [clear s1v | gw_hide s1v | idtac]; first [clear s0v | gw_hide s0v | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; try gw_hide st; first [clear m0 | gw_hide m0 | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear K | gw_hide K | idtac].
intros until sc. intros SCE SC48 NFIT ASP MR TK UA MI ST FR ERR AUX PE.
pose proof (RAS_STACK_ge 0) as ASG. unfold st1 in *.
rewrite malloc_small_ctrl_eq. rewrite <- SCE. change (coarse_sc (set_tick t st) sc) with (coarse_sc st sc). cbv zeta.
pose proof (coarse_sc_cases st sc SC48) as CC.
assert (SC48' : 0 <= coarse_sc st sc < 48) by (destruct CC as [-> | (-> & H4 & EV)]; [lia| apply lor1_range; lia]).
assert (NFIT' : n + 4 <= 16 * size_class (coarse_sc st sc)).
{ destruct CC as [-> | (E & H4 & EV)]; [lia|]. rewrite E. pose proof (size_class_lor1 sc H4 EV). lia. }
set (sc' := coarse_sc st sc) in *.
change (active (set_tick t st) sc') with (active st sc').
riprefixT. eapply evt_cut.
{ eapply (rcoarse_walk st LB m1 t MF MR); [gw_exact SC48| intros; apply lor1_range; lia]. }
fold sc'. intros ms' (a0' & a1' & a2' & a3' & -> & HA0).
change (active (set_tick t st) sc') with (active st sc') in HA0 |- *.
destruct (active st sc') as [g|] eqn:ACT'.
- cbn iota. change (get_meta_rec (set_tick t st) g) with (get_meta_rec st g) in HA0 |- *. subst a0'.
destruct (Z.eq_dec (m_avail (get_meta_rec st g)) 0) as [AZ|ANZ].
+
rewrite AZ, lowbit_0. cbn.
eapply evt_cut. { apply rcore0_walk. }
intros ms'' (a1'' & ->). apply evt_done.
eapply ras_call_implT; try eassumption; try lia. apply ASP; [gw_exact SC48'| gw_exact NFIT'].
+
apply evt_done.
destruct (ractive_ptr_facts st LB m1 t MF MR sc' g ACT') as (_ & _ & _ & _ & AVr & _).
destruct (lowbit_facts (m_avail (get_meta_rec st g)) ltac:(lia)) as (k & K32 & LBK).
assert (P2 : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
replace (lowbit (m_avail (get_meta_rec st g)) =? 0) with false by (rewrite LBK; symmetry; apply Z.eqb_neq; lia).
cbn [negb]. cbv iota.
change (pw (set_tick t st) (Some g)) with (pw (set_tick t st) (Some g)).
eapply rfast_core_implT; try eassumption; try lia.
- cbn iota. subst a0'.
eapply evt_cut. { change (pw (set_tick t st) None) with (pw (set_tick t st) (@None aptr)). apply rcore0_walk. }
intros ms'' (a1'' & ->). apply evt_done.
eapply ras_call_implT; try eassumption; try lia. apply ASP; [gw_exact SC48'| gw_exact NFIT'].
Qed.
End SMALL.

End RC__3.

End G.
End Mq8.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq4 Q4J3.Mq2 QJE4.Mq3 QDUx.Mqa QDUx.Mqb.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QkTt.Mq4.
Import Qy8Z.Mq9.
Import QQRC.Mq9.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac amo_step AMO ::= g_amo_step AMO. Local Ltac mkr__amo_step_2 AMO := g_amo_step AMO.
Open Scope bv_scope.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 : Z).
Variables (hi_6 hi_26 hi_31 hi_93 : bv 20).
Variables (lo_7 lo_27 lo_32 lo_94 : bv 12).
Variables (joff_245 : bv 21).
Variables (e_197bc : Z).
Hypothesis CODE : code_at segs base (ntf_code w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 984.
Hypothesis D_6 : decode_any (Z_to_bv 32 w_6) = Some (Auipc 12 hi_6, 4%Z).
Hypothesis E_6 : is_ecall (Z_to_bv 32 w_6) = false.
Hypothesis D_7 : decode_any (Z_to_bv 32 w_7) = Some (Load SZ8 true 9 12 lo_7, 4%Z).
Hypothesis E_7 : is_ecall (Z_to_bv 32 w_7) = false.
Hypothesis D_26 : decode_any (Z_to_bv 32 w_26) = Some (Auipc 16 hi_26, 4%Z).
Hypothesis E_26 : is_ecall (Z_to_bv 32 w_26) = false.
Hypothesis D_27 : decode_any (Z_to_bv 32 w_27) = Some (OpImm ALU_ADD 18 16 lo_27, 4%Z).
Hypothesis E_27 : is_ecall (Z_to_bv 32 w_27) = false.
Hypothesis D_31 : decode_any (Z_to_bv 32 w_31) = Some (Auipc 16 hi_31, 4%Z).
Hypothesis E_31 : is_ecall (Z_to_bv 32 w_31) = false.
Hypothesis D_32 : decode_any (Z_to_bv 32 w_32) = Some (OpImm ALU_ADD 16 16 lo_32, 4%Z).
Hypothesis E_32 : is_ecall (Z_to_bv 32 w_32) = false.
Hypothesis D_93 : decode_any (Z_to_bv 32 w_93) = Some (Auipc 13 hi_93, 4%Z).
Hypothesis E_93 : is_ecall (Z_to_bv 32 w_93) = false.
Hypothesis D_94 : decode_any (Z_to_bv 32 w_94) = Some (OpImm ALU_ADD 13 13 lo_94, 4%Z).
Hypothesis E_94 : is_ecall (Z_to_bv 32 w_94) = false.
Hypothesis D_245 : decode_any (Z_to_bv 32 w_245) = Some (Jal 1 joff_245, 4%Z).
Hypothesis E_245 : is_ecall (Z_to_bv 32 w_245) = false.
Hypothesis ANCH_7 : gw_anch (Z.shiftl (bv_signed hi_6) 12 + (base + 24) + bv_signed lo_7)%Z RGOT_SSP.
Hypothesis ANCH_27 : gw_anch (Z.shiftl (bv_signed hi_26) 12 + (base + 104) + bv_signed lo_27)%Z (RATP + 131968).
Hypothesis ANCH_32 : gw_anch (Z.shiftl (bv_signed hi_31) 12 + (base + 124) + bv_signed lo_32)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_94 : gw_anch (Z.shiftl (bv_signed hi_93) 12 + (base + 372) + bv_signed lo_94)%Z (RATP + 131968).
Hypothesis LINK_245 : gw_anch (base + 980 + bv_signed joff_245)%Z (e_197bc + 0)%Z.
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

Definition rfree_fp : ltac:(gw_rebind_ty (@QDXD.Mq2.rfree_fp RATP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rfree_fp RATP) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QQRC.Mq9.rfree_fp RATP) (@rfree_fp) (gw_ent (@Qy8Z.Mq9.rfree_fp RATP) (@rfree_fp) (gw_ent (@QDXD.Mq2.rfree_fp RATP) (@rfree_fp) gw_tbl_0))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QQRC.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_1)))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QQRC.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_2)))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QQRC.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_3)))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QQRC.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_4)))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QQRC.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_5)))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QQRC.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_6)))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QQRC.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_7)))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QQRC.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_8)))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QQRC.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_9)))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QQRC.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_10)))))).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@QQRC.Mq9.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq9.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) gw_tbl_11)))).

Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).
Definition rmrep_group_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_group_read) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_group_read)).
Definition rmrep_set_active : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_set_active) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_set_active)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmrep_active_read : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_active_read) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_active_read)).
Definition rmeta_slot_bounds : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmeta_slot_bounds) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmeta_slot_bounds)).
Definition rfree_fp_stack : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rfree_fp_stack) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rfree_fp_stack)).
Definition rfree_fp_ctx : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rfree_fp_ctx) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rfree_fp_ctx)).
Definition rfree_fp_meta : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rfree_fp_meta) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rfree_fp_meta)).
Definition rpres_except_of_munch_cov : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rpres_except_of_munch_cov) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rpres_except_of_munch_cov)).

Ltac rmeta_open cq MUq WMq :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(cq, cq + 40)]%Z mX) as MUq;
pose proof (wmono_refl segs mX) as WMq end.
Ltac rmeta_chunk MR MSq CH :=
pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
rewrite ?get_meta_rec_put_same in CH;
rewrite ?conc_put_meta, ?pw_put_meta in CH;
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta_word meta0
m_set_prev m_set_next m_set_mem m_set_avail m_set_freed Z.mul Z.add] in CH;
rewrite ?meta_word_meta0 in CH; unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.

Definition rconc_meta_inj : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq9.rconc_meta_inj) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq9.rconc_meta_inj)).
Ltac rmeta_close2 MRold MSq MUq WMq CH st' MRnew E1 E2 :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRnew : rmrep st' mX)
by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
eapply rw_cells_congr; [ | | | exact CH];
[ unfold meta_cells; unfold pw; cbn [oconc m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen m_set_prev m_set_next];
unfold wz; rewrite ?E1, ?E2; cbn [oconc]; reflexivity
| reflexivity | cbn; tauto]);
clear MUq WMq CH end.

#[using="RGOT_SSP e_197bc RATP RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_6 E_6 D_7 E_7 D_26 E_26 D_27 E_27 D_31 E_31 D_32 E_32 D_93 E_93 D_94 E_94 D_245 E_245 ANCH_7 ANCH_27 ANCH_32 ANCH_94 LINK_245 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rraw_store_finish A bs' FR ST MU WM SOK :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); (gw_expose_fam RATP; unfold wa); f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by first [reflexivity | (cbn; lia)];
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
apply (rw_cells_frame segs mX _ _ A bs') in FR; [| gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; cbn [cells_size csize Nat.add]; lia];
apply (stk_write segs mX _ _ A bs') in ST; [| gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; lia];
apply (munch_write _ _ mX A bs') in MU; [| gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; cbn [inside]; lia];
apply (wmono_write segs _ mX (wa A) bs') in WM;
lazymatch goal with HI : mem_inv segs mX |- _ =>
apply (mem_inv_store segs mX (wa A) bs') in HI;
[| first [ gw_exact SOK | rewrite <- ?L; replace (wa A) with a by ((gw_expose_fam RATP; unfold wa); f_equal; lia); gw_exact SOK ] ]
end;
clear L SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
end.
Section RC__1.

Definition rat9c_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (sc : Z) (fr : list cell) : machine_state -> Prop :=
fun ms' => exists a3 a4 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 ((RATP + 131968) + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (RATP + 131968)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x1c4)) fc None m' (seg_rom segs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp + -96)
/\ rw_cells segs m' (bv_unsigned sp + -96) fr
/\ rmrep st' m'.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 CODE LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved"] Lemma rntf_deqself : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (fr : list cell) st (g : aptr) (sc lo : Z),
rmrep st m -> mem_inv segs m -> meta_slot st g -> 0 <= sc < 48 ->
m_next (get_meta_rec st g) = Some g ->
rw_cells segs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
stk segs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt segs (rat9c_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 F fc lo st m
(deq_mid (LActive sc) g st) g sc fr)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 ((RATP + 131968) + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (RATP + 131968)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x1bc)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 CODE LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved segs base RATP. gw_expose_fam RATP.
intros until lo. intros MR MI MSL SC GN FR FRL ST LO LOLE.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); ((RATP + 131968), (RATP + 132896))]%Z m) as MU.
pose proof (wmono_refl segs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
(gw_expose_fam RATP; unfold alloc_ceiling in *).
st1.
pose proof MR as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok segs _ _ (actives st) sc (Z_to_bv 64 ((RATP + 131968) + sc * 8 + 80)) ACTS
ltac:(rewrite actives_length; lia) ltac:((gw_expose_fam RATP; unfold wa); f_equal; lia)) as SOK.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st mX sc None MR SC) as MR2; gw_expose_fam RATP end.
clear ACTS.
rraw_store_finish ((RATP + 132048) + 8 * sc) (le8 (pw st None)) FR ST MU WM SOK.
assert (EQ : deq_mid (LActive sc) g st = set_active sc None st).
{ unfold deq_mid. rewrite GN, optr_eqb_refl. reflexivity. }
rewrite EQ.
apply evt_done. unfold rat9c_post. do 3 eexists. split; [cbv delta [mkR]; gw_expose_fam RATP; reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [gw_exact MU|gw_exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ apply rfree_fp_ctx. gw_expose_fam RATP. lia. }
split; [gw_exact WM|]. split; [assumption|]. split; [gw_exact ST|]. split; [gw_exact FR|gw_exact MR2].
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved"] Lemma rntf_deq : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (fr : list cell) st (g nx pv : aptr) (sc lo : Z),
rmrep st m -> mem_inv segs m -> meta_slot st g -> 0 <= sc < 48 ->
m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv ->
nx <> g -> pv <> g -> meta_slot st nx -> meta_slot st pv ->
(active st sc = None \/ exists q, active st sc = Some q /\ meta_slot st q) ->
a2 = pw st (active st sc) ->
rw_cells segs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
stk segs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt segs (rat9c_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 F fc lo st m
(deq_mid (LActive sc) g st) g sc fr)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 ((RATP + 131968) + sc * 8)) a2 (Z_to_bv 64 (conc st nx)) a4 a5 a6 a7 (Z_to_bv 64 (RATP + 131968)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x138)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved segs base RATP. gw_expose_fam RATP.
intros until lo. intros MR MI MSL SC GN GP NEn NEp MSn MSp ACT HA2 FR FRL ST LO LOLE.
pose proof (wmono_refl segs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
pose proof (rmeta_slot_bounds st m nx MR MSn) as NB. pose proof (rmeta_slot_bounds st m pv MR MSp) as PB.
pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
(gw_expose_fam RATP; unfold alloc_ceiling in *).
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40); ((RATP + 131968), (RATP + 132896))]%Z m) as MU.

rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
st1. clear CH.

rmeta_open (conc st pv) MUp WMp.
rmeta_chunk MR MSp CH.
st1.
rmeta_close2 MR MSp MUp WMp CH (put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) MR1 GP GN.
set (st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) in MR1.
assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; gw_exact MSL).
assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; gw_exact MSn).

rmeta_chunk MR1 MSg1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; gw_exact E).
rewrite GN, GP in CH. cbn [oconc] in CH.
st1. st1. clear CH.

rmeta_open (conc st nx) MUn WMn.
rmeta_chunk MR1 MSn1 CH.
st1.
rmeta_close2 MR1 MSn1 MUn WMn CH (put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) MR2 GP GN.
set (st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) in MR2.
assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; gw_exact MSg1).

pose proof (rmrep_active_read st2 _ sc (wa ((RATP + 132048) + 8 * sc)) MR2 SC eq_refl) as RDA. gw_expose_fam RATP.
replace (wa ((RATP + 132048) + 8 * sc)) with (Z_to_bv 64 ((RATP + 131968) + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
assert (HACT : active st2 sc = active st sc) by first [reflexivity | (cbn; lia)]. rewrite HACT in RDA.
assert (HPW : forall q, pw st2 q = pw st q) by (intros [q|]; reflexivity). rewrite HPW in RDA.
st1. clear RDA.
assert (EQmid : deq_mid (LActive sc) g st =
if optr_eqb (active st sc) (Some g) then set_active sc (Some nx) st2 else st2).
{ unfold deq_mid. rewrite GN, GP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx g NEn). cbn [negb get_head].
rewrite !upd_meta_put. fold st1. fold st2. rewrite HACT. reflexivity. }

st1. if_cases K; zify_cond K.
-
assert (HA : optr_eqb (active st sc) (Some g) = false).
{ destruct (active st sc) as [q|]; [|reflexivity]. cbn [optr_eqb]. apply aptr_eqb_neq. intros ->. apply K.
unfold pw, wz; cbn [oconc]. rewrite ?unsigned_lit by lia. reflexivity. }
rewrite HA in EQmid. rewrite <- EQmid in MR2. subst a2.
apply evt_done. unfold rat9c_post. do 3 eexists. split; [cbv delta [mkR]; gw_expose_fam RATP; reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [gw_exact MU|gw_exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ eapply rfree_fp_meta; [gw_exact MR | gw_exact MSL | lia].
+ eapply rfree_fp_meta; [gw_exact MR | gw_exact MSp | lia].
+ eapply rfree_fp_meta; [gw_exact MR | gw_exact MSn | lia].
+ apply rfree_fp_ctx. gw_expose_fam RATP. lia. }
split; [gw_exact WM|]. split; [assumption|]. split; [gw_exact ST|]. split; [gw_exact FR| gw_exact MR2].
-
assert (HA : active st sc = Some g).
{ destruct ACT as [A0|(q & Aq & MSq)].
- exfalso. rewrite A0 in K. unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia.
- rewrite Aq in K |- *. unfold pw, wz in K; cbn [oconc] in K.
pose proof (rmeta_slot_bounds st m q MR MSq) as QB. rewrite ?unsigned_lit in K by lia.
rewrite (rconc_meta_inj st m g q MR MSL MSq ltac:(lia)). reflexivity. }
rewrite HA, optr_eqb_refl in EQmid.
rmeta_chunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; gw_exact E).
unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; gw_exact E).
rewrite GN, GP in CH. cbn [oconc] in CH.
st1. clear CH. st1.
pose proof MR2 as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok segs _ _ (actives st2) sc (Z_to_bv 64 ((RATP + 131968) + sc * 8 + 80)) ACTS
ltac:(rewrite actives_length; lia) ltac:((gw_expose_fam RATP; unfold wa); f_equal; lia)) as SOK.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st2 mX sc (Some nx) MR2 SC) as MR3; gw_expose_fam RATP end.
clear ACTS.
rraw_store_finish ((RATP + 132048) + 8 * sc) (le8 (pw st2 (Some nx))) FR ST MU WM SOK.
rewrite <- EQmid in MR3. subst a2.
apply evt_done. unfold rat9c_post. do 3 eexists. split; [cbv delta [mkR]; gw_expose_fam RATP; reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [gw_exact MU|gw_exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ eapply rfree_fp_meta; [gw_exact MR | gw_exact MSL | lia].
+ eapply rfree_fp_meta; [gw_exact MR | gw_exact MSp | lia].
+ eapply rfree_fp_meta; [gw_exact MR | gw_exact MSn | lia].
+ apply rfree_fp_ctx. gw_expose_fam RATP. lia. }
split; [gw_exact WM|]. split; [assumption|]. split; [gw_exact ST|]. split; [gw_exact FR| gw_exact MR3].
Qed.

#[using="Type"] Lemma land_mod_pow2 a b n : 0 <= n -> (Z.land a b) mod 2^n = Z.land (a mod 2^n) (b mod 2^n).
Proof. clear - a b n.
intros Hn. rewrite <- !Z.land_ones by lia.
apply Z.bits_inj'. intros k Hk. rewrite !Z.land_spec.
destruct (Z.testbit a k), (Z.testbit b k), (Z.testbit (Z.ones n) k); reflexivity.
Qed.

#[using="Type"] Lemma act_mask_le4 f y z : 0 <= f < 2^32 -> 1 <= y <= 2^32 -> z mod 2^32 = (y - 1) mod 2^32 ->
le4 (Z_to_bv 64 (Z.land (sxv f) (bv_unsigned (Z_to_bv 64 z)))) = le4 (wz (Z.land f (y - 1))).
Proof. clear - f y z.
intros Hf Hy Hz. apply le4_congr.
pose proof (sxv_range f). rewrite (unsigned_lit_wrap z). pose proof (Z.mod_pos_bound z (2^64) ltac:(lia)).
assert (R1 : 0 <= Z.land (sxv f) (z mod 2^64) < 2^64) by (apply land_range64; lia).
assert (R2 : 0 <= Z.land f (y - 1) < 2^32).
{ split; [apply Z.land_nonneg; lia|]. pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)). lia. }
rewrite unsigned_lit, wz_unsigned by lia.
rewrite land_mod_pow2, sxv_mod32, mod64_mod32, Hz by lia.
rewrite !Z.mod_small by lia. reflexivity.
Qed.

Definition rat00_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (fr : list cell) : machine_state -> Prop :=
fun ms' => exists t0 a1 a2 a3 a4 a5 a6 a7 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (RATP + 131968)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x228)) fc None m' (seg_rom segs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp + -96)
/\ rw_cells segs m' (bv_unsigned sp + -96) fr
/\ rmrep st' m'.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 ROM_reservedZ LAY_ref_reserved"] Lemma rntf_postdeq : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (fr : list cell) stm (g : aptr) (sc lo : Z) (an : bool),
let st1 := upd_meta g clr_links stm in
rmrep stm m -> mem_inv segs m -> meta_slot stm g -> 0 <= sc < 48 ->
(if an then bv_unsigned a2 = conc stm g else bv_unsigned a2 <> conc stm g) ->
(an = true -> forall a, active st1 sc = Some a ->
meta_slot st1 a /\ a <> g /\ m_avail (get_meta_rec st1 a) = 0 /\ 0 <= m_freed (get_meta_rec st1 a) < 2^32
/\ exists ba gh, m_mem (get_meta_rec st1 a) = Some ba /\ (s_groups st1) !! ba = Some gh /\ 0 <= g_active_idx gh <= 31) ->
rw_cells segs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
stk segs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt segs (rat00_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t1 t2 t3 t4 t5 t6 F fc lo stm m (pd_st an st1 sc) g fr)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc stm g)) (Z_to_bv 64 ((RATP + 131968) + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (RATP + 131968)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x1c4)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 ROM_reservedZ LAY_ref_reserved segs base RATP. gw_expose_fam RATP.
intros until an. intros st1 MR MI MSL SC HA2 HACT FR FRL ST LO LOLE.
pose proof (wmono_refl segs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (bv_unsigned_in_range _ a2) as A2R. change (bv_modulus 64) with (2^64) in A2R.
pose proof (rmeta_slot_bounds stm m g MR MSL) as GB.
pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
(gw_expose_fam RATP; unfold alloc_ceiling in *).
pose proof (munch_refl [(conc stm g, conc stm g + 40); (conc stm g, conc stm g + 40)]%Z m) as MU.

rmeta_open (conc stm g) MUg WMg.
rmeta_chunk MR MSL CH.
st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep st1 mX)
by (unfold st1; rewrite upd_meta_put; eapply rmrep_put_meta_frame; [gw_exact MR | gw_exact MSL | gw_exact MUg | gw_exact WMg |];
eapply rw_cells_congr; [ | | | gw_exact CH]; [reflexivity | reflexivity | cbn; tauto]);
clear MUg WMg CH
end.
assert (COV : forall m', munch [(conc stm g, conc stm g + 40); (conc stm g, conc stm g + 40)]%Z m m' -> wmono segs m m' ->
rpres_except (rfree_fp stm lo (bv_unsigned sp)) m m').
{ intros m' MU' WM'. apply (rpres_except_of_munch_cov (rfree_fp stm lo (bv_unsigned sp))) in MU'; [gw_exact MU'|gw_exact WM'|].
cbn [ivs_covered]. repeat split; intros x Hx; (eapply rfree_fp_meta; [gw_exact MR | gw_exact MSL | lia]). }
assert (MSg1 : meta_slot st1 g) by (unfold st1; rewrite upd_meta_put; apply meta_slot_put_meta; gw_exact MSL).
assert (Hconc : forall q, conc st1 q = conc stm q) by (intros; reflexivity).

st1. if_cases K; zify_cond K.
-
destruct an. { exfalso. apply K. rewrite ?unsigned_lit by lia. lia. }
cbn [pd_st].
apply evt_done. unfold rat00_post. do 9 eexists. split; [cbv delta [mkR]; gw_expose_fam RATP; reflexivity|].
split; [apply COV; [gw_exact MU|gw_exact WM]|]. split; [gw_exact WM|]. split; [assumption|]. split; [gw_exact ST|]. split; [gw_exact FR|gw_exact MR1].
-
destruct an. 2:{ exfalso. apply HA2. rewrite ?unsigned_lit in K by lia. lia. }
cbn [pd_st].

pose proof (rmrep_active_read st1 _ sc (wa ((RATP + 132048) + 8 * sc)) MR1 SC eq_refl) as RDA. gw_expose_fam RATP.
assert (HPW : forall q, pw st1 q = pw stm q) by (intros [q|]; reflexivity). rewrite HPW in RDA.
replace (wa ((RATP + 132048) + 8 * sc)) with (Z_to_bv 64 ((RATP + 131968) + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
st1. clear RDA.

st1. destruct (active st1 sc) as [a|] eqn:HA1.
+ destruct (HACT eq_refl a eq_refl) as (MSa & NEa & AV0 & FRR & ba & gh & Hmem & Hgh & AI).
pose proof (rmeta_slot_bounds st1 _ a MR1 MSa) as AB. rewrite !Hconc in AB.
munch_grow MU (conc stm a, conc stm a + 40).
unfold pw, wz; cbn [oconc]. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.

rmeta_chunk MR1 MSa CHa. rewrite AV0, Hmem in CHa. cbn [oconc] in CHa.
st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. rewrite ?unsigned_lit by lia. reflexivity. } clear K3.

st1.

destruct (rmrep_group_read st1 _ ba gh MR1 Hgh) as [_ (w8 & RD8 & Hw8)].
rewrite Hconc in RD8.
st1.
pose proof (bv_unsigned_in_range _ w8) as W8R. change (bv_modulus 8) with 256 in W8R.
assert (MOD8 : bv_unsigned w8 mod 32 = g_active_idx gh).
{ rewrite <- Hw8. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. }

st1. st1. unfold zxb. rewrite (sllw2_word (bv_unsigned w8)) by lia. rewrite MOD8.
set (y := 2 ^ (g_active_idx gh + 1)).
st1. st1. rewrite negw_word.

clear CHa. rmeta_open (conc stm a) MUa WMa.
rmeta_chunk MR1 MSa CHa. rewrite Hmem in CHa. cbn [oconc] in CHa.
pose proof (sxv_range (m_freed (get_meta_rec st1 a))) as RF. pose proof (sxv_range (- y)) as RY. pose proof (sxv_range y) as RY1.
st1. rewrite sx32_wz_sxv by lia.
st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite sxv_land.

assert (AMO : amo_aligned AW (Z_to_bv 64 (conc stm a + 28)) = true).
{ apply amo_aligned_intro; [lia|]. Z.div_mod_to_equations. lia. }
amo_step AMO. rewrite ?sx32_wz_sxv by lia.
st1. if_false.
amo_step AMO.
st1. if_false.
st1. rewrite ?sextw_sxv, ?sextw_sxv', ?sextw_sxv0, ?sextw_sxv1. st1. if_false.

st1. st1. st1.

set (f := m_freed (get_meta_rec st1 a)) in *.
assert (AI31 : Z.land (g_active_idx gh) 31 = g_active_idx gh).
{ change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
assert (ACT : act_of st1 a = y - 1).
{ unfold act_of. rewrite Hmem. cbn [default]. unfold group_active_idx, get_group. rewrite Hgh, AI31. unfold mask_upto, y. reflexivity. }
assert (E1 : Z.land f (- y) = Z.ldiff f (y - 1)) by (unfold y; apply land_neg_pow2; lia).
assert (Y1 : 1 <= y <= 2^32).
{ unfold y. split; [pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh + 1)); lia| apply Z.pow_le_mono_r; lia]. }
pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)) as R1.
pose proof (ldiff_le f (y - 1) ltac:(lia) ltac:(lia)) as R2.
pose proof (Z.ldiff_nonneg f (y - 1)) as R3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep (act_st st1 a (act_of st1 a)) mX)
end.
{ unfold act_st. rewrite upd_meta_put, ACT. eapply rmrep_put_meta_frame; [gw_exact MR1 | gw_exact MSa | gw_exact MUa | gw_exact WMa |].
eapply rw_cells_congr; [ | | | gw_exact CHa]; [ | reflexivity | cbn; tauto].
unfold meta_cells. unfold pw. cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail m_set_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen oconc].
fold f. rewrite E1. rewrite (act_mask_le4 f y) ; [| lia | gw_exact Y1 | rewrite <- Zplus_mod_idemp_l, swrap32_mod32, Zplus_mod_idemp_l; reflexivity].
rewrite !le4_sxv by lia. rewrite Hmem. cbn [oconc]. reflexivity. }
clear MUa WMa CHa.
apply evt_done. unfold rat00_post. do 9 eexists. split; [cbv delta [mkR]; gw_expose_fam RATP; reflexivity|].
split. { apply (rpres_except_of_munch_cov (rfree_fp stm lo (bv_unsigned sp))) in MU; [gw_exact MU|gw_exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
- eapply rfree_fp_meta; [gw_exact MR | gw_exact MSL | lia].
- eapply rfree_fp_meta; [gw_exact MR | gw_exact MSa | lia].
- eapply rfree_fp_meta; [gw_exact MR | gw_exact MSL | lia]. }
split; [gw_exact WM|]. split; [assumption|]. split; [gw_exact ST|]. split; [gw_exact FR|].
unfold pd_st. rewrite ?HA1. gw_exact MR2.
+
unfold pw, wz; cbn [oconc]. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. rewrite ?unsigned_lit by lia. reflexivity. } clear K2.
apply evt_done. unfold rat00_post. do 9 eexists. split; [cbv delta [mkR]; gw_expose_fam RATP; reflexivity|].
split; [apply COV; [gw_exact MU|gw_exact WM]|]. split; [gw_exact WM|]. split; [assumption|]. split; [gw_exact ST|]. split; [gw_exact FR|].
unfold pd_st. rewrite ?HA1. gw_exact MR1.
Qed.

End RC__1.

End G.
End Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4vs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq4 Q4J3.Mq2 Q9Ay.Mqb Q4vs QDUx.Mqb QPjm.Mq3.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QkTt.Mq4.
Import Qy8Z.Mq3.
Import Qy8Z.Mq9.
Import QQRC.Mq9.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope bv_scope.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 : Z).
Variables (hi_6 hi_26 hi_31 hi_93 : bv 20).
Variables (lo_7 lo_27 lo_32 lo_94 : bv 12).
Variables (joff_245 : bv 21).
Variables (e_197bc : Z).
Hypothesis CODE : code_at segs base (ntf_code w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 984.
Hypothesis D_6 : decode_any (Z_to_bv 32 w_6) = Some (Auipc 12 hi_6, 4%Z).
Hypothesis E_6 : is_ecall (Z_to_bv 32 w_6) = false.
Hypothesis D_7 : decode_any (Z_to_bv 32 w_7) = Some (Load SZ8 true 9 12 lo_7, 4%Z).
Hypothesis E_7 : is_ecall (Z_to_bv 32 w_7) = false.
Hypothesis D_26 : decode_any (Z_to_bv 32 w_26) = Some (Auipc 16 hi_26, 4%Z).
Hypothesis E_26 : is_ecall (Z_to_bv 32 w_26) = false.
Hypothesis D_27 : decode_any (Z_to_bv 32 w_27) = Some (OpImm ALU_ADD 18 16 lo_27, 4%Z).
Hypothesis E_27 : is_ecall (Z_to_bv 32 w_27) = false.
Hypothesis D_31 : decode_any (Z_to_bv 32 w_31) = Some (Auipc 16 hi_31, 4%Z).
Hypothesis E_31 : is_ecall (Z_to_bv 32 w_31) = false.
Hypothesis D_32 : decode_any (Z_to_bv 32 w_32) = Some (OpImm ALU_ADD 16 16 lo_32, 4%Z).
Hypothesis E_32 : is_ecall (Z_to_bv 32 w_32) = false.
Hypothesis D_93 : decode_any (Z_to_bv 32 w_93) = Some (Auipc 13 hi_93, 4%Z).
Hypothesis E_93 : is_ecall (Z_to_bv 32 w_93) = false.
Hypothesis D_94 : decode_any (Z_to_bv 32 w_94) = Some (OpImm ALU_ADD 13 13 lo_94, 4%Z).
Hypothesis E_94 : is_ecall (Z_to_bv 32 w_94) = false.
Hypothesis D_245 : decode_any (Z_to_bv 32 w_245) = Some (Jal 1 joff_245, 4%Z).
Hypothesis E_245 : is_ecall (Z_to_bv 32 w_245) = false.
Hypothesis ANCH_7 : gw_anch (Z.shiftl (bv_signed hi_6) 12 + (base + 24) + bv_signed lo_7)%Z RGOT_SSP.
Hypothesis ANCH_27 : gw_anch (Z.shiftl (bv_signed hi_26) 12 + (base + 104) + bv_signed lo_27)%Z (RATP + 131968).
Hypothesis ANCH_32 : gw_anch (Z.shiftl (bv_signed hi_31) 12 + (base + 124) + bv_signed lo_32)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_94 : gw_anch (Z.shiftl (bv_signed hi_93) 12 + (base + 372) + bv_signed lo_94)%Z (RATP + 131968).
Hypothesis LINK_245 : gw_anch (base + 980 + bv_signed joff_245)%Z (e_197bc + 0)%Z.
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

Definition rntf_frame : ltac:(gw_rebind_ty (@Qy8Z.Mq9.rntf_frame RC__) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Qy8Z.Mq9.rntf_frame RC__) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@Qy8Z.Mq9.rntf_frame RC__) (@rntf_frame) gw_tbl_0).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QQRC.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq3.rarea_rep segs) (@rarea_rep) gw_tbl_1))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QQRC.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq3.rmrep_areas segs) (@rmrep_areas) gw_tbl_2))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QQRC.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_3))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QQRC.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_4))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QQRC.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq3.rgroup_rep segs) (@rgroup_rep) gw_tbl_5))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QQRC.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq3.rmrep_groups segs) (@rmrep_groups) gw_tbl_6))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QQRC.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq3.rshadow_rep segs) (@rshadow_rep) gw_tbl_7))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QQRC.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq3.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_8))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QQRC.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_9))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QQRC.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_10))))))).

Hypothesis meta_word_sc2 : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qy8Z.Mq3.gw_all) (@Qy8Z.Mq3.meta_word_sc2) (base + -732)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_11))) in let T := gw_fold_pcs T base (-732)%Z [0; 36; 80; 108; 180; 260]%Z in exact T).
Hypothesis meta_word_pg : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qy8Z.Mq3.gw_all) (@Qy8Z.Mq3.meta_word_pg) (base + -732)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_11))) in let T := gw_fold_pcs T base (-732)%Z [0; 36; 80; 108; 180; 260]%Z in exact T).

Definition rsize_classes_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rsize_classes_read) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rsize_classes_read)).
Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).
Definition rmrep_transport_high : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_transport_high) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_transport_high)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmrep_active_read : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_active_read) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_active_read)).
Definition rmrep_usage_read : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_usage_read) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_usage_read)).
Definition rmrep_bounces_read : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_bounces_read) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_bounces_read)).
Definition rmeta_slot_bounds : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmeta_slot_bounds) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmeta_slot_bounds)).

Ltac rmeta_chunk MR MSq CH :=
pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
rewrite ?get_meta_rec_put_same in CH;
rewrite ?conc_put_meta, ?pw_put_meta in CH;
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta_word meta0
m_set_prev m_set_next m_set_mem m_set_avail m_set_freed Z.mul Z.add] in CH;
rewrite ?meta_word_meta0 in CH; unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.

Definition rconc_meta_inj : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq9.rconc_meta_inj) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq9.rconc_meta_inj)).

#[using="RGOT_SSP e_197bc RATP RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_6 E_6 D_7 E_7 D_26 E_26 D_27 E_27 D_31 E_31 D_32 E_32 D_93 E_93 D_94 E_94 D_245 E_245 ANCH_7 ANCH_27 ANCH_32 ANCH_94 LINK_245 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ meta_word_sc2 meta_word_pg"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

Section POST.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (st : mstate) (g : aptr) (i : Z) (m1 : word -> option byte).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -96)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation G28 := (Z_to_bv 64 (conc st g + 28)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Local Notation HD := (pw st (active st sc)).
Local Notation GUARD := (Z_to_bv 64 (RATP + 131696)).
Local Notation CTXW := (Z_to_bv 64 (RATP + 131968)).
Local Notation PHEAD := (Z_to_bv 64 ((RATP + 131968) + sc * 8)).
Definition RAT (pc : Z) (R : bvmap 5 word) (ms' : machine_state) : Prop := ms' = MS R F (Z_to_bv 64 pc) fc None m1 (seg_rom segs).

Definition rentry_cases (ms' : machine_state) : Prop :=

(ntf_cond st g i = false /\ mask <> 0 /\
exists t0 t1 t2 a0 a2 a3 a5 a6 a7 s2x t3 t4 t5 t6,
RAT (base + 0x380) (mkR ra sp' gp tp t0 t1 t2 s0 GUARD a0 SELF a2 a3 G28 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
\/
(ntf_cond st g i = false /\ mask = 0 /\
exists t0 t1 t2 a3 a5 a6 a7 s2x t3 t4 t5 t6,
RAT (base + 0x164) (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) a3 G28 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
\/
(ntf_cond st g i = true /\ m_next mr = None /\
exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
RAT (base + 0x228) (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G a1 a2 a3 a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
\/
(ntf_cond st g i = true /\ m_next mr = Some g /\ sc < 48 /\
exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
RAT (base + 0x1bc) (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G PHEAD HD a3 a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
\/
(ntf_cond st g i = true /\ sc < 48 /\
exists nx, m_next mr = Some nx /\ nx <> g /\
exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6,
RAT (base + 0x138) (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G PHEAD HD (Z_to_bv 64 (conc st nx)) a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms').
End POST.

Definition rentry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(st : mstate) (g : aptr) (i lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists m1 junk,
rentry_cases ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i m1 ms'
/\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 /\ wmono segs m m1 /\ mem_inv segs m1
/\ stk segs m1 lo (bv_unsigned sp + -96)
/\ rw_cells segs m1 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra)
/\ rmrep st m1.

#[using="Type"] Lemma meta_word_sc52 mr : mw_ok mr ->
Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (meta_word mr) 52))) 58 = m_sizeclass mr.
Proof. clear - mr.
intros MW. pose proof (meta_word_range mr MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold meta_word.
replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr) * 2 ^ 52)
with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2^52 + m_maplen mr * 2^64) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2 ^ 52) with ((m_last_idx mr + 32 * m_freeable mr) * 2^52 + m_sizeclass mr * 2^58) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

#[using="Type"] Lemma meta_word_mod32 mr : mw_ok mr -> meta_word mr mod 32 = m_last_idx mr.
Proof. clear - mr.
intros MW. pose proof MW as (LI & FB & SCR & ML). unfold meta_word.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Section ENTRY.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : word -> option byte) (st : mstate) (g : aptr) (i lo : Z).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation maskw := (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr))).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -96)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Local Notation GUARD := (Z_to_bv 64 (RATP + 131696)).
Local Notation CTXW := (Z_to_bv 64 (RATP + 131968)).
Local Notation POST := (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i lo m).

Hypothesis EH : entry_hyps st g i.
Hypothesis MI0 : mem_inv segs m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - 96.

Definition rmid_ctx (m1 : word -> option byte) (junk : list byte) : Prop :=
munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 /\ wmono segs m m1 /\ mem_inv segs m1
/\ stk segs m1 lo (bv_unsigned sp + -96) /\ rw_cells segs m1 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra) /\ rmrep st m1.

#[using="i EH"] Lemma rmaskw_zero : maskw = 0 <-> mask = 0.
Proof. clear - i EH ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st g lo MI0 LO LOLE. first [clear LOLE | gw_hide LOLE | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear MI0 | gw_hide MI0 | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear g | gw_hide g | idtac]; first [clear st | gw_hide st | idtac]; first [clear m | gw_hide m | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]. apply lor_sxv_zero; [apply (eh_freed _ _ _ EH) | apply (eh_avail _ _ _ EH)]. Qed.
#[using="Type"] Lemma rmaskw_range : 0 <= maskw < 2^64.
Proof. clear - ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st g i lo EH MI0 LO LOLE. first [clear LOLE | gw_hide LOLE | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear MI0 | gw_hide MI0 | idtac]; first [clear EH | gw_hide EH | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear i | gw_hide i | idtac]; first [clear g | gw_hide g | idtac]; first [clear st | gw_hide st | idtac]; first [clear m | gw_hide m | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]. apply lor_range64; apply sxv_range. Qed.

Ltac rpost_common MU WM MI ST FR MR m1 junk :=
apply evt_done; exists m1, junk; split; [| exact (conj MU (conj WM (conj MI (conj ST (conj FR MR)))))].

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 CODE LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved EH"] Lemma rntf_notall : forall (t0 t1 t2 a4 a5 a6 a7 s2x t3 t4 t5 t6 : word) m1 junk,
rmid_ctx m1 junk -> ntf_cond st g i = false ->
evt segs POST
(MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) a4 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x15c)) fc None m1 (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 CODE LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved EH segs base RATP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st g i lo MI0 LO LOLE. gw_expose_fam RATP. first [clear LOLE | gw_hide LOLE | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear MI0 | gw_hide MI0 | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear i | gw_hide i | idtac]; try gw_hide g; try gw_hide st; first [clear m | gw_hide m | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac].
intros until junk. intros (MU & WM & MI & ST & FR & MR) HC.
pose proof rmaskw_range as MWR'. pose proof rmaskw_zero as MZ.
pose proof (rmeta_slot_bounds st m1 g MR (eh_slot _ _ _ EH)) as (GB0 & GB1 & GB2 & _). unfold alloc_ceiling in *.
st1. rewrite ?(unsigned_lit (conc st g)) by lia.
st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; unmask64 K.
-
rpost_common MU WM MI ST FR MR m1 junk.
left. split; [gw_exact HC|]. split; [intros E; apply K, MZ, E|].
do 14 eexists. (gw_expose_fam RATP; unfold RAT). cbv delta [mkR]. reflexivity.
-
assert (M0 : mask = 0) by (apply MZ; lia).
rpost_common MU WM MI ST FR MR m1 junk.
right; left. split; [gw_exact HC|]. split; [gw_exact M0|].
do 12 eexists. (gw_expose_fam RATP; unfold RAT). cbv delta [mkR]. reflexivity.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 CODE LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 ROM_reservedZ LAY_ref_reserved EH"] Lemma rntf_fge : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m1 junk,
rmid_ctx m1 junk -> mask + bit i = mask_upto (m_last_idx mr) -> okay_to_free st g = true ->
evt segs POST
(MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x114)) fc None m1 (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 CODE LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 ROM_reservedZ LAY_ref_reserved EH segs base RATP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st g i lo MI0 LO LOLE. gw_expose_fam RATP. first [clear LOLE | gw_hide LOLE | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear MI0 | gw_hide MI0 | idtac]; first [clear lo | gw_hide lo | idtac]; try gw_hide i; try gw_hide g; try gw_hide st; first [clear m | gw_hide m | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac].
intros until junk. intros (MU & WM & MI & ST & FR & MR) HALL OKT.
pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
pose proof MW as (LI & FB & SCR & ML).
pose proof (rmeta_slot_bounds st m1 g MR MSL) as (GB0 & GB1 & GB2 & _).
(gw_expose_fam RATP; unfold alloc_ceiling in *).
assert (HALLb : (mask + bit i =? mask_upto (m_last_idx mr)) = true) by (apply Z.eqb_eq; gw_exact HALL).
assert (HC : ntf_cond st g i = true) by (rewrite ntf_cond_unfold, HALLb, OKT; reflexivity).
assert (NXW : forall nx, m_next mr = Some nx -> 0 < conc st nx /\ conc st nx < 2^64 /\ (conc st nx = conc st g -> nx = g)).
{ intros nx Hnx. pose proof (HNX nx Hnx) as MSn. pose proof (rmeta_slot_bounds st m1 nx MR MSn) as (B0 & B1 & _).
split; [lia|]. split; [lia|]. intros E. apply (rconc_meta_inj st m1 g nx MR MSL MSn). gw_exact E. }
rmeta_chunk MR MSL CH.

st1. clear CH.
destruct (m_next mr) as [nx|] eqn:NX; unfold pw; cbn [oconc]; unfold wz.
- destruct (NXW nx eq_refl) as (N0 & N1 & NINJ).
st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia. { exfalso. lia. }
specialize (G50 HC ltac:(congruence)).

st1. st1. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia. 2:{ exfalso. lia. }

st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1.
pose proof (rmrep_active_read st m1 sc (wa ((RATP + 132048) + 8 * sc)) MR ltac:(lia) eq_refl) as RDA. gw_expose_fam RATP.
replace (wa ((RATP + 132048) + 8 * sc)) with (Z_to_bv 64 ((RATP + 131968) + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
st1. clear RDA.

st1. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
+ pose proof (NINJ ltac:(lia)) as ->.
rpost_common MU WM MI ST FR MR m1 junk.
do 3 right; left. split; [gw_exact HC|]. split; [gw_exact NX|]. split; [lia|].
do 12 eexists. (gw_expose_fam RATP; unfold RAT). cbv delta [mkR]. reflexivity.
+ assert (NE : nx <> g) by (intros ->; apply K5; reflexivity).
rpost_common MU WM MI ST FR MR m1 junk.
do 4 right. split; [gw_exact HC|]. split; [lia|]. exists nx. split; [gw_exact NX|]. split; [gw_exact NE|].
do 11 eexists. (gw_expose_fam RATP; unfold RAT). cbv delta [mkR]. reflexivity.
- st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia. 2:{ exfalso. lia. }
rpost_common MU WM MI ST FR MR m1 junk.
do 2 right; left. split; [gw_exact HC|]. split; [gw_exact NX|].
do 14 eexists. (gw_expose_fam RATP; unfold RAT). cbv delta [mkR]. reflexivity.
Qed.

#[using="RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 hi_26 hi_31 lo_27 lo_32 CODE D_26 E_26 D_27 E_27 D_31 E_31 D_32 E_32 ANCH_27 ANCH_32 RNG_RDEBRUIJN LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved meta_word_sc2 meta_word_pg EH"] Lemma rntf_okchk : forall (t0 t1 t2 a4 a6 a7 t3 t4 t5 t6 : word) m1 junk,
rmid_ctx m1 junk -> mask + bit i = mask_upto (m_last_idx mr) -> m_freeable mr <> 0 ->
evt segs POST
(MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) a4 (Z_to_bv 64 (meta_word mr)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x64)) fc None m1 (seg_rom segs)).
Proof. clear - RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 hi_26 hi_31 lo_27 lo_32 CODE D_26 E_26 D_27 E_27 D_31 E_31 D_32 E_32 ANCH_27 ANCH_32 RNG_RDEBRUIJN LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved meta_word_sc2 meta_word_pg EH segs base RATP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st g i lo MI0 LO LOLE. gw_expose_fam RATP; gw_expose_fam RDEBRUIJN. first [clear LOLE | gw_hide LOLE | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear MI0 | gw_hide MI0 | idtac]; first [clear lo | gw_hide lo | idtac]; try gw_hide i; try gw_hide g; try gw_hide st; first [clear m | gw_hide m | idtac]; try gw_hide fc; try gw_hide F; try gw_hide s11; try gw_hide s10; try gw_hide s9; try gw_hide s8; try gw_hide s7; try gw_hide s6; try gw_hide s5; try gw_hide s4; try gw_hide s3; first [clear s2 | gw_hide s2 | idtac]; first [clear s1 | gw_hide s1 | idtac]; try gw_hide s0; try gw_hide tp; try gw_hide gp; try gw_hide sp; try gw_hide ra.
intros until junk. intros MC HALL FRNZ. pose proof MC as (MU & WM & MI & ST & FR & MR).
pose proof rmaskw_range as MWR'. pose proof rmaskw_zero as MZ.
pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
pose proof MW as (LI & FB & SCR & ML).
pose proof (meta_word_range _ MW) as MWR. pose proof (meta_word_lt4096 _ MW) as M4.
pose proof (rmeta_slot_bounds st m1 g MR MSL) as (GB0 & GB1 & GB2 & _).
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold alloc_ceiling in *.
assert (HALLb : (mask + bit i =? mask_upto (m_last_idx mr)) = true) by (apply Z.eqb_eq; gw_exact HALL).
assert (FRZ : (m_freeable mr =? 0) = false) by (apply Z.eqb_neq; lia).

st1. st1. st1.
st1. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
{
eapply (rntf_fge t0 t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
rewrite okf_unfold, FRZ. replace (48 <=? sc) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
assert (SC48 : sc < 48) by lia. clear K2.
assert (NB48 : (48 <=? sc) = false) by (apply Z.leb_gt; lia).
specialize (USG SC48).
pose proof (size_class_range sc ltac:(lia)) as SZ.
assert (RS' : ov_read_bytes segs m1 (Z_to_bv 64 ((RDEBRUIJN + 32) + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))).
{ replace (Z_to_bv 64 ((RDEBRUIJN + 32) + 2 * sc)) with (wa ((RDEBRUIJN + 32) + 2 * sc)) by ((gw_expose_fam RDEBRUIJN; unfold wa); f_equal; lia).
apply rsize_classes_read; [assumption| lia]. }

st1. rewrite (meta_word_last_idx _ MW). st1. rewrite (meta_word_maplen _ MW). st1. st1.

assert (K690 : forall (t0' : word),
m_maplen mr <> 0 ->
evt segs POST
(MS (mkR ra sp' gp tp t0' t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) (Z_to_bv 64 (m_last_idx mr)) (Z_to_bv 64 (get_stride mr)) (Z_to_bv 64 (RDEBRUIJN + 32)) (Z_to_bv 64 (m_maplen mr)) (Z_to_bv 64 (RATP + 131968)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xb8)) fc None m1 (seg_rom segs))).
{ intros t0' MLNZ.
assert (MLF : (m_maplen mr =? 0) = false) by (apply Z.eqb_neq; gw_exact MLNZ).
assert (GSR : 0 < get_stride mr < 2^64).
{ unfold get_stride. destruct (m_last_idx mr =? 0), (m_maplen mr =? 0); cbn [andb negb]; unfold UNIT; lia. }

st1. rewrite ?(unsigned_lit sc), ?(Z.shiftl_mul_pow2 sc 1) by lia. change (2 ^ 1) with 2. st1.
replace ((RDEBRUIJN + 32) + sc * 2) with ((RDEBRUIJN + 32) + 2 * sc) by lia.
st1. try rewrite (Z.mod_small (size_class sc)) by lia.
st1. rewrite ?(unsigned_lit (size_class sc)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.

st1. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
{ eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
rewrite okf_unfold, FRZ, NB48. cbn [orb].
replace (get_stride mr <? UNIT * size_class sc) with true by (symmetry; apply Z.ltb_lt; unfold UNIT; lia). reflexivity. }
assert (STRF : (get_stride mr <? UNIT * size_class sc) = false) by (apply Z.ltb_ge; unfold UNIT; lia).
assert (OKF : okay_to_free st g =
if negb (optr_eqb (m_next mr) (Some g)) then true
else if negb (is_bouncing sc st) then true
else if (9 * (m_last_idx mr + 1) <=? usage st sc) && (m_last_idx mr + 1 <? 20) then true else false).
{ rewrite okf_unfold, FRZ, NB48, STRF, MLF. reflexivity. }

rmeta_chunk MR MSL CH.
st1. clear CH.
assert (NXW : forall nx, m_next mr = Some nx -> 0 < conc st nx /\ conc st nx < 2^64 /\ (conc st nx = conc st g -> nx = g)).
{ intros nx Hnx. pose proof (HNX nx Hnx) as MSn. pose proof (rmeta_slot_bounds st m1 nx MR MSn) as (B0 & B1 & _).
split; [lia|]. split; [lia|]. intros E. apply (rconc_meta_inj st m1 g nx MR MSL MSn). gw_exact E. }
destruct (m_next mr) as [nx|] eqn:NX; unfold pw; cbn [oconc]; unfold wz.
2:{ st1. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia. 2:{ exfalso. lia. }
eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). rewrite OKF. reflexivity. }
destruct (NXW nx eq_refl) as (N0 & N1 & NINJ).
st1. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia.
{ assert (NE : nx <> g) by (intros ->; apply K6; reflexivity).
eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). rewrite OKF.
cbn [optr_eqb]. rewrite (aptr_eqb_neq nx g NE). reflexivity. }
pose proof (NINJ ltac:(lia)) as Enx. subst nx.
rewrite optr_eqb_refl in OKF. cbn [negb] in OKF.

st1. rewrite ?(unsigned_lit sc) by lia. st1.
st1. if_cases K7; zify_cond K7.
{ assert (NR : sc_in_seq_range sc = false) by (apply (proj1 (seq_range_test sc ltac:(lia))); gw_exact K7).
unfold is_bouncing in OKF. rewrite NR in OKF. cbn [andb negb] in OKF.
eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). gw_exact OKF. }
assert (SR : sc_in_seq_range sc = true).
{ destruct (sc_in_seq_range sc) eqn:E; [reflexivity|]. exfalso. apply (proj2 (seq_range_test sc ltac:(lia))) in E. lia. }
assert (SR' : 7 <= sc < 39).
{ unfold sc_in_seq_range in SR. apply andb_true_iff in SR. destruct SR as [Sa Sb]. apply Z.leb_le in Sa. apply Z.ltb_lt in Sb. lia. }
unfold is_bouncing in OKF. rewrite SR in OKF. cbn [andb] in OKF.

st1.
pose proof (rmrep_bounces_read st m1 (sc - 7) (wa ((RATP + 132848) + (sc - 7))) MR ltac:(lia) eq_refl) as RDB. (gw_expose_fam RATP; unfold wa in RDB).
pose proof (BND (sc - 7)) as BR.
replace (Z_to_bv 64 ((RATP + 132848) + (sc - 7))) with (Z_to_bv 64 ((RATP + 131968) + (sc + -7) + 880)) in RDB by (f_equal; lia).
st1. clear RDB. st1.
st1. if_cases K8; zify_cond K8; rewrite ?b8_unsigned, ?unsigned_lit in K8 by lia.
{ replace (100 <=? bounces st (sc - 7)) with false in OKF by (symmetry; apply Z.leb_gt; lia). cbn [negb] in OKF.
eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). gw_exact OKF. }
replace (100 <=? bounces st (sc - 7)) with true in OKF by (symmetry; apply Z.leb_le; lia). cbn [negb] in OKF.

st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1.
pose proof (rmrep_usage_read st m1 sc (wa ((RATP + 132432) + 8 * sc)) MR ltac:(lia) eq_refl) as RDU. gw_expose_fam RATP.
replace (wa ((RATP + 132432) + 8 * sc)) with (Z_to_bv 64 ((RATP + 131968) + sc * 8 + 464)) in RDU by (unfold wa; f_equal; lia).
st1. clear RDU.
st1. rewrite ?(unsigned_lit (m_last_idx mr)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1. st1.

st1. if_cases K9; zify_cond K9; rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia.
{ replace (9 * (m_last_idx mr + 1) <=? usage st sc) with false in OKF by (symmetry; apply Z.leb_gt; lia). cbn [andb] in OKF.
assert (HC : ntf_cond st g i = false) by (rewrite ntf_cond_unfold, HALLb, OKF; reflexivity).
eapply (rntf_notall _ t1 t2 _ _ _ _ _ t3 t4 t5 t6 m1 junk MC HC). }
replace (9 * (m_last_idx mr + 1) <=? usage st sc) with true in OKF by (symmetry; apply Z.leb_le; lia). cbn [andb] in OKF.

st1. st1. if_cases K10; zify_cond K10; rewrite ?unsigned_lit in K10 by lia.
- replace (m_last_idx mr + 1 <? 20) with false in OKF by (symmetry; apply Z.ltb_ge; lia).
assert (HC : ntf_cond st g i = false) by (rewrite ntf_cond_unfold, HALLb, OKF; reflexivity).
eapply (rntf_notall _ t1 t2 _ _ _ _ _ t3 t4 t5 t6 m1 junk MC HC).
- replace (m_last_idx mr + 1 <? 20) with true in OKF by (symmetry; apply Z.ltb_lt; lia).
eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). gw_exact OKF. }

assert (K678 :
(m_maplen mr = 0 \/ m_last_idx mr <> 0) ->
evt segs POST
(MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) (Z_to_bv 64 (m_last_idx mr)) (Z_to_bv 64 (meta_word mr)) (Z_to_bv 64 (RDEBRUIJN + 32)) (Z_to_bv 64 (m_maplen mr)) (Z_to_bv 64 (RATP + 131968)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xa0)) fc None m1 (seg_rom segs))).
{ intros COND.
assert (STR : get_stride mr = 16 * size_class sc).
{ unfold get_stride. destruct COND as [C|C]; [rewrite (proj2 (Z.eqb_eq _ _) C), andb_false_r; reflexivity|].
rewrite (proj2 (Z.eqb_neq _ _) C). reflexivity. }
assert (MW5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).

st1. st1. try rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite (meta_word_sc2 _ MW). st1.
st1. try rewrite (Z.mod_small (size_class sc)) by lia.
st1. rewrite ?(unsigned_lit (size_class sc)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.

st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
- eapply (rntf_fge t0 t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
rewrite okf_unfold, FRZ, NB48. cbn [orb].
replace (m_maplen mr =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
destruct (get_stride mr <? UNIT * size_class sc); reflexivity.
- replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 (get_stride mr)) by (rewrite STR; f_equal; lia).
apply K690. lia. }

st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
{ apply K678. left. lia. }

st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
{ apply K678. right. lia. }

st1. st1. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite land_pgmask by lia. rewrite (meta_word_pg _ MW). st1.
st1. if_cases Km2; zify_cond Km2; rewrite ?unsigned_lit in Km2 by lia. 2:{ exfalso. lia. }
replace (Z_to_bv 64 (4096 * m_maplen mr + -16)) with (Z_to_bv 64 (get_stride mr)).
2:{ unfold get_stride. rewrite (proj2 (Z.eqb_eq _ _) Kl). replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. f_equal. unfold UNIT. lia. }
apply K690. lia.
Qed.

#[using="RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 hi_6 hi_26 hi_31 lo_7 lo_27 lo_32 CODE D_6 E_6 D_7 E_7 D_26 E_26 D_27 E_27 D_31 E_31 D_32 E_32 ANCH_7 ANCH_27 ANCH_32 LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved meta_word_sc2 meta_word_pg EH MI0 LO LOLE"] Lemma rntf_entry : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
rmrep st m -> stk segs m lo (bv_unsigned sp) ->
evt segs POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 G (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof. clear - RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 hi_6 hi_26 hi_31 lo_7 lo_27 lo_32 CODE D_6 E_6 D_7 E_7 D_26 E_26 D_27 E_27 D_31 E_31 D_32 E_32 ANCH_7 ANCH_27 ANCH_32 LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved meta_word_sc2 meta_word_pg EH MI0 LO LOLE segs base RATP RGOT_SSP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st g i lo. gw_expose_fam RATP; gw_expose_fam RGOT_SSP. first [clear lo | gw_hide lo | idtac]; try gw_hide i; try gw_hide g; try gw_hide st; try gw_hide m; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; try gw_hide sp; first [clear ra | gw_hide ra | idtac].
intros until t6. intros MR ST.
pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
pose proof MW as (LI & FB & SCR & ML).
pose proof (meta_word_range _ MW) as MWR.
pose proof (rmeta_slot_bounds st m g MR MSL) as (GB0 & GB1 & GB2 & _).
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof rmaskw_range as MWR'.
pose proof MR as (_ & _ & (_ & _ & _ & G4 & G5) & _).
(gw_expose_fam RGOT_SSP; gw_expose_fam RATP; unfold alloc_ceiling in *). unfold wz in G4.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl segs m) as WM.

st1. carve_frame 96%nat ST. st1. st1. st1. st1. st1.

st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep st mX)
by (eapply rmrep_transport_high; [gw_exact MR | gw_exact MU | gw_exact WM | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
clear MR G4 G5.
lazymatch goal with H : rw_cells segs _ (bv_unsigned sp + -96) (CB 48 ?j :: _) |- _ => set (junk48 := j) in H; clearbody junk48; rename H into FR end.
rmeta_chunk MR1 MSL CH.

st1. st1. st1. rewrite ?sx32_wz_sxv by lia. st1.
st1. rewrite ?(unsigned_lit i) by lia. rewrite (sllw1_word i) by lia.
st1. rewrite ?(unsigned_lit (meta_word mr)) by lia.
st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
st1. rewrite (meta_word_freeable _ MW).
st1. rewrite (meta_word_sc52 _ MW).
clear CH.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MC : rmid_ctx mX junk48) by (split; [gw_exact MU|]; split; [gw_exact WM|]; split; [assumption|]; split; [gw_exact ST|]; split; [gw_exact FR|gw_exact MR1]) end.

st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
{ assert (HC : ntf_cond st g i = false).
{ rewrite ntf_cond_unfold, okf_unfold. replace (m_freeable mr =? 0) with true by (symmetry; apply Z.eqb_eq; lia). apply andb_false_r. }
eapply (rntf_notall t0 t1 t2 _ _ _ _ _ t3 t4 t5 t6 _ junk48 MC HC). }

st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite ?(unsigned_lit (Z.lor _ _)) by (apply lor_range64; apply sxv_range).
rewrite addw_word. replace (maskw + sxv (2 ^ i)) with (sxv (2 ^ i) + maskw) by lia.
st1. st1. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 _ MW).
st1. rewrite addiw_m1_word.

pose proof (sxv_range (sxv (2 ^ i) + maskw)) as R1. pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as R2.
st1. if_cases K2; zify_cond K2; rewrite ?wz_unsigned in K2 by (apply sxv_range).
- assert (HC : ntf_cond st g i = false).
{ rewrite ntf_cond_unfold. replace (mask + bit i =? mask_upto (m_last_idx mr)) with false; [reflexivity|].
symmetry. apply Z.eqb_neq. unfold bit, mask_upto. intros E. apply K2.
apply (proj2 (free_all_test (m_freed mr) (m_avail mr) i (m_last_idx mr) FRD AV HI ltac:(lia))). gw_exact E. }
eapply (rntf_notall t0 t1 t2 _ _ _ _ _ t3 t4 t5 t6 _ junk48 MC HC).
-
apply (proj1 (free_all_test (m_freed mr) (m_avail mr) i (m_last_idx mr) FRD AV HI ltac:(lia))) in K2.
eapply (rntf_okchk t0 t1 t2 _ _ _ t3 t4 t5 t6 _ junk48 MC); [unfold bit, mask_upto; gw_exact K2 | lia].
Qed.
End ENTRY.

End RC__1.

End G.
End Mqa.

Module Mqb.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import Qy8Z.Mq8.
Import QQRC.Mqa.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope bv_scope.
Open Scope Z_scope.

Definition errno_loc_code : list Z :=
[0x00020513; 0xf5c50513; 0x00008067]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rerrno_loc_entry rvm_wait_entry : Z).
Variables (w_15 w_59 w_62 w_67 w_70 w_145 w_147 w_185 w_238 : Z).
Variables (hi_59 hi_67 hi_145 : bv 20).
Variables (lo_62 lo_70 lo_147 : bv 12).
Variables (joff_15 joff_185 joff_238 : bv 21).
Variables (e_24f80 : Z).
Hypothesis CODE : code_at segs base (realloc_code w_15 w_59 w_62 w_67 w_70 w_145 w_147 w_185 w_238).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 1092.
Let rmremap_entry := (rvm_wait_entry + 312)%Z.
Hypothesis D_15 : decode_any (Z_to_bv 32 w_15) = Some (Jal 1 joff_15, 4%Z).
Hypothesis E_15 : is_ecall (Z_to_bv 32 w_15) = false.
Hypothesis D_59 : decode_any (Z_to_bv 32 w_59) = Some (Auipc 15 hi_59, 4%Z).
Hypothesis E_59 : is_ecall (Z_to_bv 32 w_59) = false.
Hypothesis D_62 : decode_any (Z_to_bv 32 w_62) = Some (Load SZ8 true 15 15 lo_62, 4%Z).
Hypothesis E_62 : is_ecall (Z_to_bv 32 w_62) = false.
Hypothesis D_67 : decode_any (Z_to_bv 32 w_67) = Some (Auipc 15 hi_67, 4%Z).
Hypothesis E_67 : is_ecall (Z_to_bv 32 w_67) = false.
Hypothesis D_70 : decode_any (Z_to_bv 32 w_70) = Some (OpImm ALU_ADD 15 15 lo_70, 4%Z).
Hypothesis E_70 : is_ecall (Z_to_bv 32 w_70) = false.
Hypothesis D_145 : decode_any (Z_to_bv 32 w_145) = Some (Auipc 6 hi_145, 4%Z).
Hypothesis E_145 : is_ecall (Z_to_bv 32 w_145) = false.
Hypothesis D_147 : decode_any (Z_to_bv 32 w_147) = Some (OpImm ALU_ADD 6 6 lo_147, 4%Z).
Hypothesis E_147 : is_ecall (Z_to_bv 32 w_147) = false.
Hypothesis D_185 : decode_any (Z_to_bv 32 w_185) = Some (Jal 1 joff_185, 4%Z).
Hypothesis E_185 : is_ecall (Z_to_bv 32 w_185) = false.
Hypothesis D_238 : decode_any (Z_to_bv 32 w_238) = Some (Jal 1 joff_238, 4%Z).
Hypothesis E_238 : is_ecall (Z_to_bv 32 w_238) = false.
Hypothesis ANCH_62 : gw_anch (Z.shiftl (bv_signed hi_59) 12 + (base + 236) + bv_signed lo_62)%Z (RATP + 131968).
Hypothesis ANCH_70 : gw_anch (Z.shiftl (bv_signed hi_67) 12 + (base + 268) + bv_signed lo_70)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_147 : gw_anch (Z.shiftl (bv_signed hi_145) 12 + (base + 580) + bv_signed lo_147)%Z RDEBRUIJN.
Hypothesis LINK_15 : gw_anch (base + 60 + bv_signed joff_15)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_185 : gw_anch (base + 740 + bv_signed joff_185)%Z (rmremap_entry + 0)%Z.
Hypothesis LINK_238 : gw_anch (base + 952 + bv_signed joff_238)%Z (e_24f80 + 0)%Z.
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
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis AL_rerrno_loc_entry : gw_al rerrno_loc_entry 4.
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Hypothesis rdbi_range : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qy8Z.Mq8.gw_all) (@Qy8Z.Mq8.rdbi_range) (base + -3804)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_0))) in let T := gw_fold_pcs T base (-3804)%Z [0; 116; 472; 500; 524]%Z in exact T).
Hypothesis rdebruijn_read : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qy8Z.Mq8.gw_all) (@Qy8Z.Mq8.rdebruijn_read) (base + -3804)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_0))) in let T := gw_fold_pcs T base (-3804)%Z [0; 116; 472; 500; 524]%Z in exact T).
Hypothesis mul_srliw27 : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qy8Z.Mq8.gw_all) (@Qy8Z.Mq8.mul_srliw27) (base + -3804)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_0))) in let T := gw_fold_pcs T base (-3804)%Z [0; 116; 472; 500; 524]%Z in exact T).
Hypothesis rclz_pow_eq : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qy8Z.Mq8.gw_all) (@Qy8Z.Mq8.rclz_pow_eq) (base + -3804)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_0))) in let T := gw_fold_pcs T base (-3804)%Z [0; 116; 472; 500; 524]%Z in exact T).
Hypothesis lxor_4k_124 : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qy8Z.Mq8.gw_all) (@Qy8Z.Mq8.lxor_4k_124) (base + -3804)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_0))) in let T := gw_fold_pcs T base (-3804)%Z [0; 116; 472; 500; 524]%Z in exact T).
Hypothesis lor_even_1 : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qy8Z.Mq8.gw_all) (@Qy8Z.Mq8.lor_even_1) (base + -3804)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_0))) in let T := gw_fold_pcs T base (-3804)%Z [0; 116; 472; 500; 524]%Z in exact T).

Definition rsize_classes_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rsize_classes_read) constr:(gw_tbl_0)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rsize_classes_read)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_0)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

#[using="RDEBRUIJN rerrno_loc_entry rmremap_entry e_24f80 RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry CODE BASE4 BASER D_15 E_15 D_59 E_59 D_62 E_62 D_67 E_67 D_70 E_70 D_145 E_145 D_147 E_147 D_185 E_185 D_238 E_238 ANCH_62 ANCH_70 ANCH_147 LINK_15 LINK_185 LINK_238 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rmremap_entry rdbi_range rdebruijn_read mul_srliw27 rclz_pow_eq lxor_4k_124 lor_even_1"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

#[using="rvm_wait_entry w_15 w_59 w_62 w_67 w_70 w_145 w_147 w_185 w_238 hi_145 lo_147 CODE D_145 E_145 D_147 E_147 ANCH_147 RNG_RDEBRUIJN ROM_RSIZE_CLASSES rdbi_range rdebruijn_read mul_srliw27 rclz_pow_eq lxor_4k_124 lor_even_1 rmremap_entry"] Lemma rr_s2c_walk : forall (x1 x2 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m0 : mem) (n : Z) Q,
a1 = Z_to_bv 64 n -> 0 <= n < MMAP_THRESHOLD -> mem_inv segs m0 ->
(forall a4v a5v a7v t1v,
evt segs Q (MS (mkR x1 x2 gp tp t0 t1v t2 s0 s1 a0 a1 (Z_to_bv 64 (size_to_class n + 1)) a3 a4v a5v a6 a7v s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x388)) fc None m0 (seg_rom segs))) ->
evt segs Q (MS (mkR x1 x2 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 (Z_to_bv 64 (RDEBRUIJN + 32)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x1f8)) fc None m0 (seg_rom segs)).
Proof. clear - rvm_wait_entry w_15 w_59 w_62 w_67 w_70 w_145 w_147 w_185 w_238 hi_145 lo_147 CODE D_145 E_145 D_147 E_147 ANCH_147 RNG_RDEBRUIJN ROM_RSIZE_CLASSES rdbi_range rdebruijn_read mul_srliw27 rclz_pow_eq lxor_4k_124 lor_even_1 rmremap_entry segs base RDEBRUIJN. gw_expose_fam RDEBRUIJN.
intros until Q. intros HA N MI K. subst a1.
pose proof (size_to_class_props n N) as (SCR & SFIT & LG). unfold MMAP_THRESHOLD in N. gw_expose_fam RDEBRUIJN.

step. step. step.
rewrite (unsigned_lit (n + 3)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
set (q := (n + 3) / 16) in *. assert (QR : 0 <= q < 8191) by (subst q; Z.div_mod_to_equations; lia).
assert (STC : size_to_class n = stc_q q) by (apply size_to_class_q; lia).

assert (J0 : forall a4v a5v a7v t1v,
evt segs Q (MS (mkR x1 x2 gp tp t0 t1v t2 s0 s1 a0 (Z_to_bv 64 n) (Z_to_bv 64 (size_to_class n)) a3 a4v a5v a6 a7v s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x384)) fc None m0 (seg_rom segs))).
{ intros a4v a5v a7v t1v. step. rewrite (unsigned_lit (size_to_class n)) by lia.
rewrite swrap32_small by lia. apply K. }
step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit n) in K2 by lia.
-
replace (Z_to_bv 64 q) with (Z_to_bv 64 (size_to_class n)).
2:{ f_equal. rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; subst q; Z.div_mod_to_equations; lia). reflexivity. }
apply J0.
-
assert (Q10 : 10 <= q) by (subst q; Z.div_mod_to_equations; lia).
step. rewrite ?(unsigned_lit q) by lia. set (x := q + 1) in *. assert (XR : 11 <= x < 8192) by lia.
destruct (rclz_pow_eq x XR) as [PW RV4].

step.
step. rewrite (unsigned_lit x), srliw_small by lia.
pose proof (shiftr_small 13 x 1 ltac:(lia) ltac:(lia)) as R1. pose proof (shiftr_small 13 x 2 ltac:(lia) ltac:(lia)) as R2.
step. rewrite (unsigned_lit (Z.shiftr x 2)), (unsigned_lit x) by lia.
set (v1 := Z.lor (Z.shiftr x 2) x). assert (RX : 0 <= x < 2 ^ 13) by lia. pose proof (lor_small 13 _ _ ltac:(lia) R2 RX) as RV1. fold v1 in RV1.
step. rewrite (unsigned_lit x), srliw_small by lia.
step. rewrite (unsigned_lit v1), (unsigned_lit (Z.shiftr x 1)) by lia.
set (v2 := Z.lor v1 (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) RV1 R1) as RV2. fold v2 in RV2.

step. rewrite (unsigned_lit v2), srliw_small by lia. pose proof (shiftr_small 13 v2 2 RV2 ltac:(lia)) as R3.
step. rewrite (unsigned_lit (Z.shiftr v2 2)), (unsigned_lit (Z.shiftr x 1)) by lia.
set (w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) R3 R1) as RW2. fold w2 in RW2.

step. rewrite (unsigned_lit w2) by lia. pose proof (shiftr_small 13 w2 4 RW2 ltac:(lia)) as R4.
step. rewrite (unsigned_lit (Z.shiftr w2 4)), (unsigned_lit w2) by lia.
set (w3 := Z.lor (Z.shiftr w2 4) w2). pose proof (lor_small 13 _ _ ltac:(lia) R4 RW2) as RW3. fold w3 in RW3.

step. rewrite (unsigned_lit w3) by lia. pose proof (shiftr_small 13 w3 8 RW3 ltac:(lia)) as R5.
step. rewrite (unsigned_lit (Z.shiftr w3 8)), (unsigned_lit w3) by lia.
set (w4 := Z.lor (Z.shiftr w3 8) w3). pose proof (lor_small 13 _ _ ltac:(lia) R5 RW3) as RW4. fold w4 in RW4.
assert (EW4 : w4 = rclz_v4 x) by first [reflexivity | (cbn; lia)].

step. step. rewrite ?(unsigned_lit w4) by lia.
step. rewrite ?(unsigned_lit (w4 + 1)) by lia. rewrite (unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (rclz_pow x). rewrite PW.
set (k := Z.log2 x) in *.
assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
assert (EK : k = Z.log2 x) by first [reflexivity | (cbn; lia)]. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
assert (EX : x = q + 1) by first [reflexivity | (cbn; lia)]. clearbody x.
assert (K13 : 3 <= k <= 12) by (apply LG; lia).

step. step. step.
step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
step. rewrite (mul_srliw27 k) by lia.
pose proof (rdbi_range k) as DR.
step. rewrite ?(unsigned_lit (rdbi k)) by lia.
pose proof (rdebruijn_read m0 k MI ltac:(lia)) as DBR; gw_expose_fam RDEBRUIJN.
step. rewrite ?zxb_b8 by lia. clear DBR.

step. rewrite (wz_unsigned k), (Z.shiftl_mul_pow2 k) by lia. change (2 ^ 2) with 4.
step. rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
replace (124 - 4 * k) with (120 - i) by lia.
assert (STQ : stc_q q = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
{ unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
clearbody i. clear EK.
pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.
step. step. rewrite (unsigned_lit (120 - i)) by lia. replace (121 + - (120 - i)) with (i + 1) by lia.
step. rewrite (unsigned_lit (i + 1)), (Z.shiftl_mul_pow2 (i + 1)) by lia. change (2 ^ 1) with 2.
step. replace ((RDEBRUIJN + 32) + (i + 1) * 2) with ((RDEBRUIJN + 32) + 2 * (i + 1)) by lia.
pose proof (rsize_classes_read m0 (i + 1) MI ltac:(lia)) as RS1; gw_expose_fam RDEBRUIJN.
step. rewrite ?zx16_wz by lia. clear RS1.

assert (J1 : forall (i1 c : Z) t1v,
i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
evt segs Q
(MS (mkR x1 x2 gp tp t0 t1v t2 s0 s1 a0 (Z_to_bv 64 n) (Z_to_bv 64 q) a3 (Z_to_bv 64 (120 - i)) (Z_to_bv 64 (RDEBRUIJN + 32)) a6 (Z_to_bv 64 c)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x368)) fc None m0 (seg_rom segs))).
{ intros i1 c t1v Hi1 Hc.
assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
{ subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
destruct I1R as [I1R I1E].
pose proof (size_class_range i1 ltac:(lia)) as SR2.

step. rewrite ?(unsigned_lit c), ?(unsigned_lit (120 - i)) by lia. replace (c + - (120 - i)) with i1 by lia.
step. rewrite (unsigned_lit i1), (Z.shiftl_mul_pow2 i1) by lia. change (2 ^ 1) with 2.
step. replace ((RDEBRUIJN + 32) + i1 * 2) with ((RDEBRUIJN + 32) + 2 * i1) by lia.
pose proof (rsize_classes_read m0 i1 MI ltac:(lia)) as RS2. gw_expose_fam RDEBRUIJN.
step. rewrite ?zx16_wz by lia. clear RS2.

step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
step. step.
destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
* rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
replace (Z_to_bv 64 i1) with (Z_to_bv 64 (size_to_class n)).
2:{ f_equal. rewrite STC, STQ. cbv zeta. rewrite <- Hi1. replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
apply J0.
* rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
replace (Z_to_bv 64 (i1 + 1)) with (Z_to_bv 64 (size_to_class n)).
2:{ f_equal. rewrite STC, STQ. cbv zeta. rewrite <- Hi1. replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
apply J0. }
step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K3 by lia.
+
step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
+
step. step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.

Definition cond_inplace (n avail sc : Z) : bool := (n <=? avail) && (n <? MMAP_THRESHOLD) && (sc <=? size_to_class n + 1).
Definition cond_mremap (n sc : Z) : bool := (48 <=? sc) && (MMAP_THRESHOLD <=? n).

#[using="rvm_wait_entry w_15 w_59 w_62 w_67 w_70 w_145 w_147 w_185 w_238 hi_145 lo_147 CODE D_145 E_145 D_147 E_147 ANCH_147 RNG_RDEBRUIJN ROM_RSIZE_CLASSES rdbi_range rdebruijn_read mul_srliw27 rclz_pow_eq lxor_4k_124 lor_even_1 rmremap_entry"] Lemma rr_branch : forall (ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 t2 t3 t4 : word) F fc (m0 : mem)
(G B sc mword stride idx E rsv n : Z) Q,
a1 = Z_to_bv 64 n -> 0 <= n < 2^64 -> 0 <= sc < 64 -> 0 <= bv_unsigned a0 <= E -> E < 2^64 -> mem_inv segs m0 ->

(cond_inplace n (E - bv_unsigned a0) sc = true ->
forall a2v a4v a5v a7v t1v t2v t3v t4v,
evt segs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) t1v t2v s0 (wz G)
a0 a1 a2v (Z_to_bv 64 sc) a4v a5v (Z_to_bv 64 (E + 4)) a7v
(Z_to_bv 64 (E - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4v t5 t6)
F (Z_to_bv 64 (base + 0x3cc)) fc None m0 (seg_rom segs))) ->

(cond_inplace n (E - bv_unsigned a0) sc = false -> cond_mremap n sc = false ->
forall a2v a4v a5v a7v t1v t2v t3v t4v,
evt segs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) t1v t2v s0 (wz G)
a0 a1 a2v (Z_to_bv 64 sc) a4v a5v (Z_to_bv 64 (E + 4)) a7v
(Z_to_bv 64 (E - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4v t5 t6)
F (Z_to_bv 64 (base + 0x38c)) fc None m0 (seg_rom segs))) ->

(cond_inplace n (E - bv_unsigned a0) sc = false -> cond_mremap n sc = true ->
forall t2v t3v,
evt segs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) (Z_to_bv 64 (E + 4 - stride)) t2v s0 (wz G)
a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 48) (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - bv_unsigned a0))
(Z_to_bv 64 (E - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4 t5 t6)
F (Z_to_bv 64 (base + 0x298)) fc None m0 (seg_rom segs))) ->
evt segs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) (Z_to_bv 64 (E + 4 - stride)) t2 s0 (wz G)
a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 (RDEBRUIJN + 32)) (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - bv_unsigned a0))
(Z_to_bv 64 (E - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x1e8)) fc None m0 (seg_rom segs)).
Proof. clear - rvm_wait_entry w_15 w_59 w_62 w_67 w_70 w_145 w_147 w_185 w_238 hi_145 lo_147 CODE D_145 E_145 D_147 E_147 ANCH_147 RNG_RDEBRUIJN ROM_RSIZE_CLASSES rdbi_range rdebruijn_read mul_srliw27 rclz_pow_eq lxor_4k_124 lor_even_1 rmremap_entry segs base RDEBRUIJN. gw_expose_fam RDEBRUIJN.
intros until Q. intros HA N SC PE EHI MI KIN KGEN KMR.
pose proof (bv_unsigned_in_range 64 a0) as A0R.

assert (KD4 : MMAP_THRESHOLD <= n \/ E - bv_unsigned a0 < n ->
forall t3v,
evt segs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) (Z_to_bv 64 (E + 4 - stride)) (Z_to_bv 64 0x20000) s0 (wz G)
a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 (RDEBRUIJN + 32)) (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - bv_unsigned a0))
(Z_to_bv 64 (E - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4 t5 t6)
F (Z_to_bv 64 (base + 0x288)) fc None m0 (seg_rom segs))).
{ intros HC t3v.
assert (NI : cond_inplace n (E - bv_unsigned a0) sc = false).
{ unfold cond_inplace, MMAP_THRESHOLD in *. destruct HC as [HC|HC].
- replace (n <? 131052) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r. reflexivity.
- replace (n <=? E - bv_unsigned a0) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }

step. step. if_cases K1; zify_cond K1; rewrite ?HA, ?unsigned_lit in K1 by lia.
- apply KGEN; [gw_exact NI|]. unfold cond_mremap, MMAP_THRESHOLD. replace (131052 <=? n) with false by (symmetry; apply Z.leb_gt; lia). apply andb_false_r.
-
step. step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
+ apply KGEN; [gw_exact NI|]. unfold cond_mremap. replace (48 <=? sc) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
+ apply KMR; [gw_exact NI|]. unfold cond_mremap, MMAP_THRESHOLD. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }

step. step. step. if_cases K1; zify_cond K1; rewrite ?HA, ?unsigned_lit in K1 by lia.
{ apply KD4. left. unfold MMAP_THRESHOLD. lia. }

step. if_cases K2; zify_cond K2; rewrite ?HA, ?unsigned_lit in K2 by lia.
{ apply KD4. right. lia. }

eapply rr_s2c_walk; [gw_exact HA| unfold MMAP_THRESHOLD; lia| gw_exact MI|].
intros a4v a5v a7v t1v.
pose proof (size_to_class_props n ltac:(unfold MMAP_THRESHOLD; lia)) as (SCR & _ & _).

step. if_cases K3; zify_cond K3.
- rewrite ?signed_wz_small in K3 by lia.
apply KIN. unfold cond_inplace, MMAP_THRESHOLD. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
- rewrite ?signed_wz_small in K3 by lia.
apply KGEN.
+ unfold cond_inplace. replace (sc <=? size_to_class n + 1) with false by (symmetry; apply Z.leb_gt; lia). apply andb_false_r.
+ unfold cond_mremap, MMAP_THRESHOLD. replace (131052 <=? n) with false by (symmetry; apply Z.leb_gt; lia). apply andb_false_r.
Qed.

End RC__1.

End G.
End Mqb.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlQE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlQE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8P7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export Q8P7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBeb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export QBeb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8QT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8QT.Mq4.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen GwCallee GwApply GwFold.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G Require Import GwFamMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
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

#[using="RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Notation RAMpre := (@AMpre_g ref_reserved rc_secret).
Import Q6q3.
Section RC__1.

Section PURE.
Variable st : mstate.
Hypothesis AMP : RAMpre st.

#[using="AMP"] Lemma rAMpre_init : RAMpre (am_init_st st).
Proof. clear - AMP st. try gw_hide st.
unfold am_init_st. destruct (c_init_done (ctx st) =? 0); [| gw_exact AMP].
destruct AMP as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17]. split; cbn; try assumption.
- rewrite A3. gw_exact rc_secret_range.
- right; reflexivity.
- destruct A8 as [L1 L2 L3 L4]. split; cbn; assumption.
Qed.

#[using="Type"] Lemma ram_init_regions : s_regions (am_init_st st) = s_regions st.
Proof. clear - ROM_reservedZ st AMP. try clear ROM_reservedZ. first [clear AMP | gw_hide AMP | idtac]; try gw_hide st. unfold am_init_st. destruct (c_init_done (ctx st) =? 0); reflexivity. Qed.
#[using="Type"] Lemma ram_init_brk : c_brk (ctx (am_init_st st)) = c_brk (ctx st).
Proof. clear - ROM_reservedZ st AMP. try clear ROM_reservedZ. first [clear AMP | gw_hide AMP | idtac]; try gw_hide st. unfold am_init_st. destruct (c_init_done (ctx st) =? 0); reflexivity. Qed.
#[using="Type"] Lemma ram_init_conc q : conc (am_init_st st) q = conc st q.
Proof. clear - q ROM_reservedZ st AMP. try clear ROM_reservedZ. first [clear AMP | gw_hide AMP | idtac]; first [clear st | gw_hide st | idtac]. unfold conc, get_region. rewrite ram_init_regions. reflexivity. Qed.

#[using="ref_reserved RC__ AMP"] Lemma rAMI_init : AMI st (am_init_st st).
Proof. clear - ref_reserved RC__ AMP st. try gw_hide st.
unfold am_init_st. destruct (c_init_done (ctx st) =? 0);
(split; [ repeat split; reflexivity | | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| intros rid r Hr; exists r; repeat split; auto; lia
| intros rid r' H1 H2; cbn in H1; congruence
| cbn; lia
| intros P _ HP; gw_exact HP || (destruct HP as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10); repeat split; assumption)
| intros rid Hrid; apply (proj2 (amp_ptrs st AMP)); gw_exact Hrid
| exact (amp_rpos st AMP) ]).
- cbn. rewrite (amp_s_secret st AMP). gw_exact rc_secret_range.
- exact (amp_secret st AMP).
Qed.

#[using="Type"] Lemma rptrs_in_upd_ctx (P : N -> Prop) st0 f :
optr_in P (c_free_meta_head (f (ctx st0))) -> optr_in P (c_avail_meta (f (ctx st0))) ->
optr_in P (c_meta_area_head (f (ctx st0))) -> optr_in P (c_meta_area_tail (f (ctx st0))) ->
optr_in P (c_avail_meta_areas (f (ctx st0))) -> c_active (f (ctx st0)) = c_active (ctx st0) ->
match c_brk (f (ctx st0)) with BrkLive rid _ => P rid | _ => True end ->
ptrs_in P st0 -> ptrs_in P (upd_ctx f st0).
Proof. clear - P st0 f ROM_reservedZ st AMP. try clear ROM_reservedZ. first [clear AMP | gw_hide AMP | idtac]; first [clear st | gw_hide st | idtac].
intros E1 E2 E3 E4 E5 E6 E7 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
unfold ptrs_in, ctx, active in *. cbn [s_ctx upd_ctx s_metas s_areas s_groups] in *.
rewrite E6.
split; [gw_exact E1|]. split; [gw_exact E2|]. split; [gw_exact E3|]. split; [gw_exact E4|]. split; [gw_exact E5|].
split; [gw_exact H6|]. split; [gw_exact E7|]. split; [|split; [gw_exact H9| gw_exact H10]].
intros g. exact (H8 g).
Qed.

#[using="Type"] Lemma ram_rel_final stX st1 mo :
AMI st stX ->
c_active (ctx st1) = c_active (ctx stX) -> c_usage (ctx st1) = c_usage (ctx stX) -> c_unmap_seq (ctx st1) = c_unmap_seq (ctx stX) ->
c_bounces (ctx st1) = c_bounces (ctx stX) -> c_seq (ctx st1) = c_seq (ctx stX) -> c_mmap_counter (ctx st1) = c_mmap_counter (ctx stX) ->
s_groups st1 = s_groups stX -> s_slots st1 = s_slots stX -> s_shadow st1 = s_shadow stX -> s_tick st1 = s_tick stX ->
s_reserved st1 = s_reserved stX -> s_regions st1 = s_regions stX -> s_next_rid st1 = s_next_rid stX ->
(forall a, is_Some ((s_areas stX) !! a) -> is_Some ((s_areas st1) !! a)) ->
(forall g, Some g <> mo -> (m_mem (get_meta_rec st g) <> None \/ m_next (get_meta_rec st g) = None) -> get_meta_rec st1 g = get_meta_rec stX g) ->
(forall m, mo = Some m -> get_meta_rec st1 m = meta0 /\ meta_slot st1 m) ->
(forall P : N -> Prop, (forall rid r, (s_regions stX) !! rid = Some r -> r_kind r <> RKGroup -> P rid) -> ptrs_in P stX -> ptrs_in P st1) ->
am_rel st st1 mo.
Proof. clear - stX st1 mo ROM_reservedZ st AMP. try clear ROM_reservedZ. first [clear AMP | gw_hide AMP | idtac]; first [clear st | gw_hide st | idtac].
intros AI E1 E2 E3 E4 E5 E6 EG ESl ESh ET ERs ER EN HA HM HR HP.
destruct AI as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
split.
- intros sc. unfold active. rewrite E1, C7. reflexivity.
- intros sc. unfold usage. rewrite E2, C8. reflexivity.
- intros i. unfold bounces. rewrite E4, C10. reflexivity.
- intros i. unfold unmap_seq. rewrite E3, C9. reflexivity.
- rewrite E5, C11. reflexivity.
- rewrite E6, C1. reflexivity.
- rewrite EG, XG. reflexivity.
- rewrite ESl, XS. reflexivity.
- rewrite ESh, XSH. reflexivity.
- rewrite ET, XT. reflexivity.
- rewrite ERs, XR. reflexivity.
- intros g Hg Hm. rewrite (HM g Hg Hm). unfold get_meta_rec. rewrite XM. reflexivity.
- gw_exact HR.
- intros rid r Hr. rewrite ER. exact (XREG rid r Hr).
- intros rid r' H1 H2. rewrite ER in H1. exact (XNEW rid r' H1 H2).
- rewrite EN. gw_exact XNX.
- intros a Ha. apply HA. rewrite XA. gw_exact Ha.
- intros P HPn HP0. apply HP; [intros rid r Hr Hk; apply (HPn rid r); [rewrite ER|]; assumption|].
apply XP; [| gw_exact HP0]. intros rid r Hr Hk. apply (HPn rid r); [rewrite ER|]; assumption.
- intros rid Hrid. rewrite ER, ESh, XSH. rewrite EN in Hrid. destruct (XF rid Hrid) as [A B]. split; [gw_exact A| reflexivity].
Qed.

#[using="Type"] Lemma ram_rel_none stX : AMI st stX -> am_rel st stX None.
Proof. clear - stX ROM_reservedZ st AMP. try clear ROM_reservedZ. first [clear AMP | gw_hide AMP | idtac]; first [clear st | gw_hide st | idtac].
intros AI. eapply (ram_rel_final stX stX None AI); try reflexivity; auto.
- intros m Hm. discriminate.
Qed.

#[using="Type"] Lemma ram_rel_take stX q :
AMI st stX -> c_avail_meta (ctx st) = Some q -> (s_metas st) !! q = None -> meta_slot st q ->
am_rel st (am_took stX q (c_avail_meta_count (ctx stX) - 1)) (Some q).
Proof. clear - stX q ROM_reservedZ st AMP. try clear ROM_reservedZ. first [clear AMP | gw_hide AMP | idtac]; first [clear st | gw_hide st | idtac].
intros AI AVM MQ MSq. pose proof AI as AI'.
destruct AI' as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
unfold am_took. rewrite upd_meta_put.
eapply (ram_rel_final stX _ (Some q) AI); try reflexivity.
- intros a Ha. gw_exact Ha.
- intros g Hg _. rewrite get_meta_rec_put_other by congruence. reflexivity.
- intros m Hm. inversion Hm; subst m. split.
+ rewrite get_meta_rec_put_same. unfold get_meta_rec. cbn [s_metas upd_ctx]. rewrite XM, MQ. reflexivity.
+ apply meta_slot_put_meta. eapply meta_slot_same_areas; [| gw_exact MSq]. cbn. rewrite XA. reflexivity.
- intros P HPn HP0. apply QWTl.Mq5.ptrs_in_put_meta.
+ cbn. exact I.
+ cbn. exact I.
+ unfold get_meta_rec. cbn [s_metas upd_ctx]. rewrite XM, MQ. cbn. exact I.
+ pose proof HP0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
apply rptrs_in_upd_ctx; cbn [c_free_meta_head c_avail_meta c_meta_area_head c_meta_area_tail c_avail_meta_areas c_active c_brk set_avail_meta set_avail_meta_count];
try assumption; try reflexivity.
cbn. rewrite C3, AVM in H2. gw_exact H2.
Qed.

#[using="Type"] Lemma ram_rel_carve stX p r :
AMI st stX -> (s_regions stX) !! (fst p) = Some r -> r_kind r <> RKGroup ->
(s_areas stX) !! p = None -> (forall k, 0 <= k < NSLOTS -> (s_metas stX) !! (aadd p (AREA_HDR + META_SIZE * k)) = None) ->
(forall tl, c_meta_area_tail (ctx stX) = Some tl -> is_Some ((s_areas stX) !! tl)) ->
am_rel st (am_took (carve_st stX p) (aadd p AREA_HDR) 100) (Some (aadd p AREA_HDR)).
Proof. clear - stX p r ROM_reservedZ st AMP. try clear ROM_reservedZ. first [clear AMP | gw_hide AMP | idtac]; first [clear st | gw_hide st | idtac].
intros AI Hr NK ANone FRESH TL. pose proof AI as AI'.
destruct AI' as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
assert (M0 : (s_metas stX) !! (aadd p AREA_HDR) = None).
{ replace (aadd p AREA_HDR) with (aadd p (AREA_HDR + META_SIZE * 0)) by (unfold aadd, AREA_HDR, META_SIZE; f_equal; lia). apply FRESH. unfold NSLOTS; lia. }

assert (EX : exists stC, carve_st stX p = set_areas (<[p := mkArea (c_secret (ctx stX)) None NSLOTS]> (s_areas stC)) stC
/\ s_regions stC = s_regions stX /\ s_metas stC = s_metas stX /\ s_groups stC = s_groups stX /\ s_slots stC = s_slots stX
/\ s_shadow stC = s_shadow stX /\ s_tick stC = s_tick stX /\ s_reserved stC = s_reserved stX /\ s_next_rid stC = s_next_rid stX
/\ c_active (ctx stC) = c_active (ctx stX) /\ c_usage (ctx stC) = c_usage (ctx stX) /\ c_unmap_seq (ctx stC) = c_unmap_seq (ctx stX)
/\ c_bounces (ctx stC) = c_bounces (ctx stX) /\ c_seq (ctx stC) = c_seq (ctx stX) /\ c_mmap_counter (ctx stC) = c_mmap_counter (ctx stX)
/\ (forall a, is_Some ((s_areas stX) !! a) -> is_Some ((s_areas stC) !! a))
/\ (forall P : N -> Prop, P (fst p) -> ptrs_in P stX -> ptrs_in P stC)).
{ destruct (c_meta_area_tail (ctx stX)) as [tl|] eqn:HT.
- destruct (TL tl eq_refl) as [ar Har]. rewrite (carve_st_some stX p tl ar HT Har ANone). cbv zeta.
eexists. split; [reflexivity|]. repeat (split; [reflexivity|]). split.
+ intros a Ha. cbn. destruct (decide (a = tl)) as [->|NE]; [rewrite lookup_insert_eq; eauto| rewrite lookup_insert_ne by congruence; gw_exact Ha].
+ intros P HP H0. apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity.
* destruct H0 as (H1 & _). gw_exact H1.
* destruct H0 as (_ & H2 & _). gw_exact H2.
* destruct H0 as (_ & _ & H3 & _). gw_exact H3.
* gw_exact HP.
* gw_exact HP.
* destruct H0 as (_ & _ & _ & _ & _ & _ & H7 & _). gw_exact H7.
* pose proof H0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
assert (PI : ptrs_in P (upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) stX)).
{ apply rptrs_in_upd_ctx; cbn; try assumption; try reflexivity. }
destruct PI as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
unfold ptrs_in. cbn [ctx s_ctx set_areas upd_ctx s_areas s_groups s_metas].
split; [gw_exact Q1|]. split; [gw_exact Q2|]. split; [gw_exact Q3|]. split; [gw_exact Q4|]. split; [gw_exact Q5|]. split; [gw_exact Q6|]. split; [gw_exact Q7|].
split; [gw_exact Q8|]. split; [| gw_exact Q10].
intros a ar' Ha. destruct (decide (a = tl)) as [->|NE].
-- rewrite lookup_insert_eq in Ha. inversion Ha; subst. cbn. split; [| gw_exact HP]. exact (proj1 (H9 tl ar Har)).
-- rewrite lookup_insert_ne in Ha by congruence. exact (H9 a ar' Ha).
- rewrite (carve_st_none stX p HT ANone). cbv zeta.
eexists. split; [reflexivity|]. repeat (split; [reflexivity|]). split.
+ intros a Ha. gw_exact Ha.
+ intros P HP H0. pose proof H0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption.
apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption.
apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption. }
destruct EX as (stC & EC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & RA & RP).
rewrite EC. unfold am_took. rewrite upd_meta_put.
set (stD := set_areas _ stC).
eapply (ram_rel_final stX _ (Some (aadd p AREA_HDR)) AI); cbn [ctx s_ctx upd_ctx put_meta set_metas set_areas s_groups s_slots s_shadow s_tick s_reserved s_regions s_next_rid s_areas stD
c_active c_usage c_unmap_seq c_bounces c_seq c_mmap_counter set_avail_meta set_avail_meta_count]; try assumption.
- intros a Ha. destruct (decide (a = p)) as [->|NE]; [rewrite lookup_insert_eq; eauto| rewrite lookup_insert_ne by congruence]. apply RA. gw_exact Ha.
- intros g Hg _. rewrite get_meta_rec_put_other by congruence. unfold get_meta_rec. cbn. rewrite R2. reflexivity.
- intros m Hm. inversion Hm; subst m. split.
+ rewrite get_meta_rec_put_same. unfold get_meta_rec. cbn. rewrite R2, M0. reflexivity.
+ apply meta_slot_put_meta. exists p, (mkArea (c_secret (ctx stX)) None NSLOTS), 0. cbn. rewrite lookup_insert_eq.
split; [reflexivity|]. split; [unfold NSLOTS; lia|]. unfold aadd, AREA_HDR, META_SIZE. f_equal; lia.
- intros P HPn HP0. assert (HPp : P (fst p)) by (apply (HPn (fst p) r Hr NK)).
apply QWTl.Mq5.ptrs_in_put_meta; [cbn; exact I| cbn; exact I| |].
+ unfold get_meta_rec. cbn. rewrite R2, M0. cbn. exact I.
+ apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity.
* destruct (RP P HPp HP0) as (H1 & _). gw_exact H1.
* gw_exact HPp.
* destruct (RP P HPp HP0) as (_ & _ & H3 & _). gw_exact H3.
* destruct (RP P HPp HP0) as (_ & _ & _ & H4 & _). gw_exact H4.
* destruct (RP P HPp HP0) as (_ & _ & _ & _ & H5 & _). gw_exact H5.
* destruct (RP P HPp HP0) as (_ & _ & _ & _ & _ & _ & H7 & _). gw_exact H7.
* pose proof (RP P HPp HP0) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
unfold ptrs_in. cbn [ctx s_ctx set_areas s_areas s_groups s_metas].
split; [gw_exact H1|]. split; [gw_exact H2|]. split; [gw_exact H3|]. split; [gw_exact H4|]. split; [gw_exact H5|]. split; [gw_exact H6|]. split; [gw_exact H7|].
split; [gw_exact H8|]. split; [| gw_exact H10].
intros a ar' Ha. destruct (decide (a = p)) as [->|NE].
-- rewrite lookup_insert_eq in Ha. inversion Ha; subst. cbn. split; [gw_exact HPp| exact I].
-- rewrite lookup_insert_ne in Ha by congruence. exact (H9 a ar' Ha).
Qed.

#[using="Type"] Lemma ram_rel_deq stI h nx pv :
AMI st stI ->
c_free_meta_head (ctx st) = Some h -> c_free_meta_head (ctx stI) = Some h ->
m_next (get_meta_rec st h) = Some nx -> m_prev (get_meta_rec st h) = Some pv -> (nx = h <-> pv = h) ->
meta_slot st h -> clr_links (get_meta_rec st h) = meta0 ->
m_mem (get_meta_rec st nx) = None -> m_next (get_meta_rec st nx) <> None ->
m_mem (get_meta_rec st pv) = None -> m_next (get_meta_rec st pv) <> None ->
am_rel st (dequeue LFree h stI) (Some h).
Proof. clear - stI h nx pv ROM_reservedZ st AMP. try clear ROM_reservedZ. first [clear AMP | gw_hide AMP | idtac]; try gw_hide st.
intros AI FMH FMHI HN HP SELF MSh CL MN NN MP NP. pose proof AI as AI'.
destruct AI' as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
assert (GM : forall g, get_meta_rec stI g = get_meta_rec st g) by (intros; unfold get_meta_rec; rewrite XM; reflexivity).
rewrite dequeue_mid. unfold deq_mid. rewrite !GM, HN, HP. cbn [optr_eqb negb get_head]. rewrite FMHI.
destruct (aptr_eqb nx h) eqn:E.
-
apply aptr_eqb_eq in E. subst nx. cbn [negb]. rewrite upd_meta_put. unfold set_head.
eapply (ram_rel_final stI _ (Some h) AI); cbn; try reflexivity; try assumption.
+ intros a Ha; gw_exact Ha.
+ intros g Hg _. rewrite get_meta_rec_put_other by congruence. reflexivity.
+ intros m Hm. inversion Hm; subst m. split.
* rewrite get_meta_rec_put_same. change (get_meta_rec (upd_ctx (set_free_meta_head None) stI) h) with (get_meta_rec stI h). rewrite GM. gw_exact CL.
* apply meta_slot_put_meta. eapply meta_slot_same_areas; [| gw_exact MSh]. cbn. rewrite XA. reflexivity.
+ intros P HPn HP0. apply QWTl.Mq5.ptrs_in_put_meta; [cbn; exact I| cbn; exact I| |].
* change (get_meta_rec (upd_ctx (set_free_meta_head None) stI) h) with (get_meta_rec stI h). rewrite GM, CL0 || (rewrite GM; destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & H8 & _);
destruct (H8 h) as (_ & _ & Q); rewrite GM in Q; cbn; gw_exact Q).
* pose proof HP0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption.
-
assert (NEn : nx <> h) by (intros ->; rewrite aptr_eqb_refl in E; discriminate).
assert (NEp : pv <> h) by (intros Ep; apply NEn; apply (proj2 SELF); gw_exact Ep).
cbn [negb]. rewrite optr_eqb_refl. rewrite !upd_meta_put. unfold set_head.
set (st1 := put_meta pv _ stI). set (st2 := put_meta nx _ st1). set (st3 := upd_ctx _ st2).
assert (R3 : get_meta_rec st3 h = get_meta_rec st h).
{ change (get_meta_rec st3 h) with (get_meta_rec st2 h). unfold st2, st1.
rewrite !get_meta_rec_put_other by congruence. apply GM. }
eapply (ram_rel_final stI _ (Some h) AI); cbn; try reflexivity; try assumption.
+ intros a Ha; gw_exact Ha.
+ intros g Hg Hm. rewrite get_meta_rec_put_other by congruence.
change (get_meta_rec st3 g) with (get_meta_rec st2 g). unfold st2, st1.
assert (g <> nx) by (intros ->; destruct Hm as [Hm|Hm]; [apply Hm; gw_exact MN| apply NN; gw_exact Hm]).
assert (g <> pv) by (intros ->; destruct Hm as [Hm|Hm]; [apply Hm; gw_exact MP| apply NP; gw_exact Hm]).
rewrite !get_meta_rec_put_other by assumption. reflexivity.
+ intros m Hm. inversion Hm; subst m. split.
* rewrite get_meta_rec_put_same, R3. gw_exact CL.
* apply meta_slot_put_meta. eapply meta_slot_same_areas; [| gw_exact MSh]. cbn. rewrite XA. reflexivity.
+ intros P HPn HP0. pose proof HP0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
destruct (H8 h) as (Q1 & Q2 & Q3). rewrite GM, HP in Q1. rewrite GM, HN in Q2. cbn in Q1, Q2.
assert (P1 : ptrs_in P st1).
{ unfold st1. apply QWTl.Mq5.ptrs_in_put_meta; [| cbn; gw_exact Q2 | | gw_exact HP0].
- destruct (H8 pv) as (X & _ & _). gw_exact X.
- destruct (H8 pv) as (_ & _ & X). gw_exact X. }
assert (P2 : ptrs_in P st2).
{ unfold st2. apply QWTl.Mq5.ptrs_in_put_meta; [cbn; gw_exact Q1 | | | gw_exact P1].
- unfold st1. rewrite get_meta_rec_put. destruct (aptr_eqb nx pv); cbn; [gw_exact Q2|]. destruct (H8 nx) as (_ & X & _). gw_exact X.
- unfold st1. rewrite get_meta_rec_put. destruct (aptr_eqb nx pv); cbn; [| destruct (H8 nx) as (_ & _ & X); gw_exact X].
destruct (H8 pv) as (_ & _ & X). gw_exact X. }
assert (P3 : ptrs_in P st3).
{ unfold st3. pose proof P2 as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10).
apply rptrs_in_upd_ctx; cbn; try reflexivity.
- gw_exact Q2.
- change (ctx st2) with (ctx stI). gw_exact H2.
- change (ctx st2) with (ctx stI). gw_exact H3.
- change (ctx st2) with (ctx stI). gw_exact H4.
- change (ctx st2) with (ctx stI). gw_exact H5.
- change (ctx st2) with (ctx stI). gw_exact H7.
- gw_exact P2. }
apply QWTl.Mq5.ptrs_in_put_meta; [cbn; exact I| cbn; exact I| | gw_exact P3].
rewrite R3. rewrite <- GM. gw_exact Q3.
Qed.

#[using="Type"] Lemma rAMI_ctx stX f :
AMI st stX ->
ctx_core_eq (ctx stX) (f (ctx stX)) -> 0 <= c_secret (f (ctx stX)) < 2^64 ->
(c_avail_meta_areas (f (ctx stX)) = c_avail_meta_areas (ctx stX)
\/ exists q r, c_avail_meta_areas (f (ctx stX)) = Some q /\ (s_regions stX) !! (fst q) = Some r /\ r_kind r <> RKGroup) ->
(c_brk (f (ctx stX)) = c_brk (ctx stX)
\/ c_brk (f (ctx stX)) = BrkDead
\/ exists rid off r, c_brk (f (ctx stX)) = BrkLive rid off /\ (s_regions stX) !! rid = Some r /\ r_kind r <> RKGroup) ->
AMI st (upd_ctx f stX).
Proof. clear - stX f ROM_reservedZ st AMP. try clear ROM_reservedZ. first [clear AMP | gw_hide AMP | idtac]; first [clear st | gw_hide st | idtac].
intros AI CE SR HA HB. pose proof AI as AI'.
destruct AI' as [CC XSR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
split; cbn; try assumption.
- destruct CC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11).
destruct CE as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
unfold ctx_core_eq. change (ctx (upd_ctx f stX)) with (f (ctx stX)).
rewrite D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11. repeat split; assumption.
- intros P HPn HP0. pose proof (XP P HPn HP0) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
destruct CE as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
apply rptrs_in_upd_ctx; rewrite ?D2, ?D3, ?D5, ?D6, ?D7; try assumption; try reflexivity.
+ destruct HA as [-> | (q & r & -> & Hq & Kq)]; [gw_exact H5|]. cbn. exact (HPn _ _ Hq Kq).
+ destruct HB as [-> | [-> | (rid & off & r & -> & Hq & Kq)]]; [gw_exact H7| exact I|]. exact (HPn _ _ Hq Kq).
+ exact (XP P HPn HP0).
Qed.

#[using="Type"] Lemma rAMI_new_region stX k base len :
AMI st stX -> k <> RKGroup -> 0 < len ->
AMI st (fst (new_region k base len stX))
/\ (s_regions (fst (new_region k base len stX))) !! (s_next_rid stX) = Some (mkRegion k base len)
/\ (forall q, fst q <> s_next_rid stX -> conc (fst (new_region k base len stX)) q = conc stX q)
/\ (forall off, conc (fst (new_region k base len stX)) (s_next_rid stX, off) = base + off).
Proof. clear - stX k base len ROM_reservedZ st AMP. try clear ROM_reservedZ. first [clear AMP | gw_hide AMP | idtac]; first [clear st | gw_hide st | idtac].
intros AI NK LEN. pose proof AI as AI'.
destruct AI' as [CC XSR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
destruct (XF (s_next_rid stX) ltac:(lia)) as [FRr FRs].
unfold new_region. cbn [fst].
set (rid := s_next_rid stX). set (st' := set_next_rid _ _).
assert (LK : forall q, (s_regions st') !! q = if decide (q = rid) then Some (mkRegion k base len) else (s_regions stX) !! q).
{ intros q. cbn. destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. }
split; [| split; [| split]].
- split; cbn -[insert]; try assumption.
+ intros q r Hq. destruct (XREG q r Hq) as (r' & Hr' & REST). exists r'. rewrite LK.
destruct (decide (q = rid)) as [->|NE]; [rewrite FRr in Hr'; discriminate|]. auto.
+ intros q r' Hq Hn. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; gw_exact NK|]. exact (XNEW q r' Hq Hn).
+ unfold rid. lia.
+ intros P HPn HP0. apply (QWTl.Mq5.ptrs_in_new_region stX base len k). apply XP; [| gw_exact HP0].
intros q r Hq Hk. apply (HPn q r); [| gw_exact Hk]. rewrite LK. destruct (decide (q = rid)) as [->|NE]; [rewrite FRr in Hq; discriminate| gw_exact Hq].
+ intros q Hq. rewrite LK. destruct (decide (q = rid)) as [->|NE]; [unfold rid in Hq; lia|]. apply XF. unfold rid in Hq. lia.
+ intros q rq Hq. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; cbn; lia|]. exact (XRP q rq Hq).
- rewrite LK. destruct (decide (rid = rid)); [reflexivity| congruence].
- intros q Hq. unfold conc, get_region. rewrite LK. destruct (decide (fst q = rid)) as [E|NE]; [exfalso; apply Hq; gw_exact E| reflexivity].
- intros off. unfold conc, get_region. cbn [fst snd]. rewrite LK. destruct (decide (rid = rid)); [reflexivity| congruence].
Qed.

#[using="Type"] Lemma rAMI_grow stX rid r off :
AMI st stX -> (s_regions stX) !! rid = Some r -> r_kind r <> RKGroup -> r_len r = off ->
let st' := set_regions (<[rid := mkRegion (r_kind r) (r_base r) (off + 4096)]> (s_regions stX)) stX in
AMI st st' /\ (forall q, conc st' q = conc stX q) /\ (s_regions st') !! rid = Some (mkRegion (r_kind r) (r_base r) (off + 4096)).
Proof. clear - stX rid r off ROM_reservedZ st AMP. try clear ROM_reservedZ. first [clear AMP | gw_hide AMP | idtac]; first [clear st | gw_hide st | idtac].
intros AI Hr NK LEN st'. pose proof AI as AI'.
destruct AI' as [CC XSR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
assert (LK : forall q, (s_regions st') !! q = if decide (q = rid) then Some (mkRegion (r_kind r) (r_base r) (off + 4096)) else (s_regions stX) !! q).
{ intros q. cbn. destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. }
assert (CQ : forall q, conc st' q = conc stX q).
{ intros q. unfold conc, get_region. rewrite LK. destruct (decide (fst q = rid)) as [E|NE]; [rewrite E, Hr|]; reflexivity. }
split; [| split; [gw_exact CQ| rewrite LK; destruct (decide (rid = rid)); [reflexivity| congruence]]].
split; cbn -[insert]; try assumption.
- intros q rq Hq. destruct (XREG q rq Hq) as (r' & Hr' & K' & B' & L' & G'). rewrite LK.
destruct (decide (q = rid)) as [->|NE].
+ rewrite Hr in Hr'. inversion Hr'; subst r'. eexists. split; [reflexivity|]. cbn. split; [gw_exact K'|]. split; [gw_exact B'|]. split; [lia|].
intros HG. exfalso. apply NK. rewrite K'. gw_exact HG.
+ exists r'. auto.
- intros q r' Hq Hn. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; gw_exact NK|]. exact (XNEW q r' Hq Hn).
- intros P HPn HP0. apply XP; [| gw_exact HP0]. intros q rq Hq Hk.
destruct (decide (q = rid)) as [->|NE].
+ apply (HPn rid (mkRegion (r_kind r) (r_base r) (off + 4096))); [rewrite LK; destruct (decide (rid = rid)); [reflexivity|congruence]|]. cbn. rewrite Hr in Hq. inversion Hq; subst. gw_exact Hk.
+ apply (HPn q rq); [rewrite LK; destruct (decide (q = rid)); [congruence| gw_exact Hq]| gw_exact Hk].
- intros q Hq. rewrite LK. destruct (decide (q = rid)) as [->|NE].
+ destruct (XF rid Hq) as [A _]. rewrite Hr in A. discriminate.
+ apply XF. gw_exact Hq.
- intros q rq Hq. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; cbn; pose proof (XRP rid r Hr); lia|]. exact (XRP q rq Hq).
Qed.
End PURE.

End RC__1.

End G.
