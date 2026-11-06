(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q5Rg Qfw3_c1 QWxq_c1 Qc3B QlEo_c1 Lib.GwApply QsjA QZAi Ql2m QqdR QYTG Lib.SepCache QnDM_c1 QVbl QQLG Q91D QQRC G.T_shp G.T_pe Qbz7 QFau Q8l1 QZxv QEN3 QK0e QROt Lib.CodeAt Lib.StepGen Lib.StepGenX Lib.StepGenX2 Lib.GwCallee Lib.GwFold.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3_c1.Mq2 QWxq_c1.Mq0 Qc3B QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.

Import QZAi.Mq1 Ql2m.Mq3 QZAi QqdR QYTG.Mq2.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1.
Import QVbl.Mq4.
Import QVbl.Mq3.
Import QQLG.Mq8.
Import Q91D.Mq6.
Import QQLG.Mq7.
Import Q91D.Mq2.
Import QQRC.Mq0.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_shp.F_fmt_fp.
Import Q91D.Mq3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.
Import Qbz7.
Import QFau.
Import Q8l1.Mq1.

Export QROt.Mq0.
Import Qfw3_c1.Mq1.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 : Z).
Variables (hi_22 hi_281 hi_332 hi_360 hi_395 hi_438 hi_453 hi_467 hi_473 hi_533 hi_543 : bv 20).
Variables (lo_25 lo_282 lo_333 lo_362 lo_396 lo_439 lo_454 lo_468 lo_474 lo_534 lo_545 : bv 12).
Variables (joff_81 joff_381 joff_383 joff_389 joff_530 joff_627 joff_639 joff_648 joff_655 joff_668 joff_680 joff_689 joff_701 joff_713 joff_722 joff_729 joff_742 joff_754 joff_762 joff_798 joff_883 joff_907 : bv 21).
Variables (G_102fd G_107e0 G_11778 G_118c0 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_194bc e_194c8 e_197bc e_fwritex e_memset e_2596c e_memchr : Z).
Variables (jt_11778_o1504 jt_11778_o1432 jt_11778_o1800 jt_11778_o1744 jt_11778_o1864 jt_11778_o1352 : Z).
Hypothesis CODE : code_at segs base (printf_core_code w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 3632.
Hypothesis D_22 : decode_any (Z_to_bv 32 w_22) = Some (Auipc 10 hi_22, 4%Z).
Hypothesis E_22 : is_ecall (Z_to_bv 32 w_22) = false.
Hypothesis D_25 : decode_any (Z_to_bv 32 w_25) = Some (Load SZ8 true 12 10 lo_25, 4%Z).
Hypothesis E_25 : is_ecall (Z_to_bv 32 w_25) = false.
Hypothesis D_81 : decode_any (Z_to_bv 32 w_81) = Some (Jal 1 joff_81, 4%Z).
Hypothesis E_81 : is_ecall (Z_to_bv 32 w_81) = false.
Hypothesis D_281 : decode_any (Z_to_bv 32 w_281) = Some (Auipc 13 hi_281, 4%Z).
Hypothesis E_281 : is_ecall (Z_to_bv 32 w_281) = false.
Hypothesis D_282 : decode_any (Z_to_bv 32 w_282) = Some (OpImm ALU_ADD 13 13 lo_282, 4%Z).
Hypothesis E_282 : is_ecall (Z_to_bv 32 w_282) = false.
Hypothesis D_332 : decode_any (Z_to_bv 32 w_332) = Some (Auipc 11 hi_332, 4%Z).
Hypothesis E_332 : is_ecall (Z_to_bv 32 w_332) = false.
Hypothesis D_333 : decode_any (Z_to_bv 32 w_333) = Some (OpImm ALU_ADD 11 11 lo_333, 4%Z).
Hypothesis E_333 : is_ecall (Z_to_bv 32 w_333) = false.
Hypothesis D_360 : decode_any (Z_to_bv 32 w_360) = Some (Auipc 11 hi_360, 4%Z).
Hypothesis E_360 : is_ecall (Z_to_bv 32 w_360) = false.
Hypothesis D_362 : decode_any (Z_to_bv 32 w_362) = Some (OpImm ALU_ADD 11 11 lo_362, 4%Z).
Hypothesis E_362 : is_ecall (Z_to_bv 32 w_362) = false.
Hypothesis D_389 : decode_any (Z_to_bv 32 w_389) = Some (Jal 1 joff_389, 4%Z).
Hypothesis E_389 : is_ecall (Z_to_bv 32 w_389) = false.
Hypothesis D_395 : decode_any (Z_to_bv 32 w_395) = Some (Auipc 12 hi_395, 4%Z).
Hypothesis E_395 : is_ecall (Z_to_bv 32 w_395) = false.
Hypothesis D_396 : decode_any (Z_to_bv 32 w_396) = Some (OpImm ALU_ADD 12 12 lo_396, 4%Z).
Hypothesis E_396 : is_ecall (Z_to_bv 32 w_396) = false.
Hypothesis D_438 : decode_any (Z_to_bv 32 w_438) = Some (Auipc 11 hi_438, 4%Z).
Hypothesis E_438 : is_ecall (Z_to_bv 32 w_438) = false.
Hypothesis D_439 : decode_any (Z_to_bv 32 w_439) = Some (OpImm ALU_ADD 17 11 lo_439, 4%Z).
Hypothesis E_439 : is_ecall (Z_to_bv 32 w_439) = false.
Hypothesis D_453 : decode_any (Z_to_bv 32 w_453) = Some (Auipc 10 hi_453, 4%Z).
Hypothesis E_453 : is_ecall (Z_to_bv 32 w_453) = false.
Hypothesis D_454 : decode_any (Z_to_bv 32 w_454) = Some (OpImm ALU_ADD 10 10 lo_454, 4%Z).
Hypothesis E_454 : is_ecall (Z_to_bv 32 w_454) = false.
Hypothesis D_467 : decode_any (Z_to_bv 32 w_467) = Some (Auipc 11 hi_467, 4%Z).
Hypothesis E_467 : is_ecall (Z_to_bv 32 w_467) = false.
Hypothesis D_468 : decode_any (Z_to_bv 32 w_468) = Some (OpImm ALU_ADD 14 11 lo_468, 4%Z).
Hypothesis E_468 : is_ecall (Z_to_bv 32 w_468) = false.
Hypothesis D_473 : decode_any (Z_to_bv 32 w_473) = Some (Auipc 13 hi_473, 4%Z).
Hypothesis E_473 : is_ecall (Z_to_bv 32 w_473) = false.
Hypothesis D_474 : decode_any (Z_to_bv 32 w_474) = Some (OpImm ALU_ADD 13 13 lo_474, 4%Z).
Hypothesis E_474 : is_ecall (Z_to_bv 32 w_474) = false.
Hypothesis D_533 : decode_any (Z_to_bv 32 w_533) = Some (Auipc 11 hi_533, 4%Z).
Hypothesis E_533 : is_ecall (Z_to_bv 32 w_533) = false.
Hypothesis D_534 : decode_any (Z_to_bv 32 w_534) = Some (OpImm ALU_ADD 11 11 lo_534, 4%Z).
Hypothesis E_534 : is_ecall (Z_to_bv 32 w_534) = false.
Hypothesis D_543 : decode_any (Z_to_bv 32 w_543) = Some (Auipc 11 hi_543, 4%Z).
Hypothesis E_543 : is_ecall (Z_to_bv 32 w_543) = false.
Hypothesis D_545 : decode_any (Z_to_bv 32 w_545) = Some (OpImm ALU_ADD 17 11 lo_545, 4%Z).
Hypothesis E_545 : is_ecall (Z_to_bv 32 w_545) = false.
Hypothesis D_627 : decode_any (Z_to_bv 32 w_627) = Some (Jal 1 joff_627, 4%Z).
Hypothesis E_627 : is_ecall (Z_to_bv 32 w_627) = false.
Hypothesis D_648 : decode_any (Z_to_bv 32 w_648) = Some (Jal 1 joff_648, 4%Z).
Hypothesis E_648 : is_ecall (Z_to_bv 32 w_648) = false.
Hypothesis D_655 : decode_any (Z_to_bv 32 w_655) = Some (Jal 1 joff_655, 4%Z).
Hypothesis E_655 : is_ecall (Z_to_bv 32 w_655) = false.
Hypothesis D_668 : decode_any (Z_to_bv 32 w_668) = Some (Jal 1 joff_668, 4%Z).
Hypothesis E_668 : is_ecall (Z_to_bv 32 w_668) = false.
Hypothesis D_689 : decode_any (Z_to_bv 32 w_689) = Some (Jal 1 joff_689, 4%Z).
Hypothesis E_689 : is_ecall (Z_to_bv 32 w_689) = false.
Hypothesis D_701 : decode_any (Z_to_bv 32 w_701) = Some (Jal 1 joff_701, 4%Z).
Hypothesis E_701 : is_ecall (Z_to_bv 32 w_701) = false.
Hypothesis D_722 : decode_any (Z_to_bv 32 w_722) = Some (Jal 1 joff_722, 4%Z).
Hypothesis E_722 : is_ecall (Z_to_bv 32 w_722) = false.
Hypothesis D_729 : decode_any (Z_to_bv 32 w_729) = Some (Jal 1 joff_729, 4%Z).
Hypothesis E_729 : is_ecall (Z_to_bv 32 w_729) = false.
Hypothesis D_742 : decode_any (Z_to_bv 32 w_742) = Some (Jal 1 joff_742, 4%Z).
Hypothesis E_742 : is_ecall (Z_to_bv 32 w_742) = false.
Hypothesis D_762 : decode_any (Z_to_bv 32 w_762) = Some (Jal 1 joff_762, 4%Z).
Hypothesis E_762 : is_ecall (Z_to_bv 32 w_762) = false.
Hypothesis ANCH_25 : gw_anch (Z.shiftl (bv_signed hi_22) 12 + (base + 88) + bv_signed lo_25)%Z got_ssp.
Hypothesis ANCH_282 : gw_anch (Z.shiftl (bv_signed hi_281) 12 + (base + 1124) + bv_signed lo_282)%Z G_118c0.
Hypothesis ANCH_333 : gw_anch (Z.shiftl (bv_signed hi_332) 12 + (base + 1328) + bv_signed lo_333)%Z G_11778.
Hypothesis ANCH_362 : gw_anch (Z.shiftl (bv_signed hi_360) 12 + (base + 1440) + bv_signed lo_362)%Z G_102fd.
Hypothesis ANCH_396 : gw_anch (Z.shiftl (bv_signed hi_395) 12 + (base + 1580) + bv_signed lo_396)%Z G_102fd.
Hypothesis ANCH_439 : gw_anch (Z.shiftl (bv_signed hi_438) 12 + (base + 1752) + bv_signed lo_439)%Z G_102fd.
Hypothesis ANCH_454 : gw_anch (Z.shiftl (bv_signed hi_453) 12 + (base + 1812) + bv_signed lo_454)%Z G_102fd.
Hypothesis ANCH_468 : gw_anch (Z.shiftl (bv_signed hi_467) 12 + (base + 1868) + bv_signed lo_468)%Z G_102fd.
Hypothesis ANCH_474 : gw_anch (Z.shiftl (bv_signed hi_473) 12 + (base + 1892) + bv_signed lo_474)%Z G_107e0.
Hypothesis ANCH_534 : gw_anch (Z.shiftl (bv_signed hi_533) 12 + (base + 2132) + bv_signed lo_534)%Z G_102fd.
Hypothesis ANCH_545 : gw_anch (Z.shiftl (bv_signed hi_543) 12 + (base + 2172) + bv_signed lo_545)%Z G_102fd.
Hypothesis LINK_81 : gw_anch (base + 324 + bv_signed joff_81)%Z (e_fwritex + 0)%Z.
Hypothesis LINK_381 : gw_anch (base + 1524 + bv_signed joff_381)%Z (e_194bc + 0)%Z.
Hypothesis LINK_383 : gw_anch (base + 1532 + bv_signed joff_383)%Z (e_194c8 + 0)%Z.
Hypothesis LINK_389 : gw_anch (base + 1556 + bv_signed joff_389)%Z (e_2596c + 0)%Z.
Hypothesis LINK_530 : gw_anch (base + 2120 + bv_signed joff_530)%Z (e_fwritex + 0)%Z.
Hypothesis LINK_627 : gw_anch (base + 2508 + bv_signed joff_627)%Z (e_memset + 0)%Z.
Hypothesis LINK_639 : gw_anch (base + 2556 + bv_signed joff_639)%Z (e_fwritex + 0)%Z.
Hypothesis LINK_648 : gw_anch (base + 2592 + bv_signed joff_648)%Z (e_fwritex + 0)%Z.
Hypothesis LINK_655 : gw_anch (base + 2620 + bv_signed joff_655)%Z (e_fwritex + 0)%Z.
Hypothesis LINK_668 : gw_anch (base + 2672 + bv_signed joff_668)%Z (e_memset + 0)%Z.
Hypothesis LINK_680 : gw_anch (base + 2720 + bv_signed joff_680)%Z (e_fwritex + 0)%Z.
Hypothesis LINK_689 : gw_anch (base + 2756 + bv_signed joff_689)%Z (e_fwritex + 0)%Z.
Hypothesis LINK_701 : gw_anch (base + 2804 + bv_signed joff_701)%Z (e_memset + 0)%Z.
Hypothesis LINK_713 : gw_anch (base + 2852 + bv_signed joff_713)%Z (e_fwritex + 0)%Z.
Hypothesis LINK_722 : gw_anch (base + 2888 + bv_signed joff_722)%Z (e_fwritex + 0)%Z.
Hypothesis LINK_729 : gw_anch (base + 2916 + bv_signed joff_729)%Z (e_fwritex + 0)%Z.
Hypothesis LINK_742 : gw_anch (base + 2968 + bv_signed joff_742)%Z (e_memset + 0)%Z.
Hypothesis LINK_754 : gw_anch (base + 3016 + bv_signed joff_754)%Z (e_fwritex + 0)%Z.
Hypothesis LINK_762 : gw_anch (base + 3048 + bv_signed joff_762)%Z (e_fwritex + 0)%Z.
Hypothesis LINK_798 : gw_anch (base + 3192 + bv_signed joff_798)%Z (e_194bc + 0)%Z.
Hypothesis LINK_883 : gw_anch (base + 3532 + bv_signed joff_883)%Z (e_194bc + 0)%Z.
Hypothesis LINK_907 : gw_anch (base + 3628 + bv_signed joff_907)%Z (e_197bc + 0)%Z.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis LAY_lo_got_ssp : gw_le 65536 got_ssp.
Hypothesis AL_got_ssp : gw_al got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis LAY_lo_ssp_guard : gw_le 65536 ssp_guard.
Hypothesis AL_ssp_guard : gw_al ssp_guard 8.
Hypothesis RNG_GLOBALS_TOP : gw_br GLOBALS_TOP 8.
Hypothesis LAY_lo_GLOBALS_TOP : gw_le 65536 GLOBALS_TOP.
Hypothesis LAY_STATIC_SPLIT_got_ssp : gw_le (STATIC_SPLIT + 8) got_ssp.
Hypothesis LAY_got_ssp_ssp_guard : gw_le (got_ssp + 8) ssp_guard.
Hypothesis LAY_ssp_guard_GLOBALS_TOP : gw_le (ssp_guard + 8) GLOBALS_TOP.
Hypothesis RNG_G_118c0 : gw_br G_118c0 116.
Hypothesis ROM_G_118c0 : ro_bytes segs G_118c0 [Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 10; Z_to_bv 8 10; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 3; Z_to_bv 8 10; Z_to_bv 8 7; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 27; Z_to_bv 8 9; Z_to_bv 8 11; Z_to_bv 8 24; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 6; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 6; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 14; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 11; Z_to_bv 8 13; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 2; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 14; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 14; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 14; Z_to_bv 8 0; Z_to_bv 8 0].
Hypothesis RNG_G_102fd : gw_br G_102fd 12.
Hypothesis ROM_G_102fd : ro_bytes segs G_102fd [Z_to_bv 8 45; Z_to_bv 8 43; Z_to_bv 8 32; Z_to_bv 8 32; Z_to_bv 8 32; Z_to_bv 8 48; Z_to_bv 8 88; Z_to_bv 8 48; Z_to_bv 8 120; Z_to_bv 8 0; Z_to_bv 8 125; Z_to_bv 8 0].
Hypothesis RNG_G_107e0 : gw_br G_107e0 16.
Hypothesis ROM_G_107e0 : ro_bytes segs G_107e0 [Z_to_bv 8 48; Z_to_bv 8 49; Z_to_bv 8 50; Z_to_bv 8 51; Z_to_bv 8 52; Z_to_bv 8 53; Z_to_bv 8 54; Z_to_bv 8 55; Z_to_bv 8 56; Z_to_bv 8 57; Z_to_bv 8 65; Z_to_bv 8 66; Z_to_bv 8 67; Z_to_bv 8 68; Z_to_bv 8 69; Z_to_bv 8 70].
Hypothesis LAY_G_102fd_STATIC_SPLIT : gw_le (G_102fd + 12) STATIC_SPLIT.
Hypothesis LAY_got_ssp_240_ssp_guard : gw_le (got_ssp + 240) ssp_guard.
Hypothesis RNG_G_11778 : gw_br G_11778 224.
Hypothesis JTL_jt_11778_o1504 : gw_anch (bv_unsigned (sx32 (Z_to_bv 64 jt_11778_o1504)) + G_11778)%Z (base + 1504)%Z.
Hypothesis ROM_jt_11778_50 : ro_bytes segs (G_11778 + 200) (le4 (Z_to_bv 64 jt_11778_o1504)).
Hypothesis JTL_jt_11778_o1432 : gw_anch (bv_unsigned (sx32 (Z_to_bv 64 jt_11778_o1432)) + G_11778)%Z (base + 1432)%Z.
Hypothesis ROM_jt_11778_35 : ro_bytes segs (G_11778 + 140) (le4 (Z_to_bv 64 jt_11778_o1432)).
Hypothesis ROM_jt_11778_40 : ro_bytes segs (G_11778 + 160) (le4 (Z_to_bv 64 jt_11778_o1432)).
Hypothesis JTL_jt_11778_o1800 : gw_anch (bv_unsigned (sx32 (Z_to_bv 64 jt_11778_o1800)) + G_11778)%Z (base + 1800)%Z.
Hypothesis ROM_jt_11778_34 : ro_bytes segs (G_11778 + 136) (le4 (Z_to_bv 64 jt_11778_o1800)).
Hypothesis JTL_jt_11778_o1744 : gw_anch (bv_unsigned (sx32 (Z_to_bv 64 jt_11778_o1744)) + G_11778)%Z (base + 1744)%Z.
Hypothesis ROM_jt_11778_52 : ro_bytes segs (G_11778 + 208) (le4 (Z_to_bv 64 jt_11778_o1744)).
Hypothesis JTL_jt_11778_o1864 : gw_anch (bv_unsigned (sx32 (Z_to_bv 64 jt_11778_o1864)) + G_11778)%Z (base + 1864)%Z.
Hypothesis ROM_jt_11778_55 : ro_bytes segs (G_11778 + 220) (le4 (Z_to_bv 64 jt_11778_o1864)).
Hypothesis ROM_jt_11778_23 : ro_bytes segs (G_11778 + 92) (le4 (Z_to_bv 64 jt_11778_o1864)).
Hypothesis JTL_jt_11778_o1352 : gw_anch (bv_unsigned (sx32 (Z_to_bv 64 jt_11778_o1352)) + G_11778)%Z (base + 1352)%Z.
Hypothesis ROM_jt_11778_36 : ro_bytes segs (G_11778 + 144) (le4 (Z_to_bv 64 jt_11778_o1352)).
Hypothesis ROM_jt_11778_37 : ro_bytes segs (G_11778 + 148) (le4 (Z_to_bv 64 jt_11778_o1352)).
Hypothesis ROM_jt_11778_38 : ro_bytes segs (G_11778 + 152) (le4 (Z_to_bv 64 jt_11778_o1352)).
Hypothesis ROM_jt_11778_4 : ro_bytes segs (G_11778 + 16) (le4 (Z_to_bv 64 jt_11778_o1352)).
Hypothesis ROM_jt_11778_5 : ro_bytes segs (G_11778 + 20) (le4 (Z_to_bv 64 jt_11778_o1352)).
Hypothesis ROM_jt_11778_6 : ro_bytes segs (G_11778 + 24) (le4 (Z_to_bv 64 jt_11778_o1352)).

Local Definition gw_tbl_0 := tt.

Definition wfile : ltac:(gw_rebind_ty (@QQLG.Mq7.wfile segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QQLG.Mq7.wfile segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@QROt.Mq0.wfile segs) wfile (gw_ent (@QEN3.Mq6.wfile segs) wfile (gw_ent (@QZxv.Mqa.wfile segs) wfile (gw_ent (@QEN3.wfile segs) wfile (gw_ent (@QK0e.wfile segs) wfile (gw_ent (@QZxv.Mq0.wfile segs) wfile (gw_ent (@QZxv.Mq1.wfile segs) wfile (gw_ent (@QEN3.Mq1.wfile segs) wfile (gw_ent (@QZxv.Mq3.wfile segs) wfile (gw_ent (@QEN3.Mq8.wfile segs) wfile (gw_ent (@QZxv.Mq2.wfile segs) wfile (gw_ent (@QEN3.Mq0.wfile segs) wfile (gw_ent (@QEN3.Mq4.wfile segs) wfile (gw_ent (@QEN3.Mq5.wfile segs) wfile (gw_ent (@QEN3.Mq2.wfile segs) wfile (gw_ent (@QZxv.Mq8.wfile segs) wfile (gw_ent (@QZxv.Mq9.wfile segs) wfile (gw_ent (@QZxv.Mqj.wfile segs) wfile (gw_ent (@QZxv.Mqe.wfile segs) wfile (gw_ent (@QZxv.Mqf.wfile segs) wfile (gw_ent (@QZxv.Mqg.wfile segs) wfile (gw_ent (@QEN3.Mq7.wfile segs) wfile (gw_ent (@QZxv.Mqh.wfile segs) wfile (gw_ent (@QZxv.Mqi.wfile segs) wfile (gw_ent (@QZxv.Mq4.wfile segs) wfile (gw_ent (@QZxv.Mqd.wfile segs) wfile (gw_ent (@QZxv.Mqb.wfile segs) wfile (gw_ent (@QZxv.Mqk.wfile segs) wfile (gw_ent (@QEN3.Mq3.wfile segs) wfile (gw_ent (@QZxv.Mqc.wfile segs) wfile (gw_ent (@QZxv.Mq7.wfile segs) wfile (gw_ent (@QZxv.Mq5.wfile segs) wfile (gw_ent (@QZxv.Mq6.wfile segs) wfile (gw_ent (@Q8l1.Mq1.wfile segs) wfile (gw_ent (@Q91D.Mq2.wfile segs) wfile (gw_ent (@QQLG.Mq7.wfile segs) wfile gw_tbl_0)))))))))))))))))))))))))))))))))))).
Definition ssp_cells : ltac:(gw_rebind_ty (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QROt.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq6.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqa.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QK0e.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq8.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq4.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq5.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq8.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq9.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqj.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqe.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqf.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqg.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq7.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqh.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqi.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq4.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqd.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqb.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqk.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqc.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq7.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq5.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq6.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q8l1.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_1))))))))))))))))))))))))))))))))))).
Definition va_area : ltac:(gw_rebind_ty (@Q91D.Mq3.va_area segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q91D.Mq3.va_area segs) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@QROt.Mq0.va_area segs) va_area (gw_ent (@QEN3.Mq6.va_area segs) va_area (gw_ent (@QZxv.Mqa.va_area segs) va_area (gw_ent (@QEN3.va_area segs) va_area (gw_ent (@QK0e.va_area segs) va_area (gw_ent (@QZxv.Mq0.va_area segs) va_area (gw_ent (@QZxv.Mq1.va_area segs) va_area (gw_ent (@QEN3.Mq1.va_area segs) va_area (gw_ent (@QZxv.Mq3.va_area segs) va_area (gw_ent (@QEN3.Mq8.va_area segs) va_area (gw_ent (@QZxv.Mq2.va_area segs) va_area (gw_ent (@QEN3.Mq0.va_area segs) va_area (gw_ent (@QEN3.Mq4.va_area segs) va_area (gw_ent (@QEN3.Mq5.va_area segs) va_area (gw_ent (@QEN3.Mq2.va_area segs) va_area (gw_ent (@QZxv.Mq8.va_area segs) va_area (gw_ent (@QZxv.Mq9.va_area segs) va_area (gw_ent (@QZxv.Mqj.va_area segs) va_area (gw_ent (@QZxv.Mqe.va_area segs) va_area (gw_ent (@QZxv.Mqf.va_area segs) va_area (gw_ent (@QZxv.Mqg.va_area segs) va_area (gw_ent (@QEN3.Mq7.va_area segs) va_area (gw_ent (@QZxv.Mqh.va_area segs) va_area (gw_ent (@QZxv.Mqi.va_area segs) va_area (gw_ent (@QZxv.Mq4.va_area segs) va_area (gw_ent (@QZxv.Mqd.va_area segs) va_area (gw_ent (@QZxv.Mqb.va_area segs) va_area (gw_ent (@QZxv.Mqk.va_area segs) va_area (gw_ent (@QEN3.Mq3.va_area segs) va_area (gw_ent (@QZxv.Mqc.va_area segs) va_area (gw_ent (@QZxv.Mq7.va_area segs) va_area (gw_ent (@QZxv.Mq5.va_area segs) va_area (gw_ent (@QZxv.Mq6.va_area segs) va_area (gw_ent (@Q8l1.Mq1.va_area segs) va_area (gw_ent (@Q91D.Mq3.va_area segs) va_area gw_tbl_2))))))))))))))))))))))))))))))))))).
Definition sink_frame_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@QROt.Mq0.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QEN3.Mq6.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mqa.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QEN3.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QK0e.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mq0.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mq1.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QEN3.Mq1.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mq3.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QEN3.Mq8.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mq2.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QEN3.Mq0.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QEN3.Mq4.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QEN3.Mq5.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QEN3.Mq2.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mq8.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mq9.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mqj.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mqe.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mqf.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mqg.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QEN3.Mq7.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mqh.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mqi.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mq4.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mqd.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mqb.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mqk.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QEN3.Mq3.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mqc.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mq7.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mq5.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mq6.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@Q8l1.Mq1.sink_frame_stmt segs) sink_frame_stmt gw_tbl_3)))))))))))))))))))))))))))))))))).
#[global] Arguments sink_frame_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope.
Definition sink_flags_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@QROt.Mq0.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QEN3.Mq6.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mqa.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QEN3.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QK0e.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mq0.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mq1.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QEN3.Mq1.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mq3.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QEN3.Mq8.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mq2.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QEN3.Mq0.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QEN3.Mq4.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QEN3.Mq5.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QEN3.Mq2.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mq8.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mq9.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mqj.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mqe.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mqf.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mqg.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QEN3.Mq7.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mqh.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mqi.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mq4.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mqd.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mqb.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mqk.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QEN3.Mq3.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mqc.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mq7.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mq5.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mq6.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@Q8l1.Mq1.sink_flags_stmt segs) sink_flags_stmt gw_tbl_4)))))))))))))))))))))))))))))))))).
#[global] Arguments sink_flags_stmt {St}%_type_scope Fp%_Z_scope SINK%_function_scope.
Definition out_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QROt.Mq0.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QEN3.Mq6.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mqa.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QEN3.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QK0e.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mq0.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mq1.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QEN3.Mq1.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mq3.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QEN3.Mq8.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mq2.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QEN3.Mq0.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QEN3.Mq4.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QEN3.Mq5.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QEN3.Mq2.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mq8.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mq9.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mqj.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mqe.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mqf.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mqg.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QEN3.Mq7.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mqh.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mqi.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mq4.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mqd.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mqb.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mqk.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QEN3.Mq3.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mqc.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mq7.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mq5.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mq6.out_post segs got_ssp ssp_guard) out_post (gw_ent (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) out_post gw_tbl_5)))))))))))))))))))))))))))))))))).
#[global] Arguments out_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F fc%_bv_scope S%_Z_scope bs%_list_scope lo%_Z_scope canary%_bv_scope m%_function_scope _ _ _.
Definition out_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QROt.Mq0.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QEN3.Mq6.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mqa.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QEN3.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QK0e.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mq0.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QEN3.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mq3.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QEN3.Mq8.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mq2.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QEN3.Mq0.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QEN3.Mq4.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QEN3.Mq5.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QEN3.Mq2.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mq8.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mq9.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mqj.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mqe.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mqf.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mqg.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QEN3.Mq7.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mqh.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mqi.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mq4.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mqd.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mqb.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mqk.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QEN3.Mq3.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mqc.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mq7.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mq5.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mq6.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt gw_tbl_6)))))))))))))))))))))))))))))))))).
#[global] Arguments out_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope.
Definition POST : ltac:(gw_rebind_ty (@QROt.Mq0.POST segs got_ssp ssp_guard) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@QROt.Mq0.POST segs got_ssp ssp_guard) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QROt.Mq0.POST segs got_ssp ssp_guard) POST (gw_ent (@QEN3.POST segs got_ssp ssp_guard) POST (gw_ent (@QK0e.POST segs got_ssp ssp_guard) POST (gw_ent (@QZxv.Mq0.POST segs got_ssp ssp_guard) POST (gw_ent (@QZxv.Mq1.POST segs got_ssp ssp_guard) POST (gw_ent (@QEN3.Mq1.POST segs got_ssp ssp_guard) POST (gw_ent (@QZxv.Mq3.POST segs got_ssp ssp_guard) POST (gw_ent (@QZxv.Mq2.POST segs got_ssp ssp_guard) POST (gw_ent (@QEN3.Mq0.POST segs got_ssp ssp_guard) POST (gw_ent (@QEN3.Mq4.POST segs got_ssp ssp_guard) POST (gw_ent (@QEN3.Mq5.POST segs got_ssp ssp_guard) POST (gw_ent (@QZxv.Mq8.POST segs got_ssp ssp_guard) POST (gw_ent (@QZxv.Mq9.POST segs got_ssp ssp_guard) POST (gw_ent (@QZxv.Mqj.POST segs got_ssp ssp_guard) POST (gw_ent (@QZxv.Mqe.POST segs got_ssp ssp_guard) POST (gw_ent (@QZxv.Mqf.POST segs got_ssp ssp_guard) POST (gw_ent (@QZxv.Mqg.POST segs got_ssp ssp_guard) POST (gw_ent (@QEN3.Mq7.POST segs got_ssp ssp_guard) POST (gw_ent (@QZxv.Mqh.POST segs got_ssp ssp_guard) POST (gw_ent (@QZxv.Mqi.POST segs got_ssp ssp_guard) POST (gw_ent (@QZxv.Mq5.POST segs got_ssp ssp_guard) POST (gw_ent (@QZxv.Mq6.POST segs got_ssp ssp_guard) POST gw_tbl_7)))))))))))))))))))))).
#[global] Arguments POST {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F m0%_function_scope lo%_Z_scope canary%_bv_scope AP%_Z_scope _%_Z_scope _ _.
Definition finv : ltac:(gw_rebind_ty (@QROt.Mq0.finv segs got_ssp ssp_guard) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@QROt.Mq0.finv segs got_ssp ssp_guard) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QROt.Mq0.finv segs got_ssp ssp_guard) finv (gw_ent (@QEN3.Mq6.finv segs got_ssp ssp_guard) finv (gw_ent (@QZxv.Mqa.finv segs got_ssp ssp_guard) finv (gw_ent (@QEN3.finv segs got_ssp ssp_guard) finv (gw_ent (@QK0e.finv segs got_ssp ssp_guard) finv (gw_ent (@QZxv.Mq0.finv segs got_ssp ssp_guard) finv (gw_ent (@QZxv.Mq1.finv segs got_ssp ssp_guard) finv (gw_ent (@QEN3.Mq1.finv segs got_ssp ssp_guard) finv (gw_ent (@QZxv.Mq3.finv segs got_ssp ssp_guard) finv (gw_ent (@QZxv.Mq2.finv segs got_ssp ssp_guard) finv (gw_ent (@QEN3.Mq0.finv segs got_ssp ssp_guard) finv (gw_ent (@QEN3.Mq4.finv segs got_ssp ssp_guard) finv (gw_ent (@QEN3.Mq5.finv segs got_ssp ssp_guard) finv (gw_ent (@QZxv.Mq8.finv segs got_ssp ssp_guard) finv (gw_ent (@QZxv.Mq9.finv segs got_ssp ssp_guard) finv (gw_ent (@QZxv.Mqj.finv segs got_ssp ssp_guard) finv (gw_ent (@QZxv.Mqe.finv segs got_ssp ssp_guard) finv (gw_ent (@QZxv.Mqf.finv segs got_ssp ssp_guard) finv (gw_ent (@QZxv.Mqg.finv segs got_ssp ssp_guard) finv (gw_ent (@QEN3.Mq7.finv segs got_ssp ssp_guard) finv (gw_ent (@QZxv.Mqh.finv segs got_ssp ssp_guard) finv (gw_ent (@QZxv.Mqi.finv segs got_ssp ssp_guard) finv (gw_ent (@QZxv.Mq4.finv segs got_ssp ssp_guard) finv (gw_ent (@QZxv.Mqd.finv segs got_ssp ssp_guard) finv (gw_ent (@QZxv.Mqb.finv segs got_ssp ssp_guard) finv (gw_ent (@QZxv.Mqk.finv segs got_ssp ssp_guard) finv (gw_ent (@QEN3.Mq3.finv segs got_ssp ssp_guard) finv (gw_ent (@QZxv.Mqc.finv segs got_ssp ssp_guard) finv (gw_ent (@QZxv.Mq7.finv segs got_ssp ssp_guard) finv (gw_ent (@QZxv.Mq5.finv segs got_ssp ssp_guard) finv (gw_ent (@QZxv.Mq6.finv segs got_ssp ssp_guard) finv gw_tbl_8))))))))))))))))))))))))))))))).
Definition lo_cells : ltac:(gw_rebind_ty (@QROt.Mq0.lo_cells ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QROt.Mq0.lo_cells ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QROt.Mq0.lo_cells ssp_guard) lo_cells (gw_ent (@QEN3.Mq6.lo_cells ssp_guard) lo_cells (gw_ent (@QZxv.Mqa.lo_cells ssp_guard) lo_cells (gw_ent (@QEN3.lo_cells ssp_guard) lo_cells (gw_ent (@QK0e.lo_cells ssp_guard) lo_cells (gw_ent (@QZxv.Mq0.lo_cells ssp_guard) lo_cells (gw_ent (@QZxv.Mq1.lo_cells ssp_guard) lo_cells (gw_ent (@QEN3.Mq1.lo_cells ssp_guard) lo_cells (gw_ent (@QZxv.Mq3.lo_cells ssp_guard) lo_cells (gw_ent (@QZxv.Mq2.lo_cells ssp_guard) lo_cells (gw_ent (@QEN3.Mq0.lo_cells ssp_guard) lo_cells (gw_ent (@QEN3.Mq4.lo_cells ssp_guard) lo_cells (gw_ent (@QEN3.Mq5.lo_cells ssp_guard) lo_cells (gw_ent (@QZxv.Mq8.lo_cells ssp_guard) lo_cells (gw_ent (@QZxv.Mq9.lo_cells ssp_guard) lo_cells (gw_ent (@QZxv.Mqj.lo_cells ssp_guard) lo_cells (gw_ent (@QZxv.Mqe.lo_cells ssp_guard) lo_cells (gw_ent (@QZxv.Mqf.lo_cells ssp_guard) lo_cells (gw_ent (@QZxv.Mqg.lo_cells ssp_guard) lo_cells (gw_ent (@QEN3.Mq7.lo_cells ssp_guard) lo_cells (gw_ent (@QZxv.Mqh.lo_cells ssp_guard) lo_cells (gw_ent (@QZxv.Mqi.lo_cells ssp_guard) lo_cells (gw_ent (@QZxv.Mq4.lo_cells ssp_guard) lo_cells (gw_ent (@QZxv.Mqb.lo_cells ssp_guard) lo_cells (gw_ent (@QZxv.Mqk.lo_cells ssp_guard) lo_cells (gw_ent (@QZxv.Mq7.lo_cells ssp_guard) lo_cells (gw_ent (@QZxv.Mq5.lo_cells ssp_guard) lo_cells (gw_ent (@QZxv.Mq6.lo_cells ssp_guard) lo_cells gw_tbl_9)))))))))))))))))))))))))))).
Definition S_EXIT : ltac:(gw_rebind_ty (@QROt.Mq0.S_EXIT segs base got_ssp ssp_guard) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_EXIT segs base got_ssp ssp_guard) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QROt.Mq0.S_EXIT segs base got_ssp ssp_guard) S_EXIT (gw_ent (@QZxv.Mq5.S_EXIT segs base got_ssp ssp_guard) S_EXIT (gw_ent (@QZxv.Mq6.S_EXIT segs base got_ssp ssp_guard) S_EXIT gw_tbl_10))).
#[global] Arguments S_EXIT {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_END : ltac:(gw_rebind_ty (@QROt.Mq0.S_END segs base got_ssp ssp_guard) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_END segs base got_ssp ssp_guard) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QROt.Mq0.S_END segs base got_ssp ssp_guard) S_END (gw_ent (@QEN3.S_END segs base got_ssp ssp_guard) S_END (gw_ent (@QZxv.Mq5.S_END segs base got_ssp ssp_guard) S_END gw_tbl_11))).
#[global] Arguments S_END {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition POST1 : ltac:(gw_rebind_ty (@QROt.Mq0.POST1 segs got_ssp ssp_guard) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QROt.Mq0.POST1 segs got_ssp ssp_guard) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QROt.Mq0.POST1 segs got_ssp ssp_guard) POST1 (gw_ent (@QZxv.Mqa.POST1 segs got_ssp ssp_guard) POST1 (gw_ent (@QZxv.Mq7.POST1 segs got_ssp ssp_guard) POST1 gw_tbl_12))).
Definition S_EXIT1 : ltac:(gw_rebind_ty (@QROt.Mq0.S_EXIT1 segs base got_ssp ssp_guard) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_EXIT1 segs base got_ssp ssp_guard) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@QROt.Mq0.S_EXIT1 segs base got_ssp ssp_guard) S_EXIT1 (gw_ent (@QZxv.Mqa.S_EXIT1 segs base got_ssp ssp_guard) S_EXIT1 (gw_ent (@QZxv.Mq7.S_EXIT1 segs base got_ssp ssp_guard) S_EXIT1 gw_tbl_13))).
Definition S_SCAN : ltac:(gw_rebind_ty (@QROt.Mq0.S_SCAN segs base got_ssp ssp_guard) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_SCAN segs base got_ssp ssp_guard) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@QROt.Mq0.S_SCAN segs base got_ssp ssp_guard) S_SCAN (gw_ent (@QZxv.Mqa.S_SCAN segs base got_ssp ssp_guard) S_SCAN (gw_ent (@QEN3.S_SCAN segs base got_ssp ssp_guard) S_SCAN (gw_ent (@QZxv.Mqc.S_SCAN segs base got_ssp ssp_guard) S_SCAN gw_tbl_14)))).
Definition S_FLAGS : ltac:(gw_rebind_ty (@QROt.Mq0.S_FLAGS segs base got_ssp ssp_guard) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_FLAGS segs base got_ssp ssp_guard) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@QROt.Mq0.S_FLAGS segs base got_ssp ssp_guard) S_FLAGS (gw_ent (@QZxv.Mq4.S_FLAGS segs base got_ssp ssp_guard) S_FLAGS (gw_ent (@QEN3.Mq3.S_FLAGS segs base got_ssp ssp_guard) S_FLAGS gw_tbl_15))).
Definition S_WLOOP : ltac:(gw_rebind_ty (@QROt.Mq0.S_WLOOP segs base got_ssp ssp_guard) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_WLOOP segs base got_ssp ssp_guard) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@QROt.Mq0.S_WLOOP segs base got_ssp ssp_guard) S_WLOOP (gw_ent (@QZxv.Mqk.S_WLOOP segs base got_ssp ssp_guard) S_WLOOP gw_tbl_16)).
Definition S_WIDTH : ltac:(gw_rebind_ty (@QROt.Mq0.S_WIDTH segs base got_ssp ssp_guard) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_WIDTH segs base got_ssp ssp_guard) constr:(gw_tbl_17)).
Local Definition gw_tbl_18 := (gw_ent (@QROt.Mq0.S_WIDTH segs base got_ssp ssp_guard) S_WIDTH (gw_ent (@QZxv.Mq4.S_WIDTH segs base got_ssp ssp_guard) S_WIDTH (gw_ent (@QZxv.Mqk.S_WIDTH segs base got_ssp ssp_guard) S_WIDTH gw_tbl_17))).
Definition S_PLOOP : ltac:(gw_rebind_ty (@QROt.Mq0.S_PLOOP segs base got_ssp ssp_guard) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_PLOOP segs base got_ssp ssp_guard) constr:(gw_tbl_18)).
Local Definition gw_tbl_19 := (gw_ent (@QROt.Mq0.S_PLOOP segs base got_ssp ssp_guard) S_PLOOP (gw_ent (@QZxv.Mqb.S_PLOOP segs base got_ssp ssp_guard) S_PLOOP gw_tbl_18)).
Definition S_PREC : ltac:(gw_rebind_ty (@QROt.Mq0.S_PREC segs base got_ssp ssp_guard) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_PREC segs base got_ssp ssp_guard) constr:(gw_tbl_19)).
Local Definition gw_tbl_20 := (gw_ent (@QROt.Mq0.S_PREC segs base got_ssp ssp_guard) S_PREC (gw_ent (@QZxv.Mq4.S_PREC segs base got_ssp ssp_guard) S_PREC (gw_ent (@QZxv.Mqb.S_PREC segs base got_ssp ssp_guard) S_PREC gw_tbl_19))).
Definition S_STATE : ltac:(gw_rebind_ty (@QROt.Mq0.S_STATE segs base got_ssp ssp_guard) constr:(gw_tbl_20)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_STATE segs base got_ssp ssp_guard) constr:(gw_tbl_20)).
Local Definition gw_tbl_21 := (gw_ent (@QROt.Mq0.S_STATE segs base got_ssp ssp_guard) S_STATE (gw_ent (@QZxv.Mq4.S_STATE segs base got_ssp ssp_guard) S_STATE (gw_ent (@QZxv.Mqd.S_STATE segs base got_ssp ssp_guard) S_STATE gw_tbl_20))).
Definition S_STATEL : ltac:(gw_rebind_ty (@QROt.Mq0.S_STATEL segs base got_ssp ssp_guard) constr:(gw_tbl_21)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_STATEL segs base got_ssp ssp_guard) constr:(gw_tbl_21)).
Local Definition gw_tbl_22 := (gw_ent (@QROt.Mq0.S_STATEL segs base got_ssp ssp_guard) S_STATEL (gw_ent (@QZxv.Mq4.S_STATEL segs base got_ssp ssp_guard) S_STATEL (gw_ent (@QZxv.Mqd.S_STATEL segs base got_ssp ssp_guard) S_STATEL gw_tbl_21))).
Definition S_DIR : ltac:(gw_rebind_ty (@QROt.Mq0.S_DIR segs base got_ssp ssp_guard) constr:(gw_tbl_22)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_DIR segs base got_ssp ssp_guard) constr:(gw_tbl_22)).
Local Definition gw_tbl_23 := (gw_ent (@QROt.Mq0.S_DIR segs base got_ssp ssp_guard) S_DIR (gw_ent (@QZxv.Mqa.S_DIR segs base got_ssp ssp_guard) S_DIR (gw_ent (@QEN3.S_DIR segs base got_ssp ssp_guard) S_DIR (gw_ent (@QZxv.Mq4.S_DIR segs base got_ssp ssp_guard) S_DIR gw_tbl_22)))).
Definition memset_postZ : ltac:(gw_rebind_ty (@Q91D.Mq2.memset_postZ segs) constr:(gw_tbl_23)) := ltac:(gw_rebind_tm (@Q91D.Mq2.memset_postZ segs) constr:(gw_tbl_23)).
Local Definition gw_tbl_24 := (gw_ent (@QZxv.Mqe.memset_postZ segs) memset_postZ (gw_ent (@QZxv.Mqg.memset_postZ segs) memset_postZ (gw_ent (@QEN3.Mq7.memset_postZ segs) memset_postZ (gw_ent (@QZxv.Mqi.memset_postZ segs) memset_postZ (gw_ent (@Q91D.Mq2.memset_postZ segs) memset_postZ gw_tbl_23))))).
Definition out_postq : ltac:(gw_rebind_ty (@QROt.Mq0.out_postq segs got_ssp ssp_guard) constr:(gw_tbl_24)) := ltac:(gw_rebind_tm (@QROt.Mq0.out_postq segs got_ssp ssp_guard) constr:(gw_tbl_24)).
Local Definition gw_tbl_25 := (gw_ent (@QROt.Mq0.out_postq segs got_ssp ssp_guard) out_postq (gw_ent (@QEN3.out_postq segs got_ssp ssp_guard) out_postq (gw_ent (@QZxv.Mqe.out_postq segs got_ssp ssp_guard) out_postq (gw_ent (@QZxv.Mqf.out_postq segs got_ssp ssp_guard) out_postq (gw_ent (@QZxv.Mqg.out_postq segs got_ssp ssp_guard) out_postq (gw_ent (@QEN3.Mq7.out_postq segs got_ssp ssp_guard) out_postq (gw_ent (@QZxv.Mqh.out_postq segs got_ssp ssp_guard) out_postq (gw_ent (@QZxv.Mqi.out_postq segs got_ssp ssp_guard) out_postq gw_tbl_24)))))))).
#[global] Arguments out_postq {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope q%_Z_scope gp%_bv_scope tp%_bv_scope lo%_Z_scope canary%_bv_scope ra'%_bv_scope Ft fc%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope S%_Z_scope bs%_list_scope m%_function_scope _ _ _.
Definition arg_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_25)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_25)).
Local Definition gw_tbl_26 := (gw_ent (@QROt.Mq0.arg_ok segs) arg_ok (gw_ent (@QEN3.arg_ok segs) arg_ok (gw_ent (@QK0e.arg_ok segs) arg_ok (gw_ent (@QZxv.Mq0.arg_ok segs) arg_ok (gw_ent (@QZxv.Mq1.arg_ok segs) arg_ok (gw_ent (@QEN3.Mq1.arg_ok segs) arg_ok (gw_ent (@QZxv.Mq3.arg_ok segs) arg_ok (gw_ent (@QZxv.Mq2.arg_ok segs) arg_ok (gw_ent (@QEN3.Mq0.arg_ok segs) arg_ok (gw_ent (@QEN3.Mq4.arg_ok segs) arg_ok (gw_ent (@QEN3.Mq5.arg_ok segs) arg_ok (gw_ent (@QZxv.Mq8.arg_ok segs) arg_ok (gw_ent (@QZxv.Mq9.arg_ok segs) arg_ok (gw_ent (@QZxv.Mqj.arg_ok segs) arg_ok (gw_ent (@QZxv.Mqe.arg_ok segs) arg_ok (gw_ent (@QZxv.Mqf.arg_ok segs) arg_ok (gw_ent (@QZxv.Mqg.arg_ok segs) arg_ok (gw_ent (@QEN3.Mq7.arg_ok segs) arg_ok (gw_ent (@QZxv.Mqh.arg_ok segs) arg_ok (gw_ent (@QZxv.Mqi.arg_ok segs) arg_ok (gw_ent (@Q8l1.Mq1.arg_ok segs) arg_ok gw_tbl_25))))))))))))))))))))).
Definition args_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_26)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_26)).
Local Definition gw_tbl_27 := (gw_ent (@QROt.Mq0.args_ok segs) args_ok (gw_ent (@QEN3.args_ok segs) args_ok (gw_ent (@QK0e.args_ok segs) args_ok (gw_ent (@QZxv.Mq0.args_ok segs) args_ok (gw_ent (@QZxv.Mq1.args_ok segs) args_ok (gw_ent (@QEN3.Mq1.args_ok segs) args_ok (gw_ent (@QZxv.Mq3.args_ok segs) args_ok (gw_ent (@QZxv.Mq2.args_ok segs) args_ok (gw_ent (@QEN3.Mq0.args_ok segs) args_ok (gw_ent (@QEN3.Mq4.args_ok segs) args_ok (gw_ent (@QEN3.Mq5.args_ok segs) args_ok (gw_ent (@QZxv.Mq8.args_ok segs) args_ok (gw_ent (@QZxv.Mq9.args_ok segs) args_ok (gw_ent (@QZxv.Mqj.args_ok segs) args_ok (gw_ent (@QZxv.Mqe.args_ok segs) args_ok (gw_ent (@QZxv.Mqf.args_ok segs) args_ok (gw_ent (@QZxv.Mqg.args_ok segs) args_ok (gw_ent (@QEN3.Mq7.args_ok segs) args_ok (gw_ent (@QZxv.Mqh.args_ok segs) args_ok (gw_ent (@QZxv.Mqi.args_ok segs) args_ok (gw_ent (@Q8l1.Mq1.args_ok segs) args_ok gw_tbl_26))))))))))))))))))))).
Definition fpcall_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) constr:(gw_tbl_27)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) constr:(gw_tbl_27)).
Local Definition gw_tbl_28 := (gw_ent (@QROt.Mq0.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QEN3.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QK0e.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QZxv.Mq0.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QZxv.Mq1.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QEN3.Mq1.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QZxv.Mq3.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QZxv.Mq2.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QEN3.Mq0.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QEN3.Mq4.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QEN3.Mq5.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QZxv.Mq8.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QZxv.Mq9.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QZxv.Mqj.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QZxv.Mqe.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QZxv.Mqf.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QZxv.Mqg.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QEN3.Mq7.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QZxv.Mqh.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QZxv.Mqi.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) fpcall_post gw_tbl_27))))))))))))))))))))).
#[global] Arguments fpcall_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F lo%_Z_scope canary%_bv_scope m%_function_scope _%_Z_scope _ _.
Definition fpcall_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_28)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_28)).
Local Definition gw_tbl_29 := (gw_ent (@QROt.Mq0.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QEN3.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QK0e.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QZxv.Mq0.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QZxv.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QEN3.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QZxv.Mq3.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QZxv.Mq2.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QEN3.Mq0.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QEN3.Mq4.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QEN3.Mq5.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QZxv.Mq8.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QZxv.Mq9.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QZxv.Mqj.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QZxv.Mqe.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QZxv.Mqf.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QZxv.Mqg.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QEN3.Mq7.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QZxv.Mqh.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QZxv.Mqi.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt gw_tbl_28))))))))))))))))))))).
#[global] Arguments fpcall_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUTFP%_function_scope c.
Definition S_HEAD : ltac:(gw_rebind_ty (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_29)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_29)).
Local Definition gw_tbl_30 := (gw_ent (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD (gw_ent (@QEN3.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD (gw_ent (@QK0e.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD (gw_ent (@QZxv.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD (gw_ent (@QZxv.Mq1.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD (gw_ent (@QEN3.Mq1.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD (gw_ent (@QZxv.Mq3.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD (gw_ent (@QZxv.Mq2.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD (gw_ent (@QEN3.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD (gw_ent (@QEN3.Mq4.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD (gw_ent (@QEN3.Mq5.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD (gw_ent (@QZxv.Mq8.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD (gw_ent (@QZxv.Mq9.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD (gw_ent (@QZxv.Mqj.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD (gw_ent (@QZxv.Mqe.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD (gw_ent (@QZxv.Mqf.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD (gw_ent (@QZxv.Mqg.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD (gw_ent (@QEN3.Mq7.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD (gw_ent (@QZxv.Mqh.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD (gw_ent (@QZxv.Mqi.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD gw_tbl_29)))))))))))))))))))).
#[global] Arguments S_HEAD {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope fuel%_nat_scope.
Definition tinv : ltac:(gw_rebind_ty (@QROt.Mq0.tinv segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_30)) := ltac:(gw_rebind_tm (@QROt.Mq0.tinv segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_30)).
Local Definition gw_tbl_31 := (gw_ent (@QROt.Mq0.tinv segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) tinv (gw_ent (@QZxv.Mqj.tinv segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) tinv (gw_ent (@QZxv.Mqe.tinv segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) tinv (gw_ent (@QZxv.Mqf.tinv segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) tinv (gw_ent (@QZxv.Mqg.tinv segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) tinv (gw_ent (@QEN3.Mq7.tinv segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) tinv (gw_ent (@QZxv.Mqh.tinv segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) tinv (gw_ent (@QZxv.Mqi.tinv segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) tinv gw_tbl_30)))))))).
#[global] Arguments tinv {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope m%_function_scope st k%_Z_scope i4%_Z_scope args%_list_scope fuel%_nat_scope PFXA%_Z_scope fl%_Z_scope n%_Z_scope pl%_Z_scope pq%_Z_scope BA%_Z_scope prefix%_list_scope body%_list_scope alo%_bv_scope ahi%_bv_scope j128%_list_scope digs%_list_scope pad%_list_scope.
Definition S_T6 : ltac:(gw_rebind_ty (@QROt.Mq0.S_T6 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_31)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_T6 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_31)).
Local Definition gw_tbl_32 := (gw_ent (@QROt.Mq0.S_T6 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T6 (gw_ent (@QZxv.Mqh.S_T6 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T6 (gw_ent (@QZxv.Mqi.S_T6 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T6 gw_tbl_31))).
#[global] Arguments S_T6 {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_T5 : ltac:(gw_rebind_ty (@QROt.Mq0.S_T5 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_32)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_T5 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_32)).
Local Definition gw_tbl_33 := (gw_ent (@QROt.Mq0.S_T5 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T5 (gw_ent (@QEN3.Mq7.S_T5 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T5 (gw_ent (@QZxv.Mqh.S_T5 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T5 gw_tbl_32))).
#[global] Arguments S_T5 {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_T4 : ltac:(gw_rebind_ty (@QROt.Mq0.S_T4 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_33)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_T4 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_33)).
Local Definition gw_tbl_34 := (gw_ent (@QROt.Mq0.S_T4 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T4 (gw_ent (@QZxv.Mqg.S_T4 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T4 (gw_ent (@QEN3.Mq7.S_T4 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T4 gw_tbl_33))).
#[global] Arguments S_T4 {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_T3 : ltac:(gw_rebind_ty (@QROt.Mq0.S_T3 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_34)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_T3 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_34)).
Local Definition gw_tbl_35 := (gw_ent (@QROt.Mq0.S_T3 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T3 (gw_ent (@QZxv.Mqf.S_T3 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T3 (gw_ent (@QZxv.Mqg.S_T3 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T3 gw_tbl_34))).
#[global] Arguments S_T3 {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_T2 : ltac:(gw_rebind_ty (@QROt.Mq0.S_T2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_35)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_T2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_35)).
Local Definition gw_tbl_36 := (gw_ent (@QROt.Mq0.S_T2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T2 (gw_ent (@QZxv.Mqj.S_T2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T2 (gw_ent (@QZxv.Mqe.S_T2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T2 (gw_ent (@QZxv.Mqf.S_T2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T2 gw_tbl_35)))).
#[global] Arguments S_T2 {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_T1 : ltac:(gw_rebind_ty (@QROt.Mq0.S_T1 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_36)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_T1 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_36)).
Local Definition gw_tbl_37 := (gw_ent (@QROt.Mq0.S_T1 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T1 (gw_ent (@QZxv.Mqj.S_T1 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T1 (gw_ent (@QZxv.Mqe.S_T1 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T1 gw_tbl_36))).
#[global] Arguments S_T1 {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_TAIL : ltac:(gw_rebind_ty (@QROt.Mq0.S_TAIL segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_37)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_TAIL segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_37)).
Local Definition gw_tbl_38 := (gw_ent (@QROt.Mq0.S_TAIL segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_TAIL (gw_ent (@QZxv.Mq0.S_TAIL segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_TAIL (gw_ent (@QEN3.Mq1.S_TAIL segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_TAIL (gw_ent (@QZxv.Mq9.S_TAIL segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_TAIL (gw_ent (@QZxv.Mqj.S_TAIL segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_TAIL gw_tbl_37))))).
#[global] Arguments S_TAIL {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_INTC2 : ltac:(gw_rebind_ty (@QROt.Mq0.S_INTC2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_38)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_INTC2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_38)).
Local Definition gw_tbl_39 := (gw_ent (@QROt.Mq0.S_INTC2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_INTC2 (gw_ent (@QZxv.Mq8.S_INTC2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_INTC2 (gw_ent (@QZxv.Mq9.S_INTC2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_INTC2 gw_tbl_38))).
#[global] Arguments S_INTC2 {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_INTC : ltac:(gw_rebind_ty (@QROt.Mq0.S_INTC segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_39)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_INTC segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_39)).
Local Definition gw_tbl_40 := (gw_ent (@QROt.Mq0.S_INTC segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_INTC (gw_ent (@QZxv.Mq3.S_INTC segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_INTC (gw_ent (@QEN3.Mq5.S_INTC segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_INTC (gw_ent (@QZxv.Mq8.S_INTC segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_INTC gw_tbl_39)))).
#[global] Arguments S_INTC {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition dloop_post : ltac:(gw_rebind_ty (@QROt.Mq0.dloop_post segs base) constr:(gw_tbl_40)) := ltac:(gw_rebind_tm (@QROt.Mq0.dloop_post segs base) constr:(gw_tbl_40)).
Local Definition gw_tbl_41 := (gw_ent (@QROt.Mq0.dloop_post segs base) dloop_post (gw_ent (@QEN3.Mq4.dloop_post segs base) dloop_post (gw_ent (@QEN3.Mq2.dloop_post segs base) dloop_post gw_tbl_40))).
Definition S_DLOOP : ltac:(gw_rebind_ty (@QROt.Mq0.S_DLOOP segs base) constr:(gw_tbl_41)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_DLOOP segs base) constr:(gw_tbl_41)).
Local Definition gw_tbl_42 := (gw_ent (@QROt.Mq0.S_DLOOP segs base) S_DLOOP (gw_ent (@QEN3.Mq4.S_DLOOP segs base) S_DLOOP (gw_ent (@QEN3.Mq2.S_DLOOP segs base) S_DLOOP gw_tbl_41))).
Definition S_FMTU2 : ltac:(gw_rebind_ty (@QROt.Mq0.S_FMTU2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_42)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_FMTU2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_42)).
Local Definition gw_tbl_43 := (gw_ent (@QROt.Mq0.S_FMTU2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_FMTU2 (gw_ent (@QEN3.Mq4.S_FMTU2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_FMTU2 (gw_ent (@QEN3.Mq5.S_FMTU2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_FMTU2 gw_tbl_42))).
#[global] Arguments S_FMTU2 {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_FMTU : ltac:(gw_rebind_ty (@QROt.Mq0.S_FMTU segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_43)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_FMTU segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_43)).
Local Definition gw_tbl_44 := (gw_ent (@QROt.Mq0.S_FMTU segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_FMTU (gw_ent (@QZxv.Mq2.S_FMTU segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_FMTU (gw_ent (@QEN3.Mq0.S_FMTU segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_FMTU (gw_ent (@QEN3.Mq4.S_FMTU segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_FMTU gw_tbl_43)))).
#[global] Arguments S_FMTU {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_CV_D : ltac:(gw_rebind_ty (@QROt.Mq0.S_CV_D segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_44)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_CV_D segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_44)).
Local Definition gw_tbl_45 := (gw_ent (@QROt.Mq0.S_CV_D segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_D (gw_ent (@QK0e.S_CV_D segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_D (gw_ent (@QEN3.Mq0.S_CV_D segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_D gw_tbl_44))).
#[global] Arguments S_CV_D {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_CV_U : ltac:(gw_rebind_ty (@QROt.Mq0.S_CV_U segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_45)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_CV_U segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_45)).
Local Definition gw_tbl_46 := (gw_ent (@QROt.Mq0.S_CV_U segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_U (gw_ent (@QK0e.S_CV_U segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_U (gw_ent (@QZxv.Mq2.S_CV_U segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_U gw_tbl_45))).
#[global] Arguments S_CV_U {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition xloop_post : ltac:(gw_rebind_ty (@QROt.Mq0.xloop_post segs base) constr:(gw_tbl_46)) := ltac:(gw_rebind_tm (@QROt.Mq0.xloop_post segs base) constr:(gw_tbl_46)).
Local Definition gw_tbl_47 := (gw_ent (@QROt.Mq0.xloop_post segs base) xloop_post (gw_ent (@QZxv.Mq3.xloop_post segs base) xloop_post (gw_ent (@QEN3.Mq8.xloop_post segs base) xloop_post gw_tbl_46))).
Definition S_XLOOP : ltac:(gw_rebind_ty (@QROt.Mq0.S_XLOOP segs base) constr:(gw_tbl_47)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_XLOOP segs base) constr:(gw_tbl_47)).
Local Definition gw_tbl_48 := (gw_ent (@QROt.Mq0.S_XLOOP segs base) S_XLOOP (gw_ent (@QZxv.Mq3.S_XLOOP segs base) S_XLOOP (gw_ent (@QEN3.Mq8.S_XLOOP segs base) S_XLOOP gw_tbl_47))).
Definition S_CV_X : ltac:(gw_rebind_ty (@QROt.Mq0.S_CV_X segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_48)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_CV_X segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_48)).
Local Definition gw_tbl_49 := (gw_ent (@QROt.Mq0.S_CV_X segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_X (gw_ent (@QK0e.S_CV_X segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_X (gw_ent (@QZxv.Mq3.S_CV_X segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_X gw_tbl_48))).
#[global] Arguments S_CV_X {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition strnlen_post : ltac:(gw_rebind_ty (@Q91D.Mq6.strnlen_post segs) constr:(gw_tbl_49)) := ltac:(gw_rebind_tm (@Q91D.Mq6.strnlen_post segs) constr:(gw_tbl_49)).
Local Definition gw_tbl_50 := (gw_ent (@QROt.Mq0.strnlen_post segs) strnlen_post (gw_ent (@QK0e.strnlen_post segs) strnlen_post (gw_ent (@QEN3.Mq1.strnlen_post segs) strnlen_post (gw_ent (@Q91D.Mq6.strnlen_post segs) strnlen_post gw_tbl_49)))).
Definition pop_arg_post : ltac:(gw_rebind_ty (@Q91D.Mq3.pop_arg_post segs) constr:(gw_tbl_50)) := ltac:(gw_rebind_tm (@Q91D.Mq3.pop_arg_post segs) constr:(gw_tbl_50)).
Local Definition gw_tbl_51 := (gw_ent (@QROt.Mq0.pop_arg_post segs) pop_arg_post (gw_ent (@QK0e.pop_arg_post segs) pop_arg_post (gw_ent (@QEN3.Mq1.pop_arg_post segs) pop_arg_post (gw_ent (@Q91D.Mq3.pop_arg_post segs) pop_arg_post gw_tbl_50)))).
Definition S_CV_S : ltac:(gw_rebind_ty (@QROt.Mq0.S_CV_S segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_51)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_CV_S segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_51)).
Local Definition gw_tbl_52 := (gw_ent (@QROt.Mq0.S_CV_S segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_S (gw_ent (@QK0e.S_CV_S segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_S (gw_ent (@QEN3.Mq1.S_CV_S segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_S gw_tbl_51))).
#[global] Arguments S_CV_S {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_CV_FP : ltac:(gw_rebind_ty (@QROt.Mq0.S_CV_FP segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_52)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_CV_FP segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_52)).
Local Definition gw_tbl_53 := (gw_ent (@QROt.Mq0.S_CV_FP segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_FP (gw_ent (@QK0e.S_CV_FP segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_FP (gw_ent (@QZxv.Mq1.S_CV_FP segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_FP gw_tbl_52))).
#[global] Arguments S_CV_FP {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_CV_C : ltac:(gw_rebind_ty (@QROt.Mq0.S_CV_C segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_53)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_CV_C segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_53)).
Local Definition gw_tbl_54 := (gw_ent (@QROt.Mq0.S_CV_C segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_C (gw_ent (@QK0e.S_CV_C segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_C (gw_ent (@QZxv.Mq0.S_CV_C segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_C gw_tbl_53))).
#[global] Arguments S_CV_C {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition lo_cells14 : ltac:(gw_rebind_ty (@QROt.Mq0.lo_cells14 ssp_guard) constr:(gw_tbl_54)) := ltac:(gw_rebind_tm (@QROt.Mq0.lo_cells14 ssp_guard) constr:(gw_tbl_54)).
Local Definition gw_tbl_55 := (gw_ent (@QROt.Mq0.lo_cells14 ssp_guard) lo_cells14 (gw_ent (@QK0e.lo_cells14 ssp_guard) lo_cells14 gw_tbl_54)).
Definition S_CONV : ltac:(gw_rebind_ty (@QROt.Mq0.S_CONV segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_55)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_CONV segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_55)).
Local Definition gw_tbl_56 := (gw_ent (@QROt.Mq0.S_CONV segs base got_ssp GLOBALS_TOP ssp_guard) S_CONV (gw_ent (@QEN3.S_CONV segs base got_ssp GLOBALS_TOP ssp_guard) S_CONV (gw_ent (@QK0e.S_CONV segs base got_ssp GLOBALS_TOP ssp_guard) S_CONV gw_tbl_55))).
#[global] Arguments S_CONV {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_P1 : ltac:(gw_rebind_ty (@QROt.Mq0.S_P1 segs base got_ssp ssp_guard) constr:(gw_tbl_56)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_P1 segs base got_ssp ssp_guard) constr:(gw_tbl_56)).
Local Definition gw_tbl_57 := (gw_ent (@QROt.Mq0.S_P1 segs base got_ssp ssp_guard) S_P1 (gw_ent (@QZxv.Mqa.S_P1 segs base got_ssp ssp_guard) S_P1 gw_tbl_56)).
Definition S_PRO : ltac:(gw_rebind_ty (@QROt.Mq0.S_PRO segs base got_ssp ssp_guard) constr:(gw_tbl_57)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_PRO segs base got_ssp ssp_guard) constr:(gw_tbl_57)).
Local Definition gw_tbl_58 := (gw_ent (@QROt.Mq0.S_PRO segs base got_ssp ssp_guard) S_PRO (gw_ent (@QEN3.Mq6.S_PRO segs base got_ssp ssp_guard) S_PRO gw_tbl_57)).
Definition printf_core_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.printf_core_post segs got_ssp ssp_guard) constr:(gw_tbl_58)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.printf_core_post segs got_ssp ssp_guard) constr:(gw_tbl_58)).
Local Definition gw_tbl_59 := (gw_ent (@Q8l1.Mq1.printf_core_post segs got_ssp ssp_guard) printf_core_post gw_tbl_58).
#[global] Arguments printf_core_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F AP%_Z_scope lo%_Z_scope canary%_bv_scope m%_function_scope _%_Z_scope _ _.
Definition printf_core_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.printf_core_stmt segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_59)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.printf_core_stmt segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_59)).
Local Definition gw_tbl_60 := (gw_ent (@Q8l1.Mq1.printf_core_stmt segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) printf_core_stmt gw_tbl_59).
#[global] Arguments printf_core_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope.
Definition printf_core1_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.printf_core1_post segs got_ssp ssp_guard) constr:(gw_tbl_60)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.printf_core1_post segs got_ssp ssp_guard) constr:(gw_tbl_60)).
Local Definition gw_tbl_61 := (gw_ent (@Q8l1.Mq1.printf_core1_post segs got_ssp ssp_guard) printf_core1_post gw_tbl_60).
Definition printf_core1_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.printf_core1_stmt segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_61)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.printf_core1_stmt segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_61)).
Local Definition gw_tbl_62 := (gw_ent (@Q8l1.Mq1.printf_core1_stmt segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) printf_core1_stmt gw_tbl_61).
Hypothesis memset_callZ : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q91D.Mq2.gw_all) (@Q91D.Mq2.memset_callZ) (base + 3940)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_62))) in let T := gw_fold_pcs T base (3940)%Z [0; 168]%Z in exact T).
Hypothesis strnlen_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q91D.Mq6.gw_all) (@Q91D.Mq6.strnlen_spec) e_2596c)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_62))) in exact T).
Hypothesis va_area_bound : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q91D.Mq3.gw_all) (@Q91D.Mq3.va_area_bound) (base + 3632)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_62))) in let T := gw_fold_pcs T base (3632)%Z [0]%Z in exact T).
Hypothesis pop_arg_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q91D.Mq3.gw_all) (@Q91D.Mq3.pop_arg_spec) (base + 3632)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_62))) in let T := gw_fold_pcs T base (3632)%Z [0]%Z in exact T).

Notation parg := G.T_printf.parg.

Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
Definition bytes_at_nil : ltac:(gw_ctx_fold_ty (@QROt.Mq0.bytes_at_nil) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.bytes_at_nil)).
Definition implM_eq_ms : ltac:(gw_ctx_fold_ty (@QROt.Mq0.implM_eq_ms) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.implM_eq_ms)).
#[global] Arguments implM_eq_ms {St}%_type_scope {X}%_type_scope c s Q%_function_scope ms ms' _ _.
Definition sink_store : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_store) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_store)).
#[global] Arguments sink_store {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR m%_function_scope st a%_Z_scope bs%_list_scope _ _ _ _ _.
Definition sink_call : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_call) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_call)).
#[global] Arguments sink_call {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR Wc%_list_scope m%_function_scope m'%_function_scope st _ _ _ _ _.
Ltac zl := unfold zlength in *; cbn [length] in *; lia.
Ltac ienter := lazymatch goal with |- Ql2m.Mq3.implM _ _ _ _ _ => unfold Ql2m.Mq3.implM; apply impl_from_evt | |- QlEo_c1.Mq0.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.

Definition F_printf_core_common__Fok_refl : ltac:(gw_ctx_fold_ty (@QROt.Mq0.Fok_refl) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.Fok_refl)).
Notation F_printf_core_common__POST := POST (only parsing).
Notation F_printf_core_common__POST1 := POST1 (only parsing).
Notation F_printf_core_common__S_CONV := S_CONV (only parsing).
Notation F_printf_core_common__S_CV_C := S_CV_C (only parsing).
Notation F_printf_core_common__S_CV_D := S_CV_D (only parsing).
Notation F_printf_core_common__S_CV_FP := S_CV_FP (only parsing).
Notation F_printf_core_common__S_CV_S := S_CV_S (only parsing).
Notation F_printf_core_common__S_CV_U := S_CV_U (only parsing).
Notation F_printf_core_common__S_CV_X := S_CV_X (only parsing).
Notation F_printf_core_common__S_DIR := S_DIR (only parsing).
Notation F_printf_core_common__S_DLOOP := S_DLOOP (only parsing).
Notation F_printf_core_common__S_END := S_END (only parsing).
Notation F_printf_core_common__S_EXIT := S_EXIT (only parsing).
Notation F_printf_core_common__S_EXIT1 := S_EXIT1 (only parsing).
Notation F_printf_core_common__S_FLAGS := S_FLAGS (only parsing).
Notation F_printf_core_common__S_FMTU := S_FMTU (only parsing).
Notation F_printf_core_common__S_FMTU2 := S_FMTU2 (only parsing).
Notation F_printf_core_common__S_HEAD := S_HEAD (only parsing).
Notation F_printf_core_common__S_INTC := S_INTC (only parsing).
Notation F_printf_core_common__S_INTC2 := S_INTC2 (only parsing).
Notation F_printf_core_common__S_P1 := S_P1 (only parsing).
Notation F_printf_core_common__S_PLOOP := S_PLOOP (only parsing).
Notation F_printf_core_common__S_PREC := S_PREC (only parsing).
Notation F_printf_core_common__S_PRO := S_PRO (only parsing).
Notation F_printf_core_common__S_SCAN := S_SCAN (only parsing).
Notation F_printf_core_common__S_STATE := S_STATE (only parsing).
Notation F_printf_core_common__S_STATEL := S_STATEL (only parsing).
Notation F_printf_core_common__S_T1 := S_T1 (only parsing).
Notation F_printf_core_common__S_T2 := S_T2 (only parsing).
Notation F_printf_core_common__S_T3 := S_T3 (only parsing).
Notation F_printf_core_common__S_T4 := S_T4 (only parsing).
Notation F_printf_core_common__S_T5 := S_T5 (only parsing).
Notation F_printf_core_common__S_T6 := S_T6 (only parsing).
Notation F_printf_core_common__S_TAIL := S_TAIL (only parsing).
Notation F_printf_core_common__S_WIDTH := S_WIDTH (only parsing).
Notation F_printf_core_common__S_WLOOP := S_WLOOP (only parsing).
Notation F_printf_core_common__S_XLOOP := S_XLOOP (only parsing).
Notation F_printf_core_common__implM_eq_ms := implM_eq_ms (only parsing).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).
Definition F_printf_core_conv__L_CONV : ltac:(gw_ctx_fold_ty (@QK0e.L_CONV) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QK0e.L_CONV)).
Definition F_printf_core_cvc__L_CV_C : ltac:(gw_ctx_fold_ty (@QZxv.Mq0.L_CV_C) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QZxv.Mq0.L_CV_C)).
Definition F_printf_core_cvd__L_CV_D : ltac:(gw_ctx_fold_ty (@QEN3.Mq0.L_CV_D) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QEN3.Mq0.L_CV_D)).
Definition F_printf_core_cvfp__L_CV_FP : ltac:(gw_ctx_fold_ty (@QZxv.Mq1.L_CV_FP) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QZxv.Mq1.L_CV_FP)).
Definition F_printf_core_cvs__L_CV_S : ltac:(gw_ctx_fold_ty (@QEN3.Mq1.L_CV_S) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QEN3.Mq1.L_CV_S)).
Definition F_printf_core_cvu__L_CV_U : ltac:(gw_ctx_fold_ty (@QZxv.Mq2.L_CV_U) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QZxv.Mq2.L_CV_U)).
Definition F_printf_core_cvx__L_CV_X : ltac:(gw_ctx_fold_ty (@QZxv.Mq3.L_CV_X) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QZxv.Mq3.L_CV_X)).
Definition F_printf_core_dir__L_DIR : ltac:(gw_ctx_fold_ty (@QZxv.Mq4.L_DIR) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QZxv.Mq4.L_DIR)).
Definition F_printf_core_dloop__L_DLOOP : ltac:(gw_ctx_fold_ty (@QEN3.Mq2.L_DLOOP) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QEN3.Mq2.L_DLOOP)).
Definition F_printf_core_end__L_END : ltac:(gw_ctx_fold_ty (@QZxv.Mq5.L_END) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QZxv.Mq5.L_END)).
Definition F_printf_core_exit__L_EXIT : ltac:(gw_ctx_fold_ty (@QZxv.Mq6.L_EXIT) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QZxv.Mq6.L_EXIT)).
Definition F_printf_core_exit1__L_EXIT1 : ltac:(gw_ctx_fold_ty (@QZxv.Mq7.L_EXIT1) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QZxv.Mq7.L_EXIT1)).
Definition F_printf_core_flags__L_FLAGS : ltac:(gw_ctx_fold_ty (@QEN3.Mq3.L_FLAGS) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QEN3.Mq3.L_FLAGS)).
Definition F_printf_core_fmtu__L_FMTU : ltac:(gw_ctx_fold_ty (@QEN3.Mq4.L_FMTU) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QEN3.Mq4.L_FMTU)).
Definition F_printf_core_fmtu2__L_FMTU2 : ltac:(gw_ctx_fold_ty (@QEN3.Mq5.L_FMTU2) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QEN3.Mq5.L_FMTU2)).
Definition F_printf_core_head__L_HEAD : ltac:(gw_ctx_fold_ty (@QEN3.L_HEAD) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QEN3.L_HEAD)).
Definition F_printf_core_intc__L_INTC : ltac:(gw_ctx_fold_ty (@QZxv.Mq8.L_INTC) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QZxv.Mq8.L_INTC)).
Definition F_printf_core_intc2__L_INTC2 : ltac:(gw_ctx_fold_ty (@QZxv.Mq9.L_INTC2) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QZxv.Mq9.L_INTC2)).
Definition F_printf_core_p1__L_P1 : ltac:(gw_ctx_fold_ty (@QZxv.Mqa.L_P1) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QZxv.Mqa.L_P1)).
Definition F_printf_core_prec__L_PLOOP : ltac:(gw_ctx_fold_ty (@QZxv.Mqb.L_PLOOP) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QZxv.Mqb.L_PLOOP)).
Definition F_printf_core_prec__L_PREC : ltac:(gw_ctx_fold_ty (@QZxv.Mqb.L_PREC) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QZxv.Mqb.L_PREC)).
Definition F_printf_core_pro__L_PRO : ltac:(gw_ctx_fold_ty (@QEN3.Mq6.L_PRO) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QEN3.Mq6.L_PRO)).
Definition F_printf_core_scan__L_SCAN : ltac:(gw_ctx_fold_ty (@QZxv.Mqc.L_SCAN) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QZxv.Mqc.L_SCAN)).
Definition F_printf_core_state__L_STATE : ltac:(gw_ctx_fold_ty (@QZxv.Mqd.L_STATE) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QZxv.Mqd.L_STATE)).
Definition F_printf_core_state__L_STATEL : ltac:(gw_ctx_fold_ty (@QZxv.Mqd.L_STATEL) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QZxv.Mqd.L_STATEL)).
Definition F_printf_core_t1__L_T1 : ltac:(gw_ctx_fold_ty (@QZxv.Mqe.L_T1) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QZxv.Mqe.L_T1)).
Definition F_printf_core_t2__L_T2 : ltac:(gw_ctx_fold_ty (@QZxv.Mqf.L_T2) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QZxv.Mqf.L_T2)).
Definition F_printf_core_t3__L_T3 : ltac:(gw_ctx_fold_ty (@QZxv.Mqg.L_T3) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QZxv.Mqg.L_T3)).
Definition F_printf_core_t4__L_T4 : ltac:(gw_ctx_fold_ty (@QEN3.Mq7.L_T4) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QEN3.Mq7.L_T4)).
Definition F_printf_core_t5__L_T5 : ltac:(gw_ctx_fold_ty (@QZxv.Mqh.L_T5) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QZxv.Mqh.L_T5)).
Definition F_printf_core_t6__L_T6 : ltac:(gw_ctx_fold_ty (@QZxv.Mqi.L_T6) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QZxv.Mqi.L_T6)).
Definition F_printf_core_tail__L_TAIL : ltac:(gw_ctx_fold_ty (@QZxv.Mqj.L_TAIL) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QZxv.Mqj.L_TAIL)).
Definition F_printf_core_width__L_WIDTH : ltac:(gw_ctx_fold_ty (@QZxv.Mqk.L_WIDTH) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QZxv.Mqk.L_WIDTH)).
Definition F_printf_core_width__L_WLOOP : ltac:(gw_ctx_fold_ty (@QZxv.Mqk.L_WLOOP) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QZxv.Mqk.L_WLOOP)).
Definition F_printf_core_xloop__L_XLOOP : ltac:(gw_ctx_fold_ty (@QEN3.Mq8.L_XLOOP) constr:(gw_tbl_62)) := ltac:(gw_ctx_fold_tm (@QEN3.Mq8.L_XLOOP)).

#[using="G_102fd G_107e0 G_11778 G_118c0 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_194bc e_194c8 e_197bc e_fwritex e_memset e_2596c e_memchr CODE BASE4 BASER D_22 E_22 D_25 E_25 D_81 E_81 D_281 E_281 D_282 E_282 D_332 E_332 D_333 E_333 D_360 E_360 D_362 E_362 D_389 E_389 D_395 E_395 D_396 E_396 D_438 E_438 D_439 E_439 D_453 E_453 D_454 E_454 D_467 E_467 D_468 E_468 D_473 E_473 D_474 E_474 D_533 E_533 D_534 E_534 D_543 E_543 D_545 E_545 D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 ANCH_25 ANCH_282 ANCH_333 ANCH_362 ANCH_396 ANCH_439 ANCH_454 ANCH_468 ANCH_474 ANCH_534 ANCH_545 LINK_81 LINK_381 LINK_383 LINK_389 LINK_530 LINK_627 LINK_639 LINK_648 LINK_655 LINK_668 LINK_680 LINK_689 LINK_701 LINK_713 LINK_722 LINK_729 LINK_742 LINK_754 LINK_762 LINK_798 LINK_883 LINK_907 RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 RNG_G_102fd ROM_G_102fd RNG_G_107e0 ROM_G_107e0 LAY_G_102fd_STATIC_SPLIT LAY_got_ssp_240_ssp_guard RNG_G_11778 JTL_jt_11778_o1504 ROM_jt_11778_50 JTL_jt_11778_o1432 ROM_jt_11778_35 ROM_jt_11778_40 JTL_jt_11778_o1800 ROM_jt_11778_34 JTL_jt_11778_o1744 ROM_jt_11778_52 JTL_jt_11778_o1864 ROM_jt_11778_55 ROM_jt_11778_23 JTL_jt_11778_o1352 ROM_jt_11778_36 ROM_jt_11778_37 ROM_jt_11778_38 ROM_jt_11778_4 ROM_jt_11778_5 ROM_jt_11778_6 memset_callZ strnlen_spec va_area_bound pop_arg_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Section PrintfCore.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Context {St : Type}.
Variables (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
(OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
Hypothesis SFL : sink_flags_stmt Fp SINK.
Hypothesis TOK : topok_stmt TOPOK.
Hypothesis HOUT : out_stmt Fp B BS SINK TOPOK OUT.
Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
(lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
Hypothesis QHI : (q < 2^63)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= STATIC_SPLIT)%Z.

Hypothesis SEP_F : (((got_ssp + 8)%Z <= Fp /\ Fp + 232 <= ssp_guard) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : (((ssp_guard + 8)%Z <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation ctx_all := (QROt.Mq0.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation W := (QROt.Mq0.W Fp B BS q lo AP).

Local Notation Fok_refl := (F_printf_core_common__Fok_refl F).

Local Notation POST := (F_printf_core_common__POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).

Local Notation implM_eq_ms := (F_printf_core_common__implM_eq_ms (St:=St)).
Local Notation sink_store := (F_printf_core_common__sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common__sink_call (St:=St) Fp B BS SINK SFR).

Local Notation S_EXIT := (F_printf_core_common__S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_SCAN := (F_printf_core_common__S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FLAGS := (F_printf_core_common__S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_WLOOP := (F_printf_core_common__S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_WIDTH := (F_printf_core_common__S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PLOOP := (F_printf_core_common__S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PREC := (F_printf_core_common__S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_STATE := (F_printf_core_common__S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_STATEL := (F_printf_core_common__S_STATEL Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_DIR := (F_printf_core_common__S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_END := (F_printf_core_common__S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_HEAD := (F_printf_core_common__S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CONV := (F_printf_core_common__S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Local Notation S_TAIL := (F_printf_core_common__S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (QROt.Mq0.tregs Fp q gp tp A).

Local Notation S_T6 := (F_printf_core_common__S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T5 := (F_printf_core_common__S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T4 := (F_printf_core_common__S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T3 := (F_printf_core_common__S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T2 := (F_printf_core_common__S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T1 := (F_printf_core_common__S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC2 := (F_printf_core_common__S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC := (F_printf_core_common__S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Local Notation S_DLOOP := (F_printf_core_common__S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU2 := (F_printf_core_common__S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU := (F_printf_core_common__S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_D := (F_printf_core_common__S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_U := (F_printf_core_common__S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Local Notation S_XLOOP := (F_printf_core_common__S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_X := (F_printf_core_common__S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_S := (F_printf_core_common__S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_FP := (F_printf_core_common__S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_C := (F_printf_core_common__S_CV_C (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation POST1 := (F_printf_core_common__POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
Local Notation S_EXIT1 := (F_printf_core_common__S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_P1 := (F_printf_core_common__S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PRO := (F_printf_core_common__S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Notation FPv := (Z_to_bv 64 Fp).

Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal | (progress (rewrite ?Z.shiftl_0_l, ?Z.shiftr_0_l); lia) ].
Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
Tactic Notation "jumpM" tactic3(tac) :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
end.
Local Ltac transport_call_extra segs_ W m m' MU WM ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ eapply (sink_call W m m' st) in H;
[ | exact MU | exact WM
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
end.
Local Ltac transport_chunks segs_ m a bs ::= transport_chunks_fast segs_ m a bs.
Local Ltac footprint_after_store segs_ m a bs ::= footprint_after_store_fast segs_ m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs_ m m' MU WM ::= transport_after_call_fast segs_ m m' MU WM.
Local Ltac lia ::= lia3.

Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal | (progress (rewrite ?Z.shiftl_0_l, ?Z.shiftr_0_l); lia) ].

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE LO"] Lemma L_EXIT : S_EXIT.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE LO St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
first [ apply F_printf_core_exit__L_EXIT; first [eassumption]
| intros; eapply F_printf_core_exit__L_EXIT; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP GLO HAP LO SEP_F VAHI"] Lemma L_END : S_END.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP GLO HAP LO SEP_F VAHI St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF QHI TQ FRM0 HA SEP_B HVA A0 BS0.
first [ apply F_printf_core_end__L_END; first [eassumption | eexact L_EXIT]
| intros; eapply F_printf_core_end__L_END; first [eassumption | eexact L_EXIT] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE LO"] Lemma L_EXIT1 : S_EXIT1.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE LO St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
first [ apply F_printf_core_exit1__L_EXIT1; first [eassumption]
| intros; eapply F_printf_core_exit1__L_EXIT1; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP STATIC_SPLIT CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP A0 HA HF"] Lemma L_SCAN : S_SCAN.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP STATIC_SPLIT CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP A0 HA HF St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt LO GLO QHI TQ FRM0 SEP_F SEP_B HAP HVA VAHI BS0.
first [ apply F_printf_core_scan__L_SCAN; first [eassumption]
| intros; eapply F_printf_core_scan__L_SCAN; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP HF"] Lemma L_FLAGS : S_FLAGS.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP HF St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
first [ apply F_printf_core_flags__L_FLAGS; first [eassumption]
| intros; eapply F_printf_core_flags__L_FLAGS; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP HF"] Lemma L_WLOOP : S_WLOOP.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP HF St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
first [ apply F_printf_core_width__L_WLOOP; first [eassumption]
| intros; eapply F_printf_core_width__L_WLOOP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE HF"] Lemma L_WIDTH : S_WLOOP -> S_WIDTH.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE HF St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
first [ intro; apply F_printf_core_width__L_WIDTH; first [eassumption]
| intros; eapply F_printf_core_width__L_WIDTH; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP HF"] Lemma L_PLOOP : S_PLOOP.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP HF St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
first [ apply F_printf_core_prec__L_PLOOP; first [eassumption]
| intros; eapply F_printf_core_prec__L_PLOOP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP HF"] Lemma L_PREC : S_PLOOP -> S_PREC.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP HF St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
first [ intro; apply F_printf_core_prec__L_PREC; first [eassumption]
| intros; eapply F_printf_core_prec__L_PREC; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_281 lo_282 G_118c0 GLOBALS_TOP CODE D_281 E_281 D_282 E_282 ANCH_282 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 HF"] Lemma L_STATE : S_STATE.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_281 lo_282 G_118c0 GLOBALS_TOP CODE D_281 E_281 D_282 E_282 ANCH_282 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 HF St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
first [ apply F_printf_core_state__L_STATE; first [eassumption]
| intros; eapply F_printf_core_state__L_STATE; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_281 lo_282 G_118c0 GLOBALS_TOP CODE D_281 E_281 D_282 E_282 ANCH_282 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 HF"] Lemma L_STATEL : S_STATEL.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_281 lo_282 G_118c0 GLOBALS_TOP CODE D_281 E_281 D_282 E_282 ANCH_282 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 HF St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
first [ apply F_printf_core_state__L_STATEL; first [eassumption]
| intros; eapply F_printf_core_state__L_STATEL; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_281 lo_282 G_118c0 GLOBALS_TOP CODE D_281 E_281 D_282 E_282 ANCH_282 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 HF"] Lemma L_DIR : S_DIR.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_281 lo_282 G_118c0 GLOBALS_TOP CODE D_281 E_281 D_282 E_282 ANCH_282 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 HF St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
first [ apply F_printf_core_dir__L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE | eexact L_STATEL]
| intros; eapply F_printf_core_dir__L_DIR; first [eassumption | eexact L_FLAGS | eexact (L_WIDTH L_WLOOP) | eexact (L_PREC L_PLOOP) | eexact L_STATE | eexact L_STATEL] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_742 joff_762 e_fwritex e_memset CODE BASE4 BASER D_742 E_742 D_762 E_762 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ"] Lemma L_T6 : S_T6.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_742 joff_762 e_fwritex e_memset CODE BASE4 BASER D_742 E_742 D_762 E_762 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ St Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF FRM0 A0 VAHI.
first [ apply F_printf_core_t6__L_T6; first [eassumption]
| intros; eapply F_printf_core_t6__L_T6; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_729 joff_742 joff_762 e_fwritex e_memset CODE BASE4 BASER D_729 E_729 D_742 E_742 D_762 E_762 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI"] Lemma L_T5 : S_T5.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_729 joff_742 joff_762 e_fwritex e_memset CODE BASE4 BASER D_729 E_729 D_742 E_742 D_762 E_762 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI St Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF FRM0 A0.
first [ apply F_printf_core_t5__L_T5; first [eassumption | eexact L_T6]
| intros; eapply F_printf_core_t5__L_T5; first [eassumption | eexact L_T6] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_701 joff_722 joff_729 joff_742 joff_762 e_fwritex e_memset CODE BASE4 BASER D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI"] Lemma L_T4 : S_T4.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_701 joff_722 joff_729 joff_742 joff_762 e_fwritex e_memset CODE BASE4 BASER D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI St Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF FRM0 A0.
first [ apply F_printf_core_t4__L_T4; first [eassumption | eexact L_T5]
| intros; eapply F_printf_core_t4__L_T4; first [eassumption | eexact L_T5] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 e_fwritex e_memset CODE BASE4 BASER D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI"] Lemma L_T3 : S_T3.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 e_fwritex e_memset CODE BASE4 BASER D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI St Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF FRM0 A0.
first [ apply F_printf_core_t3__L_T3; first [eassumption | eexact L_T4]
| intros; eapply F_printf_core_t3__L_T3; first [eassumption | eexact L_T4] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_655 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 e_fwritex e_memset CODE BASE4 BASER D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 LINK_655 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI"] Lemma L_T2 : S_T2.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_655 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 e_fwritex e_memset CODE BASE4 BASER D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 LINK_655 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI St Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF FRM0 A0.
first [ apply F_printf_core_t2__L_T2; first [eassumption | eexact L_T3]
| intros; eapply F_printf_core_t2__L_T2; first [eassumption | eexact L_T3] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_627 joff_648 joff_655 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 e_fwritex e_memset CODE BASE4 BASER D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 LINK_627 LINK_648 LINK_655 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI"] Lemma L_T1 : S_T1.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_627 joff_648 joff_655 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 e_fwritex e_memset CODE BASE4 BASER D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 LINK_627 LINK_648 LINK_655 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI St Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF FRM0 A0.
first [ apply F_printf_core_t1__L_T1; first [eassumption | eexact L_T2]
| intros; eapply F_printf_core_t1__L_T1; first [eassumption | eexact L_T2] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_627 joff_648 joff_655 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 e_fwritex e_memset CODE BASE4 BASER D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 LINK_627 LINK_648 LINK_655 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI"] Lemma L_TAIL : S_TAIL.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_627 joff_648 joff_655 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 e_fwritex e_memset CODE BASE4 BASER D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 LINK_627 LINK_648 LINK_655 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI St Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF FRM0 A0.
first [ apply F_printf_core_tail__L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2]
| intros; eapply F_printf_core_tail__L_TAIL; first [eassumption | eexact L_T1 | eexact L_T2] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_627 joff_648 joff_655 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 e_fwritex e_memset CODE BASE4 BASER D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 LINK_627 LINK_648 LINK_655 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI"] Lemma L_INTC2 : S_INTC2.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_627 joff_648 joff_655 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 e_fwritex e_memset CODE BASE4 BASER D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 LINK_627 LINK_648 LINK_655 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI St Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF FRM0 A0.
first [ apply F_printf_core_intc2__L_INTC2; first [eassumption | eexact L_TAIL]
| intros; eapply F_printf_core_intc2__L_INTC2; first [eassumption | eexact L_TAIL] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_627 joff_648 joff_655 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 e_fwritex e_memset CODE BASE4 BASER D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 LINK_627 LINK_648 LINK_655 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI"] Lemma L_INTC : S_INTC.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_627 joff_648 joff_655 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 e_fwritex e_memset CODE BASE4 BASER D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 LINK_627 LINK_648 LINK_655 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI St Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF FRM0 A0.
first [ apply F_printf_core_intc__L_INTC; first [eassumption | eexact L_INTC2]
| intros; eapply F_printf_core_intc__L_INTC; first [eassumption | eexact L_INTC2] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP GLO LO QHI"] Lemma L_DLOOP : S_DLOOP.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP GLO LO QHI St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
first [ apply F_printf_core_dloop__L_DLOOP; first [eassumption]
| intros; eapply F_printf_core_dloop__L_DLOOP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_627 joff_648 joff_655 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 e_fwritex e_memset CODE BASE4 BASER D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 LINK_627 LINK_648 LINK_655 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI"] Lemma L_FMTU2 : S_FMTU2.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_627 joff_648 joff_655 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 e_fwritex e_memset CODE BASE4 BASER D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 LINK_627 LINK_648 LINK_655 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI St Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF FRM0 A0.
first [ apply F_printf_core_fmtu2__L_FMTU2; first [eassumption | eexact L_INTC]
| intros; eapply F_printf_core_fmtu2__L_FMTU2; first [eassumption | eexact L_INTC] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_627 joff_648 joff_655 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 e_fwritex e_memset CODE BASE4 BASER D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 LINK_627 LINK_648 LINK_655 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI"] Lemma L_FMTU : S_FMTU.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_627 joff_648 joff_655 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 e_fwritex e_memset CODE BASE4 BASER D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 LINK_627 LINK_648 LINK_655 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI St Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF FRM0 A0.
first [ apply F_printf_core_fmtu__L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP]
| intros; eapply F_printf_core_fmtu__L_FMTU; first [eassumption | eexact L_FMTU2 | eexact L_DLOOP] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_360 hi_543 lo_362 lo_545 joff_627 joff_648 joff_655 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 G_102fd STATIC_SPLIT e_fwritex e_memset CODE BASE4 BASER D_360 E_360 D_362 E_362 D_543 E_543 D_545 E_545 D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 ANCH_362 ANCH_545 LINK_627 LINK_648 LINK_655 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd LAY_G_102fd_STATIC_SPLIT memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI"] Lemma L_CV_D : S_CV_D.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_360 hi_543 lo_362 lo_545 joff_627 joff_648 joff_655 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 G_102fd STATIC_SPLIT e_fwritex e_memset CODE BASE4 BASER D_360 E_360 D_362 E_362 D_543 E_543 D_545 E_545 D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 ANCH_362 ANCH_545 LINK_627 LINK_648 LINK_655 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd LAY_G_102fd_STATIC_SPLIT memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI St Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF FRM0 A0.
first [ apply F_printf_core_cvd__L_CV_D; first [eassumption | eexact L_FMTU]
| intros; eapply F_printf_core_cvd__L_CV_D; first [eassumption | eexact L_FMTU] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_438 lo_439 joff_627 joff_648 joff_655 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 G_102fd STATIC_SPLIT e_fwritex e_memset CODE BASE4 BASER D_438 E_438 D_439 E_439 D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 ANCH_439 LINK_627 LINK_648 LINK_655 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd LAY_G_102fd_STATIC_SPLIT memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI"] Lemma L_CV_U : S_CV_U.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_438 lo_439 joff_627 joff_648 joff_655 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 G_102fd STATIC_SPLIT e_fwritex e_memset CODE BASE4 BASER D_438 E_438 D_439 E_439 D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 ANCH_439 LINK_627 LINK_648 LINK_655 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd LAY_G_102fd_STATIC_SPLIT memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI St Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF FRM0 A0.
first [ apply F_printf_core_cvu__L_CV_U; first [eassumption | eexact L_FMTU]
| intros; eapply F_printf_core_cvu__L_CV_U; first [eassumption | eexact L_FMTU] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_473 lo_474 G_107e0 GLOBALS_TOP CODE D_473 E_473 D_474 E_474 ANCH_474 RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP RNG_G_107e0 ROM_G_107e0 GLO LO QHI"] Lemma L_XLOOP : S_XLOOP.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_473 lo_474 G_107e0 GLOBALS_TOP CODE D_473 E_473 D_474 E_474 ANCH_474 RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP RNG_G_107e0 ROM_G_107e0 GLO LO QHI St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
first [ apply F_printf_core_xloop__L_XLOOP; first [eassumption]
| intros; eapply F_printf_core_xloop__L_XLOOP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_467 hi_473 hi_533 lo_468 lo_474 lo_534 joff_627 joff_648 joff_655 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 G_102fd G_107e0 STATIC_SPLIT e_fwritex e_memset CODE BASE4 BASER D_467 E_467 D_468 E_468 D_473 E_473 D_474 E_474 D_533 E_533 D_534 E_534 D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 ANCH_468 ANCH_474 ANCH_534 LINK_627 LINK_648 LINK_655 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd RNG_G_107e0 ROM_G_107e0 LAY_G_102fd_STATIC_SPLIT memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI"] Lemma L_CV_X : S_CV_X.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_467 hi_473 hi_533 lo_468 lo_474 lo_534 joff_627 joff_648 joff_655 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 G_102fd G_107e0 STATIC_SPLIT e_fwritex e_memset CODE BASE4 BASER D_467 E_467 D_468 E_468 D_473 E_473 D_474 E_474 D_533 E_533 D_534 E_534 D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 ANCH_468 ANCH_474 ANCH_534 LINK_627 LINK_648 LINK_655 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd RNG_G_107e0 ROM_G_107e0 LAY_G_102fd_STATIC_SPLIT memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI St Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF FRM0 A0.
first [ apply F_printf_core_cvx__L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP]
| intros; eapply F_printf_core_cvx__L_CV_X; first [eassumption | eexact L_INTC | eexact L_XLOOP] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_395 lo_396 joff_389 joff_627 joff_648 joff_655 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 G_102fd STATIC_SPLIT e_fwritex e_memset e_2596c CODE BASE4 BASER D_389 E_389 D_395 E_395 D_396 E_396 D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 ANCH_396 LINK_389 LINK_627 LINK_648 LINK_655 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd LAY_G_102fd_STATIC_SPLIT memset_callZ strnlen_spec BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI"] Lemma L_CV_S : S_CV_S.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_395 lo_396 joff_389 joff_627 joff_648 joff_655 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 G_102fd STATIC_SPLIT e_fwritex e_memset e_2596c CODE BASE4 BASER D_389 E_389 D_395 E_395 D_396 E_396 D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 ANCH_396 LINK_389 LINK_627 LINK_648 LINK_655 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd LAY_G_102fd_STATIC_SPLIT memset_callZ strnlen_spec BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI St Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF FRM0 A0.
first [ apply F_printf_core_cvs__L_CV_S; first [eassumption | eexact L_TAIL]
| intros; eapply F_printf_core_cvs__L_CV_S; first [eassumption | eexact L_TAIL] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 STATIC_SPLIT CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP GLO HA HAP HVA LO QHI SEP_B SEP_F TOK TQ"] Lemma L_CV_FP : S_CV_FP.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 STATIC_SPLIT CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP GLO HA HAP HVA LO QHI SEP_B SEP_F TOK TQ St Fp B BS SINK TOPOK OUT OUTFP SFR SFL HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF FRM0 A0 VAHI BS0.
first [ apply F_printf_core_cvfp__L_CV_FP; first [eassumption]
| intros; eapply F_printf_core_cvfp__L_CV_FP; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_453 lo_454 joff_627 joff_648 joff_655 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 G_102fd STATIC_SPLIT e_fwritex e_memset CODE BASE4 BASER D_453 E_453 D_454 E_454 D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 ANCH_454 LINK_627 LINK_648 LINK_655 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd LAY_G_102fd_STATIC_SPLIT memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI"] Lemma L_CV_C : S_CV_C.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_453 lo_454 joff_627 joff_648 joff_655 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 G_102fd STATIC_SPLIT e_fwritex e_memset CODE BASE4 BASER D_453 E_453 D_454 E_454 D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 ANCH_454 LINK_627 LINK_648 LINK_655 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd LAY_G_102fd_STATIC_SPLIT memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI St Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF FRM0 A0.
first [ apply F_printf_core_cvc__L_CV_C; first [eassumption | eexact L_TAIL]
| intros; eapply F_printf_core_cvc__L_CV_C; first [eassumption | eexact L_TAIL] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_332 hi_360 hi_395 hi_438 hi_453 hi_467 hi_473 hi_533 hi_543 lo_333 lo_362 lo_396 lo_439 lo_454 lo_468 lo_474 lo_534 lo_545 joff_389 joff_627 joff_648 joff_655 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 G_102fd G_107e0 G_11778 STATIC_SPLIT e_fwritex e_memset e_2596c jt_11778_o1504 jt_11778_o1432 jt_11778_o1800 jt_11778_o1744 jt_11778_o1864 jt_11778_o1352 CODE BASE4 BASER D_332 E_332 D_333 E_333 D_360 E_360 D_362 E_362 D_389 E_389 D_395 E_395 D_396 E_396 D_438 E_438 D_439 E_439 D_453 E_453 D_454 E_454 D_467 E_467 D_468 E_468 D_473 E_473 D_474 E_474 D_533 E_533 D_534 E_534 D_543 E_543 D_545 E_545 D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 ANCH_333 ANCH_362 ANCH_396 ANCH_439 ANCH_454 ANCH_468 ANCH_474 ANCH_534 ANCH_545 LINK_389 LINK_627 LINK_648 LINK_655 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd RNG_G_107e0 ROM_G_107e0 LAY_G_102fd_STATIC_SPLIT RNG_G_11778 JTL_jt_11778_o1504 ROM_jt_11778_50 JTL_jt_11778_o1432 ROM_jt_11778_35 ROM_jt_11778_40 JTL_jt_11778_o1800 ROM_jt_11778_34 JTL_jt_11778_o1744 ROM_jt_11778_52 JTL_jt_11778_o1864 ROM_jt_11778_55 ROM_jt_11778_23 JTL_jt_11778_o1352 ROM_jt_11778_36 ROM_jt_11778_37 ROM_jt_11778_38 ROM_jt_11778_4 ROM_jt_11778_5 ROM_jt_11778_6 memset_callZ strnlen_spec va_area_bound pop_arg_spec BS0 GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI"] Lemma L_CONV : S_CONV.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_332 hi_360 hi_395 hi_438 hi_453 hi_467 hi_473 hi_533 hi_543 lo_333 lo_362 lo_396 lo_439 lo_454 lo_468 lo_474 lo_534 lo_545 joff_389 joff_627 joff_648 joff_655 joff_668 joff_689 joff_701 joff_722 joff_729 joff_742 joff_762 G_102fd G_107e0 G_11778 STATIC_SPLIT e_fwritex e_memset e_2596c jt_11778_o1504 jt_11778_o1432 jt_11778_o1800 jt_11778_o1744 jt_11778_o1864 jt_11778_o1352 CODE BASE4 BASER D_332 E_332 D_333 E_333 D_360 E_360 D_362 E_362 D_389 E_389 D_395 E_395 D_396 E_396 D_438 E_438 D_439 E_439 D_453 E_453 D_454 E_454 D_467 E_467 D_468 E_468 D_473 E_473 D_474 E_474 D_533 E_533 D_534 E_534 D_543 E_543 D_545 E_545 D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 ANCH_333 ANCH_362 ANCH_396 ANCH_439 ANCH_454 ANCH_468 ANCH_474 ANCH_534 ANCH_545 LINK_389 LINK_627 LINK_648 LINK_655 LINK_668 LINK_689 LINK_701 LINK_722 LINK_729 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd RNG_G_107e0 ROM_G_107e0 LAY_G_102fd_STATIC_SPLIT RNG_G_11778 JTL_jt_11778_o1504 ROM_jt_11778_50 JTL_jt_11778_o1432 ROM_jt_11778_35 ROM_jt_11778_40 JTL_jt_11778_o1800 ROM_jt_11778_34 JTL_jt_11778_o1744 ROM_jt_11778_52 JTL_jt_11778_o1864 ROM_jt_11778_55 ROM_jt_11778_23 JTL_jt_11778_o1352 ROM_jt_11778_36 ROM_jt_11778_37 ROM_jt_11778_38 ROM_jt_11778_4 ROM_jt_11778_5 ROM_jt_11778_6 memset_callZ strnlen_spec va_area_bound pop_arg_spec BS0 GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI St Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt FRM0 A0.
first [ apply F_printf_core_conv__L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S | eexact L_CV_FP | eexact L_CV_C]
| intros; eapply F_printf_core_conv__L_CONV; first [eassumption | eexact L_CV_D | eexact L_CV_U | eexact L_CV_X | eexact L_CV_S | eexact L_CV_FP | eexact L_CV_C] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_281 hi_332 hi_360 hi_395 hi_438 hi_453 hi_467 hi_473 hi_533 hi_543 lo_282 lo_333 lo_362 lo_396 lo_439 lo_454 lo_468 lo_474 lo_534 lo_545 joff_81 joff_381 joff_383 joff_389 joff_530 joff_627 joff_639 joff_648 joff_655 joff_668 joff_680 joff_689 joff_701 joff_713 joff_722 joff_729 joff_742 joff_754 joff_762 joff_798 joff_883 joff_907 G_102fd G_107e0 G_11778 G_118c0 STATIC_SPLIT e_194bc e_194c8 e_197bc e_fwritex e_memset e_2596c jt_11778_o1504 jt_11778_o1432 jt_11778_o1800 jt_11778_o1744 jt_11778_o1864 jt_11778_o1352 CODE BASE4 BASER D_81 E_81 D_281 E_281 D_282 E_282 D_332 E_332 D_333 E_333 D_360 E_360 D_362 E_362 D_389 E_389 D_395 E_395 D_396 E_396 D_438 E_438 D_439 E_439 D_453 E_453 D_454 E_454 D_467 E_467 D_468 E_468 D_473 E_473 D_474 E_474 D_533 E_533 D_534 E_534 D_543 E_543 D_545 E_545 D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 ANCH_282 ANCH_333 ANCH_362 ANCH_396 ANCH_439 ANCH_454 ANCH_468 ANCH_474 ANCH_534 ANCH_545 LINK_81 LINK_381 LINK_383 LINK_389 LINK_530 LINK_627 LINK_639 LINK_648 LINK_655 LINK_668 LINK_680 LINK_689 LINK_701 LINK_713 LINK_722 LINK_729 LINK_742 LINK_754 LINK_762 LINK_798 LINK_883 LINK_907 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 RNG_G_102fd ROM_G_102fd RNG_G_107e0 ROM_G_107e0 LAY_G_102fd_STATIC_SPLIT RNG_G_11778 JTL_jt_11778_o1504 ROM_jt_11778_50 JTL_jt_11778_o1432 ROM_jt_11778_35 ROM_jt_11778_40 JTL_jt_11778_o1800 ROM_jt_11778_34 JTL_jt_11778_o1744 ROM_jt_11778_52 JTL_jt_11778_o1864 ROM_jt_11778_55 ROM_jt_11778_23 JTL_jt_11778_o1352 ROM_jt_11778_36 ROM_jt_11778_37 ROM_jt_11778_38 ROM_jt_11778_4 ROM_jt_11778_5 ROM_jt_11778_6 memset_callZ strnlen_spec va_area_bound pop_arg_spec A0 BS0 GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI"] Lemma L_HEAD : forall fuel, S_HEAD fuel.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_281 hi_332 hi_360 hi_395 hi_438 hi_453 hi_467 hi_473 hi_533 hi_543 lo_282 lo_333 lo_362 lo_396 lo_439 lo_454 lo_468 lo_474 lo_534 lo_545 joff_81 joff_381 joff_383 joff_389 joff_530 joff_627 joff_639 joff_648 joff_655 joff_668 joff_680 joff_689 joff_701 joff_713 joff_722 joff_729 joff_742 joff_754 joff_762 joff_798 joff_883 joff_907 G_102fd G_107e0 G_11778 G_118c0 STATIC_SPLIT e_194bc e_194c8 e_197bc e_fwritex e_memset e_2596c jt_11778_o1504 jt_11778_o1432 jt_11778_o1800 jt_11778_o1744 jt_11778_o1864 jt_11778_o1352 CODE BASE4 BASER D_81 E_81 D_281 E_281 D_282 E_282 D_332 E_332 D_333 E_333 D_360 E_360 D_362 E_362 D_389 E_389 D_395 E_395 D_396 E_396 D_438 E_438 D_439 E_439 D_453 E_453 D_454 E_454 D_467 E_467 D_468 E_468 D_473 E_473 D_474 E_474 D_533 E_533 D_534 E_534 D_543 E_543 D_545 E_545 D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 ANCH_282 ANCH_333 ANCH_362 ANCH_396 ANCH_439 ANCH_454 ANCH_468 ANCH_474 ANCH_534 ANCH_545 LINK_81 LINK_381 LINK_383 LINK_389 LINK_530 LINK_627 LINK_639 LINK_648 LINK_655 LINK_668 LINK_680 LINK_689 LINK_701 LINK_713 LINK_722 LINK_729 LINK_742 LINK_754 LINK_762 LINK_798 LINK_883 LINK_907 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 RNG_G_102fd ROM_G_102fd RNG_G_107e0 ROM_G_107e0 LAY_G_102fd_STATIC_SPLIT RNG_G_11778 JTL_jt_11778_o1504 ROM_jt_11778_50 JTL_jt_11778_o1432 ROM_jt_11778_35 ROM_jt_11778_40 JTL_jt_11778_o1800 ROM_jt_11778_34 JTL_jt_11778_o1744 ROM_jt_11778_52 JTL_jt_11778_o1864 ROM_jt_11778_55 ROM_jt_11778_23 JTL_jt_11778_o1352 ROM_jt_11778_36 ROM_jt_11778_37 ROM_jt_11778_38 ROM_jt_11778_4 ROM_jt_11778_5 ROM_jt_11778_6 memset_callZ strnlen_spec va_area_bound pop_arg_spec A0 BS0 GLO HA HAP HF HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ VAHI St Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt FRM0.
first [ intro; apply F_printf_core_head__L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END]
| intros; eapply F_printf_core_head__L_HEAD; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_CONV | eexact L_END] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_281 lo_282 G_118c0 GLOBALS_TOP STATIC_SPLIT CODE D_281 E_281 D_282 E_282 ANCH_282 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 A0 HA HF LO"] Lemma L_P1 : S_P1.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_281 lo_282 G_118c0 GLOBALS_TOP STATIC_SPLIT CODE D_281 E_281 D_282 E_282 ANCH_282 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 A0 HA HF LO St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt GLO QHI TQ FRM0 SEP_F SEP_B HAP HVA VAHI BS0.
first [ apply F_printf_core_p1__L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1]
| intros; eapply F_printf_core_p1__L_P1; first [eassumption | eexact L_SCAN | eexact L_DIR | eexact L_EXIT1] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.
#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_22 lo_25 GLOBALS_TOP STATIC_SPLIT CODE D_22 E_22 D_25 E_25 ANCH_25 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP BS0 GLO HA HAP HVA LO QHI SEP_F"] Lemma L_PRO : S_PRO.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_22 lo_25 GLOBALS_TOP STATIC_SPLIT CODE D_22 E_22 D_25 E_25 ANCH_25 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP BS0 GLO HA HAP HVA LO QHI SEP_F St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF TQ FRM0 SEP_B A0 VAHI.
first [ apply F_printf_core_pro__L_PRO; first [eassumption]
| intros; eapply F_printf_core_pro__L_PRO; first [eassumption] ].

Unshelve. all: first [exact ra | exact q | exact F | exact fc0 | exact m0 | exact fmt | exact slots].
Qed.

Let HS_PRO := L_PRO.
Let HS_HEAD := L_HEAD.
Let HS_P1 := L_P1.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_22 hi_281 hi_332 hi_360 hi_395 hi_438 hi_453 hi_467 hi_473 hi_533 hi_543 lo_25 lo_282 lo_333 lo_362 lo_396 lo_439 lo_454 lo_468 lo_474 lo_534 lo_545 joff_81 joff_381 joff_383 joff_389 joff_530 joff_627 joff_639 joff_648 joff_655 joff_668 joff_680 joff_689 joff_701 joff_713 joff_722 joff_729 joff_742 joff_754 joff_762 joff_798 joff_883 joff_907 G_102fd G_107e0 G_11778 G_118c0 STATIC_SPLIT e_194bc e_194c8 e_197bc e_fwritex e_memset e_2596c jt_11778_o1504 jt_11778_o1432 jt_11778_o1800 jt_11778_o1744 jt_11778_o1864 jt_11778_o1352 CODE BASE4 BASER D_22 E_22 D_25 E_25 D_81 E_81 D_281 E_281 D_282 E_282 D_332 E_332 D_333 E_333 D_360 E_360 D_362 E_362 D_389 E_389 D_395 E_395 D_396 E_396 D_438 E_438 D_439 E_439 D_453 E_453 D_454 E_454 D_467 E_467 D_468 E_468 D_473 E_473 D_474 E_474 D_533 E_533 D_534 E_534 D_543 E_543 D_545 E_545 D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 ANCH_25 ANCH_282 ANCH_333 ANCH_362 ANCH_396 ANCH_439 ANCH_454 ANCH_468 ANCH_474 ANCH_534 ANCH_545 LINK_81 LINK_381 LINK_383 LINK_389 LINK_530 LINK_627 LINK_639 LINK_648 LINK_655 LINK_668 LINK_680 LINK_689 LINK_701 LINK_713 LINK_722 LINK_729 LINK_742 LINK_754 LINK_762 LINK_798 LINK_883 LINK_907 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 RNG_G_102fd ROM_G_102fd RNG_G_107e0 ROM_G_107e0 LAY_G_102fd_STATIC_SPLIT RNG_G_11778 JTL_jt_11778_o1504 ROM_jt_11778_50 JTL_jt_11778_o1432 ROM_jt_11778_35 ROM_jt_11778_40 JTL_jt_11778_o1800 ROM_jt_11778_34 JTL_jt_11778_o1744 ROM_jt_11778_52 JTL_jt_11778_o1864 ROM_jt_11778_55 ROM_jt_11778_23 JTL_jt_11778_o1352 ROM_jt_11778_36 ROM_jt_11778_37 ROM_jt_11778_38 ROM_jt_11778_4 ROM_jt_11778_5 ROM_jt_11778_6 memset_callZ strnlen_spec va_area_bound pop_arg_spec FRM0 HS_HEAD HS_PRO"] Lemma L_CORE2 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (st : St) (i : Z) (args : list parg),
let _ := ctx_all in
SINK m0 st -> stk segs m0 lo q -> mem_inv segs m0 -> bytes_at segs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
rw_cells segs m0 AP [C8 (Z_to_bv 64 (VA + 8 * i))] -> (0 <= i)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat i) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls (length fmt) fmt args) ->
(0 < Fp)%Z -> (Fp + 232 <= 2^64)%Z ->
implM segs (printf_model OUT OUTFP fmt args) st POST
(MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e FPv (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x0)) fc0 None m0 (seg_rom segs)).
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_22 hi_281 hi_332 hi_360 hi_395 hi_438 hi_453 hi_467 hi_473 hi_533 hi_543 lo_25 lo_282 lo_333 lo_362 lo_396 lo_439 lo_454 lo_468 lo_474 lo_534 lo_545 joff_81 joff_381 joff_383 joff_389 joff_530 joff_627 joff_639 joff_648 joff_655 joff_668 joff_680 joff_689 joff_701 joff_713 joff_722 joff_729 joff_742 joff_754 joff_762 joff_798 joff_883 joff_907 G_102fd G_107e0 G_11778 G_118c0 STATIC_SPLIT e_194bc e_194c8 e_197bc e_fwritex e_memset e_2596c jt_11778_o1504 jt_11778_o1432 jt_11778_o1800 jt_11778_o1744 jt_11778_o1864 jt_11778_o1352 CODE BASE4 BASER D_22 E_22 D_25 E_25 D_81 E_81 D_281 E_281 D_282 E_282 D_332 E_332 D_333 E_333 D_360 E_360 D_362 E_362 D_389 E_389 D_395 E_395 D_396 E_396 D_438 E_438 D_439 E_439 D_453 E_453 D_454 E_454 D_467 E_467 D_468 E_468 D_473 E_473 D_474 E_474 D_533 E_533 D_534 E_534 D_543 E_543 D_545 E_545 D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 ANCH_25 ANCH_282 ANCH_333 ANCH_362 ANCH_396 ANCH_439 ANCH_454 ANCH_468 ANCH_474 ANCH_534 ANCH_545 LINK_81 LINK_381 LINK_383 LINK_389 LINK_530 LINK_627 LINK_639 LINK_648 LINK_655 LINK_668 LINK_680 LINK_689 LINK_701 LINK_713 LINK_722 LINK_729 LINK_742 LINK_754 LINK_762 LINK_798 LINK_883 LINK_907 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 RNG_G_102fd ROM_G_102fd RNG_G_107e0 ROM_G_107e0 LAY_G_102fd_STATIC_SPLIT RNG_G_11778 JTL_jt_11778_o1504 ROM_jt_11778_50 JTL_jt_11778_o1432 ROM_jt_11778_35 ROM_jt_11778_40 JTL_jt_11778_o1800 ROM_jt_11778_34 JTL_jt_11778_o1744 ROM_jt_11778_52 JTL_jt_11778_o1864 ROM_jt_11778_55 ROM_jt_11778_23 JTL_jt_11778_o1352 ROM_jt_11778_36 ROM_jt_11778_37 ROM_jt_11778_38 ROM_jt_11778_4 ROM_jt_11778_5 ROM_jt_11778_6 memset_callZ strnlen_spec va_area_bound pop_arg_spec FRM0 HS_HEAD HS_PRO segs base St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ HA SEP_F SEP_B HAP HVA A0 VAHI BS0 HS_P1. try clear BS0. try clear VAHI. try clear A0. try clear HVA. try clear HAP. try clear SEP_B. try clear SEP_F. try clear HA. try clear TQ. try clear QHI. try clear GLO. try clear LO. try clear HF. try clear HOUT. try clear TOK. try clear SFL. try clear SFR.
intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 st i args _ HS0 ST0 MI0 BY0 VAA0 SSP0 APC0 Hi AOK FPC HF0 HF1.
gw_expose GLOBALS_TOP; gw_expose got_ssp; unfold PC_DEPTH in LO, GLO.
unfold printf_model. ienter.
stmt HS_PRO as NXP.
eapply (NXP x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 Fp); [exact ST0 | exact MI0 | exact BY0 | exact VAA0 | exact SSP0 | lia | ].
intros m pfx s2s za pl plp alo ahi j128 digs pad a0' a1' a2' a3' FI MUq LOW DIG PAD.
pose proof FI as FI'. destruct FI' as (MI & MU & WM & _).
assert (HS : SINK m st).
{ eapply (SFR [(q + -544, q)]%Z m0 m st HS0 MUq WM); (apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]). }
assert (APC : rw_cells segs m AP [C8 (Z_to_bv 64 (VA + 8 * i))]).
{ eapply rw_cells_transport; [ | exact MUq | exact WM | cbn [disjoint_from]; simpl_sizes; lia]. exact APC0. }
stmt (HS_HEAD (length fmt)) as NXH.
jumpM (eapply NXH with (i := 0%Z) (cnt := 0%Z) (l := 0%Z) (k := i) (args := args));
[ exact FI | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
| exact FRM0 | apply Fok_refl | lia | lia | lia | unfold INT_MAX; lia ].
Qed.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_22 hi_281 lo_25 lo_282 G_118c0 GLOBALS_TOP STATIC_SPLIT CODE D_22 E_22 D_25 E_25 D_281 E_281 D_282 E_282 ANCH_25 ANCH_282 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 HS_P1 HS_PRO"] Lemma L_CORE1 : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word),
let _ := ctx_all in
stk segs m0 lo q -> mem_inv segs m0 -> bytes_at segs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
pass1_ok fmt = true ->
evt segs (POST1 0)
(MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e (Z_to_bv 64 0) (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x0)) fc0 None m0 (seg_rom segs)).
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_22 hi_281 lo_25 lo_282 G_118c0 GLOBALS_TOP STATIC_SPLIT CODE D_22 E_22 D_25 E_25 D_281 E_281 D_282 E_282 ANCH_25 ANCH_282 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 HS_P1 HS_PRO segs base St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0 HS_HEAD. try clear BS0. try clear A0. try clear HVA. try clear HAP. try clear SEP_F. try clear HA. try clear QHI. try clear GLO. try clear LO. try clear HF. try clear BS. try clear B. try clear Fp.
intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 _ ST0 MI0 BY0 VAA0 SSP0 P1.
gw_expose GLOBALS_TOP; gw_expose got_ssp; unfold PC_DEPTH in LO, GLO.
stmt HS_PRO as NXP.
eapply (NXP x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 0%Z); [exact ST0 | exact MI0 | exact BY0 | exact VAA0 | exact SSP0 | lia | ].
intros m pfx s2s za pl plp alo ahi j128 digs pad a0' a1' a2' a3' FI MUq LOW DIG PAD.
stmt HS_P1 as NX1.
jump (eapply NX1; [ exact FI | eapply munch_weaken; [|exact MUq]; unfold sub_fp; cbn [outside]; intros; lia | exact LOW | exact DIG | exact PAD | exact P1 ]).
Qed.

End PrintfCore.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_22 hi_281 hi_332 hi_360 hi_395 hi_438 hi_453 hi_467 hi_473 hi_533 hi_543 lo_25 lo_282 lo_333 lo_362 lo_396 lo_439 lo_454 lo_468 lo_474 lo_534 lo_545 joff_81 joff_381 joff_383 joff_389 joff_530 joff_627 joff_639 joff_648 joff_655 joff_668 joff_680 joff_689 joff_701 joff_713 joff_722 joff_729 joff_742 joff_754 joff_762 joff_798 joff_883 joff_907 G_102fd G_107e0 G_11778 G_118c0 e_194bc e_194c8 e_197bc e_memset e_2596c jt_11778_o1504 jt_11778_o1432 jt_11778_o1800 jt_11778_o1744 jt_11778_o1864 jt_11778_o1352 CODE BASE4 BASER D_22 E_22 D_25 E_25 D_81 E_81 D_281 E_281 D_282 E_282 D_332 E_332 D_333 E_333 D_360 E_360 D_362 E_362 D_389 E_389 D_395 E_395 D_396 E_396 D_438 E_438 D_439 E_439 D_453 E_453 D_454 E_454 D_467 E_467 D_468 E_468 D_473 E_473 D_474 E_474 D_533 E_533 D_534 E_534 D_543 E_543 D_545 E_545 D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 ANCH_25 ANCH_282 ANCH_333 ANCH_362 ANCH_396 ANCH_439 ANCH_454 ANCH_468 ANCH_474 ANCH_534 ANCH_545 LINK_81 LINK_381 LINK_383 LINK_389 LINK_530 LINK_627 LINK_639 LINK_648 LINK_655 LINK_668 LINK_680 LINK_689 LINK_701 LINK_713 LINK_722 LINK_729 LINK_742 LINK_754 LINK_762 LINK_798 LINK_883 LINK_907 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 RNG_G_102fd ROM_G_102fd RNG_G_107e0 ROM_G_107e0 LAY_G_102fd_STATIC_SPLIT LAY_got_ssp_240_ssp_guard RNG_G_11778 JTL_jt_11778_o1504 ROM_jt_11778_50 JTL_jt_11778_o1432 ROM_jt_11778_35 ROM_jt_11778_40 JTL_jt_11778_o1800 ROM_jt_11778_34 JTL_jt_11778_o1744 ROM_jt_11778_52 JTL_jt_11778_o1864 ROM_jt_11778_55 ROM_jt_11778_23 JTL_jt_11778_o1352 ROM_jt_11778_36 ROM_jt_11778_37 ROM_jt_11778_38 ROM_jt_11778_4 ROM_jt_11778_5 ROM_jt_11778_6 memset_callZ strnlen_spec va_area_bound pop_arg_spec"] Theorem printf_core_proof : forall (St : Type) (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
(OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z),
sink_frame_stmt Fp B BS SINK -> sink_flags_stmt Fp SINK -> topok_stmt TOPOK -> out_stmt Fp B BS SINK TOPOK OUT ->
printf_core_stmt Fp B BS SINK TOPOK OUT OUTFP.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_22 hi_281 hi_332 hi_360 hi_395 hi_438 hi_453 hi_467 hi_473 hi_533 hi_543 lo_25 lo_282 lo_333 lo_362 lo_396 lo_439 lo_454 lo_468 lo_474 lo_534 lo_545 joff_81 joff_381 joff_383 joff_389 joff_530 joff_627 joff_639 joff_648 joff_655 joff_668 joff_680 joff_689 joff_701 joff_713 joff_722 joff_729 joff_742 joff_754 joff_762 joff_798 joff_883 joff_907 G_102fd G_107e0 G_11778 G_118c0 e_194bc e_194c8 e_197bc e_memset e_2596c jt_11778_o1504 jt_11778_o1432 jt_11778_o1800 jt_11778_o1744 jt_11778_o1864 jt_11778_o1352 CODE BASE4 BASER D_22 E_22 D_25 E_25 D_81 E_81 D_281 E_281 D_282 E_282 D_332 E_332 D_333 E_333 D_360 E_360 D_362 E_362 D_389 E_389 D_395 E_395 D_396 E_396 D_438 E_438 D_439 E_439 D_453 E_453 D_454 E_454 D_467 E_467 D_468 E_468 D_473 E_473 D_474 E_474 D_533 E_533 D_534 E_534 D_543 E_543 D_545 E_545 D_627 E_627 D_648 E_648 D_655 E_655 D_668 E_668 D_689 E_689 D_701 E_701 D_722 E_722 D_729 E_729 D_742 E_742 D_762 E_762 ANCH_25 ANCH_282 ANCH_333 ANCH_362 ANCH_396 ANCH_439 ANCH_454 ANCH_468 ANCH_474 ANCH_534 ANCH_545 LINK_81 LINK_381 LINK_383 LINK_389 LINK_530 LINK_627 LINK_639 LINK_648 LINK_655 LINK_668 LINK_680 LINK_689 LINK_701 LINK_713 LINK_722 LINK_729 LINK_742 LINK_754 LINK_762 LINK_798 LINK_883 LINK_907 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 RNG_G_102fd ROM_G_102fd RNG_G_107e0 ROM_G_107e0 LAY_G_102fd_STATIC_SPLIT LAY_got_ssp_240_ssp_guard RNG_G_11778 JTL_jt_11778_o1504 ROM_jt_11778_50 JTL_jt_11778_o1432 ROM_jt_11778_35 ROM_jt_11778_40 JTL_jt_11778_o1800 ROM_jt_11778_34 JTL_jt_11778_o1744 ROM_jt_11778_52 JTL_jt_11778_o1864 ROM_jt_11778_55 ROM_jt_11778_23 JTL_jt_11778_o1352 ROM_jt_11778_36 ROM_jt_11778_37 ROM_jt_11778_38 ROM_jt_11778_4 ROM_jt_11778_5 ROM_jt_11778_6 memset_callZ strnlen_spec va_area_bound pop_arg_spec.
intros St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st lo canary fmt VA i slots args
HS BY HF Ha0 APC VAA Hi AOK FPC ST LO GLO SPHI TQ SSP MI FRM HA BS0 SEPF SEPB HAP HVA VAHI.
subst a0. pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
unfold bv_modulus in Ra1, Ra2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra1, Ra2.
pose proof (L_CORE2 Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo canary
(bv_unsigned a1) fmt (bv_unsigned a2) VA slots a3 a4 HF LO GLO SPHI TQ FRM HA SEPF SEPB HAP HVA (proj1 Ra1) VAHI BS0
t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 st i args HS ST MI BY VAA SSP APC Hi AOK FPC) as C.
cbv zeta in C. rewrite !Z_to_bv_bv_unsigned in C.
eapply implM_mono.
{ apply C; gw_expose GLOBALS_TOP; gw_expose got_ssp; unfold PC_DEPTH, zlength in *; lia. }
cbv beta. intros r st' ms' P. unfold POST, W in P. unfold printf_core_post, SR.
destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & Ft & fc' & apv & m' & -> & MU & WM & MI' & FRM' & FOK & ST' & HS' & SSP' & APC' & Hr).
exists x5, x6, x7, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, Ft, fc', apv, m'.
rewrite Z_to_bv_bv_unsigned.
repeat (split; [assumption || reflexivity|]). exact Hr.
Qed.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_22 hi_281 lo_25 lo_282 G_118c0 CODE D_22 E_22 D_25 E_25 D_281 E_281 D_282 E_282 ANCH_25 ANCH_282 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 LAY_got_ssp_240_ssp_guard"] Theorem printf_core1_proof : printf_core1_stmt.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_22 hi_281 lo_25 lo_282 G_118c0 CODE D_22 E_22 D_25 E_25 D_281 E_281 D_282 E_282 ANCH_25 ANCH_282 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 LAY_got_ssp_240_ssp_guard.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary fmt
BY HF P1 Ha0 ST LO GLO SPHI SSP MI HA HAP A2HI.
subst a0. pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
unfold bv_modulus in Ra1, Ra2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra1, Ra2.
gw_expose GLOBALS_TOP; gw_expose got_ssp; gw_expose STATIC_SPLIT; unfold PC_DEPTH in LO, GLO, HA.
pose proof (L_CORE1 (got_ssp + 8)%Z 0 0 ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo canary
(bv_unsigned a1) fmt (bv_unsigned a2) (bv_unsigned a2 + 8)%Z [] a3 a4 HF
ltac:(unfold PC_DEPTH; lia) ltac:(gw_expose GLOBALS_TOP; gw_expose got_ssp; lia) SPHI HA ltac:(lia) HAP ltac:(lia) (proj1 Ra1) ltac:(lia)
t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 ST MI BY) as C.
cbv zeta in C. rewrite !Z_to_bv_bv_unsigned in C.
eapply evt_mono.
{ apply C; [ | exact SSP | exact P1 ]. unfold va_area. cbn [u64s map concat]. apply bytes_at_nil; lia. }
cbv beta. intros ms' P. unfold POST1 in P. unfold printf_core1_post.
destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & SSP').
exists x5, x6, x7, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, m'.
rewrite Z_to_bv_bv_unsigned.
repeat (split; [assumption || reflexivity|]). exact SSP'.
Qed.

End G.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfYR QfcC QDUx Q9Ay Qy5Y Qy8Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qc3B.
Import QZAi.Mq1 QZAi QfYR QfcC.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y.
Import QVbl.Mq3.
Import QQLG.Mq8.
Import Qy8Z.Mq0.
Import QROt.Mq2.
Import QQRC.Mq1.
Import QZxv.Mql.

Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition scanexp_code (w_97 w_98 : Z) : list Z :=
[0xfb010113; 0x04113423; 0x04813023; 0x02913c23; 0x03213823; 0x03313423; 0x03413023; 0x01513c23; 0x01613823; 0x01713423; 0x00050413; 0x00853503; 0x0b843603; 0x00058493; 0x00c50e63; 0x00150593; 0x00b43423; 0x00054903; 0x02b00513; 0x00a91e63; 0x0200006f; 0x00040513; 0x820fe0ef; 0x00050913; 0x02b00513; 0x00a90663; 0x02d00513; 0x02a91863; 0x00843503; 0x0b843583; 0xfd390993; 0x02b50663; 0x00150593; 0x00b43423; 0x00054903; 0x0019ba13; 0xfc69051b; 0x02049663; 0x0480006f; 0x00000a13; 0xfc69051b; 0x03c0006f; 0x00040513; 0xfcdfd0ef; 0x00050913; 0x0019ba13; 0xfc65051b; 0x02048263; 0xff500593; 0x00a5ee63; 0x0c043503; 0x00054e63; 0x00843503; 0xfff50513; 0x00a43423; 0x00c0006f; 0xff600593; 0x02b57263; 0x0c043503; 0xfff00493; 0x03f49493; 0x14054663; 0x00843503; 0xfff50513; 0x00a43423; 0x13c0006f; 0xfd09051b; 0x00000493; 0x00900a93; 0x10aae863; 0x00a00b13; 0x0cccd537; 0xccc50b9b; 0x00843503; 0x0b843583; 0x02b50463; 0x00150593; 0x00b43423; 0x00054983; 0x03648533; 0x00a90933; 0xfd09851b; 0xfd09049b; 0x02aaf463; 0x02c0006f; 0x00040513; 0xf21fd0ef; 0x00050993; 0x03648533; 0x00a90933; 0xfd09851b; 0xfd09049b; 0x00aae663; 0x00098913; 0xfb74c6e3; 0x00900913; 0x0aa96263; w_97; w_98; 0x00a00b13; 0x00843503; 0x0b843583; 0x02b50463; 0x00150593; 0x00b43423; 0x00054503; 0x036485b3; 0x00b989b3; 0xfd05059b; 0xfd098493; 0x02b97263; 0x0280006f; 0x00040513; 0xeb5fd0ef; 0x036485b3; 0x00b989b3; 0xfd05059b; 0xfd098493; 0x00b96663; 0x00050993; 0xfb54c8e3; 0x00900513; 0x02b56e63; 0x00a00913; 0x0140006f; 0x00040513; 0xe81fd0ef; 0xfd05051b; 0x03257263; 0x00843503; 0x0b843583; 0xfeb504e3; 0x00150593; 0x00b43423; 0x00054503; 0xfd05051b; 0xff2562e3; 0x0c043503; 0x00054863; 0x00843503; 0xfff50513; 0x00a43423; 0x000a0463; 0x409004b3; 0x00048513; 0x04813083; 0x04013403; 0x03813483; 0x03013903; 0x02813983; 0x02013a03; 0x01813a83; 0x01013b03; 0x00813b83; 0x05010113; 0x00008067]%Z.

Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.
Definition SCANEXP_DEPTH : Z := 240.

Lemma isdigitc_iff : forall c, (-2^31 < c < 2^31)%Z -> isdigitc c = true <-> (48 <= c <= 57)%Z.
Proof. intros c Hc. unfold isdigitc, u32. rewrite Z.ltb_lt. split; intros H; Z.div_mod_to_equations; lia. Qed.
Lemma isdigitc_t : forall c, (-2^31 < c < 2^31)%Z -> (48 <= c <= 57)%Z -> isdigitc c = true.
Proof. intros. apply (proj2 (isdigitc_iff c ltac:(lia))). lia. Qed.
Lemma isdigitc_f : forall c, (-2^31 < c < 2^31)%Z -> ~ (48 <= c <= 57)%Z -> isdigitc c = false.
Proof. intros c Hc H. destruct (isdigitc c) eqn:E; [|reflexivity]. exfalso. apply H. apply (proj1 (isdigitc_iff c Hc)). exact E. Qed.

Definition scanexp_tail (fuelc : nat) (neg c : Z) (f : shfile) : option (shfile * Z) :=
if negb (isdigitc c) then Some (sh_unget f, LLONG_MIN_) else
match scanexp_l1_loop fuelc (0%Z, c, f) with
| None => None
| Some (x, c, f) =>
match scanexp_l2_loop fuelc (x, c, f) with
| None => None
| Some (y, c, f) =>
match scanexp_l3_loop fuelc (c, f) with
| None => None
| Some (c, f) => Some (sh_unget f, if nz neg then (- y)%Z else y)
end end end.

Lemma scanexp_eq : forall fuelc f pok,
scanexp fuelc f pok =
(let '(c, f) := sh_getc f in
let '(neg, c, f) :=
(if ((c =? 43) || (c =? 45))%Z then
let neg := b2z (c =? 45)%Z in
let '(c, f) := sh_getc f in
let f := if negb (isdigitc c) && nz pok then sh_unget f else f in (neg, c, f)
else (0%Z, c, f)) in
scanexp_tail fuelc neg c f).
Proof.
intros fuelc f pok. unfold scanexp, scanexp_tail.
destruct (sh_getc f) as [c1 f1].
destruct (if ((c1 =? 43) || (c1 =? 45))%Z then _ else _) as [[neg c2] f2]. reflexivity.
Qed.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_97 w_98 : Z).
Variables (hi_97 : bv 20).
Variables (lo_98 : bv 12).
Variables (G_107a0 STRING_READ got_ssp ssp_guard : Z).
Hypothesis CODE : code_at segs base (scanexp_code w_97 w_98).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 624.
Hypothesis D_97 : decode_any (Z_to_bv 32 w_97) = Some (Auipc 10 hi_97, 4%Z).
Hypothesis E_97 : is_ecall (Z_to_bv 32 w_97) = false.
Hypothesis D_98 : decode_any (Z_to_bv 32 w_98) = Some (Load SZ8 true 21 10 lo_98, 4%Z).
Hypothesis E_98 : is_ecall (Z_to_bv 32 w_98) = false.
Hypothesis ANCH_98 : gw_anch (Z.shiftl (bv_signed hi_97) 12 + (base + 388) + bv_signed lo_98)%Z G_107a0.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis LAY_lo_got_ssp : gw_le 65536 got_ssp.
Hypothesis AL_got_ssp : gw_al got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis LAY_lo_ssp_guard : gw_le 65536 ssp_guard.
Hypothesis AL_ssp_guard : gw_al ssp_guard 8.
Hypothesis LAY_got_ssp_ssp_guard : gw_le (got_ssp + 8) ssp_guard.
Hypothesis RNG_G_107a0 : gw_br G_107a0 8.
Hypothesis ROM_G_107a0 : ro_bytes segs G_107a0 (le8 (Z_to_bv 64 92233720368547758)).

Local Definition gw_tbl_0 := tt.

Definition SHGETC := (base + -8072)%Z.
Local Definition gw_tbl_1 := (gw_ent (@QZxv.Mql.SHGETC (base + -8128)%Z) SHGETC (gw_ent (@QROt.Mq2.SHGETC (base + -8128)%Z) SHGETC (gw_ent (@QQRC.Mq3.SHGETC (base + -8128)%Z) SHGETC gw_tbl_0))).
Definition ssp_cells : ltac:(gw_rebind_ty (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QZxv.Mql.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_1))).
Definition ssJ : ltac:(gw_rebind_ty (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@QZxv.Mql.ssJ STRING_READ) ssJ (gw_ent (@QROt.Mq2.ssJ STRING_READ) ssJ (gw_ent (@QQRC.Mq3.ssJ STRING_READ) ssJ gw_tbl_2))).
Definition RFI : ltac:(gw_rebind_ty (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@QZxv.Mql.RFI STRING_READ) RFI (gw_ent (@QQRC.Mq3.RFI STRING_READ) RFI gw_tbl_3)).
Definition shgetc_post : ltac:(gw_rebind_ty (@QROt.Mq2.shgetc_post segs got_ssp STRING_READ ssp_guard) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@QROt.Mq2.shgetc_post segs got_ssp STRING_READ ssp_guard) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@QZxv.Mql.shgetc_post segs got_ssp STRING_READ ssp_guard) shgetc_post (gw_ent (@QROt.Mq2.shgetc_post segs got_ssp STRING_READ ssp_guard) shgetc_post gw_tbl_4)).
Definition RFJ : ltac:(gw_rebind_ty (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QZxv.Mql.RFJ STRING_READ) RFJ gw_tbl_5).

Hypothesis RFI_rpos : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_rpos) (base + -8128)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_6))) in let T := gw_fold_pcs T base (-8128)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_rpos _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_fast : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_fast) (base + -8128)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_6))) in let T := gw_fold_pcs T base (-8128)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_fast _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_fast_lt : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_fast_lt) (base + -8128)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_6))) in let T := gw_fold_pcs T base (-8128)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_fast_lt _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_slow : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_slow) (base + -8128)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_6))) in let T := gw_fold_pcs T base (-8128)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_slow _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis RFI_getc : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_getc) (base + -8128)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_6))) in let T := gw_fold_pcs T base (-8128)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_getc _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis RFI_unget : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_unget) (base + -8128)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_6))) in let T := gw_fold_pcs T base (-8128)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_unget _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_unget_eq : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_unget_eq) (base + -8128)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_6))) in let T := gw_fold_pcs T base (-8128)%Z [0; 56; 256; 396]%Z in exact T).
Hypothesis rf_unget_nop : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_unget_nop) (base + -8128)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_6))) in let T := gw_fold_pcs T base (-8128)%Z [0; 56; 256; 396]%Z in exact T).
Hypothesis shgetc_callJ : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.shgetc_callJ) (base + -8128)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_6))) in let T := gw_fold_pcs T base (-8128)%Z [0; 56; 256; 396]%Z in exact T).  Arguments shgetc_callJ _%_bv_scope _%_Z_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope _%_Z_scope _%_Z_scope _ _%_Z_scope _%_Z_scope _ _%_list_scope _%_list_scope _%_list_scope _%_bv_scope.
Notation rfj := G.T_rfj.rfj.
Notation j_flags := G.T_rfj.j_flags.
Notation j_pad0 := G.T_rfj.j_pad0.
Notation j_close := G.T_rfj.j_close.
Notation j_wend := G.T_rfj.j_wend.
Notation j_wpos := G.T_rfj.j_wpos.
Notation j_mbz1 := G.T_rfj.j_mbz1.
Notation j_wbase := G.T_rfj.j_wbase.
Notation j_read := G.T_rfj.j_read.
Notation j_write := G.T_rfj.j_write.
Notation j_seek := G.T_rfj.j_seek.
Notation j_bufsize := G.T_rfj.j_bufsize.
Notation j_prev := G.T_rfj.j_prev.
Notation j_next := G.T_rfj.j_next.
Notation j_fd := G.T_rfj.j_fd.
Notation j_ppid := G.T_rfj.j_ppid.
Notation j_lockcount := G.T_rfj.j_lockcount.
Notation j_mode := G.T_rfj.j_mode.
Notation j_lock := G.T_rfj.j_lock.
Notation j_lbf := G.T_rfj.j_lbf.
Notation j_pad1 := G.T_rfj.j_pad1.
Notation j_cookie := G.T_rfj.j_cookie.
Notation j_off := G.T_rfj.j_off.
Notation j_getln := G.T_rfj.j_getln.
Notation j_mbz2 := G.T_rfj.j_mbz2.
Notation j_pl := G.T_rfj.j_pl.
Notation j_nl := G.T_rfj.j_nl.
Notation j_locale := G.T_rfj.j_locale.

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
Ltac fixw2 := rewrite ?swrap32_landW, ?swrap32_landW_sub; try rewrite !swrap32_small by lia.

#[using="G_107a0 STRING_READ got_ssp ssp_guard CODE BASE4 BASER D_97 E_97 D_98 E_98 ANCH_98 RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_got_ssp_ssp_guard RNG_G_107a0 ROM_G_107a0 RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq rf_unget_nop shgetc_callJ"] Lemma gw_all : True. Proof. exact I. Qed.

Definition SCANEXP : Z := (base + 0x0).

Definition scanexp_rpost (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp T p : Z) (J : rfj) (txt : list Z) (canary : word) (fR : shfile) (e10 : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' k' c',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e10) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(q - SCANEXP_DEPTH, q); (Fp, Fp + 232)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' (q - SCANEXP_DEPTH) q
/\ rw_cells segs m' Fp (rf_cells T p true fR J)
/\ RFJ T txt p true J k' c' fR /\ (1 <= k')%Z
/\ bytes_at segs m' T (zbytes txt)
/\ ssp_cells m' canary.

Definition scanexp_rstmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
(Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z) (fR : shfile) (e10 : Z),
scanexp fuelc f0 pok = Some (fR, e10) ->
rw_cells segs m Fp (rf_cells T p true f0 J) -> RFJ T txt p true J kmin0 c0 f0 -> (1 <= kmin0)%Z -> c0 <> 0%Z ->
(sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre) ->
Forall (fun c => 0 <= c < 256)%Z txt -> (0 <= p < zlength txt)%Z -> znth txt p = 0%Z ->
bytes_at segs m T (zbytes txt) -> ssp_cells m canary ->
(0 < T)%Z -> (T + 2^41 <= 2^63)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
stk segs m (q - SCANEXP_DEPTH) q -> (4096 <= q - SCANEXP_DEPTH)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
(T + zlength txt <= q - SCANEXP_DEPTH \/ q <= T)%Z ->
(ssp_guard + 8 <= q - SCANEXP_DEPTH)%Z ->
(T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
(0 <= pok <= 1)%Z -> (0 <= q)%Z -> (q < 2^63)%Z ->
mem_inv segs m ->
evt segs (scanexp_rpost ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p J txt canary fR e10 m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 SCANEXP) fc None m (seg_rom segs)).

Section Scanexp.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
(Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z) (fR : shfile) (e10 : Z).
Hypothesis HM : scanexp fuelc f0 pok = Some (fR, e10).
Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.
Hypothesis T0 : (0 < T)%Z.
Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
Hypothesis SEP : (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z.
Hypothesis SPLO : (4096 <= q - SCANEXP_DEPTH)%Z.
Hypothesis SPF : (q <= Fp)%Z.
Hypothesis SPF2 : (Fp + 232 <= 2^63)%Z.
Hypothesis SPT : (T + zlength txt <= q - SCANEXP_DEPTH \/ q <= T)%Z.
Hypothesis SG1 : (ssp_guard + 8 <= q - SCANEXP_DEPTH)%Z.
Hypothesis SG2 : (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z.
Hypothesis SG3 : (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z.
Hypothesis Hpok : (0 <= pok <= 1)%Z.
Hypothesis Q0 : (0 <= q)%Z.
Hypothesis Q1 : (q < 2^63)%Z.

Notation POST := (scanexp_rpost ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p J txt canary fR e10 m0).
Notation SPv := (Z_to_bv 64 (q + -80)).
Notation RFJ' := (RFJ T txt p true J).
Definition frame (j8 : list byte) : list cell := [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Definition finv (m : word -> option byte) (j8 : list byte) : Prop :=
mem_inv segs m /\ munch [(q - SCANEXP_DEPTH, q); (Fp, Fp + 232)]%Z m0 m /\ wmono segs m0 m
/\ rw_cells segs m (q + -80) (frame j8) /\ stk segs m (q - SCANEXP_DEPTH) (q + -80)
/\ bytes_at segs m T (zbytes txt) /\ ssp_cells m canary.
Ltac dest_finv H := destruct H as (MI & MU & WM & FR & ST & BY & [SSP1 SSP2]); unfold frame in FR; unfold SCANEXP_DEPTH in MU, ST;
gw_expose got_ssp; gw_expose ssp_guard;
try (let LTX := fresh "LTX" in assert (LTX : length (zbytes txt) = length txt) by apply zbytes_length; unfold zlength in * ).
Ltac mk_finv := gw_expose got_ssp; gw_expose ssp_guard; unfold finv, frame, SCANEXP_DEPTH, ssp_cells;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; hyp.

#[using="Type"] Lemma stdio_getc : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f.
Proof. clear - ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR e10 HM ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Hpok Q0 Q1. first [clear HM | gw_hide HM | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear Q0 | gw_hide Q0 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]. intros f. unfold sh_getc. destruct (sh_stdio f); cbn [negb]; [destruct (_ =? _); reflexivity | reflexivity]. Qed.
#[using="Type"] Lemma stdio_unget : forall f, sh_stdio (sh_unget f) = sh_stdio f.
Proof. clear - ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR e10 HM ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Hpok Q0 Q1. first [clear HM | gw_hide HM | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear Q0 | gw_hide Q0 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]. intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.

#[using="w_97 w_98 CODE pre"] Lemma L_ret : forall m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c fX,
finv m j8 -> rw_cells segs m Fp (rf_cells T p true fX J) -> RFJ' k c fX -> (1 <= k)%Z -> fX = fR ->
evt segs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 e10) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x240)) fc None m (seg_rom segs)).
Proof. clear - w_97 w_98 CODE pre segs base ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 Fp T p J txt post canary pok fuelc f0 kmin0 c0 fR e10 HM ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Hpok Q0 Q1. first [clear HM | gw_hide HM | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; try gw_hide SPLO; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SPT; try gw_hide SG1; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear Q0 | gw_hide Q0 | idtac]; first [clear Q1 | gw_hide Q1 | idtac].
intros until fX. intros FI FC RJ Hk EX. subst fX. dest_finv FI. unfold SCANEXP_DEPTH in SPLO, SPT, SG1. gw_expose got_ssp; gw_expose ssp_guard.
pose proof (rw_cells_bound _ _ _ _ FC) as BFC. cbn [cells_size csize Nat.add rf_cells] in BFC.
do 12 zs.
release_frame FR ST q.
apply evt_done. unfold scanexp_rpost, SCANEXP_DEPTH. repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
split; [exact FC|]. split; [exact RJ|]. split; [exact Hk|]. split; [exact BY | split; [exact SSP1 | exact SSP2]].
Qed.

Ltac unfold_fc FC := unfold rf_cells, rf_rend in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.

#[using="w_97 w_98 CODE RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_got_ssp_ssp_guard RFI_unget rf_unget_eq rf_unget_nop pre Hp T0 T1 SEP SPF SPF2 SPT SG1 SG2 SG3"] Lemma L_end : forall m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f (v neg : Z),
finv m j8 -> rw_cells segs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (2 <= k)%Z ->
(0 <= neg <= 1)%Z -> (-2^63 <= v < 2^63)%Z ->
fR = sh_unget f -> e10 = (if nz neg then - v else v)%Z ->
evt segs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 v) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 neg) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x224)) fc None m (seg_rom segs)).
Proof. clear - w_97 w_98 CODE RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_got_ssp_ssp_guard RFI_unget rf_unget_eq rf_unget_nop pre Hp T0 T1 SEP SPF SPF2 SPT SG1 SG2 SG3 segs base ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 Fp T p J txt post canary pok fuelc f0 kmin0 c0 fR e10 HM ST0 BYT Hnul SPLO Hpok Q0 Q1. first [clear HM | gw_hide HM | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; try gw_hide SPLO; first [clear Hpok | gw_hide Hpok | idtac]; first [clear Q0 | gw_hide Q0 | idtac]; first [clear Q1 | gw_hide Q1 | idtac].
intros until neg. intros FI FC RJ Hk Rneg Rv HfR He.
pose proof FI as FI'. dest_finv FI'. unfold SCANEXP_DEPTH in SPLO, SPT, SG1. gw_expose got_ssp; gw_expose ssp_guard.
pose proof (rw_cells_bound _ _ _ _ FC) as BFC. cbn [cells_size csize Nat.add rf_cells] in BFC.
pose proof RJ as RJ2. destruct RJ2 as (OK & Rc & CC & KM & NS & SS). destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia). unfold M64 in RR.
pose proof (RFI_unget T txt p J Hp k c f RJ ltac:(lia)) as RJu.
destruct (sh_shlim_neg f) eqn:SN.
-
rewrite (rf_unget_nop f SN) in *. unfold_fc FC. rewrite SN in FC. unfold M64 in FC.
zs. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ | exfalso; lia ]).
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ assert (Ee : e10 = v) by (rewrite He; unfold nz; destruct (Z.eqb_spec neg 0); cbn; lia). rewrite <- Ee.
eapply L_ret; [exact FI | | exact RJu | lia | symmetry; exact HfR].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
+ zs. assert (Ee : e10 = (- v)%Z) by (rewrite He; unfold nz; destruct (Z.eqb_spec neg 0); cbn; lia).
replace (Z_to_bv 64 (0 - Z.land v 18446744073709551615)%Z) with (Z_to_bv 64 e10) by (apply Z_to_bv_eqm; rewrite Ee, land_W64; Z.div_mod_to_equations; lia).
eapply L_ret; [exact FI | | exact RJu | lia | symmetry; exact HfR].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
-
rewrite (rf_unget_eq f SN) in *. unfold_fc FC. rewrite SN in FC. unfold M64 in FC.
zs. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ exfalso; lia | ]).
zs. zs. zs.
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ assert (Ee : e10 = v) by (rewrite He; unfold nz; destruct (Z.eqb_spec neg 0); cbn; lia). rewrite <- Ee.
eapply L_ret; [mk_finv | | exact RJu | lia | symmetry; exact HfR].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
+ zs. assert (Ee : e10 = (- v)%Z) by (rewrite He; unfold nz; destruct (Z.eqb_spec neg 0); cbn; lia).
replace (Z_to_bv 64 (0 - Z.land v 18446744073709551615)%Z) with (Z_to_bv 64 e10) by (apply Z_to_bv_eqm; rewrite Ee, land_W64; Z.div_mod_to_equations; lia).
eapply L_ret; [mk_finv | | exact RJu | lia | symmetry; exact HfR].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
Qed.

#[using="w_97 w_98 CODE RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_got_ssp_ssp_guard RFI_unget rf_unget_eq rf_unget_nop pre Hp T0 T1 SEP SPF SPF2 SPT SG1 SG2 SG3"] Lemma L_ND : forall m j8 (x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f,
finv m j8 -> rw_cells segs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (2 <= k)%Z ->
fR = sh_unget f -> e10 = LLONG_MIN_ ->
evt segs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0xe8)) fc None m (seg_rom segs)).
Proof. clear - w_97 w_98 CODE RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_got_ssp_ssp_guard RFI_unget rf_unget_eq rf_unget_nop pre Hp T0 T1 SEP SPF SPF2 SPT SG1 SG2 SG3 segs base ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 Fp T p J txt post canary pok fuelc f0 kmin0 c0 fR e10 HM ST0 BYT Hnul SPLO Hpok Q0 Q1. first [clear HM | gw_hide HM | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; try gw_hide SPLO; first [clear Hpok | gw_hide Hpok | idtac]; first [clear Q0 | gw_hide Q0 | idtac]; first [clear Q1 | gw_hide Q1 | idtac].
intros until f. intros FI FC RJ Hk HfR He.
pose proof FI as FI'. dest_finv FI'. unfold SCANEXP_DEPTH in SPLO, SPT, SG1. gw_expose got_ssp; gw_expose ssp_guard.
pose proof (rw_cells_bound _ _ _ _ FC) as BFC. cbn [cells_size csize Nat.add rf_cells] in BFC.
pose proof RJ as RJ2. destruct RJ2 as (OK & Rc & CC & KM & NS & SS). destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia). unfold M64 in RR.
pose proof (RFI_unget T txt p J Hp k c f RJ ltac:(lia)) as RJu.
destruct (sh_shlim_neg f) eqn:SN.
- rewrite (rf_unget_nop f SN) in *. unfold_fc FC. rewrite SN in FC. unfold M64 in FC.
zs. zs. zs. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ | exfalso; lia ]).
let v := getreg 9%Z in replace v with (Z_to_bv 64 e10) by (rewrite He; apply Z_to_bv_eqm; vm_compute; reflexivity).
eapply L_ret; [exact FI | | exact RJu | lia | symmetry; exact HfR].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
- rewrite (rf_unget_eq f SN) in *. unfold_fc FC. rewrite SN in FC. unfold M64 in FC.
zs. zs. zs. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ exfalso; lia | ]).
zs. zs. zs. zs.
let v := getreg 9%Z in replace v with (Z_to_bv 64 e10) by (rewrite He; apply Z_to_bv_eqm; vm_compute; reflexivity).
eapply L_ret; [mk_finv | | exact RJu | lia | symmetry; exact HfR].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
Qed.

Ltac plia := gw_expose got_ssp; gw_expose ssp_guard; unfold zlength in *; lia.
Ltac unfold_fc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.

Ltac post_getc :=
match goal with H : ssp_cells ?m' _ |- _ =>
repeat match goal with H2 : rw_cells _ _ got_ssp _ |- _ => clear H2 | H2 : rw_cells _ _ ssp_guard _ |- _ => clear H2 end;
destruct H as [SSP1' SSP2']; gw_expose got_ssp; gw_expose ssp_guard end;
match goal with H : stk _ ?m' (q + -80 - 160)%Z _ |- _ =>
replace (q + -80 - 160)%Z with (q - 240)%Z in H by lia;
try match goal with H2 : stk _ _ (q - 240)%Z _ |- _ => tryif constr_eq H H2 then fail else clear H2 end end;
repeat match goal with H : bytes_at _ ?m' T ?x, H2 : bytes_at _ ?m' T ?x |- _ => clear H2 end.

Ltac site_facts FC RJ k c f :=
unfold SCANEXP_DEPTH in SPLO, SPT, SG1; gw_expose got_ssp; gw_expose ssp_guard;
pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC;
pose proof RJ as RJ2; destruct RJ2 as (OK & Rc & CC & KM & NS & SS); destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst);
assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia); unfold M64 in RR;
pose proof (RFI_rpos T txt p J Hp k c f RJ) as Rrp.

#[using="w_97 w_98 CODE BASE4 BASER RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_got_ssp_ssp_guard RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq rf_unget_nop shgetc_callJ pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_L3 : forall n m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f (y neg cX : Z) fX,
finv m j8 -> rw_cells segs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (1 <= k)%Z ->
sh_stdio f = sh_stdio f0 -> (48 <= c <= 57)%Z ->
scanexp_l3_loop n (sh_getc f) = Some (cX, fX) ->
fR = sh_unget fX -> e10 = (if nz neg then - y else y)%Z -> (0 <= neg <= 1)%Z -> (-2^63 <= y < 2^63)%Z ->
evt segs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 y) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 10) x19 (Z_to_bv 64 neg) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x204)) fc None m (seg_rom segs)).
Proof. clear - w_97 w_98 CODE BASE4 BASER RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_got_ssp_ssp_guard RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq rf_unget_nop shgetc_callJ pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 segs base ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 Fp T p J txt canary pok fuelc f0 kmin0 c0 fR e10 HM Hpok Q0. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear Q0 | gw_hide Q0 | idtac].
induction n as [|n IH]; [intros; discriminate|].
intros until fX. intros FI FC RJ Hk Hst Hc HL HfR He Rneg Ry.
pose proof (RFI_getc T txt p J BYT Hp Hnul k c f RJ ltac:(lia)) as RJ1.
pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
rewrite (surjective_pairing (sh_getc f)) in HL. cbn [scanexp_l3_loop scanexp_l3_body] in HL.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
assert (DIG : (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x19' x21' x22' x23' x28' x29' x30' x31' : word) x1',
finv m2 j8' -> rw_cells segs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
evt segs POST
(MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 y) x10' x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 10) x19' (Z_to_bv 64 neg) x21' x22' x23' s8 s9 s10 s11 x28' x29' x30' x31')
F (Z_to_bv 64 (base + 0x204)) fc None m2 (seg_rom segs))).
{ intros Hd. intros. rewrite (isdigitc_t (fst (sh_getc f))) in HL by lia.
eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (k + 1)%Z (fst (sh_getc f)) (snd (sh_getc f))); try eassumption; try lia. }
assert (ND : ~ (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x18' x19' x21' x22' x23' x28' x29' x30' x31' : word) x1',
finv m2 j8' -> rw_cells segs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
evt segs POST
(MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 y) x10' x11' x12' x13' x14' x15' x16' x17'
x18' x19' (Z_to_bv 64 neg) x21' x22' x23' s8 s9 s10 s11 x28' x29' x30' x31')
F (Z_to_bv 64 (base + 0x224)) fc None m2 (seg_rom segs))).
{ intros Hd. intros. rewrite (isdigitc_f (fst (sh_getc f))) in HL by lia. injection HL as E1 E2. subst cX fX.
eapply L_end with (k := (k + 1)%Z); try eassumption; try lia. }
clear IH HL.
pose proof FI as FI'. dest_finv FI'. site_facts FC RJ k c f.
destruct (Z.eq_dec (T + sh_rpos f) (rf_rend T p true f)) as [SLOW|FAST].
-
pose proof FC as FC0. unfold_fc2 FC.
zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ | exfalso; lia ]).
destruct (rf_getc_slow T txt p J Hp T1 k c f RJ SLOW) as (STD & EJ & Hn & Hrp & Hc0).
assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
zs. zs. callw (eapply shgetc_callJ;
[ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
| plia | plia | plia | replace (q + -80 - 160)%Z with (q - 240)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI ]).
post_getc. subst J. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC end.
zs. fixw2. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+  eapply ND; [mlia2 | mk_finv | exact FC].
+ eapply DIG; [mlia2 | mk_finv | exact FC].
-
pose proof (rf_getc_fast_lt T txt p J Hp k c f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp k c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply Qy5Y.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
unfold_fc2 FC.
zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ exfalso; lia | ]).
zs. zs.
pose proof (u8ro_read segs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
zs. cbv beta. rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
zs. fixw2. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ eapply DIG; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
+ eapply ND; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
Qed.

Definition LM : Z := 92233720368547758.
#[using="Type"] Lemma LM_eq : Z.quot LLONG_MAX_ 100 = LM. Proof. clear - ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR e10 HM ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Hpok Q0 Q1. first [clear HM | gw_hide HM | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear Q0 | gw_hide Q0 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]. reflexivity. Qed.

#[using="w_97 w_98 CODE BASE4 BASER RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_got_ssp_ssp_guard RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq rf_unget_nop shgetc_callJ pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_L2 : forall n m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word) x1 k c f (y neg y2 c2 : Z) f2 n3 cX fX,
finv m j8 -> rw_cells segs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (1 <= k)%Z ->
sh_stdio f = sh_stdio f0 -> (48 <= c <= 57)%Z -> (0 <= y < LM)%Z ->
scanexp_l2_loop n (y, c, f) = Some (y2, c2, f2) ->
scanexp_l3_loop n3 (c2, f2) = Some (cX, fX) ->
fR = sh_unget fX -> e10 = (if nz neg then - y2 else y2)%Z -> (0 <= neg <= 1)%Z ->
evt segs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 y) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 9) (Z_to_bv 64 c) (Z_to_bv 64 neg) (Z_to_bv 64 LM) (Z_to_bv 64 10) x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x190)) fc None m (seg_rom segs)).
Proof. clear - w_97 w_98 CODE BASE4 BASER RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_got_ssp_ssp_guard RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq rf_unget_nop shgetc_callJ pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 segs base ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 Fp T p J txt canary pok fuelc f0 kmin0 c0 fR e10 HM Hpok Q0. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear Q0 | gw_hide Q0 | idtac].
induction n as [|n IH]; [intros; discriminate|].
intros until fX. intros FI FC RJ Hk Hst Hc Hy HL HL3 HfR He Rneg. pose proof Hy as Hy0. unfold LM in Hy.
pose proof (RFI_getc T txt p J BYT Hp Hnul k c f RJ ltac:(lia)) as RJ1.
pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
cbn [scanexp_l2_loop scanexp_l2_cond scanexp_l2_body] in HL. rewrite (isdigitc_t c), LM_eq in HL by lia.
replace (y <? LM) with true in HL by (symmetry; apply Z.ltb_lt; exact (proj2 Hy0)). cbn [andb] in HL.
rewrite (surjective_pairing (sh_getc f)) in HL.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
set (y' := (10 * y + c - 48)%Z) in HL.
assert (Ry' : (0 <= y' <= 10 * LM - 1)%Z) by (unfold y', LM in *; lia).
assert (DIG : (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x12' x13' x14' x15' x16' x17' x19' x23' x28' x29' x30' x31' : word) x1',
finv m2 j8' -> rw_cells segs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
evt segs POST
(MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 y') (Z_to_bv 64 (fst (sh_getc f))) (Z_to_bv 64 (fst (sh_getc f) - 48)) x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 9) x19' (Z_to_bv 64 neg) (Z_to_bv 64 LM) (Z_to_bv 64 10) x23' s8 s9 s10 s11 x28' x29' x30' x31')
F (Z_to_bv 64 (base + 0x1dc)) fc None m2 (seg_rom segs))).
{ intros Hd. intros until x1'. intros FI2 FC2.
pose proof FI2 as FI'. dest_finv FI'. unfold LM in *.
zs. zs. brs K.
- eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (k + 1)%Z (fst (sh_getc f)) (snd (sh_getc f))); try eassumption; try lia.
- destruct n as [|n']; [discriminate HL|]. cbn [scanexp_l2_loop scanexp_l2_cond] in HL.
rewrite LM_eq in HL. replace (y' <? LM) with false in HL by (symmetry; apply Z.ltb_ge; unfold LM; lia). rewrite Bool.andb_false_r in HL.
injection HL as E1 E2 E3. subst y2 c2 f2.
destruct n3 as [|n3']; [discriminate HL3|]. cbn [scanexp_l3_loop scanexp_l3_body] in HL3. rewrite (isdigitc_t (fst (sh_getc f))) in HL3 by lia.
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia); [ exfalso; lia | ]); try (exfalso; mlia2). zs. zs.
eapply L_L3 with (k := (k + 1)%Z); try eassumption; unfold LM in *; try lia. }
assert (ND : ~ (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x10' x12' x13' x14' x15' x16' x17' x18' x19' x23' x28' x29' x30' x31' : word) x1',
finv m2 j8' -> rw_cells segs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
evt segs POST
(MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 y') x10' (Z_to_bv 64 (fst (sh_getc f) - 48)) x12' x13' x14' x15' x16' x17'
x18' x19' (Z_to_bv 64 neg) (Z_to_bv 64 LM) (Z_to_bv 64 10) x23' s8 s9 s10 s11 x28' x29' x30' x31')
F (Z_to_bv 64 (base + 0x1e4)) fc None m2 (seg_rom segs))).
{ intros Hd. intros until x1'. intros FI2 FC2.
destruct n as [|n']; [discriminate HL|]. cbn [scanexp_l2_loop scanexp_l2_cond] in HL.
rewrite (isdigitc_f (fst (sh_getc f))) in HL by lia. cbn [andb] in HL. injection HL as E1 E2 E3. subst y2 c2 f2.
destruct n3 as [|n3']; [discriminate HL3|]. cbn [scanexp_l3_loop scanexp_l3_body] in HL3. rewrite (isdigitc_f (fst (sh_getc f))) in HL3 by lia.
injection HL3 as E4 E5. subst cX fX.
pose proof FI2 as FI'. dest_finv FI'.
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)); try (exfalso; mlia2).
eapply L_end with (k := (k + 1)%Z); try eassumption; unfold LM in *; try lia. }
clear IH HL HL3.
pose proof FI as FI'. dest_finv FI'. site_facts FC RJ k c f.
destruct (Z.eq_dec (T + sh_rpos f) (rf_rend T p true f)) as [SLOW|FAST].
-
pose proof FC as FC0. unfold_fc2 FC.
zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ | exfalso; lia ]).
destruct (rf_getc_slow T txt p J Hp T1 k c f RJ SLOW) as (STD & EJ & Hn & Hrp & Hc0).
assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
zs. zs. callw (eapply shgetc_callJ;
[ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
| plia | plia | plia | replace (q + -80 - 160)%Z with (q - 240)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI ]).
post_getc. subst J. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC end.
zs. zs. zs. fixw2. zs.
let v := getreg 9%Z in replace v with (Z_to_bv 64 y') by (apply Z_to_bv_eqm; f_equal; rewrite ?land_W64; rewrite ?(Z.mod_small y) by lia; lia).
let v := getreg 11%Z in replace v with (Z_to_bv 64 (fst (sh_getc f) - 48)) by reflexivity.
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+  eapply ND; [mlia2 | mk_finv | exact FC].
+ eapply DIG; [mlia2 | mk_finv | exact FC].
-
pose proof (rf_getc_fast_lt T txt p J Hp k c f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp k c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply Qy5Y.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
unfold_fc2 FC.
zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ exfalso; lia | ]).
zs. zs.
pose proof (u8ro_read segs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
zs. cbv beta. rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
zs. zs. zs. fixw2. zs.
let v := getreg 9%Z in replace v with (Z_to_bv 64 y') by (apply Z_to_bv_eqm; f_equal; rewrite ?land_W64; rewrite ?(Z.mod_small y) by lia; lia).
let v := getreg 11%Z in replace v with (Z_to_bv 64 (znth txt (sh_rpos f) - 48)) by reflexivity.
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ eapply DIG; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
+ zs. eapply ND; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
Qed.

Definition IM : Z := 214748364.
#[using="Type"] Lemma IM_eq : Z.quot INT_MAX_ 10 = IM. Proof. clear - ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR e10 HM ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Hpok Q0 Q1. first [clear HM | gw_hide HM | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear Q0 | gw_hide Q0 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]. reflexivity. Qed.

#[using="w_97 w_98 hi_97 lo_98 G_107a0 CODE BASE4 BASER D_97 E_97 D_98 E_98 ANCH_98 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_got_ssp_ssp_guard RNG_G_107a0 ROM_G_107a0 RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq rf_unget_nop shgetc_callJ pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_L1 : forall n m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word) x1 k c f (x neg xv c1 : Z) f1 n2 y2 c2 f2 n3 cX fX,
finv m j8 -> rw_cells segs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (1 <= k)%Z ->
sh_stdio f = sh_stdio f0 -> (48 <= c <= 57)%Z -> (0 <= x < IM)%Z ->
scanexp_l1_loop n (x, c, f) = Some (xv, c1, f1) ->
scanexp_l2_loop n2 (xv, c1, f1) = Some (y2, c2, f2) ->
scanexp_l3_loop n3 (c2, f2) = Some (cX, fX) ->
fR = sh_unget fX -> e10 = (if nz neg then - y2 else y2)%Z -> (0 <= neg <= 1)%Z ->
evt segs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 x) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 c) x19 (Z_to_bv 64 neg) (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 IM) s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x124)) fc None m (seg_rom segs)).
Proof. clear - w_97 w_98 hi_97 lo_98 G_107a0 CODE BASE4 BASER D_97 E_97 D_98 E_98 ANCH_98 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_got_ssp_ssp_guard RNG_G_107a0 ROM_G_107a0 RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq rf_unget_nop shgetc_callJ pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 segs base ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 Fp T p J txt canary pok fuelc f0 kmin0 c0 fR e10 HM Hpok Q0. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear Q0 | gw_hide Q0 | idtac].
induction n as [|n IH]; [intros; discriminate|].
intros until fX. intros FI FC RJ Hk Hst Hc Hx HL HL2 HL3 HfR He Rneg. pose proof Hx as Hx0. unfold IM in Hx.
pose proof (RFI_getc T txt p J BYT Hp Hnul k c f RJ ltac:(lia)) as RJ1.
pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
cbn [scanexp_l1_loop scanexp_l1_cond scanexp_l1_body] in HL. rewrite (isdigitc_t c), IM_eq in HL by lia.
replace (x <? IM) with true in HL by (symmetry; apply Z.ltb_lt; exact (proj2 Hx0)). cbn [andb] in HL.
rewrite (surjective_pairing (sh_getc f)) in HL.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
set (x' := (10 * x + c - 48)%Z) in HL.
assert (Rx' : (0 <= x' < 2^31)%Z) by (unfold x' in *; lia).
assert (DIG : (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x18' x28' x29' x30' x31' : word) x1',
finv m2 j8' -> rw_cells segs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
evt segs POST
(MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 x') (Z_to_bv 64 (fst (sh_getc f) - 48)) x11' x12' x13' x14' x15' x16' x17'
x18' (Z_to_bv 64 (fst (sh_getc f))) (Z_to_bv 64 neg) (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 IM) s8 s9 s10 s11 x28' x29' x30' x31')
F (Z_to_bv 64 (base + 0x174)) fc None m2 (seg_rom segs))).
{ intros Hd. intros until x1'. intros FI2 FC2.
pose proof FI2 as FI'. dest_finv FI'. unfold IM in *.
zs. zs. brs K.
- eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (k + 1)%Z (fst (sh_getc f)) (snd (sh_getc f))); try eassumption; try lia.
- destruct n as [|n']; [discriminate HL|]. cbn [scanexp_l1_loop scanexp_l1_cond] in HL.
rewrite IM_eq in HL. replace (x' <? IM) with false in HL by (symmetry; apply Z.ltb_ge; unfold IM; lia). rewrite Bool.andb_false_r in HL.
injection HL as E1 E2 E3. subst xv c1 f1.
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia); [ exfalso; lia | ]); try (exfalso; mlia2). zs. zs. zs.
eapply L_L2 with (k := (k + 1)%Z); try eassumption; unfold LM; try lia. }
assert (ND : ~ (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x18' x19' x28' x29' x30' x31' : word) x1',
finv m2 j8' -> rw_cells segs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
evt segs POST
(MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 x') (Z_to_bv 64 (fst (sh_getc f) - 48)) x11' x12' x13' x14' x15' x16' x17'
x18' x19' (Z_to_bv 64 neg) (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 IM) s8 s9 s10 s11 x28' x29' x30' x31')
F (Z_to_bv 64 (base + 0x17c)) fc None m2 (seg_rom segs))).
{ intros Hd. intros until x1'. intros FI2 FC2.
destruct n as [|n']; [discriminate HL|]. cbn [scanexp_l1_loop scanexp_l1_cond] in HL.
rewrite (isdigitc_f (fst (sh_getc f))) in HL by lia. cbn [andb] in HL. injection HL as E1 E2 E3. subst xv c1 f1.
destruct n2 as [|n2']; [discriminate HL2|]. cbn [scanexp_l2_loop scanexp_l2_cond] in HL2.
rewrite (isdigitc_f (fst (sh_getc f))) in HL2 by lia. cbn [andb] in HL2. injection HL2 as E4 E5 E6. subst y2 c2 f2.
destruct n3 as [|n3']; [discriminate HL3|]. cbn [scanexp_l3_loop scanexp_l3_body] in HL3. rewrite (isdigitc_f (fst (sh_getc f))) in HL3 by lia.
injection HL3 as E7 E8. subst cX fX.
pose proof FI2 as FI'. dest_finv FI'.
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)); try (exfalso; mlia2).
eapply L_end with (k := (k + 1)%Z); try eassumption; try lia. }
clear IH HL HL2 HL3.
pose proof FI as FI'. dest_finv FI'. site_facts FC RJ k c f.
destruct (Z.eq_dec (T + sh_rpos f) (rf_rend T p true f)) as [SLOW|FAST].
-
pose proof FC as FC0. unfold_fc2 FC.
zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ | exfalso; lia ]).
destruct (rf_getc_slow T txt p J Hp T1 k c f RJ SLOW) as (STD & EJ & Hn & Hrp & Hc0).
assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
zs. zs. callw (eapply shgetc_callJ;
[ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
| plia | plia | plia | replace (q + -80 - 160)%Z with (q - 240)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI ]).
post_getc. subst J. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC end.
zs. zs. zs. zs. fixw2. zs. fixw2.
let v := getreg 9%Z in replace v with (Z_to_bv 64 x') by (apply Z_to_bv_eqm; f_equal; rewrite ?land_W64; rewrite ?(Z.mod_small x) by lia; lia).
let v := getreg 10%Z in replace v with (Z_to_bv 64 (fst (sh_getc f) - 48)) by reflexivity.
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+  eapply ND; [mlia2 | mk_finv | exact FC].
+ eapply DIG; [mlia2 | mk_finv | exact FC].
-
pose proof (rf_getc_fast_lt T txt p J Hp k c f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp k c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply Qy5Y.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
unfold_fc2 FC.
zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ exfalso; lia | ]).
zs. zs.
pose proof (u8ro_read segs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
zs. cbv beta. rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
zs. zs. zs. fixw2. zs. fixw2.
let v := getreg 9%Z in replace v with (Z_to_bv 64 x') by (apply Z_to_bv_eqm; f_equal; rewrite ?land_W64; rewrite ?(Z.mod_small x) by lia; lia).
let v := getreg 10%Z in replace v with (Z_to_bv 64 (znth txt (sh_rpos f) - 48)) by reflexivity.
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ eapply DIG; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
+ zs. eapply ND; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
Qed.

#[using="w_97 w_98 hi_97 lo_98 G_107a0 CODE BASE4 BASER D_97 E_97 D_98 E_98 ANCH_98 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_got_ssp_ssp_guard RNG_G_107a0 ROM_G_107a0 RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq rf_unget_nop shgetc_callJ pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_E4 : forall m j8 (x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f (neg : Z),
finv m j8 -> rw_cells segs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (2 <= k)%Z ->
sh_stdio f = sh_stdio f0 -> (-1 <= c < 256)%Z ->
scanexp_tail fuelc neg c f = Some (fR, e10) -> (0 <= neg <= 1)%Z ->
evt segs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) x9 (Z_to_bv 64 (c - 58)) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 c) x19 (Z_to_bv 64 neg) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0xe0)) fc None m (seg_rom segs)).
Proof. clear - w_97 w_98 hi_97 lo_98 G_107a0 CODE BASE4 BASER D_97 E_97 D_98 E_98 ANCH_98 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_got_ssp_ssp_guard RNG_G_107a0 ROM_G_107a0 RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq rf_unget_nop shgetc_callJ pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 segs base ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 Fp T p J txt canary pok fuelc f0 kmin0 c0 fR e10 HM Hpok Q0. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear Q0 | gw_hide Q0 | idtac].
intros until neg. intros FI FC RJ Hk Hst Hc HT Rneg.
pose proof FI as FI'. dest_finv FI'. unfold scanexp_tail in HT.
zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia)).
-
rewrite (isdigitc_t c) in HT by mlia2. cbn [negb] in HT.
destruct (scanexp_l1_loop fuelc (0%Z, c, f)) as [[[xv c1] f1]|] eqn:HL1; [|discriminate HT].
destruct (scanexp_l2_loop fuelc (xv, c1, f1)) as [[[y2 c2] f2]|] eqn:HL2; [|discriminate HT].
destruct (scanexp_l3_loop fuelc (c2, f2)) as [[cX fX]|] eqn:HL3; [|discriminate HT].
injection HT as E1 E2.
zs. fixw2. zs. zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)); try (exfalso; mlia2).
zs. zs. zs.
eapply L_L1 with (k := k); try eassumption; unfold IM; try lia; try mlia2. all: symmetry; assumption.
-
rewrite (isdigitc_f c) in HT by mlia2. cbn [negb] in HT. injection HT as E1 E2.
eapply L_ND; try eassumption; try lia. all: symmetry; assumption.
Qed.

#[using="w_97 w_98 hi_97 lo_98 G_107a0 CODE BASE4 BASER D_97 E_97 D_98 E_98 ANCH_98 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_got_ssp_ssp_guard RNG_G_107a0 ROM_G_107a0 RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq rf_unget_nop shgetc_callJ pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Hpok Q1"] Lemma L_C4 : forall m j8 (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f (neg : Z),
finv m j8 -> rw_cells segs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (3 <= k)%Z ->
sh_stdio f = sh_stdio f0 -> (-1 <= c < 256)%Z ->
scanexp_tail fuelc neg c (if negb (isdigitc c) && nz pok then sh_unget f else f) = Some (fR, e10) ->
(0 <= neg <= 1)%Z -> pok <> 0%Z ->
evt segs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) (Z_to_bv 64 (c - 58)) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 c) x19 (Z_to_bv 64 neg) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0xc0)) fc None m (seg_rom segs)).
Proof. clear - w_97 w_98 hi_97 lo_98 G_107a0 CODE BASE4 BASER D_97 E_97 D_98 E_98 ANCH_98 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_got_ssp_ssp_guard RNG_G_107a0 ROM_G_107a0 RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq rf_unget_nop shgetc_callJ pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Hpok Q1 segs base ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 Fp T p J txt canary pok fuelc f0 kmin0 c0 fR e10 HM Q0. first [clear HM | gw_hide HM | idtac]; first [clear Q0 | gw_hide Q0 | idtac].
intros until neg. intros FI FC RJ Hk Hst Hc HT Rneg Hpk.
replace (nz pok) with true in HT by (unfold nz; destruct (Z.eqb_spec pok 0); [lia|reflexivity]).
pose proof FI as FI'. dest_finv FI'.
zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia)).
-
rewrite (isdigitc_t c) in HT by mlia2. cbn [negb andb] in HT.
eapply L_E4; try eassumption; try lia.
-
rewrite (isdigitc_f c) in HT by mlia2. cbn [negb andb] in HT.
site_facts FC RJ k c f.
pose proof (RFI_unget T txt p J Hp k c f RJ ltac:(lia)) as RJu.
pose proof (stdio_unget f) as Hstu. rewrite Hst in Hstu.
destruct (sh_shlim_neg f) eqn:SN.
+ rewrite (rf_unget_nop f SN) in *. unfold_fc2 FC. rewrite SN in FC. unfold M64 in FC.
zs. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ | exfalso; lia ]).
eapply L_ND with (k := (k - 1)%Z); try eassumption; try lia.
all: try (unfold scanexp_tail in HT; rewrite (isdigitc_f c) in HT by mlia2; cbn [negb] in HT; injection HT as E1 E2; symmetry; assumption).
unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
+ rewrite (rf_unget_eq f SN) in *. unfold_fc2 FC. rewrite SN in FC. unfold M64 in FC.
zs. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ exfalso; lia | ]).
zs. zs. zs. zs.
eapply L_ND with (k := (k - 1)%Z); try eassumption; try lia.
all: try (unfold scanexp_tail in HT; rewrite (isdigitc_f c) in HT by mlia2; cbn [negb] in HT; injection HT as E1 E2; symmetry; assumption).
1: mk_finv.
unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
Qed.

#[using="w_97 w_98 hi_97 lo_98 G_107a0 CODE BASE4 BASER D_97 E_97 D_98 E_98 ANCH_98 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_got_ssp_ssp_guard RNG_G_107a0 ROM_G_107a0 RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq rf_unget_nop shgetc_callJ pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Hpok Q1"] Lemma L_SGN : forall m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f,
finv m j8 -> rw_cells segs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (2 <= k)%Z ->
sh_stdio f = sh_stdio f0 -> (c = 43 \/ c = 45)%Z ->
scanexp_tail fuelc (b2z (c =? 45)%Z) (fst (sh_getc f))
(if negb (isdigitc (fst (sh_getc f))) && nz pok then sh_unget (snd (sh_getc f)) else snd (sh_getc f)) = Some (fR, e10) ->
evt segs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 c) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x70)) fc None m (seg_rom segs)).
Proof. clear - w_97 w_98 hi_97 lo_98 G_107a0 CODE BASE4 BASER D_97 E_97 D_98 E_98 ANCH_98 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_got_ssp_ssp_guard RNG_G_107a0 ROM_G_107a0 RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq rf_unget_nop shgetc_callJ pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Hpok Q1 segs base ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 Fp T p J txt canary pok fuelc f0 kmin0 c0 fR e10 HM Q0. first [clear HM | gw_hide HM | idtac]; first [clear Q0 | gw_hide Q0 | idtac].
intros until f. intros FI FC RJ Hk Hst Hc HT.
pose proof (RFI_getc T txt p J BYT Hp Hnul k c f RJ ltac:(lia)) as RJ1.
pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
assert (Rneg : (0 <= b2z (c =? 45)%Z <= 1)%Z) by (unfold b2z; destruct (c =? 45)%Z; lia).
pose proof FI as FI'. dest_finv FI'. site_facts FC RJ k c f.
destruct (Z.eq_dec (T + sh_rpos f) (rf_rend T p true f)) as [SLOW|FAST].
-
pose proof FC as FC0. unfold_fc2 FC.
zs. zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ | exfalso; lia ]).
destruct (rf_getc_slow T txt p J Hp T1 k c f RJ SLOW) as (STD & EJ & Hn & Hrp & Hc0).
assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
zs. zs. callw (eapply shgetc_callJ;
[ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
| plia | plia | plia | replace (q + -80 - 160)%Z with (q - 240)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI ]).
post_getc. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rewrite <- EJ in H; rename H into FC end.
zs. zs. zs. fixw2.
let v := getreg 20%Z in replace v with (Z_to_bv 64 (b2z (c =? 45)%Z)) by (destruct Hc as [-> | ->]; reflexivity).
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+  eapply L_E4 with (k := (k + 1)%Z); try eassumption; try lia. 1: mk_finv.
replace (nz pok) with false in HT by (unfold nz; destruct (Z.eqb_spec pok 0); [reflexivity|mlia2]). rewrite Bool.andb_false_r in HT. exact HT.
+ eapply L_C4 with (k := (k + 1)%Z); try eassumption; try lia; try mlia2. mk_finv.
-
pose proof (rf_getc_fast_lt T txt p J Hp k c f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp k c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply Qy5Y.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
unfold_fc2 FC.
zs. zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ exfalso; lia | ]).
zs. zs.
pose proof (u8ro_read segs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
zs. cbv beta. rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
zs. zs. fixw2.
let v := getreg 20%Z in replace v with (Z_to_bv 64 (b2z (c =? 45)%Z)) by (destruct Hc as [-> | ->]; reflexivity).
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+  eapply L_C4 with (k := (k + 1)%Z); try eassumption; try lia; try mlia2.
1: mk_finv. unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells.
+ zs. eapply L_E4 with (k := (k + 1)%Z); try eassumption; try lia.
1: mk_finv. 1: unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells.
replace (nz pok) with false in HT by (unfold nz; destruct (Z.eqb_spec pok 0); [reflexivity|mlia2]). rewrite Bool.andb_false_r in HT. exact HT.
Qed.

#[using="w_97 w_98 hi_97 lo_98 G_107a0 CODE BASE4 BASER D_97 E_97 D_98 E_98 ANCH_98 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_got_ssp_ssp_guard RNG_G_107a0 ROM_G_107a0 RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq rf_unget_nop shgetc_callJ pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Hpok Q1"] Lemma L_6c : forall m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f,
finv m j8 -> rw_cells segs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (2 <= k)%Z ->
sh_stdio f = sh_stdio f0 -> (-1 <= c < 256)%Z -> c <> 43%Z ->
(c = 45%Z -> scanexp_tail fuelc (b2z (c =? 45)%Z) (fst (sh_getc f))
(if negb (isdigitc (fst (sh_getc f))) && nz pok then sh_unget (snd (sh_getc f)) else snd (sh_getc f)) = Some (fR, e10)) ->
(c <> 45%Z -> scanexp_tail fuelc 0%Z c f = Some (fR, e10)) ->
evt segs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 c) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x68)) fc None m (seg_rom segs)).
Proof. clear - w_97 w_98 hi_97 lo_98 G_107a0 CODE BASE4 BASER D_97 E_97 D_98 E_98 ANCH_98 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_got_ssp_ssp_guard RNG_G_107a0 ROM_G_107a0 RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq rf_unget_nop shgetc_callJ pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Hpok Q1 segs base ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 Fp T p J txt canary pok fuelc f0 kmin0 c0 fR e10 HM Q0. first [clear HM | gw_hide HM | idtac]; first [clear Q0 | gw_hide Q0 | idtac].
intros until f. intros FI FC RJ Hk Hst Hc H43 H45 Hother.
pose proof FI as FI'. dest_finv FI'.
zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia)).
-
zs. zs. fixw2. zs.
eapply L_E4 with (k := k) (neg := 0%Z); try eassumption; try lia. apply Hother. mlia2.
- eapply L_SGN with (k := k); try eassumption; try lia. 1: right; mlia2. apply H45. mlia2.
Qed.

#[using="w_97 w_98 hi_97 lo_98 G_107a0 CODE BASE4 BASER D_97 E_97 D_98 E_98 ANCH_98 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_got_ssp_ssp_guard RNG_G_107a0 ROM_G_107a0 RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq rf_unget_nop shgetc_callJ pre post fuelc HM ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Hpok Q1"] Lemma L_main : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
rw_cells segs m0 Fp (rf_cells T p true f0 J) -> RFJ' kmin0 c0 f0 -> (1 <= kmin0)%Z -> c0 <> 0%Z ->
bytes_at segs m0 T (zbytes txt) -> ssp_cells m0 canary ->
stk segs m0 (q - SCANEXP_DEPTH) q -> mem_inv segs m0 ->
evt segs POST
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 SCANEXP) fc None m0 (seg_rom segs)).
Proof. clear - w_97 w_98 hi_97 lo_98 G_107a0 CODE BASE4 BASER D_97 E_97 D_98 E_98 ANCH_98 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_got_ssp_ssp_guard RNG_G_107a0 ROM_G_107a0 RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq rf_unget_nop shgetc_callJ pre post fuelc HM ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Hpok Q1 segs ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 Fp T p J txt canary pok f0 kmin0 c0 fR e10 Q0. first [clear Q0 | gw_hide Q0 | idtac].
intros until t6. intros FC RJ Hk Hc0nz BY [SSP1 SSP2] ST MI.
pose proof (munch_refl [(q - SCANEXP_DEPTH, q); (Fp, Fp + 232)]%Z m0) as MU. pose proof (wmono_refl segs m0) as WM.
unfold SCANEXP, SCANEXP_DEPTH in *. gw_expose got_ssp; gw_expose ssp_guard.
assert (LTX : length (zbytes txt) = length txt) by apply zbytes_length. unfold zlength in *.
pose proof HM as HT. rewrite scanexp_eq, (surjective_pairing (sh_getc f0)) in HT. cbn beta iota zeta in HT.
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin0 c0 f0 RJ Hc0nz) as RJ1.
pose proof (stdio_getc f0) as Hst1.
assert (Rc' : (-1 <= fst (sh_getc f0) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).

assert (JS : forall m2 j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1,
finv m2 j8 -> rw_cells segs m2 Fp (rf_cells T p true (snd (sh_getc f0)) J) ->
(fst (sh_getc f0) = 43 \/ fst (sh_getc f0) = 45)%Z ->
evt segs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (fst (sh_getc f0))) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x70)) fc None m2 (seg_rom segs))).
{ intros until x1. intros FI2 FC2 H4345.
eapply L_SGN with (k := (kmin0 + 1)%Z); try eassumption; try lia.
replace (((fst (sh_getc f0) =? 43) || (fst (sh_getc f0) =? 45))%Z) with true in HT
by (symmetry; destruct H4345 as [E|E]; rewrite E; reflexivity).
rewrite (surjective_pairing (sh_getc (snd (sh_getc f0)))) in HT. cbn beta iota zeta in HT. exact HT. }
assert (J6 : forall m2 j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1,
finv m2 j8 -> rw_cells segs m2 Fp (rf_cells T p true (snd (sh_getc f0)) J) ->
(fst (sh_getc f0) <> 43)%Z ->
evt segs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (fst (sh_getc f0))) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x68)) fc None m2 (seg_rom segs))).
{ intros until x1. intros FI2 FC2 H43.
eapply L_6c with (k := (kmin0 + 1)%Z); try eassumption; try lia.
- intros E45. replace (((fst (sh_getc f0) =? 43) || (fst (sh_getc f0) =? 45))%Z) with true in HT
by (symmetry; rewrite E45; reflexivity).
rewrite (surjective_pairing (sh_getc (snd (sh_getc f0)))) in HT. cbn beta iota zeta in HT. exact HT.
- intros N45. replace (((fst (sh_getc f0) =? 43) || (fst (sh_getc f0) =? 45))%Z) with false in HT
by (symmetry; apply Bool.orb_false_intro; apply Z.eqb_neq; assumption).
cbn beta iota zeta in HT. exact HT. }
site_facts FC RJ kmin0 c0 f0.
zs. carve_frame 80%nat ST.
do 9 zs.
zs.
destruct (Z.eq_dec (T + sh_rpos f0) (rf_rend T p true f0)) as [SLOW|FAST].
-
pose proof FC as FC0. unfold_fc2 FC.
zs. zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ | exfalso; lia ]).
destruct (rf_getc_slow T txt p J Hp T1 kmin0 c0 f0 RJ SLOW) as (STD & EJ & Hn & Hrp & Hc0).
destruct (ST0 STD) as [TXT Hpre].
zs. zs. callw (eapply shgetc_callJ;
[ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
| plia | plia | plia | replace (q + -80 - 160)%Z with (q - 240)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI ]).
post_getc. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rewrite <- EJ in H; rename H into FC end.
zs. zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ eapply JS; [mk_finv | exact FC | left; mlia2].
+ eapply J6; [mk_finv | exact FC | mlia2].
-
pose proof (rf_getc_fast_lt T txt p J Hp kmin0 c0 f0 RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin0 c0 f0 RJ FAST) in *. cbn [fst snd] in *.
pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f0)) ltac:(apply Qy5Y.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
unfold_fc2 FC.
zs. zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ exfalso; lia | ]).
zs. zs.
pose proof (u8ro_read segs _ T (zbytes txt) (sh_rpos f0) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f0) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
zs. cbv beta. rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f0))) by lia. clear RDb.
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ eapply J6; [mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells | mlia2].
+ zs. eapply JS; [mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells | left; mlia2].
Qed.
End Scanexp.

#[using="w_97 w_98 hi_97 lo_98 G_107a0 CODE BASE4 BASER D_97 E_97 D_98 E_98 ANCH_98 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_got_ssp_ssp_guard RNG_G_107a0 ROM_G_107a0 RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq rf_unget_nop shgetc_callJ"] Lemma scanexp_rspec : scanexp_rstmt.
Proof. clear - w_97 w_98 hi_97 lo_98 G_107a0 CODE BASE4 BASER D_97 E_97 D_98 E_98 ANCH_98 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_got_ssp_ssp_guard RNG_G_107a0 ROM_G_107a0 RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq rf_unget_nop shgetc_callJ.
unfold scanexp_rstmt. intros.
eapply L_main; eassumption.
Qed.

End G.
End Mq1.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Q2qa Q4J3 QytA Qnxq QJE4 QWTl QPjm QUZl Q7S0 QGeV QLsg QkQT QlkP QM7w QXxF Q8QT QCa8 QDXD QkTt Q6q3 G.GwFamMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w QXxF.Mq1.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QCa8.Mq4.
Import QDXD.Mq2.
Import QkTt.Mq3.
Import QkTt.Mq4.
Import QDXD.Mq1.
Import Qy8Z.Mqa.
Import QkTt.Mq5.
Import Qy8Z.Mq8.
Import Qy8Z.Mq1.
Import QQRC.Mq4.
Import QQRC.Mqc.
Import QROt.Mq3.
Import QZxv.Mqo.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rvm_wait_entry : Z).
Variables (w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 : Z).
Variables (hi_14 hi_18 hi_114 hi_121 hi_130 hi_136 hi_148 hi_218 hi_311 : bv 20).
Variables (lo_15 lo_19 lo_116 lo_122 lo_131 lo_137 lo_149 lo_220 lo_313 : bv 12).
Variables (joff_427 joff_552 : bv 21).
Variables (e_197bc : Z).
Hypothesis CODE : code_at segs base (alloc_slot_code w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 2212.
Let ralloc_meta_entry := (base + -1608)%Z.
Let ralloc_slot_entry := (base + 0)%Z.
Let rmmap_entry := (rvm_wait_entry + 4)%Z.
Hypothesis D_14 : decode_any (Z_to_bv 32 w_14) = Some (Auipc 10 hi_14, 4%Z).
Hypothesis E_14 : is_ecall (Z_to_bv 32 w_14) = false.
Hypothesis D_15 : decode_any (Z_to_bv 32 w_15) = Some (Load SZ8 true 20 10 lo_15, 4%Z).
Hypothesis E_15 : is_ecall (Z_to_bv 32 w_15) = false.
Hypothesis D_18 : decode_any (Z_to_bv 32 w_18) = Some (Auipc 11 hi_18, 4%Z).
Hypothesis E_18 : is_ecall (Z_to_bv 32 w_18) = false.
Hypothesis D_19 : decode_any (Z_to_bv 32 w_19) = Some (OpImm ALU_ADD 22 11 lo_19, 4%Z).
Hypothesis E_19 : is_ecall (Z_to_bv 32 w_19) = false.
Hypothesis D_114 : decode_any (Z_to_bv 32 w_114) = Some (Auipc 11 hi_114, 4%Z).
Hypothesis E_114 : is_ecall (Z_to_bv 32 w_114) = false.
Hypothesis D_116 : decode_any (Z_to_bv 32 w_116) = Some (OpImm ALU_ADD 11 11 lo_116, 4%Z).
Hypothesis E_116 : is_ecall (Z_to_bv 32 w_116) = false.
Hypothesis D_121 : decode_any (Z_to_bv 32 w_121) = Some (Auipc 10 hi_121, 4%Z).
Hypothesis E_121 : is_ecall (Z_to_bv 32 w_121) = false.
Hypothesis D_122 : decode_any (Z_to_bv 32 w_122) = Some (OpImm ALU_ADD 25 10 lo_122, 4%Z).
Hypothesis E_122 : is_ecall (Z_to_bv 32 w_122) = false.
Hypothesis D_130 : decode_any (Z_to_bv 32 w_130) = Some (Auipc 11 hi_130, 4%Z).
Hypothesis E_130 : is_ecall (Z_to_bv 32 w_130) = false.
Hypothesis D_131 : decode_any (Z_to_bv 32 w_131) = Some (Load SZ8 true 11 11 lo_131, 4%Z).
Hypothesis E_131 : is_ecall (Z_to_bv 32 w_131) = false.
Hypothesis D_136 : decode_any (Z_to_bv 32 w_136) = Some (Auipc 13 hi_136, 4%Z).
Hypothesis E_136 : is_ecall (Z_to_bv 32 w_136) = false.
Hypothesis D_137 : decode_any (Z_to_bv 32 w_137) = Some (OpImm ALU_ADD 13 13 lo_137, 4%Z).
Hypothesis E_137 : is_ecall (Z_to_bv 32 w_137) = false.
Hypothesis D_148 : decode_any (Z_to_bv 32 w_148) = Some (Auipc 13 hi_148, 4%Z).
Hypothesis E_148 : is_ecall (Z_to_bv 32 w_148) = false.
Hypothesis D_149 : decode_any (Z_to_bv 32 w_149) = Some (OpImm ALU_ADD 13 13 lo_149, 4%Z).
Hypothesis E_149 : is_ecall (Z_to_bv 32 w_149) = false.
Hypothesis D_218 : decode_any (Z_to_bv 32 w_218) = Some (Auipc 13 hi_218, 4%Z).
Hypothesis E_218 : is_ecall (Z_to_bv 32 w_218) = false.
Hypothesis D_220 : decode_any (Z_to_bv 32 w_220) = Some (OpImm ALU_ADD 13 13 lo_220, 4%Z).
Hypothesis E_220 : is_ecall (Z_to_bv 32 w_220) = false.
Hypothesis D_311 : decode_any (Z_to_bv 32 w_311) = Some (Auipc 14 hi_311, 4%Z).
Hypothesis E_311 : is_ecall (Z_to_bv 32 w_311) = false.
Hypothesis D_313 : decode_any (Z_to_bv 32 w_313) = Some (OpImm ALU_ADD 14 14 lo_313, 4%Z).
Hypothesis E_313 : is_ecall (Z_to_bv 32 w_313) = false.
Hypothesis D_427 : decode_any (Z_to_bv 32 w_427) = Some (Jal 1 joff_427, 4%Z).
Hypothesis E_427 : is_ecall (Z_to_bv 32 w_427) = false.
Hypothesis D_552 : decode_any (Z_to_bv 32 w_552) = Some (Jal 1 joff_552, 4%Z).
Hypothesis E_552 : is_ecall (Z_to_bv 32 w_552) = false.
Hypothesis ANCH_15 : gw_anch (Z.shiftl (bv_signed hi_14) 12 + (base + 56) + bv_signed lo_15)%Z RGOT_SSP.
Hypothesis ANCH_19 : gw_anch (Z.shiftl (bv_signed hi_18) 12 + (base + 72) + bv_signed lo_19)%Z (RATP + 131960).
Hypothesis ANCH_116 : gw_anch (Z.shiftl (bv_signed hi_114) 12 + (base + 456) + bv_signed lo_116)%Z RDEBRUIJN.
Hypothesis ANCH_122 : gw_anch (Z.shiftl (bv_signed hi_121) 12 + (base + 484) + bv_signed lo_122)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_131 : gw_anch (Z.shiftl (bv_signed hi_130) 12 + (base + 520) + bv_signed lo_131)%Z (RATP + 131776).
Hypothesis ANCH_137 : gw_anch (Z.shiftl (bv_signed hi_136) 12 + (base + 544) + bv_signed lo_137)%Z (RDEBRUIJN + 128).
Hypothesis ANCH_149 : gw_anch (Z.shiftl (bv_signed hi_148) 12 + (base + 592) + bv_signed lo_149)%Z (RDEBRUIJN + 155).
Hypothesis ANCH_220 : gw_anch (Z.shiftl (bv_signed hi_218) 12 + (base + 872) + bv_signed lo_220)%Z RDEBRUIJN.
Hypothesis ANCH_313 : gw_anch (Z.shiftl (bv_signed hi_311) 12 + (base + 1244) + bv_signed lo_313)%Z (RDEBRUIJN + 32).
Hypothesis LINK_427 : gw_anch (base + 1708 + bv_signed joff_427)%Z (rmmap_entry + 0)%Z.
Hypothesis LINK_552 : gw_anch (base + 2208 + bv_signed joff_552)%Z (e_197bc + 0)%Z.
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
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rt1_regs : ltac:(gw_rebind_ty (@QZxv.Mqo.rt1_regs RATP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QZxv.Mqo.rt1_regs RATP) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QZxv.Mqo.rt1_regs RATP) (@rt1_regs) gw_tbl_0).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QZxv.Mqo.rarea_rep segs) (@rarea_rep) (gw_ent (@QROt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mqc.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_1)))))))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QZxv.Mqo.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QROt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mqc.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_2)))))))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QZxv.Mqo.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QROt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mqc.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_3)))))))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QZxv.Mqo.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QROt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mqc.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_4)))))))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QZxv.Mqo.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QROt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mqc.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_5)))))))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QZxv.Mqo.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QROt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mqc.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_6)))))))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QZxv.Mqo.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QROt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mqc.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_7)))))))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QZxv.Mqo.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QROt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mqc.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_8)))))))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QZxv.Mqo.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QROt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mqc.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_9)))))))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QZxv.Mqo.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QROt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mqc.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_10)))))))))))))).

Hypothesis rdbi_range : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qy8Z.Mq8.gw_all) (@Qy8Z.Mq8.rdbi_range) (base + -880)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_11))) in let T := gw_fold_pcs T base (-880)%Z [0; 116; 472; 500; 524]%Z in exact T).
Hypothesis rdebruijn_read : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qy8Z.Mq8.gw_all) (@Qy8Z.Mq8.rdebruijn_read) (base + -880)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_11))) in let T := gw_fold_pcs T base (-880)%Z [0; 116; 472; 500; 524]%Z in exact T).
Hypothesis mul_srliw27 : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qy8Z.Mq8.gw_all) (@Qy8Z.Mq8.mul_srliw27) (base + -880)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_11))) in let T := gw_fold_pcs T base (-880)%Z [0; 116; 472; 500; 524]%Z in exact T).
Hypothesis rclz_pow_eq : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qy8Z.Mq8.gw_all) (@Qy8Z.Mq8.rclz_pow_eq) (base + -880)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_11))) in let T := gw_fold_pcs T base (-880)%Z [0; 116; 472; 500; 524]%Z in exact T).
Hypothesis lxor_4k_124 : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qy8Z.Mq8.gw_all) (@Qy8Z.Mq8.lxor_4k_124) (base + -880)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_11))) in let T := gw_fold_pcs T base (-880)%Z [0; 116; 472; 500; 524]%Z in exact T).
Hypothesis lor_even_1 : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qy8Z.Mq8.gw_all) (@Qy8Z.Mq8.lor_even_1) (base + -880)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_11))) in let T := gw_fold_pcs T base (-880)%Z [0; 116; 472; 500; 524]%Z in exact T).

Definition rsize_classes_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rsize_classes_read) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rsize_classes_read)).
Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).

#[using="RDEBRUIJN RGOT_SSP e_197bc rvm_wait_entry rmmap_entry RATP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 D_114 E_114 D_116 E_116 D_121 E_121 D_122 E_122 D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 D_218 E_218 D_220 E_220 D_311 E_311 D_313 E_313 D_427 E_427 D_552 E_552 ANCH_15 ANCH_19 ANCH_116 ANCH_122 ANCH_131 ANCH_137 ANCH_149 ANCH_220 ANCH_313 LINK_427 LINK_552 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ ralloc_meta_entry ralloc_slot_entry rmmap_entry rdbi_range rdebruijn_read mul_srliw27 rclz_pow_eq lxor_4k_124 lor_even_1"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

Section AG1.
Variables (sc : Z).
Hypothesis SC : 0 <= sc < 48.

#[using="rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_121 lo_122 CODE D_121 E_121 D_122 E_122 ANCH_122 RNG_RDEBRUIJN ROM_RSIZE_CLASSES ralloc_meta_entry ralloc_slot_entry rmmap_entry SC"] Lemma rag_entry_walk :
forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
mem_inv segs m ->
evt segs (fun ms' =>
ms' = MS (rt1_regs sc (Z_to_bv 64 (base + 0x1f8)) sp gp tp t0 t1 t2 s1 (Z_to_bv 64 ((RDEBRUIJN + 32) + sc * 2)) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (sc * 2))
(wz (size_class sc)) (Z_to_bv 64 (RDEBRUIJN + 32)) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom segs))
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x1e0)) fc None m (seg_rom segs)).
Proof. clear - rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_121 lo_122 CODE D_121 E_121 D_122 E_122 ANCH_122 RNG_RDEBRUIJN ROM_RSIZE_CLASSES ralloc_meta_entry ralloc_slot_entry rmmap_entry SC segs base RDEBRUIJN RATP sc. gw_expose_fam RATP; gw_expose_fam RDEBRUIJN. try gw_hide sc.
intros until m. intros MI. (gw_expose_fam RDEBRUIJN; gw_expose_fam RATP; unfold rt1_regs, ralloc_meta_entry in *).
pose proof (size_class_range sc SC) as SZR.
step. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. step. step. step.
pose proof (rsize_classes_read m sc MI SC) as SCRD. gw_expose_fam RDEBRUIJN.
replace ((RDEBRUIJN + 32) + 2 * sc) with ((RDEBRUIJN + 32) + sc * 2) in SCRD by lia.
step. rewrite zx16_wz by lia. clear SCRD.
step. apply evt_done. reflexivity.
Qed.
End AG1.

#[using="w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE"] Lemma rag_ret_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (gm : Z),
0 <= gm < 2^64 -> mem_inv segs m ->
evt segs (fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 gm) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (if gm =? 0 then (base + 0x860) else (base + 0x204))) fc None m (seg_rom segs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 gm) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x1f8)) fc None m (seg_rom segs)).
Proof. clear - w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE segs base.
intros until gm. intros GR MI.
step. step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
- subst gm. cbn [Z.eqb]. apply evt_done. reflexivity.
- replace (gm =? 0) with false by (symmetry; apply Z.eqb_neq; gw_exact K). apply evt_done. reflexivity.
Qed.

Section STC.
Variables (szc cnt : Z).
Hypothesis SZC : 1 <= szc <= 8191.
Hypothesis CR : 1 <= cnt <= 32.
Hypothesis SMALL : szc * 16 * cnt + 16 <= 2048.
Let n' := szc * 16 * cnt + 12.
Let j := size_to_class n'.

#[using="base rvm_wait_entry ralloc_meta_entry ralloc_slot_entry rmmap_entry SZC CR SMALL"] Lemma rstc_q_eq : j = stc_q (szc * cnt).
Proof. clear - base rvm_wait_entry ralloc_meta_entry ralloc_slot_entry rmmap_entry SZC CR SMALL szc cnt n' j. try gw_hide j; try gw_hide n'; first [clear cnt | gw_hide cnt | idtac]; first [clear szc | gw_hide szc | idtac].
unfold j, n'. rewrite size_to_class_q by nia. f_equal. Z.div_mod_to_equations. nia.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_218 lo_220 CODE D_218 E_218 D_220 E_220 ANCH_220 RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES rdbi_range rdebruijn_read mul_srliw27 rclz_pow_eq lxor_4k_124 lor_even_1 ralloc_meta_entry ralloc_slot_entry rmmap_entry SZC CR SMALL"] Lemma rnest_call_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) F fc m,
mem_inv segs m ->
evt segs (fun ms' => exists a2' a3' a4',
ms' = MS (mkR (Z_to_bv 64 (base + 0x3e0)) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2' a3' a4' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (RDEBRUIJN + 32)) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom segs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (wz (szc * 16 * cnt)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (RDEBRUIJN + 32)) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x310)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_218 lo_220 CODE D_218 E_218 D_220 E_220 ANCH_220 RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES rdbi_range rdebruijn_read mul_srliw27 rclz_pow_eq lxor_4k_124 lor_even_1 ralloc_meta_entry ralloc_slot_entry rmmap_entry SZC CR SMALL segs base RDEBRUIJN szc cnt n' j. gw_expose_fam RDEBRUIJN. try gw_hide j; try gw_hide n'; try gw_hide cnt; try gw_hide szc.
intros until m. intros MI.
assert (PR : 16 <= szc * 16 * cnt <= 2032) by nia.
set (q := szc * cnt). assert (QR : 1 <= q <= 127) by (subst q; nia).
pose proof rstc_q_eq as STC. fold q in STC.
(gw_expose_fam RDEBRUIJN; unfold ralloc_slot_entry in *).

assert (CALL : forall (a0' a2' a3' : word) (jv : Z), jv = j ->
evt segs (fun ms' => exists a2'' a3'' a4'',
ms' = MS (mkR (Z_to_bv 64 (base + 0x3e0)) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2'' a3'' a4'' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (RDEBRUIJN + 32)) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 base) fc None m (seg_rom segs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (wz n') a2' a3' (Z_to_bv 64 jv) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (RDEBRUIJN + 32)) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x3d4)) fc None m (seg_rom segs))).
{ intros a0' a2' a3' jv ->.
pose proof (size_to_class_props n' ltac:(unfold n', MMAP_THRESHOLD; lia)) as (SCRj & _).
step. rewrite Qfw3_c1.Mq2.sextw_small by lia. step. step.
rewrite ?Z.add_0_r. apply evt_done. do 3 eexists. reflexivity. }

step. rewrite (wz_unsigned (szc * 16 * cnt)) by lia. fold n'. change (Z_to_bv 64 n') with (wz n').
step. step. rewrite (wz_unsigned (szc * 16 * cnt)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
replace (szc * 16 * cnt / 16) with q by (subst q; Z.div_mod_to_equations; nia).

step. if_cases K; zify_cond K; rewrite ?(wz_unsigned n'), ?unsigned_lit in K by (unfold n'; lia).
-
apply CALL. rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; unfold n' in K; Z.div_mod_to_equations; nia). reflexivity.
-
assert (Q10 : 10 <= q) by (unfold n' in K; nia).
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

step. step. step.
rewrite (unsigned_lit w4), (Z.shiftl_mul_pow2 w4) by lia. rewrite (unsigned_lit (w4 * 2 ^ 33)) by lia.
replace ((w4 * 2 ^ 33) ≫ 49) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
rewrite (unsigned_lit 0), Z.lor_0_l by lia.

step. step. rewrite (unsigned_lit w4) by lia.
step. rewrite (unsigned_lit (w4 + 1)) by lia. rewrite (unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (rclz_pow x). rewrite PW.
set (k := Z.log2 x) in *.
pose proof (size_to_class_props n' ltac:(unfold n', MMAP_THRESHOLD; lia)) as (SCRj & SFIT & LG).
assert (K13 : 3 <= k <= 12).
{ unfold n' in LG. replace ((szc * 16 * cnt + 12 + 3) / 16) with q in LG by (subst q; Z.div_mod_to_equations; nia). subst k x. lia. }
assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
assert (EK : k = Z.log2 x) by first [reflexivity | (cbn; lia)]. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
assert (EX : x = q + 1) by first [reflexivity | (cbn; lia)]. clearbody x.

step. step. step.
step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
step. rewrite (mul_srliw27 k) by lia.
pose proof (rdbi_range k) as DR.
step. rewrite ?(unsigned_lit (rdbi k)) by lia.
pose proof (rdebruijn_read m k MI ltac:(lia)) as DBR. gw_expose_fam RDEBRUIJN.
step. rewrite ?zxb_b8 by lia. clear DBR.

step. rewrite (wz_unsigned k), (Z.shiftl_mul_pow2 k) by lia. change (2 ^ 2) with 4.
step. rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
replace (124 - 4 * k) with (120 - i) by lia.
assert (STQ : j = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
{ rewrite STC. unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
clearbody i. clear EK.
pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.
step. step. rewrite (unsigned_lit (120 - i)) by lia. replace (121 + - (120 - i)) with (i + 1) by lia.
step. rewrite (unsigned_lit (i + 1)), (Z.shiftl_mul_pow2 (i + 1)) by lia. change (2 ^ 1) with 2.
step. replace ((RDEBRUIJN + 32) + (i + 1) * 2) with ((RDEBRUIJN + 32) + 2 * (i + 1)) by lia.
pose proof (rsize_classes_read m (i + 1) MI ltac:(lia)) as RS1. gw_expose_fam RDEBRUIJN.
step. rewrite ?zx16_wz by lia. clear RS1.

assert (J1 : forall (i1 c : Z),
i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
evt segs (fun ms' => exists a2'' a3'' a4'',
ms' = MS (mkR (Z_to_bv 64 (base + 0x3e0)) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2'' a3'' a4'' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (RDEBRUIJN + 32)) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 base) fc None m (seg_rom segs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (120 - i)) (wz n') (Z_to_bv 64 c) (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 q) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (RDEBRUIJN + 32)) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x3b8)) fc None m (seg_rom segs))).
{ intros i1 c Hi1 Hc.
assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
{ subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
destruct I1R as [I1R I1E].
pose proof (size_class_range i1 ltac:(lia)) as SR2.

step. rewrite ?(unsigned_lit c), ?(unsigned_lit (120 - i)) by lia. replace (c + - (120 - i)) with i1 by lia.
step. rewrite (unsigned_lit i1), (Z.shiftl_mul_pow2 i1) by lia. change (2 ^ 1) with 2.
step. replace ((RDEBRUIJN + 32) + i1 * 2) with ((RDEBRUIJN + 32) + 2 * i1) by lia.
pose proof (rsize_classes_read m i1 MI ltac:(lia)) as RS2. gw_expose_fam RDEBRUIJN.
step. rewrite ?zx16_wz by lia. clear RS2.

step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
step. step.
destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
* rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
apply CALL. rewrite STQ. cbv zeta. rewrite <- Hi1.
replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
* rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
apply CALL. rewrite STQ. cbv zeta. rewrite <- Hi1.
replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K3 by lia.
+
step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
+
step. step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.
End STC.

#[using="rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE ralloc_meta_entry ralloc_slot_entry rmmap_entry"] Lemma rnest_ret_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (idx : Z),
-1 <= idx < 32 -> mem_inv segs m ->
evt segs (fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (if idx =? -1 then (base + 0x458) else (base + 0x3e4))) fc None m (seg_rom segs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x3e0)) fc None m (seg_rom segs)).
Proof. clear - rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE ralloc_meta_entry ralloc_slot_entry rmmap_entry segs base.
intros until idx. intros IR MI.
step. if_cases K; zify_cond K.
- replace (idx =? -1) with true.
2:{ symmetry. apply Z.eqb_eq. destruct (Z.eq_dec idx (-1)) as [E|NE]; [gw_exact E|]. exfalso.
change 18446744073709551615 with (Z.ones 64) in K. rewrite Z.land_ones, Z.mod_small in K by lia. lia. }
apply evt_done. reflexivity.
- replace (idx =? -1) with false.
2:{ symmetry. apply Z.eqb_neq. intros ->. rewrite Z.land_m1_l in K. cbn in K. lia. }
apply evt_done. reflexivity.
Qed.

End RC__1.

End G.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6y7 QTyG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w Q6y7.Mq0 QTyG.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QCa8.Mq4.
Import QDXD.Mq2.
Import QkTt.Mq3.
Import QkTt.Mq4.
Import QDXD.Mq1.
Import Qy8Z.Mqa.
Import QkTt.Mq5.
Import QCa8.Mq3.
Import Qy8Z.Mq1.
Import QQRC.Mq4.
Import QQRC.Mqc.
Import Qy8Z.Mq9.
Import QROt.Mq3.
Import QZxv.Mqo.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rvm_wait_entry : Z).
Variables (w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 : Z).
Variables (hi_14 hi_18 hi_114 hi_121 hi_130 hi_136 hi_148 hi_218 hi_311 : bv 20).
Variables (lo_15 lo_19 lo_116 lo_122 lo_131 lo_137 lo_149 lo_220 lo_313 : bv 12).
Variables (joff_427 joff_552 : bv 21).
Variables (e_197bc : Z).
Hypothesis CODE : code_at segs base (alloc_slot_code w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 2212.
Let rmmap_entry := (rvm_wait_entry + 4)%Z.
Hypothesis D_14 : decode_any (Z_to_bv 32 w_14) = Some (Auipc 10 hi_14, 4%Z).
Hypothesis E_14 : is_ecall (Z_to_bv 32 w_14) = false.
Hypothesis D_15 : decode_any (Z_to_bv 32 w_15) = Some (Load SZ8 true 20 10 lo_15, 4%Z).
Hypothesis E_15 : is_ecall (Z_to_bv 32 w_15) = false.
Hypothesis D_18 : decode_any (Z_to_bv 32 w_18) = Some (Auipc 11 hi_18, 4%Z).
Hypothesis E_18 : is_ecall (Z_to_bv 32 w_18) = false.
Hypothesis D_19 : decode_any (Z_to_bv 32 w_19) = Some (OpImm ALU_ADD 22 11 lo_19, 4%Z).
Hypothesis E_19 : is_ecall (Z_to_bv 32 w_19) = false.
Hypothesis D_114 : decode_any (Z_to_bv 32 w_114) = Some (Auipc 11 hi_114, 4%Z).
Hypothesis E_114 : is_ecall (Z_to_bv 32 w_114) = false.
Hypothesis D_116 : decode_any (Z_to_bv 32 w_116) = Some (OpImm ALU_ADD 11 11 lo_116, 4%Z).
Hypothesis E_116 : is_ecall (Z_to_bv 32 w_116) = false.
Hypothesis D_121 : decode_any (Z_to_bv 32 w_121) = Some (Auipc 10 hi_121, 4%Z).
Hypothesis E_121 : is_ecall (Z_to_bv 32 w_121) = false.
Hypothesis D_122 : decode_any (Z_to_bv 32 w_122) = Some (OpImm ALU_ADD 25 10 lo_122, 4%Z).
Hypothesis E_122 : is_ecall (Z_to_bv 32 w_122) = false.
Hypothesis D_130 : decode_any (Z_to_bv 32 w_130) = Some (Auipc 11 hi_130, 4%Z).
Hypothesis E_130 : is_ecall (Z_to_bv 32 w_130) = false.
Hypothesis D_131 : decode_any (Z_to_bv 32 w_131) = Some (Load SZ8 true 11 11 lo_131, 4%Z).
Hypothesis E_131 : is_ecall (Z_to_bv 32 w_131) = false.
Hypothesis D_136 : decode_any (Z_to_bv 32 w_136) = Some (Auipc 13 hi_136, 4%Z).
Hypothesis E_136 : is_ecall (Z_to_bv 32 w_136) = false.
Hypothesis D_137 : decode_any (Z_to_bv 32 w_137) = Some (OpImm ALU_ADD 13 13 lo_137, 4%Z).
Hypothesis E_137 : is_ecall (Z_to_bv 32 w_137) = false.
Hypothesis D_148 : decode_any (Z_to_bv 32 w_148) = Some (Auipc 13 hi_148, 4%Z).
Hypothesis E_148 : is_ecall (Z_to_bv 32 w_148) = false.
Hypothesis D_149 : decode_any (Z_to_bv 32 w_149) = Some (OpImm ALU_ADD 13 13 lo_149, 4%Z).
Hypothesis E_149 : is_ecall (Z_to_bv 32 w_149) = false.
Hypothesis D_218 : decode_any (Z_to_bv 32 w_218) = Some (Auipc 13 hi_218, 4%Z).
Hypothesis E_218 : is_ecall (Z_to_bv 32 w_218) = false.
Hypothesis D_220 : decode_any (Z_to_bv 32 w_220) = Some (OpImm ALU_ADD 13 13 lo_220, 4%Z).
Hypothesis E_220 : is_ecall (Z_to_bv 32 w_220) = false.
Hypothesis D_311 : decode_any (Z_to_bv 32 w_311) = Some (Auipc 14 hi_311, 4%Z).
Hypothesis E_311 : is_ecall (Z_to_bv 32 w_311) = false.
Hypothesis D_313 : decode_any (Z_to_bv 32 w_313) = Some (OpImm ALU_ADD 14 14 lo_313, 4%Z).
Hypothesis E_313 : is_ecall (Z_to_bv 32 w_313) = false.
Hypothesis D_427 : decode_any (Z_to_bv 32 w_427) = Some (Jal 1 joff_427, 4%Z).
Hypothesis E_427 : is_ecall (Z_to_bv 32 w_427) = false.
Hypothesis D_552 : decode_any (Z_to_bv 32 w_552) = Some (Jal 1 joff_552, 4%Z).
Hypothesis E_552 : is_ecall (Z_to_bv 32 w_552) = false.
Hypothesis ANCH_15 : gw_anch (Z.shiftl (bv_signed hi_14) 12 + (base + 56) + bv_signed lo_15)%Z RGOT_SSP.
Hypothesis ANCH_19 : gw_anch (Z.shiftl (bv_signed hi_18) 12 + (base + 72) + bv_signed lo_19)%Z (RATP + 131960).
Hypothesis ANCH_116 : gw_anch (Z.shiftl (bv_signed hi_114) 12 + (base + 456) + bv_signed lo_116)%Z RDEBRUIJN.
Hypothesis ANCH_122 : gw_anch (Z.shiftl (bv_signed hi_121) 12 + (base + 484) + bv_signed lo_122)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_131 : gw_anch (Z.shiftl (bv_signed hi_130) 12 + (base + 520) + bv_signed lo_131)%Z (RATP + 131776).
Hypothesis ANCH_137 : gw_anch (Z.shiftl (bv_signed hi_136) 12 + (base + 544) + bv_signed lo_137)%Z (RDEBRUIJN + 128).
Hypothesis ANCH_149 : gw_anch (Z.shiftl (bv_signed hi_148) 12 + (base + 592) + bv_signed lo_149)%Z (RDEBRUIJN + 155).
Hypothesis ANCH_220 : gw_anch (Z.shiftl (bv_signed hi_218) 12 + (base + 872) + bv_signed lo_220)%Z RDEBRUIJN.
Hypothesis ANCH_313 : gw_anch (Z.shiftl (bv_signed hi_311) 12 + (base + 1244) + bv_signed lo_313)%Z (RDEBRUIJN + 32).
Hypothesis LINK_427 : gw_anch (base + 1708 + bv_signed joff_427)%Z (rmmap_entry + 0)%Z.
Hypothesis LINK_552 : gw_anch (base + 2208 + bv_signed joff_552)%Z (e_197bc + 0)%Z.
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
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition ren3_post : ltac:(gw_rebind_ty (@QCa8.Mq3.ren3_post segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QCa8.Mq3.ren3_post segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QCa8.Mq3.ren3_post segs) (@ren3_post) gw_tbl_0).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QZxv.Mqo.rarea_rep segs) (@rarea_rep) (gw_ent (@QROt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mqc.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_1))))))))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QZxv.Mqo.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QROt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mqc.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_2))))))))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QZxv.Mqo.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QROt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mqc.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_3))))))))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QZxv.Mqo.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QROt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mqc.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_4))))))))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QZxv.Mqo.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QROt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mqc.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_5))))))))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QZxv.Mqo.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QROt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mqc.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_6))))))))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QZxv.Mqo.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QROt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mqc.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_7))))))))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QZxv.Mqo.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QROt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mqc.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_8))))))))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QZxv.Mqo.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QROt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mqc.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_9))))))))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QZxv.Mqo.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QROt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mqc.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_10))))))))))))))).

Hypothesis renframe_walk : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QCa8.Mq3.gw_all) (@QCa8.Mq3.renframe_walk) (base + 2212)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_11))) in let T := gw_fold_pcs T base (2212)%Z [0; 36; 64; 124; 184; 220]%Z in exact T).

Definition rmrep_shadow_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_shadow_read) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_shadow_read)).
Definition rsize_classes_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rsize_classes_read) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rsize_classes_read)).
Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).
Definition rmrep_wr8 : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_wr8) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_wr8)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmrep_active_read : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_active_read) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_active_read)).
Definition rmeta_slot_bounds : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmeta_slot_bounds) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmeta_slot_bounds)).

Definition renframe_mrep : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.renframe_mrep) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.renframe_mrep)).
Definition rmeta_chunk_facts : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rmeta_chunk_facts) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rmeta_chunk_facts)).
Definition rregion_facts : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rregion_facts) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rregion_facts)).
Definition rslot_facts : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rslot_facts) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rslot_facts)).

Ltac rraw_store_finish0 A bs' MU WM SOK :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); (gw_expose_fam RATP; unfold wa); f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
apply (munch_write _ _ mX A bs') in MU; [| gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; cbn [inside]; lia];
apply (wmono_write segs _ mX (wa A) bs') in WM;
lazymatch goal with HI : mem_inv segs mX |- _ =>
apply (mem_inv_store segs mX (wa A) bs') in HI;
[| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by ((gw_expose_fam RATP; unfold wa); f_equal; lia); exact SOK ] ]
end;
clear L SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
end.
Ltac rmchunk MR MSq CH :=
pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
rewrite ?get_meta_rec_put_same in CH;
rewrite ?conc_put_meta, ?pw_put_meta in CH;
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen
m_set_prev m_set_next m_set_mem m_set_avail m_set_freed] in CH;
unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.

Ltac rmeta_open cq MUq WMq :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(cq, cq + 40)]%Z mX) as MUq;
pose proof (wmono_refl segs mX) as WMq end.
#[using="RDEBRUIJN RGOT_SSP e_197bc rvm_wait_entry rmmap_entry RATP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 D_114 E_114 D_116 E_116 D_121 E_121 D_122 E_122 D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 D_218 E_218 D_220 E_220 D_311 E_311 D_313 E_313 D_427 E_427 D_552 E_552 ANCH_15 ANCH_19 ANCH_116 ANCH_122 ANCH_131 ANCH_137 ANCH_149 ANCH_220 ANCH_313 LINK_427 LINK_552 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rmmap_entry renframe_walk"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := first [clear - hs segs base w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_14 hi_18 hi_114 hi_121 hi_130 hi_136 hi_148 hi_218 hi_311 lo_15 lo_19 lo_116 lo_122 lo_131 lo_137 lo_149 lo_220 lo_313 joff_427 joff_552 RDEBRUIJN RGOT_SSP e_197bc rvm_wait_entry rmmap_entry RATP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 D_114 E_114 D_116 E_116 D_121 E_121 D_122 E_122 D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 D_218 E_218 D_220 E_220 D_311 E_311 D_313 E_313 D_427 E_427 D_552 E_552 ANCH_15 ANCH_19 ANCH_116 ANCH_122 ANCH_131 ANCH_137 ANCH_149 ANCH_220 ANCH_313 LINK_427 LINK_552 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ renframe_walk | clear - hs segs base w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_14 hi_18 hi_114 hi_121 hi_130 hi_136 hi_148 hi_218 hi_311 lo_15 lo_19 lo_116 lo_122 lo_131 lo_137 lo_149 lo_220 lo_313 joff_427 joff_552 RDEBRUIJN RGOT_SSP e_197bc rvm_wait_entry rmmap_entry RATP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 D_114 E_114 D_116 E_116 D_121 E_121 D_122 E_122 D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 D_218 E_218 D_220 E_220 D_311 E_311 D_313 E_313 D_427 E_427 D_552 E_552 ANCH_15 ANCH_19 ANCH_116 ANCH_122 ANCH_131 ANCH_137 ANCH_149 ANCH_220 ANCH_313 LINK_427 LINK_552 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay renframe_walk].

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

Section ENF.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx j : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P := B + 16 + stride * idx.
Let N := UNIT * size_class j - IB.
Hypothesis MR : rmrep st m1.
Hypothesis UA : unk_agree st o m1.
Hypothesis J : 0 <= j < 48.
Hypothesis HA : active st j = Some g.
Hypothesis MSL : meta_slot st g.
Hypothesis MW : mw_ok mr.
Hypothesis SCg : m_sizeclass mr = j.
Hypothesis STR : stride = UNIT * size_class j.
Hypothesis SO : slot_ok st g b r idx N.
Hypothesis TK : ticks_ok st.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE BASE4 BASER LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved ref_wview_overlay ref_seg_rom_none ref_mrd_overlay renframe_walk rmmap_entry o r N MR UA J HA MSL MW SCg STR SO TK"] Lemma rnenf_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word) F fc,
0 <= c_mmap_counter (ctx st) < 2^32 -> mem_inv segs m1 ->
evt segs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
ms' = MS (mkR (Z_to_bv 64 (base + 0x410)) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 P) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 ((RDEBRUIJN + 32) + j * 2)) s3 s4 s5 (Z_to_bv 64 (RATP + 131960)) s7 s8 (Z_to_bv 64 (RDEBRUIJN + 32)) s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 (base + 0x410)) fc None m' (seg_rom segs)
/\ munch [(P - 3, P)]%Z m1 m' /\ wmono segs m1 m' /\ mem_inv segs m'
/\ rmrep (enf0_st st g b idx) m' /\ ticks_ok (enf0_st st g b idx))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 j) s3 s4 s5 (Z_to_bv 64 (RATP + 131960)) s7 s8 (Z_to_bv 64 (RDEBRUIJN + 32)) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x3e4)) fc None m1 (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE BASE4 BASER LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved ref_wview_overlay ref_seg_rom_none ref_mrd_overlay renframe_walk rmmap_entry o r N MR UA J HA MSL MW SCg STR SO TK segs base RATP RDEBRUIJN st m1 g b idx j mr stride B P. gw_expose_fam RATP; gw_expose_fam RDEBRUIJN. try gw_hide P; try gw_hide B; try gw_hide stride; try gw_hide mr; try gw_hide j; try gw_hide idx; try gw_hide b; try gw_hide g; try gw_hide m1; try gw_hide st.
intros until fc. intros CTR MI.
pose proof (enf_facts st g b r idx j SO) as (Hmem & Hr & Hk & B0 & B16 & IDX & LI32 & SPAN & S16 & SMOD & NOGRP & HDR0 & Q16).
fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
pose proof (size_class_range j J) as SZR.
assert (STN : stride = N + 4) by (rewrite STR; unfold N, UNIT, IB; lia).
assert (NR : 12 <= N < 2^18) by (unfold N, UNIT, IB; lia).
assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
{ eapply Z.le_trans; [|gw_exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
destruct (rslot_facts st m1 o g b r idx MR UA Hr Hk B0 ltac:(lia) SPAN1 S16 B16 SMOD HDR0)
as (x3 & x2 & x1 & WRs & Y & E3 & E2 & E1 & CB & R4 & PEND & RC & RI1).
fold mr in WRs, Y, E3, E2, E1, PEND. fold stride in WRs, Y, E3, E2, E1, PEND. fold B in CB, Y, WRs, PEND.
pose proof (rmeta_chunk_facts st m1 g MR MSL) as (MM & G0 & GC & GI1 & GI2 & GDJ & GRG).
unfold alloc_ceiling in RC, GC.
set (G := conc st g) in *.
pose proof (GDJ (fst b) r Hr Hk) as GR.
change (get_meta_rec st g) with mr in MM. unfold meta_cells in MM. rewrite Hmem in MM.
unfold pw at 3 in MM. cbn [oconc] in MM. unfold meta_word in MM. fold B in MM.
pose proof (byte_range x3) as X3. pose proof (byte_range x2) as X2. pose proof (byte_range x1) as X1.
assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
pose proof (bytes_at_read segs m1 _ _ 0 1 Y ltac:(lia) ltac:(cbn; lia)) as RD4. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD4.
pose proof (bytes_at_read segs m1 _ _ 1 1 Y ltac:(lia) ltac:(cbn; lia)) as RD3. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD3.
pose proof (bytes_at_read segs m1 _ _ 2 2 Y ltac:(lia) ltac:(cbn; lia)) as RD2. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD2.
rewrite Z.add_0_r in RD4.
replace (B + 16 + stride * idx - 4 + 1) with (B + 16 + stride * idx - 3) in RD3 by lia.
replace (B + 16 + stride * idx - 4 + 2) with (B + 16 + stride * idx - 2) in RD2 by lia.
rewrite <- (le2_lohi (bv_unsigned x2) (bv_unsigned x1)) in RD2 by lia.
pose proof MW as (LI0 & FB0 & SCR0 & ML0).
pose proof MR as (WF' & CX & GL & _). destruct CX as (CH & _). unfold ctx_head_cells in CH.
(gw_expose_fam RDEBRUIJN; gw_expose_fam RATP).

step. step. rewrite ?(unsigned_lit j), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
step. rewrite ?(unsigned_lit j), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
step. step.

pose proof (rsize_classes_read m1 j MI J) as SCRD. gw_expose_fam RDEBRUIJN.
replace ((RDEBRUIJN + 32) + 2 * j) with ((RDEBRUIJN + 32) + j * 2) in SCRD by lia.
step. rewrite zx16_wz by lia. clear SCRD.

pose proof (rmrep_active_read st m1 j (wa ((RATP + 132048) + 8 * j)) MR J eq_refl) as RDA. rewrite HA in RDA. unfold pw in RDA. cbn [oconc] in RDA. unfold wz in RDA. fold G in RDA.
replace (wa ((RATP + 132048) + 8 * j)) with (Z_to_bv 64 ((RATP + 131960) + j * 8 + 88)) in RDA by (unfold wa; f_equal; lia).
step. clear RDA.

step. rewrite sx32_wz_sxv by lia.

step. rewrite (wz_unsigned (size_class j)), (Z.shiftl_mul_pow2 (size_class j)) by lia. change (2 ^ 4) with 16.
step.

step.
eapply evt_mono.
{ eapply (renframe_walk (Z_to_bv 64 (base + 0x410)) sp gp tp _ _ _ s0 s1 _ _ _ _ _ s3 s4 s5 _ s7 s8 _ s10 s11 _ _ _ _ (Z_to_bv 64 G) _
(pw st (m_prev mr)) (pw st (m_next mr)) F fc m1 B stride N idx (c_mmap_counter (ctx st)) (m_avail mr) (m_freed mr)
(m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (bv_unsigned x3) (bv_unsigned x2 + 256 * bv_unsigned x1)).
all: lazymatch goal with
| |- rw_cells _ _ (bv_unsigned _) _ => rewrite (unsigned_lit G) by lia; gw_exact MM
| |- mem_inv _ _ => gw_exact MI
| |- wr_at _ _ _ _ => gw_exact WRs
| |- ov_read_bytes _ _ _ 2 = _ => gw_exact RD2
| |- ov_read_bytes _ _ _ _ = Some [b8 0] => gw_exact RD4
| |- ov_read_bytes _ _ _ _ = _ => gw_exact RD3
| |- bv_unsigned (Z_to_bv 64 _) = _ => rewrite unsigned_lit by lia; unfold N, UNIT, IB; lia
| |- _ => idtac end.
all: try (rewrite (unsigned_lit G) by lia).
all: try lia.
- subst stride. unfold get_stride, UNIT. reflexivity.
- intros off' O1 O2. pose proof (Q16 off' O1 O2). lia.
- exact (so_maplen _ _ _ _ _ _ SO). }

intros ms' PO. cbv beta in PO. unfold ren3_post in PO.
destruct PO as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & -> & EM & MI').
set (off0 := if bv_unsigned x3 =? 0 then Z.land (c_mmap_counter (ctx st)) 255 else Z.land (bv_unsigned x2 + 256 * bv_unsigned x1 + 1) 255) in EM |- *.
assert (OFF0 : 0 <= off0 < 256).
{ subst off0. destruct (bv_unsigned x3 =? 0).
- split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
- split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
replace ((stride - 4 - N) / 16) with 0 in EM |- * by (rewrite STN; replace (N + 4 - 4 - N) with 0 by lia; reflexivity).
pose proof (fold_off_le_slack off0 0 OFF0 ltac:(lia)) as OFF.
replace (fold_off off0 0) with 0 in EM |- * by lia.
rewrite Z.mul_0_r, Z.add_0_r in EM |- *.
try g_ret_pc_any.

assert (S31n : stride - 4 - N < 2^31) by lia.
assert (SPAN2 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)) by (rewrite Z.mul_add_distr_l, Z.mul_1_r; gw_exact SPAN1).
assert (T1 : 0 <= idx < 32) by lia. assert (T3 : 16 * 0 + N + 4 <= stride) by lia. assert (T0 : 0 <= 0) by lia. assert (TN : 0 <= N) by lia.
assert (T4 : (stride * idx + 16 * 0) / 16 < 65536) by (apply (Q16 0); lia).
destruct (renframe_mrep st m1 g b r idx N 0 MR TK Hmem Hr Hk B0 T1 SPAN2 S16 S31n NOGRP T0 TN T3 T4)
as (MRr & TKr & CONCr & FSTr & SNDr). clear T1 T3 T0 TN T4.
rewrite Z.mul_0_r, Z.add_0_r in MRr.
change (conc st b) with B in MRr. change (get_stride (get_meta_rec st g)) with stride in MRr.
fold P in MRr, EM. rewrite <- EM in MRr.
destruct (enf0_st_eq st g b r idx j STR SO) as [E1st _]. fold N in E1st. rewrite E1st in MRr, TKr.

assert (EM' : m' = write_to_mem (write_to_mem (write_to_mem m1 (wa (P - 3)) [b8 idx]) (wa (P - 2)) (le2 (wz ((P - B - 16) / 16)))) (wa (P - 3)) [b8 (Z.land idx 31 + Z.shiftl 0 5)]).
{ rewrite EM. unfold renframe_tail_mem, renframe_off_mem. cbn [Z.eqb].
replace (P + stride - 4 - P - N) with 0 by lia. cbn [Z.eqb Z.leb]. reflexivity. }
assert (MU : munch [(P - 3, P)]%Z m1 m').
{ rewrite EM'. apply munch_write; [| lia| cbn; lia| cbn; lia].
apply munch_write; [| lia| cbn; lia| cbn; lia].
apply munch_write; [apply munch_refl| lia| cbn; lia| cbn; lia]. }
assert (WM : wmono segs m1 m').
{ rewrite EM'. apply wmono_write. apply wmono_write. apply wmono_write. apply wmono_refl. }
do 14 eexists. exists m'.
split; [unfold P, G; reflexivity|].
split; [gw_exact MU|]. split; [gw_exact WM|]. split; [gw_exact MI'|]. split; [gw_exact MRr| gw_exact TKr].
Qed.
#[using="rvm_wait_entry rmmap_entry st g b idx j mr stride B P N"] Lemma lor_192 a : 0 <= a < 32 -> Z.lor a 192 = a + 192.
Proof. clear - rvm_wait_entry rmmap_entry st g b idx j mr stride B P N a m1 o r MR UA J HA MSL MW SCg STR SO TK. first [clear TK | gw_hide TK | idtac]; first [clear SO | gw_hide SO | idtac]; first [clear STR | gw_hide STR | idtac]; first [clear SCg | gw_hide SCg | idtac]; first [clear MW | gw_hide MW | idtac]; first [clear MSL | gw_hide MSL | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear J | gw_hide J | idtac]; first [clear UA | gw_hide UA | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear r | gw_hide r | idtac]; first [clear o | gw_hide o | idtac]; first [clear m1 | gw_hide m1 | idtac]. intros Ha. change 192 with (3 * 2 ^ 6). rewrite (lor_small_shl 3 6 a) by lia. lia. Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmmap_entry m1 r j N MR J SO TK"] Lemma renfD_walk :
forall (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (mt : aptr) (cnt : Z) mC,
meta_slot st mt -> mw_ok (get_meta_rec st mt) -> 1 <= cnt <= 32 ->
rmrep (enf0_st st g b idx) mC -> ticks_ok (enf0_st st g b idx) -> mem_inv segs mC ->
evt segs (fun ms' => exists m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st mt)) (Z_to_bv 64 P) (Z_to_bv 64 (cnt + 1)) (Z_to_bv 64 (P + 12)) a3 a4 a5 a6 a7
s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x438)) fc None m' (seg_rom segs)
/\ munch [(conc st mt, conc st mt + 40); (P - 3, P - 2)]%Z mC m' /\ wmono segs mC m' /\ mem_inv segs m'
/\ rmrep (wr8 (fst b, snd b + (16 + stride * idx) + -3) (Z.lor (Z.land idx 31) 192)
(put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) (enf0_st st g b idx))) m'
/\ ticks_ok (wr8 (fst b, snd b + (16 + stride * idx) + -3) (Z.lor (Z.land idx 31) 192)
(put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) (enf0_st st g b idx))))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st mt)) (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x410)) fc None mC (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmmap_entry m1 r j N MR J SO TK segs base st o g b idx mr stride B P UA HA MSL MW SCg STR. first [clear STR | gw_hide STR | idtac]; first [clear SCg | gw_hide SCg | idtac]; first [clear MW | gw_hide MW | idtac]; first [clear MSL | gw_hide MSL | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear UA | gw_hide UA | idtac]; try gw_hide P; try gw_hide B; try gw_hide stride; try gw_hide mr; try gw_hide idx; try gw_hide b; try gw_hide g; first [clear o | gw_hide o | idtac]; try gw_hide st.
intros until mC. intros MST MWT CR MRC TKC MIC.
pose proof (enf_facts st g b r idx j SO) as (Hmem & Hr & Hk & B0 & B16 & IDX & LI32 & SPAN & S16 & SMOD & NOGRP & HDR0 & Q16).
fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
{ eapply Z.le_trans; [|gw_exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
pose proof (rregion_facts st m1 (fst b) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). unfold alloc_ceiling in RC.
assert (CB : B = r_base r + snd b) by (unfold B; apply conc_region'; gw_exact Hr).
set (st0' := enf0_st st g b idx) in *.
assert (MST0 : meta_slot st0' mt) by (eapply meta_slot_same_areas; [| gw_exact MST]; reflexivity).
pose proof (rmeta_slot_bounds st0' mC mt MRC MST0) as (Tpos & TC & TI & _ & _).
change (conc st0' mt) with (conc st mt) in Tpos, TC, TI.
pose proof (rmeta_chunk_facts st0' mC mt MRC MST0) as (_ & _ & _ & _ & _ & GDJ & _).
assert (RG0 : s_regions st0' = s_regions st) by (unfold st0', enf0_st, wr16; rewrite !s_regions_wr8; reflexivity).
assert (GR0 : s_groups st0' = s_groups st) by (unfold st0', enf0_st, wr16; rewrite !s_groups_wr8; reflexivity).
rewrite RG0 in GDJ. pose proof (GDJ (fst b) r Hr Hk) as TDJ. change (conc st0' mt) with (conc st mt) in TDJ.
pose proof (munch_refl [(conc st mt, conc st mt + 40); (P - 3, P - 2)]%Z mC) as MU. pose proof (wmono_refl segs mC) as WM.
pose proof MWT as (LI0 & FB0 & SCR0 & ML0). pose proof (meta_word_range _ MWT) as MWR.
unfold alloc_ceiling in TC.

rmchunk MRC MST0 CH. change (conc st0' mt) with (conc st mt) in CH. change (get_meta_rec st0' mt) with (get_meta_rec st mt) in CH.
rmeta_open (conc st mt) MUt WMt.
step.

step. step. rewrite ?(unsigned_lit (meta_word (get_meta_rec st mt))) by lia.
set (w := meta_word (get_meta_rec st mt)) in *.
rewrite (Z_to_bv_unsigned 64 (Z.shiftl w 52)). unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
rewrite (zb_shl_shr w 52) by lia. change (2 ^ (64 - 52)) with 4096.
rewrite (meta_word_mod4096 st g b idx j _ MWT).
step.
lazymatch goal with H : rw_cells segs ?mX (conc st mt) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR5 : rmrep (put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) st0') mX);
[ eapply rmrep_put_meta_frame; [gw_exact MRC| gw_exact MST0| gw_exact MUt| gw_exact WMt|];
eapply rw_cells_congr; [| | | gw_exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_maplen oconc]; reflexivity
| clear MUt WMt H ] end.
set (st5 := put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) st0') in *.
assert (TK5 : ticks_ok st5) by (exact (ticks_ok_upd_meta st0' mt (fun _ => m_set_maplen 0 (get_meta_rec st mt)) TKC)).

pose proof (land31_range idx) as L31.
assert (K3 : cell_read (get_shadow st5 (fst b)) (snd b + (16 + stride * idx) + -3) = Known (Z.land idx 31)).
{ change (get_shadow st5 (fst b)) with (get_shadow st0' (fst b)). unfold st0', enf0_st.
rewrite (cell_read_wr8_same (wr8 _ _ (wr16 _ _ st)) (fst b, snd b + (16 + stride * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5));
[| apply ticks_ok_wr8, ticks_ok_wr16; gw_exact TK | change (Z.shiftl 0 5) with 0; lia].
change (Z.shiftl 0 5) with 0. rewrite Z.add_0_r. reflexivity. }
destruct (rmrep_shadow_read st5 _ (fst b) r (snd b + (16 + stride * idx) + -3) (Z.land idx 31) MR5 Hr Hk ltac:(lia) K3) as [RDK _].
replace (wa (r_base r + (snd b + (16 + stride * idx) + -3))) with (Z_to_bv 64 (P + -3)) in RDK
by (unfold wa; f_equal; unfold P; lia).
step. rewrite zxb_b8 by lia. clear RDK. rewrite ?(unsigned_lit P) by (unfold P; lia).

step. rewrite (unsigned_lit cnt), swrap32_small by lia.
step. rewrite (wz_unsigned (Z.land idx 31)) by lia. rewrite <- (Z.land_assoc idx 31 31). change (Z.land 31 31) with 31.
step. rewrite ?(unsigned_lit (Z.land idx 31)) by lia.

pose proof MR5 as (_ & _ & _ & _ & _ & SH5). destruct (SH5 (fst b) r Hr Hk) as [WR5 _]. clear SH5.
pose proof (wr_at_store_ok segs _ _ _ (snd b + (16 + stride * idx) + -3) 1 WR5 ltac:(lia) ltac:(lia)) as SOK.
replace (wa (r_base r + (snd b + (16 + stride * idx) + -3))) with (Z_to_bv 64 (P + -3)) in SOK
by (unfold wa; f_equal; unfold P; lia).
st1.
assert (RG5 : s_regions st5 = s_regions st) by (unfold st5; gw_exact RG0).
assert (GR5 : s_groups st5 = s_groups st) by (unfold st5; gw_exact GR0).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_wr8 st5 mX (fst b, snd b + (16 + stride * idx) + -3) (Z.lor (Z.land idx 31) 192) r MR5 TK5) as MR6 end.
cbn [fst snd] in MR6. rewrite RG5, GR5 in MR6.
assert (LOR : 0 <= Z.lor (Z.land idx 31) 192 < 256) by (rewrite lor_192 by lia; lia).
specialize (MR6 Hr Hk ltac:(lia) ltac:(intros b' gh' Hb' Hf'; destruct (NOGRP b' gh' Hb' Hf'); lia) ltac:(lia)).
replace (r_base r + (snd b + (16 + stride * idx) + -3)) with (P - 3) in MR6 by (unfold P; lia).
rewrite <- (lor_192 (Z.land idx 31)) by lia.
rraw_store_finish0 (P - 3) [b8 (Z.lor (Z.land idx 31) 192)] MU WM SOK.

step. rewrite ?(unsigned_lit P) by (unfold P; lia).
apply evt_done. eexists. split; [reflexivity|].
split; [gw_exact MU|]. split; [gw_exact WM|]. split; [assumption|].
split; [gw_exact MR6| apply ticks_ok_wr8; gw_exact TK5].
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmmap_entry m1 r j N MR STR SO"] Lemma rzero_loop_walk : forall k (i szc cnt : Z) stz mC0 mC
(ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
Z.of_nat k = cnt + 1 - i -> 0 <= i <= cnt -> 1 <= szc -> 0 <= cnt < 4096 -> 16 + 16 * szc * cnt <= stride ->
s_regions stz = s_regions st -> s_groups stz = s_groups st ->
rmrep stz mC -> ticks_ok stz -> mem_inv segs mC ->
munch [(P + 12, P + 12 + 16 * szc * cnt + 1)]%Z mC0 mC -> wmono segs mC0 mC ->
evt segs (fun ms' => exists m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 (cnt - 1)) a3 a4 a5 a6 a7
s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 (Z_to_bv 64 (16 * szc)) (Z_to_bv 64 cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x708)) fc None m' (seg_rom segs)
/\ munch [(P + 12, P + 12 + 16 * szc * cnt + 1)]%Z mC0 m' /\ wmono segs mC0 m' /\ mem_inv segs m'
/\ rmrep (zero_hdrs (pp st g b idx) (16 * szc) i k stz) m' /\ ticks_ok (zero_hdrs (pp st g b idx) (16 * szc) i k stz)
/\ s_regions (zero_hdrs (pp st g b idx) (16 * szc) i k stz) = s_regions st /\ s_groups (zero_hdrs (pp st g b idx) (16 * szc) i k stz) = s_groups st
/\ (forall x, (forall j, i <= j <= cnt -> bv_unsigned x <> P + 12 + 16 * szc * j) -> m' x = mC x))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (cnt + 1 - i)) (Z_to_bv 64 (P + 12 + 16 * szc * i)) a3 a4 a5 a6 a7
s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 (Z_to_bv 64 (16 * szc)) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x438)) fc None mC (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmmap_entry m1 r j N MR STR SO segs base st o g b idx mr stride B P UA J HA MSL MW SCg TK. first [clear TK | gw_hide TK | idtac]; first [clear SCg | gw_hide SCg | idtac]; first [clear MW | gw_hide MW | idtac]; first [clear MSL | gw_hide MSL | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear J | gw_hide J | idtac]; first [clear UA | gw_hide UA | idtac]; try gw_hide P; try gw_hide B; try gw_hide stride; try gw_hide mr; try gw_hide idx; try gw_hide b; try gw_hide g; first [clear o | gw_hide o | idtac]; try gw_hide st.
induction k as [|k IH]; intros until fc; intros HK HI SZC CNT FIT RGz GRz MRz TKz MIz MU WM.
{ exfalso. lia. }
pose proof (enf_facts st g b r idx j SO) as (Hmem & Hr & Hk & B0 & B16 & IDX & LI32 & SPAN & S16 & SMOD & NOGRP & HDR0 & Q16).
fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
{ eapply Z.le_trans; [|gw_exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
assert (SZI : 0 <= 16 * szc * i <= 16 * szc * cnt) by (split; [apply Z.mul_nonneg_nonneg; lia| apply Z.mul_le_mono_nonneg_l; lia]).
pose proof (rregion_facts st m1 (fst b) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). unfold alloc_ceiling in RC.
assert (CB : B = r_base r + snd b) by (unfold B; apply conc_region'; gw_exact Hr).

assert (Hr' : (s_regions stz) !! (fst b) = Some r) by (rewrite RGz; gw_exact Hr).
pose proof MRz as (WFz & _ & _ & _ & _ & SHz). destruct (SHz (fst b) r Hr' Hk) as [WRz _]. clear SHz.
pose proof (wr_at_store_ok segs _ _ _ (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4)) 1 WRz ltac:(lia) ltac:(lia)) as SOK.
replace (wa (r_base r + (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4)))) with (Z_to_bv 64 (P + 12 + 16 * szc * i)) in SOK
by (unfold wa; f_equal; unfold P; lia).
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_wr8 stz mX (aadd (pp st g b idx) (UNIT + i * (16 * szc) - 4)) 0 r MRz TKz) as MR2 end.
unfold aadd, pp, UNIT in MR2. cbn [fst snd] in MR2. fold mr in MR2. fold stride in MR2. rewrite GRz in MR2.
specialize (MR2 Hr' Hk ltac:(lia)).
assert (NOG : forall b0 gh, (s_groups st) !! b0 = Some gh -> fst b0 = fst b ->
~ snd b0 <= snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4) < snd b0 + 9).
{ intros b0 gh Hb0 Hf0 CONTRA. pose proof MR as (WF & _). pose proof WF as (_ & _ & _ & _ & GWF).
destruct (GWF b0 gh Hb0) as (r0 & _ & _ & _ & _ & M16).
destruct (NOGRP b0 gh Hb0 Hf0) as [LE|GE]; [lia|].
assert (E0 : snd b0 = 16 * (snd b0 / 16)) by (pose proof (Z.div_mod (snd b0) 16 ltac:(lia)); lia).
assert (E1 : snd b = 16 * (snd b / 16)) by (pose proof (Z.div_mod (snd b) 16 ltac:(lia)); lia).
assert (E2 : stride = 16 * (stride / 16)) by (pose proof (Z.div_mod stride 16 ltac:(lia)); lia).

pose proof STR as STRdep__.
clear - CONTRA E0 E1 E2 RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmmap_entry segs base.
replace (stride * idx) with (16 * (stride / 16) * idx) in CONTRA by (rewrite <- E2; reflexivity).
lia. }
specialize (MR2 NOG ltac:(lia)). clear NOG.
replace (r_base r + (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4))) with (P + 12 + 16 * szc * i) in MR2 by (unfold P; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0])
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa; f_equal; lia);
assert (PW0 : forall u, 0 <= u < 2^64 -> u <> P + 12 + 16 * szc * i -> write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0] (wa u) = mX (wa u));
[ intros u Hu Hux;
rewrite write_to_mem_spec by (cbn; lia); rewrite wa_unsigned by lia; cbn [length]; replace (Z.of_nat 1) with 1 by first [reflexivity | (cbn; lia)];
destruct (Z.leb_spec0 (P + 12 + 16 * szc * i) u); destruct (Z.ltb_spec0 u (P + 12 + 16 * szc * i + 1)); cbn [andb]; try reflexivity;
exfalso; lia
| apply (munch_write _ _ mX (P + 12 + 16 * szc * i) [b8 0]) in MU; [| lia | cbn [length]; replace (Z.of_nat 1) with 1 by first [reflexivity | (cbn; lia)]; lia | cbn [length inside]; replace (Z.of_nat 1) with 1 by first [reflexivity | (cbn; lia)]; lia];
apply (wmono_write segs _ mX (wa (P + 12 + 16 * szc * i)) [b8 0]) in WM;
lazymatch goal with HI : mem_inv segs mX |- _ =>
apply (mem_inv_store segs mX (wa (P + 12 + 16 * szc * i)) [b8 0]) in HI;
[| first [ gw_exact SOK | replace (wa (P + 12 + 16 * szc * i)) with a by (unfold wa; f_equal; lia); gw_exact SOK ] ]
end;
clear SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0]) as m' eqn:Em'; clear Em' ]
end.

step. rewrite ?(unsigned_lit (cnt + 1 - i)) by lia.
step. rewrite ?unsigned_lit by lia.

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
-
replace (cnt + 1 - i + -1) with (cnt + 1 - (i + 1)) by lia.
replace (P + 12 + 16 * szc * i + 16 * szc) with (P + 12 + 16 * szc * (i + 1)) by lia.
cbn [zero_hdrs]. unfold aadd, pp, UNIT. cbn [fst snd]. fold mr. fold stride.
eapply evt_mono.
{ (eapply (IH (i + 1) szc cnt);
[ lia | lia | gw_exact SZC | gw_exact CNT | gw_exact FIT
| rewrite s_regions_wr8; gw_exact RGz
| rewrite s_groups_wr8; gw_exact GRz
| gw_exact MR2
| apply ticks_ok_wr8; gw_exact TKz
| assumption | gw_exact MU | gw_exact WM ]). }
cbv beta. intros ms' (m' & -> & X1 & X2 & X3 & X4 & X5 & X6 & X7 & PW).
eexists. split; [reflexivity|]. split; [gw_exact X1|]. split; [gw_exact X2|]. split; [gw_exact X3|]. split; [gw_exact X4|]. split; [gw_exact X5|].
split; [gw_exact X6|]. split; [gw_exact X7|].
intros x Hx. rewrite (PW x) by (intros jj Hjj; apply Hx; lia).
pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2^64) in XR.
rewrite <- (Z_to_bv_bv_unsigned x). unfold wa in PW0. apply PW0; [lia|]. apply Hx. lia.
-
assert (Ei : i = cnt) by lia. destruct k; [| exfalso; lia].

step. rewrite ?(unsigned_lit cnt) by lia. replace (cnt + -1) with (cnt - 1) by lia. step. step. step.
apply evt_done. eexists. split; [reflexivity|].
cbn [zero_hdrs]. unfold aadd, pp, UNIT. cbn [fst snd]. fold mr. fold stride.
split; [gw_exact MU|]. split; [gw_exact WM|]. split; [assumption|]. split; [gw_exact MR2|]. split; [apply ticks_ok_wr8; gw_exact TKz|].
split; [rewrite s_regions_wr8; gw_exact RGz|]. split; [rewrite s_groups_wr8; gw_exact GRz|].
intros x Hx. pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2^64) in XR.
rewrite <- (Z_to_bv_bv_unsigned x). unfold wa in PW0. apply PW0; [lia|]. apply Hx. lia.
Qed.
End ENF.

End RC__1.

End G.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w Q9Ay.Mq3 QTyG.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QCa8.Mq4.
Import QDXD.Mq2.
Import QkTt.Mq3.
Import QkTt.Mq4.
Import QDXD.Mq1.
Import Qy8Z.Mqa.
Import QkTt.Mq5.
Import Qy8Z.Mq1.
Import QQRC.Mq4.
Import QQRC.Mqc.
Import Qy8Z.Mq9.
Import QROt.Mq3.
Import QZxv.Mqo.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rvm_wait_entry : Z).
Variables (w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 : Z).
Variables (hi_14 hi_18 hi_114 hi_121 hi_130 hi_136 hi_148 hi_218 hi_311 : bv 20).
Variables (lo_15 lo_19 lo_116 lo_122 lo_131 lo_137 lo_149 lo_220 lo_313 : bv 12).
Variables (joff_427 joff_552 : bv 21).
Variables (e_197bc : Z).
Hypothesis CODE : code_at segs base (alloc_slot_code w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 2212.
Let rmmap_entry := (rvm_wait_entry + 4)%Z.
Hypothesis D_14 : decode_any (Z_to_bv 32 w_14) = Some (Auipc 10 hi_14, 4%Z).
Hypothesis E_14 : is_ecall (Z_to_bv 32 w_14) = false.
Hypothesis D_15 : decode_any (Z_to_bv 32 w_15) = Some (Load SZ8 true 20 10 lo_15, 4%Z).
Hypothesis E_15 : is_ecall (Z_to_bv 32 w_15) = false.
Hypothesis D_18 : decode_any (Z_to_bv 32 w_18) = Some (Auipc 11 hi_18, 4%Z).
Hypothesis E_18 : is_ecall (Z_to_bv 32 w_18) = false.
Hypothesis D_19 : decode_any (Z_to_bv 32 w_19) = Some (OpImm ALU_ADD 22 11 lo_19, 4%Z).
Hypothesis E_19 : is_ecall (Z_to_bv 32 w_19) = false.
Hypothesis D_114 : decode_any (Z_to_bv 32 w_114) = Some (Auipc 11 hi_114, 4%Z).
Hypothesis E_114 : is_ecall (Z_to_bv 32 w_114) = false.
Hypothesis D_116 : decode_any (Z_to_bv 32 w_116) = Some (OpImm ALU_ADD 11 11 lo_116, 4%Z).
Hypothesis E_116 : is_ecall (Z_to_bv 32 w_116) = false.
Hypothesis D_121 : decode_any (Z_to_bv 32 w_121) = Some (Auipc 10 hi_121, 4%Z).
Hypothesis E_121 : is_ecall (Z_to_bv 32 w_121) = false.
Hypothesis D_122 : decode_any (Z_to_bv 32 w_122) = Some (OpImm ALU_ADD 25 10 lo_122, 4%Z).
Hypothesis E_122 : is_ecall (Z_to_bv 32 w_122) = false.
Hypothesis D_130 : decode_any (Z_to_bv 32 w_130) = Some (Auipc 11 hi_130, 4%Z).
Hypothesis E_130 : is_ecall (Z_to_bv 32 w_130) = false.
Hypothesis D_131 : decode_any (Z_to_bv 32 w_131) = Some (Load SZ8 true 11 11 lo_131, 4%Z).
Hypothesis E_131 : is_ecall (Z_to_bv 32 w_131) = false.
Hypothesis D_136 : decode_any (Z_to_bv 32 w_136) = Some (Auipc 13 hi_136, 4%Z).
Hypothesis E_136 : is_ecall (Z_to_bv 32 w_136) = false.
Hypothesis D_137 : decode_any (Z_to_bv 32 w_137) = Some (OpImm ALU_ADD 13 13 lo_137, 4%Z).
Hypothesis E_137 : is_ecall (Z_to_bv 32 w_137) = false.
Hypothesis D_148 : decode_any (Z_to_bv 32 w_148) = Some (Auipc 13 hi_148, 4%Z).
Hypothesis E_148 : is_ecall (Z_to_bv 32 w_148) = false.
Hypothesis D_149 : decode_any (Z_to_bv 32 w_149) = Some (OpImm ALU_ADD 13 13 lo_149, 4%Z).
Hypothesis E_149 : is_ecall (Z_to_bv 32 w_149) = false.
Hypothesis D_218 : decode_any (Z_to_bv 32 w_218) = Some (Auipc 13 hi_218, 4%Z).
Hypothesis E_218 : is_ecall (Z_to_bv 32 w_218) = false.
Hypothesis D_220 : decode_any (Z_to_bv 32 w_220) = Some (OpImm ALU_ADD 13 13 lo_220, 4%Z).
Hypothesis E_220 : is_ecall (Z_to_bv 32 w_220) = false.
Hypothesis D_311 : decode_any (Z_to_bv 32 w_311) = Some (Auipc 14 hi_311, 4%Z).
Hypothesis E_311 : is_ecall (Z_to_bv 32 w_311) = false.
Hypothesis D_313 : decode_any (Z_to_bv 32 w_313) = Some (OpImm ALU_ADD 14 14 lo_313, 4%Z).
Hypothesis E_313 : is_ecall (Z_to_bv 32 w_313) = false.
Hypothesis D_427 : decode_any (Z_to_bv 32 w_427) = Some (Jal 1 joff_427, 4%Z).
Hypothesis E_427 : is_ecall (Z_to_bv 32 w_427) = false.
Hypothesis D_552 : decode_any (Z_to_bv 32 w_552) = Some (Jal 1 joff_552, 4%Z).
Hypothesis E_552 : is_ecall (Z_to_bv 32 w_552) = false.
Hypothesis ANCH_15 : gw_anch (Z.shiftl (bv_signed hi_14) 12 + (base + 56) + bv_signed lo_15)%Z RGOT_SSP.
Hypothesis ANCH_19 : gw_anch (Z.shiftl (bv_signed hi_18) 12 + (base + 72) + bv_signed lo_19)%Z (RATP + 131960).
Hypothesis ANCH_116 : gw_anch (Z.shiftl (bv_signed hi_114) 12 + (base + 456) + bv_signed lo_116)%Z RDEBRUIJN.
Hypothesis ANCH_122 : gw_anch (Z.shiftl (bv_signed hi_121) 12 + (base + 484) + bv_signed lo_122)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_131 : gw_anch (Z.shiftl (bv_signed hi_130) 12 + (base + 520) + bv_signed lo_131)%Z (RATP + 131776).
Hypothesis ANCH_137 : gw_anch (Z.shiftl (bv_signed hi_136) 12 + (base + 544) + bv_signed lo_137)%Z (RDEBRUIJN + 128).
Hypothesis ANCH_149 : gw_anch (Z.shiftl (bv_signed hi_148) 12 + (base + 592) + bv_signed lo_149)%Z (RDEBRUIJN + 155).
Hypothesis ANCH_220 : gw_anch (Z.shiftl (bv_signed hi_218) 12 + (base + 872) + bv_signed lo_220)%Z RDEBRUIJN.
Hypothesis ANCH_313 : gw_anch (Z.shiftl (bv_signed hi_311) 12 + (base + 1244) + bv_signed lo_313)%Z (RDEBRUIJN + 32).
Hypothesis LINK_427 : gw_anch (base + 1708 + bv_signed joff_427)%Z (rmmap_entry + 0)%Z.
Hypothesis LINK_552 : gw_anch (base + 2208 + bv_signed joff_552)%Z (e_197bc + 0)%Z.
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
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rrepfoot : ltac:(gw_rebind_ty (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QQRC.Mqc.rrepfoot RATP RGOT_SSP) (@rrepfoot) (gw_ent (@QkTt.Mq4.rrepfoot RATP RGOT_SSP) (@rrepfoot) (gw_ent (@QkTt.Mq3.rrepfoot RATP RGOT_SSP) (@rrepfoot) (gw_ent (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) (@rrepfoot) gw_tbl_0)))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QZxv.Mqo.rarea_rep segs) (@rarea_rep) (gw_ent (@QROt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mqc.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_1))))))))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QZxv.Mqo.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QROt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mqc.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_2))))))))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QZxv.Mqo.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QROt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mqc.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_3))))))))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QZxv.Mqo.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QROt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mqc.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_4))))))))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QZxv.Mqo.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QROt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mqc.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_5))))))))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QZxv.Mqo.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QROt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mqc.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_6))))))))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QZxv.Mqo.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QROt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mqc.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_7))))))))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QZxv.Mqo.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QROt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mqc.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_8))))))))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QZxv.Mqo.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QROt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mqc.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_9))))))))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QZxv.Mqo.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QROt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mqc.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_10))))))))))))))).

Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).
Definition rarea_lr_lo : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_lr_lo) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_lr_lo)).
Definition rarea_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_conc) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_conc)).
Definition rgroup_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rgroup_conc) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rgroup_conc)).
Definition rmrep_set_active : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_set_active) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_set_active)).
Definition rmrep_hdr_havoc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_hdr_havoc) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_hdr_havoc)).
Definition rwr_at_bytes_exist : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rwr_at_bytes_exist) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rwr_at_bytes_exist)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rmrep_transport_unowned : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_transport_unowned) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_transport_unowned)).
Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmrep_usage_read : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_usage_read) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_usage_read)).
Definition rmeta_slot_bounds : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmeta_slot_bounds) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmeta_slot_bounds)).

Definition rmrep_set_usage : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq4.rmrep_set_usage) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq4.rmrep_set_usage)).

Definition rmrep_put_group_new : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mqa.rmrep_put_group_new) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mqa.rmrep_put_group_new)).

Definition rmeta_chunk_facts : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rmeta_chunk_facts) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rmeta_chunk_facts)).
Definition rregion_facts : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rregion_facts) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rregion_facts)).

Ltac rraw_store_finish0 A bs' MU WM SOK :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); (gw_expose_fam RATP; unfold wa); f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
apply (munch_write _ _ mX A bs') in MU; [| gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; cbn [inside]; lia];
apply (wmono_write segs _ mX (wa A) bs') in WM;
lazymatch goal with HI : mem_inv segs mX |- _ =>
apply (mem_inv_store segs mX (wa A) bs') in HI;
[| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by ((gw_expose_fam RATP; unfold wa); f_equal; lia); exact SOK ] ]
end;
clear L SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
end.
Ltac rmchunk MR MSq CH :=
pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
rewrite ?get_meta_rec_put_same in CH;
rewrite ?conc_put_meta, ?pw_put_meta in CH;
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen
m_set_prev m_set_next m_set_mem m_set_avail m_set_freed] in CH;
unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.

Ltac rmeta_open cq MUq WMq :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(cq, cq + 40)]%Z mX) as MUq;
pose proof (wmono_refl segs mX) as WMq end.
#[using="RDEBRUIJN RGOT_SSP e_197bc rvm_wait_entry rmmap_entry RATP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 D_114 E_114 D_116 E_116 D_121 E_121 D_122 E_122 D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 D_218 E_218 D_220 E_220 D_311 E_311 D_313 E_313 D_427 E_427 D_552 E_552 ANCH_15 ANCH_19 ANCH_116 ANCH_122 ANCH_131 ANCH_137 ANCH_149 ANCH_220 ANCH_313 LINK_427 LINK_552 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rmmap_entry"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

#[using="rvm_wait_entry rmmap_entry"] Lemma sx32_congr (a : word) (b : Z) : bv_unsigned a mod 2^32 = b mod 2^32 -> sx32 a = wz (sxv b).
Proof. clear - rvm_wait_entry rmmap_entry a b.
intros E. unfold sx32, wz, sxv. apply Z_to_bv_eqm. rewrite Z.mod_mod by lia.
f_equal. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
rewrite <- (Zplus_mod_idemp_l (bv_unsigned a)), E, Zplus_mod_idemp_l. reflexivity.
Qed.

#[using="rvm_wait_entry rmmap_entry"] Lemma unsigned_mod32_pred_sxv y : bv_unsigned (Z_to_bv 64 (bv_unsigned (wz (sxv y)) + -1)) mod 2^32 = (y - 1) mod 2^32.
Proof. clear - rvm_wait_entry rmmap_entry y.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite (wz_unsigned (sxv y)) by (apply sxv_range).
rewrite (mod_mod_pow2 _ 32 64) by lia.
rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l. f_equal.
Qed.

#[using="rvm_wait_entry rmmap_entry"] Lemma unsigned_mod32_add_not a b : 0 <= b < 2^64 ->
(bv_unsigned (wz (sxv a)) + Z.lxor b 18446744073709551615) mod 2^32 = (a - 1 - b) mod 2^32.
Proof. clear - rvm_wait_entry rmmap_entry a b.
intros Hb. rewrite zb_lxor_ones by lia. rewrite (wz_unsigned (sxv a)) by (apply sxv_range).
rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l.
replace (a + (18446744073709551615 - b)) with ((a - 1 - b) + 2^32 * 2^32) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.
#[using="rvm_wait_entry rmmap_entry"] Lemma unsigned_mod32_swrap_add_not a b :
bv_unsigned (Z_to_bv 64 (bv_swrap 32 a + Z.lxor (bv_unsigned (wz (sxv b))) 18446744073709551615)) mod 2^32 = (a - 1 - b) mod 2^32.
Proof. clear - rvm_wait_entry rmmap_entry a b.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite (mod_mod_pow2 _ 32 64) by lia.
pose proof (sxv_range b) as RB.
rewrite zb_lxor_ones by (rewrite wz_unsigned by lia; lia). rewrite (wz_unsigned (sxv b)) by lia.
replace (bv_swrap 32 a + (18446744073709551615 - sxv b)) with ((bv_swrap 32 a - sxv b - 1) + 2^32 * 2^32) by lia.
rewrite Z.mod_add by lia.
unfold sxv. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
set (x := (a + 2^31) mod 2^32). set (y := ((b + 2^31) mod 2^32 - 2^31) mod 2^64).
assert (Hx : x = (a + 2^31) mod 2^32) by first [reflexivity | (cbn; lia)]. assert (Hy : y = ((b + 2^31) mod 2^32 - 2^31) mod 2^64) by first [reflexivity | (cbn; lia)].
clearbody x y. Z.div_mod_to_equations. nia.
Qed.
#[using="rvm_wait_entry rmmap_entry"] Lemma land224_m32 x : 0 <= x < 256 -> Z.land x 224 = Z.land x 18446744073709551584.
Proof. clear - rvm_wait_entry rmmap_entry x.
intros Hx. rewrite <- (Z.mod_small x 256) by lia. change 256 with (2^8). rewrite <- Z.land_ones by lia.
rewrite <- !Z.land_assoc. reflexivity.
Qed.

Section TAIL.
Variables (stT : mstate) (sc cnt ai ml : Z) (mt p : aptr) (r : region).
Let G := conc stT mt.
Let P := conc stT p.
Let AV := mask_upto ai.
Let FR := mask_upto (cnt - 1) - mask_upto ai.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 0 <= ml < 2^52.
Hypothesis MST : meta_slot stT mt.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis Hr : (s_regions stT) !! (fst p) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis P0 : 0 <= snd p.
Hypothesis P16 : snd p mod 16 = 0.
Hypothesis PEND : snd p + 16 <= round_up_pg (r_len r).
Hypothesis GNONE : (s_groups stT) !! p = None.
Hypothesis NOGRP : forall b' gh, (s_groups stT) !! b' = Some gh -> fst b' = fst p -> snd b' + 9 <= snd p \/ snd p + 9 <= snd b'.
Hypothesis OLD12 : forall o v t, snd p <= o < snd p + 12 ->
(r_cells (get_shadow stT (fst p))) !! o = Some (v, t) -> (t < s_tick stT)%N.
Hypothesis UR : 0 <= usage stT sc < 2^60.
Hypothesis ACT : active stT sc = None.
Hypothesis TK : ticks_ok stT.

Definition rtailW : list (Z * Z) :=
[((RATP + 132432) + 8 * sc, (RATP + 132432) + 8 * sc + 8); (G, G + 40); (P, P + 9); ((RATP + 132048) + 8 * sc, (RATP + 132048) + 8 * sc + 8)]%Z.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_wview_overlay ref_mrd_overlay rmmap_entry r AV FR SC CNT AI ML MST REC Hr Hk P0 P16 PEND GNONE NOGRP OLD12 UR ACT TK"] Lemma rtail_walk :
forall (ra sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s10 s11 t3 t4 t5 t6 : word) F fc mC,
rmrep stT mC -> mem_inv segs mC ->
evt segs (fun ms' => exists (s0' a1' a2' a3' a4' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0' (Z_to_bv 64 G) (Z_to_bv 64 0) a1' a2' a3' a4' a5 a6 a7
s2 s3 s4 (Z_to_bv 64 ((RATP + 132048) + 8 * sc)) s6 (Z_to_bv 64 ((RATP + 131960) + 8 * sc)) s8 (Z_to_bv 64 cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x860)) fc None m' (seg_rom segs)
/\ munch rtailW mC m' /\ wmono segs mC m' /\ mem_inv segs m'
/\ rmrep (stFin stT sc cnt ai ml mt p) m' /\ ticks_ok (stFin stT sc cnt ai ml mt p))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 P) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 ai) a3 a4 a5 a6 a7
s2 s3 s4 (Z_to_bv 64 ((RATP + 132048) + 8 * sc)) s6 (Z_to_bv 64 ((RATP + 131960) + 8 * sc)) s8 (Z_to_bv 64 cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x708)) fc None mC (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_wview_overlay ref_mrd_overlay rmmap_entry r AV FR SC CNT AI ML MST REC Hr Hk P0 P16 PEND GNONE NOGRP OLD12 UR ACT TK segs base RATP RGOT_SSP stT sc cnt ai ml mt p G P. gw_expose_fam RATP; gw_expose_fam RGOT_SSP. try gw_hide P; try gw_hide G; try gw_hide p; try gw_hide mt; try gw_hide ml; try gw_hide ai; try gw_hide cnt; try gw_hide sc; try gw_hide stT.
intros until mC. intros MR MI.
pose proof (munch_refl rtailW mC) as MU. pose proof (wmono_refl segs mC) as WM. unfold rtailW in MU.
pose proof (rmeta_slot_bounds stT mC mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
pose proof (rregion_facts stT mC (fst p) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). unfold alloc_ceiling in RC.
assert (CP : P = r_base r + snd p) by (unfold P; apply conc_region'; gw_exact Hr).
pose proof (AV_FR_range stT cnt ai mt p CNT AI P0) as (AVR & FRR & AV1R). fold AV in AVR, AV1R. fold AV FR in FRR.

destruct (rmrep_hdr_havoc stT mC p MR TK) as [MRA TKA]. fold (stA stT p) in MRA, TKA.
(gw_expose_fam RATP; unfold alloc_ceiling in *).

pose proof (rmrep_usage_read (stA stT p) mC sc (wa ((RATP + 132432) + 8 * sc)) MRA SC eq_refl) as RDU.
change (usage (stA stT p) sc) with (usage stT sc) in RDU.
replace (wa ((RATP + 132432) + 8 * sc)) with (Z_to_bv 64 ((RATP + 131960) + 8 * sc + 472)) in RDU by (unfold wa; f_equal; lia).
step. clear RDU.

step. rewrite ?(wz_unsigned (usage stT sc)), ?(unsigned_lit cnt) by lia. step.

pose proof MRA as (_ & (_ & _ & USG & _) & _).
pose proof (u64arr_store_ok segs _ _ (usages (stA stT p)) sc (wa ((RATP + 132432) + 8 * sc)) USG
ltac:(rewrite usages_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK. clear USG.
replace (wa ((RATP + 132432) + 8 * sc)) with (Z_to_bv 64 ((RATP + 131960) + 8 * sc + 472)) in SOK by (unfold wa; f_equal; lia).
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_usage (stA stT p) mX sc (usage stT sc + cnt) MRA SC) as MRB; gw_expose_fam RATP; fold (stB stT sc cnt p) in MRB end.
rraw_store_finish0 ((RATP + 132432) + 8 * sc) (le8 (wz (usage stT sc + cnt))) MU WM SOK.
assert (TKB : ticks_ok (stB stT sc cnt p)) by gw_exact TKA.
assert (MSTB : meta_slot (stB stT sc cnt p) mt) by (eapply meta_slot_same_areas; [| gw_exact MST]; reflexivity).
clear MRA TKA.

step. rewrite ?(unsigned_lit ai) by lia. rewrite QTyG.sllw2_word by lia.
step.
set (v3 := Z_to_bv 64 (bv_unsigned (wz (sxv (2 ^ (ai + 1)))) + -1)).
rmchunk MRB MSTB CH. change (conc (stB stT sc cnt p) mt) with G in CH. change (get_meta_rec (stB stT sc cnt p) mt) with (get_meta_rec stT mt) in CH.
rewrite REC in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
replace (meta_word _) with (4096 * ml) in CH by (unfold meta_word; cbn; lia).
rmeta_open G MUa WMa.

step. step.
assert (V3 : bv_unsigned v3 mod 2^32 = AV mod 2^32).
{ subst v3. rewrite unsigned_mod32_pred_sxv. unfold AV, mask_upto. reflexivity. }
rewrite (sx32_congr v3 AV V3).

step. rewrite ?(unsigned_lit (cnt - 1)) by lia. rewrite QTyG.sllw2_word by lia. replace (cnt - 1 + 1) with cnt by lia.
step. step.
set (v4 := Z_to_bv 64 (bv_swrap 32 (2 ^ cnt) + Z.lxor (bv_unsigned (wz (sxv AV))) 18446744073709551615)).
assert (V4 : bv_unsigned v4 mod 2^32 = FR mod 2^32).
{ subst v4. rewrite unsigned_mod32_swrap_add_not. unfold FR, AV, mask_upto. replace (cnt - 1 + 1) with cnt by lia. reflexivity. }

step. step.
lazymatch goal with H : rw_cells segs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRC : rmrep (stC stT sc cnt ai ml mt p) mX);
[ eapply rmrep_put_meta_frame; [gw_exact MRB| gw_exact MSTB| gw_exact MUa| gw_exact WMa|];
eapply rw_cells_congr; [| | | gw_exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, recA, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc cells_bytes cbytes app];
change (conc (stB stT sc cnt p) p) with P; unfold wz at 3 4;
rewrite (le4_congr v3 (Z_to_bv 64 AV)) by (rewrite V3, unsigned_lit by lia; reflexivity);
rewrite (le4_congr v4 (Z_to_bv 64 FR)) by (rewrite V4, unsigned_lit by lia; reflexivity);
replace (meta_word _) with (4096 * ml) by (unfold meta_word; cbn; lia); reflexivity
| clear MUa WMa; rename H into CH1 ] end.
assert (TKC : ticks_ok (stC stT sc cnt ai ml mt p)) by (exact (ticks_ok_upd_meta (stB stT sc cnt p) mt (fun _ => recA cnt ai ml p) TKB)).
assert (MSTC : meta_slot (stC stT sc cnt ai ml mt p) mt) by (eapply meta_slot_same_areas; [| gw_exact MST]; reflexivity).
clear MRB TKB MSTB.

pose proof MRC as (WFC & _ & _ & _ & _ & SHC). pose proof WFC as (_ & _ & DJ & _ & WG).
destruct (SHC (fst p) r Hr Hk) as [WR _]. clear SHC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
destruct (rwr_at_bytes_exist mX P 9 ltac:(eapply wr_at_sub; [gw_exact WR| lia| lia]) ltac:(lia) ltac:(lia)) as (hb & LHB & HB) end.
destruct hb as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 [|y7 [|y8 [|? ?]]]]]]]]]]; try (cbn in LHB; discriminate).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (HDR : rw_cells segs mX P [CB 8 [y0; y1; y2; y3; y4; y5; y6; y7]; C1 y8]);
[ apply rw_cells_of_bytes; [cbn; repeat split; reflexivity| gw_exact HB| cbn; eapply wr_at_sub; [gw_exact WR| lia| lia]]
| clear HB LHB ] end.
pose proof (rmeta_chunk_facts (stC stT sc cnt ai ml mt p) _ mt MRC MSTC) as (_ & _ & _ & _ & _ & GRG & _).
pose proof (GRG (fst p) r Hr Hk) as GX. change (conc (stC stT sc cnt ai ml mt p) mt) with G in GX. clear GRG.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(P, P + 9)]%Z mX) as MUb; pose proof (wmono_refl segs mX) as WMb end.

step.

step.
pose proof (byte_range y8) as Y8.
step. unfold zxb.

step. rewrite ?(unsigned_lit ai) by lia.
replace (Z.land ai 31) with ai by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
step. rewrite ?(unsigned_lit (cnt - 1)) by lia.
replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
step. rewrite ?(unsigned_lit (bv_unsigned y8)) by lia.
step.
pose proof (land_upper (bv_unsigned y8) 224 ltac:(lia) ltac:(lia)) as L8R.
rewrite ?(unsigned_lit (Z.land (bv_unsigned y8) 224)), ?(unsigned_lit ai) by lia.
rewrite (land224_m32 (bv_unsigned y8)) by lia.
pose proof (hdr_byte_facts (bv_unsigned y8) ai Y8 ltac:(lia)) as [W8R W8L].

set (nbv := Z.lor (Z.land (bv_unsigned y8) 18446744073709551584) ai) in *.
step. rewrite (le1_mod nbv). mem_after_store. rewrite (Z.mod_small nbv 256) in * by lia.

lazymatch goal with H : rw_cells segs ?mX P _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
rename H into HDR2;
assert (MRC2 : rmrep (stC stT sc cnt ai ml mt p) mX);
[ eapply (rmrep_transport_unowned _ _ _ _ MRC MUb WMb)
| assert (MRD : rmrep (stD stT sc cnt ai ml mt p) mX);
[ eapply (rmrep_put_group_new (stC stT sc cnt ai ml mt p) mX p mt ai r (b8 nbv) MRC2 GNONE Hr Hk P0 PEND P16);
[ change (conc (stC stT sc cnt ai ml mt p) p) with P; unfold pw, wz; cbn [oconc]; change (conc (stC stT sc cnt ai ml mt p) mt) with G; gw_exact HDR2
| rewrite b8_unsigned by lia; rewrite W8L; symmetry; change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity ]
| ] ] end.
{
intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. intros RF.
pose proof (lr_lo_group r Hk) as LRr. specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
destruct RF as [X1|[X2|[X3|[X4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[X5|X6]]]]]]]].
- gw_expose_fam RATP. lia.
- gw_expose_fam RATP. lia.
- gw_expose_fam RATP. lia.
- gw_expose_fam RATP. lia.
- change (s_areas (stC stT sc cnt ai ml mt p)) with (s_areas stT) in Hak. change (conc (stC stT sc cnt ai ml mt p) ak) with (conc stT ak) in Rak.
destruct (rarea_conc stT ak ar WFC Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
assert (NE : fst ak <> fst p) by (intros EQ; rewrite EQ, Hr in Hra; injection Hra as E'; apply NK; rewrite <- E'; gw_exact Hk).
pose proof (rarea_lr_lo stT ak ar rga WFC Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE) as [D|D]; lia.
- change (s_groups (stC stT sc cnt ai ml mt p)) with (s_groups stT) in Hb. change (conc (stC stT sc cnt ai ml mt p) b) with (conc stT b) in Rb.
destruct (rgroup_conc stT b gh WFC Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
destruct (N.eq_dec (fst b) (fst p)) as [EQ|NE].
+ rewrite EQ, Hr in Hrb. inversion Hrb; subst rb. destruct (NOGRP b gh Hb EQ); lia.
+ pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hr NE) as [D|D]; lia.
- change (s_regions (stC stT sc cnt ai ml mt p)) with (s_regions stT) in Hq. change (get_shadow (stC stT sc cnt ai ml mt p) q) with (get_shadow (hdr_havoc p stT) q) in Cq.
destruct (N.eq_dec q (fst p)) as [->|NE].
+ rewrite Hr in Hq. inversion Hq; subst rq.
destruct (cell_read_hdr_havoc_old stT p (a - r_base r - snd p) P16 ltac:(lia)
ltac:(intros v' t' Hc; eapply (OLD12 (snd p + (a - r_base r - snd p))); [lia| gw_exact Hc])) as [h Hh].
replace (snd p + (a - r_base r - snd p)) with (a - r_base r) in Hh by lia. rewrite Hh in Cq. discriminate.
+ pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq Hr NE) as [D|D]; lia.
- gw_expose_fam RGOT_SSP. lia.
- gw_expose_fam RATP. lia. }
clear MRC MRC2 MUb WMb HDR2.
assert (TKD : ticks_ok (stD stT sc cnt ai ml mt p)) by gw_exact TKC.
assert (MSTD : meta_slot (stD stT sc cnt ai ml mt p) mt) by (eapply meta_slot_same_areas; [| gw_exact MST]; reflexivity).
clear TKC MSTC.

pose proof MRD as (_ & (_ & ACTS & _) & _). pose proof (actives_length (stD stT sc cnt ai ml mt p)) as LACT. gw_expose_fam RATP.
rmchunk MRD MSTD CH.
change (get_meta_rec (stD stT sc cnt ai ml mt p) mt) with (get_meta_rec (put_meta mt (recA cnt ai ml p) (stB stT sc cnt p)) mt) in CH. rewrite get_meta_rec_put_same in CH.
unfold recA in CH. cbn [m_prev m_next m_mem m_avail m_freed] in CH. unfold pw in CH. cbn [oconc] in CH.
change (conc (stD stT sc cnt ai ml mt p) mt) with G in CH. change (conc (stD stT sc cnt ai ml mt p) p) with P in CH. unfold wz in CH.
set (W := meta_word _) in CH. assert (EW : W = 4096 * ml) by (subst W; unfold meta_word; cbn; lia). clearbody W.
rmeta_open G MUc WMc.

step. step. step. step. step.
rewrite (unsigned_lit sc), (Z.shiftl_mul_pow2 sc), (unsigned_lit (sc * 2 ^ 58)), Z.shiftr_div_pow2 by lia.
replace (sc * 2 ^ 58 / 2 ^ 52) with (sc * 2 ^ 6) by (change (2 ^ 58) with (2 ^ 6 * 2 ^ 52); rewrite Z.mul_assoc, Z.div_mul by lia; reflexivity).
rewrite (unsigned_lit W), EW, land_pg_mask by lia.

step. rewrite ?(unsigned_lit (sc * 2 ^ 6)), ?(unsigned_lit (cnt - 1)) by lia. rewrite (lor_shl_small sc 6 (cnt - 1)) by lia.
step. rewrite ?(unsigned_lit (sc * 2 ^ 6 + (cnt - 1))), ?(unsigned_lit (4096 * ml)) by lia.
replace (4096 * ml) with (ml * 2 ^ 12) by lia. rewrite (lor_small_shl ml 12 (sc * 2 ^ 6 + (cnt - 1))) by lia.
step. rewrite ?unsigned_lit by lia.

step. step. step. step.
rewrite ?(unsigned_lit (mask_upto ai)) by lia.

step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.

lazymatch goal with H : u64arr segs ?mX _ (actives (stD stT sc cnt ai ml mt p)) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (u64arr_read segs mX ((RATP + 132048)) (actives (stD stT sc cnt ai ml mt p)) sc (pw (stD stT sc cnt ai ml mt p) (active (stD stT sc cnt ai ml mt p) sc)) (wa ((RATP + 132048) + 8 * sc)) H
(actives_nth (stD stT sc cnt ai ml mt p) sc SC) ltac:(lia) eq_refl) as RDA end.
change (active (stD stT sc cnt ai ml mt p) sc) with (active stT sc) in RDA. rewrite ACT in RDA. unfold pw in RDA. cbn [oconc] in RDA. unfold wz in RDA.
replace (wa ((RATP + 132048) + 8 * sc)) with (Z_to_bv 64 ((RATP + 132048) + 8 * sc + 0)) in RDA by (unfold wa; f_equal; lia).
step. clear RDA.

step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.

step. step. step.

lazymatch goal with H : rw_cells segs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRE : rmrep (stE stT sc cnt ai ml mt p) mX);
[ eapply rmrep_put_meta_frame; [gw_exact MRD| gw_exact MSTD| gw_exact MUc| gw_exact WMc|];
eapply rw_cells_congr; [| | | gw_exact H]
| clear MUc WMc; rename H into CH3 ] end.
{ unfold meta_cells, recF, pw. cbn [m_prev m_next m_mem m_avail m_freed oconc cells_bytes cbytes].
change (conc (stD stT sc cnt ai ml mt p) mt) with G. change (conc (stD stT sc cnt ai ml mt p) p) with P.
unfold wz. rewrite !app_nil_r.
rewrite (le4_congr (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (mask_upto ai))) + -1)) (Z_to_bv 64 (AV - 1))).
2:{ rewrite (unsigned_lit (mask_upto ai)), Z_to_bv_unsigned, (unsigned_lit (AV - 1)) by lia. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite (mod_mod_pow2 _ 32 64) by lia. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
fold AV. Z.div_mod_to_equations. lia. }
do 6 f_equal. unfold meta_word. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. f_equal. lia. }
{ reflexivity. }
{ cbn. tauto. }
assert (TKE : ticks_ok (stE stT sc cnt ai ml mt p)) by (exact (ticks_ok_upd_meta (stD stT sc cnt ai ml mt p) mt (fun _ => recF sc cnt ai ml mt p) TKD)).
clear MRD TKD MSTD.

clear CH3.
lazymatch goal with H : u64arr segs ?mX _ (actives (stD stT sc cnt ai ml mt p)) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (u64arr_store_ok segs _ _ (actives (stD stT sc cnt ai ml mt p)) sc (wa ((RATP + 132048) + 8 * sc)) H
ltac:(rewrite actives_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK; clear H end.
replace (wa ((RATP + 132048) + 8 * sc)) with (Z_to_bv 64 ((RATP + 132048) + 8 * sc + 0)) in SOK by (unfold wa; f_equal; lia).
st1.
replace (Z_to_bv 64 ((RATP + 132048) + 8 * sc + 0)) with (Z_to_bv 64 ((RATP + 132048) + 8 * sc)) in SOK by (f_equal; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active (stE stT sc cnt ai ml mt p) mX sc (Some mt) MRE SC) as MRF; gw_expose_fam RATP; fold (stFin stT sc cnt ai ml mt p) in MRF end.
unfold pw in MRF. cbn [oconc] in MRF. change (conc (stE stT sc cnt ai ml mt p) mt) with G in MRF.
rraw_store_finish0 ((RATP + 132048) + 8 * sc) (le8 (wz G)) MU WM SOK.

step.
apply evt_done. do 6 eexists. split; [reflexivity|].
split; [gw_exact MU|]. split; [gw_exact WM|]. split; [assumption|].
split; [gw_exact MRF| gw_exact TKE].
Qed.
End TAIL.

End RC__1.

End G.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w QXxF.Mq0 Q9Ay.Mq1 Q9Ay.Mq2.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QCa8.Mq4.
Import QDXD.Mq2.
Import QkTt.Mq3.
Import QkTt.Mq4.
Import QDXD.Mq1.
Import Qy8Z.Mqa.
Import QkTt.Mq5.
Import Qy8Z.Mq1.
Import QQRC.Mq4.
Import QQRC.Mqc.
Import QROt.Mq3.
Import QZxv.Mqo.
Import QZxv.Mqm.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rvm_wait_entry : Z).
Variables (w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 : Z).
Variables (hi_14 hi_18 hi_114 hi_121 hi_130 hi_136 hi_148 hi_218 hi_311 : bv 20).
Variables (lo_15 lo_19 lo_116 lo_122 lo_131 lo_137 lo_149 lo_220 lo_313 : bv 12).
Variables (joff_427 joff_552 : bv 21).
Variables (e_197bc : Z).
Hypothesis CODE : code_at segs base (alloc_slot_code w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 2212.
Let rmmap_entry := (rvm_wait_entry + 4)%Z.
Hypothesis D_14 : decode_any (Z_to_bv 32 w_14) = Some (Auipc 10 hi_14, 4%Z).
Hypothesis E_14 : is_ecall (Z_to_bv 32 w_14) = false.
Hypothesis D_15 : decode_any (Z_to_bv 32 w_15) = Some (Load SZ8 true 20 10 lo_15, 4%Z).
Hypothesis E_15 : is_ecall (Z_to_bv 32 w_15) = false.
Hypothesis D_18 : decode_any (Z_to_bv 32 w_18) = Some (Auipc 11 hi_18, 4%Z).
Hypothesis E_18 : is_ecall (Z_to_bv 32 w_18) = false.
Hypothesis D_19 : decode_any (Z_to_bv 32 w_19) = Some (OpImm ALU_ADD 22 11 lo_19, 4%Z).
Hypothesis E_19 : is_ecall (Z_to_bv 32 w_19) = false.
Hypothesis D_114 : decode_any (Z_to_bv 32 w_114) = Some (Auipc 11 hi_114, 4%Z).
Hypothesis E_114 : is_ecall (Z_to_bv 32 w_114) = false.
Hypothesis D_116 : decode_any (Z_to_bv 32 w_116) = Some (OpImm ALU_ADD 11 11 lo_116, 4%Z).
Hypothesis E_116 : is_ecall (Z_to_bv 32 w_116) = false.
Hypothesis D_121 : decode_any (Z_to_bv 32 w_121) = Some (Auipc 10 hi_121, 4%Z).
Hypothesis E_121 : is_ecall (Z_to_bv 32 w_121) = false.
Hypothesis D_122 : decode_any (Z_to_bv 32 w_122) = Some (OpImm ALU_ADD 25 10 lo_122, 4%Z).
Hypothesis E_122 : is_ecall (Z_to_bv 32 w_122) = false.
Hypothesis D_130 : decode_any (Z_to_bv 32 w_130) = Some (Auipc 11 hi_130, 4%Z).
Hypothesis E_130 : is_ecall (Z_to_bv 32 w_130) = false.
Hypothesis D_131 : decode_any (Z_to_bv 32 w_131) = Some (Load SZ8 true 11 11 lo_131, 4%Z).
Hypothesis E_131 : is_ecall (Z_to_bv 32 w_131) = false.
Hypothesis D_136 : decode_any (Z_to_bv 32 w_136) = Some (Auipc 13 hi_136, 4%Z).
Hypothesis E_136 : is_ecall (Z_to_bv 32 w_136) = false.
Hypothesis D_137 : decode_any (Z_to_bv 32 w_137) = Some (OpImm ALU_ADD 13 13 lo_137, 4%Z).
Hypothesis E_137 : is_ecall (Z_to_bv 32 w_137) = false.
Hypothesis D_148 : decode_any (Z_to_bv 32 w_148) = Some (Auipc 13 hi_148, 4%Z).
Hypothesis E_148 : is_ecall (Z_to_bv 32 w_148) = false.
Hypothesis D_149 : decode_any (Z_to_bv 32 w_149) = Some (OpImm ALU_ADD 13 13 lo_149, 4%Z).
Hypothesis E_149 : is_ecall (Z_to_bv 32 w_149) = false.
Hypothesis D_218 : decode_any (Z_to_bv 32 w_218) = Some (Auipc 13 hi_218, 4%Z).
Hypothesis E_218 : is_ecall (Z_to_bv 32 w_218) = false.
Hypothesis D_220 : decode_any (Z_to_bv 32 w_220) = Some (OpImm ALU_ADD 13 13 lo_220, 4%Z).
Hypothesis E_220 : is_ecall (Z_to_bv 32 w_220) = false.
Hypothesis D_311 : decode_any (Z_to_bv 32 w_311) = Some (Auipc 14 hi_311, 4%Z).
Hypothesis E_311 : is_ecall (Z_to_bv 32 w_311) = false.
Hypothesis D_313 : decode_any (Z_to_bv 32 w_313) = Some (OpImm ALU_ADD 14 14 lo_313, 4%Z).
Hypothesis E_313 : is_ecall (Z_to_bv 32 w_313) = false.
Hypothesis D_427 : decode_any (Z_to_bv 32 w_427) = Some (Jal 1 joff_427, 4%Z).
Hypothesis E_427 : is_ecall (Z_to_bv 32 w_427) = false.
Hypothesis D_552 : decode_any (Z_to_bv 32 w_552) = Some (Jal 1 joff_552, 4%Z).
Hypothesis E_552 : is_ecall (Z_to_bv 32 w_552) = false.
Hypothesis ANCH_15 : gw_anch (Z.shiftl (bv_signed hi_14) 12 + (base + 56) + bv_signed lo_15)%Z RGOT_SSP.
Hypothesis ANCH_19 : gw_anch (Z.shiftl (bv_signed hi_18) 12 + (base + 72) + bv_signed lo_19)%Z (RATP + 131960).
Hypothesis ANCH_116 : gw_anch (Z.shiftl (bv_signed hi_114) 12 + (base + 456) + bv_signed lo_116)%Z RDEBRUIJN.
Hypothesis ANCH_122 : gw_anch (Z.shiftl (bv_signed hi_121) 12 + (base + 484) + bv_signed lo_122)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_131 : gw_anch (Z.shiftl (bv_signed hi_130) 12 + (base + 520) + bv_signed lo_131)%Z (RATP + 131776).
Hypothesis ANCH_137 : gw_anch (Z.shiftl (bv_signed hi_136) 12 + (base + 544) + bv_signed lo_137)%Z (RDEBRUIJN + 128).
Hypothesis ANCH_149 : gw_anch (Z.shiftl (bv_signed hi_148) 12 + (base + 592) + bv_signed lo_149)%Z (RDEBRUIJN + 155).
Hypothesis ANCH_220 : gw_anch (Z.shiftl (bv_signed hi_218) 12 + (base + 872) + bv_signed lo_220)%Z RDEBRUIJN.
Hypothesis ANCH_313 : gw_anch (Z.shiftl (bv_signed hi_311) 12 + (base + 1244) + bv_signed lo_313)%Z (RDEBRUIJN + 32).
Hypothesis LINK_427 : gw_anch (base + 1708 + bv_signed joff_427)%Z (rmmap_entry + 0)%Z.
Hypothesis LINK_552 : gw_anch (base + 2208 + bv_signed joff_552)%Z (e_197bc + 0)%Z.
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
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QZxv.Mqm.rarea_rep segs) (@rarea_rep) (gw_ent (@QZxv.Mqo.rarea_rep segs) (@rarea_rep) (gw_ent (@QROt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mqc.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_0))))))))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QZxv.Mqm.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QZxv.Mqo.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QROt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mqc.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_1))))))))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QZxv.Mqm.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QZxv.Mqo.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QROt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mqc.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_2))))))))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QZxv.Mqm.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QZxv.Mqo.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QROt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mqc.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_3))))))))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QZxv.Mqm.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QZxv.Mqo.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QROt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mqc.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_4))))))))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QZxv.Mqm.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QZxv.Mqo.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QROt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mqc.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_5))))))))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QZxv.Mqm.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QZxv.Mqo.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QROt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mqc.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_6))))))))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QZxv.Mqm.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QZxv.Mqo.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QROt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mqc.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_7))))))))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QZxv.Mqm.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QZxv.Mqo.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QROt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mqc.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_8))))))))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QZxv.Mqm.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QZxv.Mqo.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QROt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mqc.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_9))))))))))))))).

Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmrep_usage_read : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_usage_read) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_usage_read)).

#[using="RDEBRUIJN RGOT_SSP e_197bc rvm_wait_entry rmmap_entry RATP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 D_114 E_114 D_116 E_116 D_121 E_121 D_122 E_122 D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 D_218 E_218 D_220 E_220 D_311 E_311 D_313 E_313 D_427 E_427 D_552 E_552 ANCH_15 ANCH_19 ANCH_116 ANCH_122 ANCH_131 ANCH_137 ANCH_149 ANCH_220 ANCH_313 LINK_427 LINK_552 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rmmap_entry"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

Section MMC.
Variables (sc size req : Z) (nos : bool).
Hypothesis SC : 0 <= sc < 48.
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis RQ : 0 <= req < 2^32.

Definition rmmc_post (ra sp gp tp t1 t2 s0 s1 s2 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
(res : Z * Z) : machine_state -> Prop :=
fun ms' => exists (t0' a0' a1' a2' a3' a4' a5' a6' a7' : word),
ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 (wz (snd res)) s4 s5 s6 s7 s8 (wz (fst res)) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x690)) fc None m (seg_rom segs).

#[using="rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE rmmap_entry SZ RQ"] Lemma rj2c_walk :
forall (ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) F fc m (c1 u1 : Z),
1 <= c1 <= 32 -> 0 <= u1 < 2^61 ->
evt segs (rmmc_post ra sp gp tp t1 t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 req) s4 s5 s6 s7 (wz size) s10 s11 t3 t4 t5 t6 F fc m
(mm_final size req u1 c1 nos))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) a4 a5 a6 a7
(Z_to_bv 64 req) s3 s4 s5 s6 s7 (wz size) (wz c1) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x634)) fc None m (seg_rom segs)).
Proof. clear - rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE rmmap_entry SZ RQ segs base sc size req nos SC. first [clear SC | gw_hide SC | idtac]; try gw_hide nos; try gw_hide req; try gw_hide size; first [clear sc | gw_hide sc | idtac].
intros until u1. intros CR UR.
assert (SCR : 16 <= size * c1 < 2^24) by nia.
pose proof (zb_b2z_range nos) as NR.
unfold rmmc_post.

step. rewrite (wz_unsigned size), (wz_unsigned c1) by lia.
step. step. step. step. step. step.
rewrite !land_4095_word. rewrite ?(unsigned_lit (size * c1)) by lia.
replace (-16 + - (size * c1)) with (- (size * c1 + 16)) by lia.
set (nd0 := round_up_pg (size * c1 + 16)).
pose proof (round_up_pg_alt (size * c1 + 16)) as RU. pose proof (round_up_pg_range (size * c1 + 16) ltac:(lia)) as RUR.
replace (size * c1 + Z.land (- (size * c1 + 16)) 4095 + 16) with nd0 by lia.
fold nd0 in RUR.
assert (EF : mm_final size req u1 c1 nos = (if negb nos && (c1 <=? 7) then mm_small size req u1 c1 nd0 else (c1, nd0))).
{ unfold mm_final, UNIT. reflexivity. }

step. if_cases KN; zify_cond KN; rewrite ?unsigned_lit in KN by lia.
{
apply evt_done. rewrite EF. replace nos with true by (destruct nos; cbn in KN; [reflexivity| lia]). cbn [negb andb fst snd].
do 9 eexists. reflexivity. }
replace nos with false in EF |- * by (destruct nos; cbn in KN; [lia| reflexivity]). cbn [negb andb] in EF.

step. step. if_cases K7; zify_cond K7; rewrite ?(wz_unsigned c1), ?unsigned_lit in K7 by lia.
{
apply evt_done. rewrite EF. replace (c1 <=? 7) with false by (symmetry; apply Z.leb_gt; lia). cbn [fst snd].
do 9 eexists. reflexivity. }
replace (c1 <=? 7) with true in EF by (symmetry; apply Z.leb_le; lia).

step. step. step. step. step.
rewrite (Z.land_comm 4095), land_4095_word. rewrite ?(unsigned_lit req) by lia.
replace (-20 + - req) with (- (req + 20)) by lia.
set (rq' := round_up_pg (req + 20)).
pose proof (round_up_pg_alt (req + 20)) as RU2. pose proof (round_up_pg_range (req + 20) ltac:(lia)) as RUR2.
replace (req + Z.land (- (req + 20)) 4095 + 20) with rq' by lia. fold rq' in RUR2.
assert (ES : mm_small size req u1 c1 nd0 = (if (rq' <? size + 16) || ((4 * PGSZ <=? rq') && (u1 <? 2 * c1)) then (1, rq') else (c1, nd0))).
{ unfold mm_small, IB, UNIT. replace (req + 4 + 16) with (req + 20) by lia. reflexivity. }
rewrite ES in EF. clear ES. unfold PGSZ in EF.

step. if_cases K1; zify_cond K1; rewrite ?(wz_unsigned (size + 16)), ?unsigned_lit in K1 by lia.
-
replace (rq' <? size + 16) with false in EF by (symmetry; apply Z.ltb_ge; lia). cbn [orb] in EF.
step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 2) with 16384.
step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
+
apply evt_done. rewrite EF. replace (4 * 4096 <=? rq') with false by (symmetry; apply Z.leb_gt; lia). cbn [andb fst snd].
do 9 eexists. reflexivity.
+ replace (4 * 4096 <=? rq') with true in EF by (symmetry; apply Z.leb_le; lia). cbn [andb] in EF.

step. rewrite (wz_unsigned c1), (Z.shiftl_mul_pow2 c1) by lia. change (2 ^ 1) with 2. rewrite swrap32_small by lia.
step. if_cases K3; zify_cond K3; rewrite ?(wz_unsigned u1), ?unsigned_lit in K3 by lia.
*
step. step. step.
apply evt_done. rewrite EF. replace (u1 <? 2 * c1) with true by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd].
do 9 eexists. reflexivity.
* apply evt_done. rewrite EF. replace (u1 <? 2 * c1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd].
do 9 eexists. reflexivity.
-
replace (rq' <? size + 16) with true in EF by (symmetry; apply Z.ltb_lt; lia). cbn [orb] in EF.
step. step. step.
apply evt_done. rewrite EF. cbn [fst snd]. do 9 eexists. reflexivity.
Qed.

#[using="rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE rmmap_entry SC SZ"] Lemma rred_walk :
forall (ra sp gp tp t0 t1 t2 s1 a5 a6 a7 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (cnt u1 : Z),
1 <= cnt <= 32 -> 0 <= u1 < 2^61 ->
evt segs (fun ms' => exists (a5' a6' a7' t0' s3' : word),
ms' = MS (mkR ra sp gp tp t0' t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5' a6' a7'
(Z_to_bv 64 req) s3' s4 s5 s6 s7 (wz size) (wz (mm_cnt_red sc size cnt u1 nos)) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x634)) fc None m (seg_rom segs))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5 a6 a7
(Z_to_bv 64 req) (wz cnt) s4 s5 s6 s7 (wz size) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x5c0)) fc None m (seg_rom segs)).
Proof. clear - rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE rmmap_entry SC SZ segs base sc size req nos RQ. first [clear RQ | gw_hide RQ | idtac]; try gw_hide nos; try gw_hide req; try gw_hide size; try gw_hide sc.
intros until u1. intros CR UR.
assert (SCR : 16 <= size * cnt < 2^24) by nia.
pose proof (zb_b2z_range nos) as NR. pose proof (Q9Ay.Mq2.land3_range sc) as L3.

assert (J28 : forall (a5' a6' a7' t0' s9' : word) (c : Z), c = mm_cnt_red sc size cnt u1 nos ->
evt segs (fun ms' => exists (a5' a6' a7' t0' s3' : word),
ms' = MS (mkR ra sp gp tp t0' t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5' a6' a7'
(Z_to_bv 64 req) s3' s4 s5 s6 s7 (wz size) (wz (mm_cnt_red sc size cnt u1 nos)) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x634)) fc None m (seg_rom segs))
(MS (mkR ra sp gp tp t0' t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5' a6' a7'
(Z_to_bv 64 req) (wz c) s4 s5 s6 s7 (wz size) s9' s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x630)) fc None m (seg_rom segs))).
{ intros a5' a6' a7' t0' s9' c ->. step. apply evt_done. do 5 eexists. reflexivity. }

step. rewrite (wz_unsigned cnt), (Z.shiftl_mul_pow2 cnt), swrap32_small by lia. change (2 ^ 2) with 4.
step. if_cases KU; zify_cond KU; rewrite ?(wz_unsigned u1), ?unsigned_lit in KU by lia.
{ eapply J28. unfold mm_cnt_red. replace (u1 <? 4 * cnt) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }

step. if_cases KN; zify_cond KN; rewrite ?unsigned_lit in KN by lia.
{ eapply J28. unfold mm_cnt_red. replace nos with true by (destruct nos; cbn in KN; [reflexivity| lia]).
rewrite Bool.andb_false_r. reflexivity. }
assert (EN : nos = false) by (destruct nos; cbn in KN; [lia| reflexivity]).
assert (ER : mm_cnt_red sc size cnt u1 nos =
(if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
else cnt)).
{ unfold mm_cnt_red. rewrite EN. replace (u1 <? 4 * cnt) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
unfold PGSZ in ER.

step. rewrite ?(unsigned_lit sc) by lia. step. step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 3) with 32768.
step. if_cases KA; zify_cond KA; rewrite ?unsigned_lit in KA by lia.
-
replace (Z.land sc 3 =? 1) with false in ER by (symmetry; apply Z.eqb_neq; lia). cbn [andb] in ER.
step. step. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia.
+
replace (Z.land sc 3 =? 2) with false in ER by (symmetry; apply Z.eqb_neq; lia). cbn [andb] in ER.

step. step. step.
step. if_cases KC; zify_cond KC.
*
rewrite ?(wz_unsigned (size * cnt)) in KC by lia.
destruct (Z.ltb_spec (Z.land sc 3) 1) as [A1|A1]; destruct (Z.ltb_spec 32768 (size * cnt)) as [LT|GE]; cbn [Z.b2z Z.land] in KC; try (exfalso; apply KC; reflexivity); [].
assert (E0 : Z.land sc 3 = 0) by lia.
step. step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia; [exfalso; lia|].
step. if_cases KE; zify_cond KE; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KE by lia; [| exfalso; lia].
apply evt_done. rewrite ER, E0. cbn [Z.eqb andb]. replace (8 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
do 5 eexists. reflexivity.
*
assert (NC : ~ (Z.land sc 3 = 0 /\ 32768 < size * cnt)).
{ intros [E0 LT]. rewrite ?(wz_unsigned (size * cnt)) in KC by lia.
replace (Z.land sc 3 <? 1) with true in KC by (symmetry; apply Z.ltb_lt; lia).
replace (32768 <? size * cnt) with true in KC by (symmetry; apply Z.ltb_lt; lia). change (Z.land (Z.b2z true) (Z.b2z true)) with 1 in KC. lia. }
clear KC. step. step.
step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia.
{
apply evt_done. rewrite ER. replace (Z.land sc 3 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
do 5 eexists. reflexivity. }
rewrite KD in ER |- *. cbn [Z.eqb andb] in ER.
replace (8 * 4096 <? size * cnt) with false in ER by (symmetry; apply Z.ltb_ge; lia).

step. if_cases KE; zify_cond KE; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KE by lia; [exfalso; lia|].
step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 1) with 8192.
step. if_cases KQ; zify_cond KQ; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KQ by lia.
-- eapply J28. rewrite ER. replace (2 * 4096 <? size * cnt) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
-- step. eapply (J28 _ _ _ _ _ 5). rewrite ER. replace (2 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
+
rewrite KB in ER |- *. cbn [Z.eqb andb] in ER.
step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 2) with 16384.
step. if_cases KC; zify_cond KC; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KC by lia.
*
replace (4 * 4096 <? size * cnt) with false in ER by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in ER.
step. step. step.
step. if_cases KG; zify_cond KG.
{ exfalso. apply KG. cbn. first [reflexivity | destruct (32768 <? _); reflexivity]. }
clear KG. step. step. step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia; [| exfalso; lia].
apply evt_done. rewrite ER. do 5 eexists. reflexivity.
*
step. step. apply evt_done. rewrite ER. replace (4 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
do 5 eexists. reflexivity.
-
rewrite KA in ER |- *. cbn [Z.eqb andb] in ER.
step. if_cases KC; zify_cond KC; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KC by lia.
+
replace (8 * 4096 <? size * cnt) with false in ER by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in ER.
step. step. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia; [| exfalso; lia].
step. step. step.
step. if_cases KG; zify_cond KG.
{ exfalso. apply KG. cbn. first [reflexivity | destruct (32768 <? _); reflexivity]. }
clear KG. step. step. step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia; [| exfalso; lia].
apply evt_done. rewrite ER. do 5 eexists. reflexivity.
+
step. step. apply evt_done. rewrite ER. replace (8 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
do 5 eexists. reflexivity.
Qed.

#[using="rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE rmmap_entry SC"] Lemma rusage1_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) m (u0 : Z),
rmrep st m -> 0 <= u0 < 2^60 -> (forall i, 0 <= usage st i < 2^60) ->
evt segs (fun ms' => exists (a5' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz (mm_usage1 st sc u0)) a1 a2 a3 a4 a5' a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 ((RATP + 131960) + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x5c0)) fc None m (seg_rom segs))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz u0) a1 a2 a3 a4 (Z_to_bv 64 31) a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 ((RATP + 131960) + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x5ac)) fc None m (seg_rom segs)).
Proof. clear - rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE rmmap_entry SC segs base RATP sc size req nos SZ RQ. gw_expose_fam RATP. first [clear RQ | gw_hide RQ | idtac]; first [clear SZ | gw_hide SZ | idtac]; first [clear nos | gw_hide nos | idtac]; first [clear req | gw_hide req | idtac]; first [clear size | gw_hide size | idtac]; try gw_hide sc.
intros until u0. intros MR UR USR. gw_expose_fam RATP.
pose proof (land_upper sc 1 ltac:(lia) ltac:(lia)) as L1R.

step. if_cases K; unfold bv_lts in K; rewrite !signed_lit_small in K by lia.
{ apply Z.ltb_lt in K. apply evt_done. unfold mm_usage1. replace (sc <? 32) with false by (symmetry; apply Z.ltb_ge; lia). rewrite Bool.andb_false_r.
eexists. reflexivity. }
apply Z.ltb_ge in K.

step. rewrite ?(unsigned_lit sc) by lia.
step. if_cases KO; zify_cond KO; rewrite ?(unsigned_lit (Z.land sc 1)) in KO by lia.
{
assert (ODD : Z.even sc = false).
{ rewrite even_of_land1. apply Z.eqb_neq. gw_exact KO. }
apply evt_done. unfold mm_usage1. rewrite ODD. cbn [andb]. eexists. reflexivity. }
assert (EV : Z.even sc = true) by (rewrite even_of_land1; apply Z.eqb_eq; gw_exact KO).

pose proof (rmrep_usage_read st m (sc + 1) (wa ((RATP + 132432) + 8 * (sc + 1))) MR ltac:(lia) eq_refl) as RDU.
replace (wa ((RATP + 132432) + 8 * (sc + 1))) with (Z_to_bv 64 ((RATP + 131960) + 8 * sc + 480)) in RDU by (unfold wa; f_equal; lia).
pose proof (USR (sc + 1)) as U1R.
step. clear RDU. step. rewrite (wz_unsigned (usage st (sc + 1))), (wz_unsigned u0) by lia.
apply evt_done. unfold mm_usage1. rewrite EV. replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
eexists. unfold wz. rewrite (Z.add_comm (usage st (sc + 1)) u0). reflexivity.
Qed.

#[using="rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE rmmap_entry SC SZ RQ"] Lemma rmmc_walk :
forall (ra sp gp tp t0 t1 t2 s1 a6 a7 s4 s5 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) m (cnt u0 : Z),
rmrep st m -> 1 <= cnt <= 32 -> 0 <= u0 < 2^60 -> (forall i, 0 <= usage st i < 2^60) ->
evt segs (rmmc_post ra sp gp tp t1 t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 req) s4 s5 (Z_to_bv 64 (RATP + 131960)) (Z_to_bv 64 ((RATP + 131960) + 8 * sc)) (wz size) s10 s11 t3 t4 t5 t6 F fc m
(mm_final size req (mm_usage1 st sc u0) (mm_cnt_red sc size cnt (mm_usage1 st sc u0) nos) nos))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz u0) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) (Z_to_bv 64 31) a6 a7
(Z_to_bv 64 req) (wz cnt) s4 s5 (Z_to_bv 64 (RATP + 131960)) (Z_to_bv 64 ((RATP + 131960) + 8 * sc)) (wz size) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x5ac)) fc None m (seg_rom segs)).
Proof. clear - rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE rmmap_entry SC SZ RQ segs base RATP sc size req nos. gw_expose_fam RATP. try gw_hide nos; first [clear req | gw_hide req | idtac]; try gw_hide size; try gw_hide sc.
intros until u0. intros MR CR UR USR.
assert (U1R : 0 <= mm_usage1 st sc u0 < 2^61).
{ unfold mm_usage1. pose proof (USR (sc + 1)). destruct (_ && _); lia. }
eapply evt_cut. { eapply (rusage1_walk _ _ _ _ t0 t1 t2 s1); [gw_exact MR| gw_exact UR| gw_exact USR]. }
cbv beta. intros ms' (a5' & ->).
eapply evt_cut. { eapply (rred_walk _ _ _ _ t0 t1 t2 s1); [gw_exact CR| gw_exact U1R]. }
cbv beta. intros ms'' (a5'' & a6'' & a7'' & t0'' & s3'' & ->).
assert (CRR : 1 <= mm_cnt_red sc size cnt (mm_usage1 st sc u0) nos <= 32).
{ unfold mm_cnt_red. destruct (_ && _); [|lia]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); lia. }
eapply evt_mono. { eapply rj2c_walk; [gw_exact CRR| gw_exact U1R]. }
cbv beta. unfold rmmc_post. intros ms3 (t0x & a0' & a1' & a2' & a3' & a4' & a5x & a6x & a7x & ->).
do 9 eexists. reflexivity.
Qed.
End MMC.

End RC__1.

End G.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w QXxF.Mq2.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QCa8.Mq4.
Import QDXD.Mq2.
Import QkTt.Mq3.
Import QkTt.Mq4.
Import Q8QT.Mq2.
Import QDXD.Mq1.
Import Qy8Z.Mqa.
Import QkTt.Mq5.
Import QCa8.Mq3.
Import Qy8Z.Mq1.
Import QQRC.Mq4.
Import QQRC.Mqc.
Import Qy8Z.Mq9.
Import QQRC.Mq7.
Import QROt.Mq3.
Import QZxv.Mqo.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rvm_wait_entry : Z).
Variables (w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 : Z).
Variables (hi_14 hi_18 hi_114 hi_121 hi_130 hi_136 hi_148 hi_218 hi_311 : bv 20).
Variables (lo_15 lo_19 lo_116 lo_122 lo_131 lo_137 lo_149 lo_220 lo_313 : bv 12).
Variables (joff_427 joff_552 : bv 21).
Variables (e_197bc : Z).
Hypothesis CODE : code_at segs base (alloc_slot_code w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 2212.
Let rmmap_entry := (rvm_wait_entry + 4)%Z.
Hypothesis D_14 : decode_any (Z_to_bv 32 w_14) = Some (Auipc 10 hi_14, 4%Z).
Hypothesis E_14 : is_ecall (Z_to_bv 32 w_14) = false.
Hypothesis D_15 : decode_any (Z_to_bv 32 w_15) = Some (Load SZ8 true 20 10 lo_15, 4%Z).
Hypothesis E_15 : is_ecall (Z_to_bv 32 w_15) = false.
Hypothesis D_18 : decode_any (Z_to_bv 32 w_18) = Some (Auipc 11 hi_18, 4%Z).
Hypothesis E_18 : is_ecall (Z_to_bv 32 w_18) = false.
Hypothesis D_19 : decode_any (Z_to_bv 32 w_19) = Some (OpImm ALU_ADD 22 11 lo_19, 4%Z).
Hypothesis E_19 : is_ecall (Z_to_bv 32 w_19) = false.
Hypothesis D_114 : decode_any (Z_to_bv 32 w_114) = Some (Auipc 11 hi_114, 4%Z).
Hypothesis E_114 : is_ecall (Z_to_bv 32 w_114) = false.
Hypothesis D_116 : decode_any (Z_to_bv 32 w_116) = Some (OpImm ALU_ADD 11 11 lo_116, 4%Z).
Hypothesis E_116 : is_ecall (Z_to_bv 32 w_116) = false.
Hypothesis D_121 : decode_any (Z_to_bv 32 w_121) = Some (Auipc 10 hi_121, 4%Z).
Hypothesis E_121 : is_ecall (Z_to_bv 32 w_121) = false.
Hypothesis D_122 : decode_any (Z_to_bv 32 w_122) = Some (OpImm ALU_ADD 25 10 lo_122, 4%Z).
Hypothesis E_122 : is_ecall (Z_to_bv 32 w_122) = false.
Hypothesis D_130 : decode_any (Z_to_bv 32 w_130) = Some (Auipc 11 hi_130, 4%Z).
Hypothesis E_130 : is_ecall (Z_to_bv 32 w_130) = false.
Hypothesis D_131 : decode_any (Z_to_bv 32 w_131) = Some (Load SZ8 true 11 11 lo_131, 4%Z).
Hypothesis E_131 : is_ecall (Z_to_bv 32 w_131) = false.
Hypothesis D_136 : decode_any (Z_to_bv 32 w_136) = Some (Auipc 13 hi_136, 4%Z).
Hypothesis E_136 : is_ecall (Z_to_bv 32 w_136) = false.
Hypothesis D_137 : decode_any (Z_to_bv 32 w_137) = Some (OpImm ALU_ADD 13 13 lo_137, 4%Z).
Hypothesis E_137 : is_ecall (Z_to_bv 32 w_137) = false.
Hypothesis D_148 : decode_any (Z_to_bv 32 w_148) = Some (Auipc 13 hi_148, 4%Z).
Hypothesis E_148 : is_ecall (Z_to_bv 32 w_148) = false.
Hypothesis D_149 : decode_any (Z_to_bv 32 w_149) = Some (OpImm ALU_ADD 13 13 lo_149, 4%Z).
Hypothesis E_149 : is_ecall (Z_to_bv 32 w_149) = false.
Hypothesis D_218 : decode_any (Z_to_bv 32 w_218) = Some (Auipc 13 hi_218, 4%Z).
Hypothesis E_218 : is_ecall (Z_to_bv 32 w_218) = false.
Hypothesis D_220 : decode_any (Z_to_bv 32 w_220) = Some (OpImm ALU_ADD 13 13 lo_220, 4%Z).
Hypothesis E_220 : is_ecall (Z_to_bv 32 w_220) = false.
Hypothesis D_311 : decode_any (Z_to_bv 32 w_311) = Some (Auipc 14 hi_311, 4%Z).
Hypothesis E_311 : is_ecall (Z_to_bv 32 w_311) = false.
Hypothesis D_313 : decode_any (Z_to_bv 32 w_313) = Some (OpImm ALU_ADD 14 14 lo_313, 4%Z).
Hypothesis E_313 : is_ecall (Z_to_bv 32 w_313) = false.
Hypothesis D_427 : decode_any (Z_to_bv 32 w_427) = Some (Jal 1 joff_427, 4%Z).
Hypothesis E_427 : is_ecall (Z_to_bv 32 w_427) = false.
Hypothesis D_552 : decode_any (Z_to_bv 32 w_552) = Some (Jal 1 joff_552, 4%Z).
Hypothesis E_552 : is_ecall (Z_to_bv 32 w_552) = false.
Hypothesis ANCH_15 : gw_anch (Z.shiftl (bv_signed hi_14) 12 + (base + 56) + bv_signed lo_15)%Z RGOT_SSP.
Hypothesis ANCH_19 : gw_anch (Z.shiftl (bv_signed hi_18) 12 + (base + 72) + bv_signed lo_19)%Z (RATP + 131960).
Hypothesis ANCH_116 : gw_anch (Z.shiftl (bv_signed hi_114) 12 + (base + 456) + bv_signed lo_116)%Z RDEBRUIJN.
Hypothesis ANCH_122 : gw_anch (Z.shiftl (bv_signed hi_121) 12 + (base + 484) + bv_signed lo_122)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_131 : gw_anch (Z.shiftl (bv_signed hi_130) 12 + (base + 520) + bv_signed lo_131)%Z (RATP + 131776).
Hypothesis ANCH_137 : gw_anch (Z.shiftl (bv_signed hi_136) 12 + (base + 544) + bv_signed lo_137)%Z (RDEBRUIJN + 128).
Hypothesis ANCH_149 : gw_anch (Z.shiftl (bv_signed hi_148) 12 + (base + 592) + bv_signed lo_149)%Z (RDEBRUIJN + 155).
Hypothesis ANCH_220 : gw_anch (Z.shiftl (bv_signed hi_218) 12 + (base + 872) + bv_signed lo_220)%Z RDEBRUIJN.
Hypothesis ANCH_313 : gw_anch (Z.shiftl (bv_signed hi_311) 12 + (base + 1244) + bv_signed lo_313)%Z (RDEBRUIJN + 32).
Hypothesis LINK_427 : gw_anch (base + 1708 + bv_signed joff_427)%Z (rvm_wait_entry + 4)%Z.
Hypothesis LINK_552 : gw_anch (base + 2208 + bv_signed joff_552)%Z (e_197bc + 0)%Z.
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
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QZxv.Mqo.rarea_rep segs) (@rarea_rep) (gw_ent (@QROt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mqc.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq7.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_0)))))))))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QZxv.Mqo.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QROt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mqc.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq7.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_1)))))))))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QZxv.Mqo.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QROt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mqc.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq7.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_2)))))))))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QZxv.Mqo.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QROt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mqc.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq7.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_3)))))))))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QZxv.Mqo.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QROt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mqc.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq7.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_4)))))))))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QZxv.Mqo.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QROt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mqc.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq7.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_5)))))))))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QZxv.Mqo.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QROt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mqc.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq7.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_6)))))))))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QZxv.Mqo.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QROt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mqc.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq7.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_7)))))))))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QZxv.Mqo.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QROt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mqc.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq7.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_8)))))))))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QZxv.Mqo.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QROt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mqc.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq7.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_9)))))))))))))))).

Hypothesis land_m4096 : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QCa8.Mq3.gw_all) (@QCa8.Mq3.land_m4096) (base + 2212)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_10))) in let T := gw_fold_pcs T base (2212)%Z [0; 36; 64; 124; 184; 220]%Z in exact T).

Hypothesis le4_swrap_succ : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQRC.Mq7.gw_all) (@QQRC.Mq7.le4_swrap_succ) (base + -880)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_10))) in let T := gw_fold_pcs T base (-880)%Z [0; 152; 388; 396; 600; 612; 804]%Z in exact T).

Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmeta_slot_bounds : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmeta_slot_bounds) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmeta_slot_bounds)).

Definition rmrep_set_mmap_counter : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mqa.rmrep_set_mmap_counter) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mqa.rmrep_set_mmap_counter)).

Ltac rraw_store_finish0 A bs' MU WM SOK :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); (gw_expose_fam RATP; unfold wa); f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
apply (munch_write _ _ mX A bs') in MU; [| gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; cbn [inside]; lia];
apply (wmono_write segs _ mX (wa A) bs') in WM;
lazymatch goal with HI : mem_inv segs mX |- _ =>
apply (mem_inv_store segs mX (wa A) bs') in HI;
[| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by ((gw_expose_fam RATP; unfold wa); f_equal; lia); exact SOK ] ]
end;
clear L SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
end.
Ltac rmchunk MR MSq CH :=
pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
rewrite ?get_meta_rec_put_same in CH;
rewrite ?conc_put_meta, ?pw_put_meta in CH;
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen
m_set_prev m_set_next m_set_mem m_set_avail m_set_freed] in CH;
unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.

Ltac rmeta_open cq MUq WMq :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(cq, cq + 40)]%Z mX) as MUq;
pose proof (wmono_refl segs mX) as WMq end.
#[using="RDEBRUIJN RGOT_SSP e_197bc rvm_wait_entry RATP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 D_114 E_114 D_116 E_116 D_121 E_121 D_122 E_122 D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 D_218 E_218 D_220 E_220 D_311 E_311 D_313 E_313 D_427 E_427 D_552 E_552 ANCH_15 ANCH_19 ANCH_116 ANCH_122 ANCH_131 ANCH_137 ANCH_149 ANCH_220 ANCH_313 LINK_427 LINK_552 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rmmap_entry land_m4096 le4_swrap_succ"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

#[using="w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 joff_427 CODE D_427 E_427 LINK_427 rmmap_entry"] Lemma rmm_call_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
evt segs (fun ms' =>
ms' = MS (mkR (Z_to_bv 64 (base + 0x6b0)) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) s3 (Z_to_bv 64 3) (Z_to_bv 64 34) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 a7
(Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom segs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x690)) fc None m (seg_rom segs)).
Proof. clear - w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 joff_427 CODE D_427 E_427 LINK_427 rmmap_entry segs base.
intros. unfold rmmap_entry.
step. step. step. step. step. step. step. step.
apply evt_done. reflexivity.
Qed.

#[using="w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE"] Lemma rmm_ret_fail_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
evt segs (fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x7d8)) fc None m (seg_rom segs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x6b0)) fc None m (seg_rom segs)).
Proof. clear - w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE segs base.
intros. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
apply evt_done. reflexivity.
Qed.

Section MMOK.
Variables (st2 : mstate) (sc cnt size nd xa c : Z) (mt : aptr).
Let G := conc st2 mt.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis ND : 16 <= nd < 2^40.
Hypothesis NDA : nd mod 4096 = 0.
Hypothesis XA : 0 < xa.
Hypothesis XA2 : xa + nd <= alloc_ceiling.
Hypothesis MST : meta_slot st2 mt.
Hypothesis REC : get_meta_rec st2 mt = meta0.
Hypothesis HC : c_mmap_counter (ctx st2) = c.
Hypothesis CR : 0 <= c < 2^32.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 ROM_reservedZ LAY_ref_reserved land_m4096 le4_swrap_succ rmmap_entry SC CNT SZ ND NDA XA XA2 MST REC HC CR"] Lemma rmm_ret_ok_walk :
forall (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s10 s11 t3 t4 t5 t6 : word) F fc m,
rmrep st2 m -> mem_inv segs m ->
evt segs (fun ms' => exists (a3' a4' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G)
(Z_to_bv 64 xa) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 (mm_ai cnt size)) a3' a4' a5 a6 a7
(Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 (RATP + 131960)) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x708)) fc None m' (seg_rom segs)
/\ munch [(G, G + 40); ((RATP + 131980), (RATP + 131984))]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rmrep (mm_st4 st2 nd mt) m' /\ c_mmap_counter (ctx (mm_st4 st2 nd mt)) = u32 (c + 1))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 xa) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 (RATP + 131960)) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x6b0)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 ROM_reservedZ LAY_ref_reserved land_m4096 le4_swrap_succ rmmap_entry SC CNT SZ ND NDA XA XA2 MST REC HC CR segs base RATP st2 sc cnt size nd xa c mt G. gw_expose_fam RATP. try gw_hide G; try gw_hide mt; try gw_hide c; try gw_hide xa; try gw_hide nd; try gw_hide size; try gw_hide cnt; try gw_hide sc; try gw_hide st2.
intros until m. intros MR MI.
pose proof (munch_refl [(G, G + 40); ((RATP + 131980), (RATP + 131984))]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (rmeta_slot_bounds st2 m mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
(gw_expose_fam RATP; unfold alloc_ceiling in *).

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1) in K. lia. }
clear K.

step.
rmchunk MR MST CH. fold G in CH. rewrite REC in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. rewrite meta_word_meta0 in CH.
rmeta_open G MUa WMa.
step.

step. rewrite (wz_unsigned nd) by lia. rewrite land_m4096 by lia. rewrite NDA, Z.sub_0_r.
step. step. step. change (bv_swrap 32 (4096 + -16)) with 4080.
rewrite (divu_word 4080 size) by lia.
pose proof (Z.div_pos 4080 size ltac:(lia) ltac:(lia)) as D0. pose proof (Z.div_le_upper_bound 4080 size 255 ltac:(lia) ltac:(lia)) as D1.
set (d := 4080 / size) in *.

pose proof MR as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. rewrite HC in CX1. gw_expose_fam RATP.
step. rewrite (sx32_wz_sxv c) by lia.

step. step. step. cbn [Z.shiftl Z.shiftr]. rewrite ?unsigned_lit by lia. rewrite ?Z.lor_0_l.
step. rewrite (wz_unsigned (sxv c)) by (apply sxv_range).

assert (ND12 : Z.shiftr nd 12 = nd / 4096) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
assert (EWD : meta_word (m_set_maplen (Z.shiftr nd 12) meta0) = nd).
{ unfold meta_word, m_set_maplen, meta0. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite ND12.
change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
Z.div_mod_to_equations. lia. }
step.
lazymatch goal with H : rw_cells segs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR3 : rmrep (upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2) mX);
[ unfold upd_meta; rewrite REC; eapply rmrep_put_meta_frame; [gw_exact MR| gw_exact MST| gw_exact MUa| gw_exact WMa|];
eapply rw_cells_congr; [| | | gw_exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells; rewrite EWD; unfold pw; cbn [m_prev m_next m_mem m_avail m_freed oconc m_set_maplen meta0]; reflexivity
| clear MUa WMa H ] end.
set (st3 := upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2) in *.

pose proof (rw_cells_store_ok_at segs _ _ _ 12 (C4 (wz c)) 4 (Z_to_bv 64 ((RATP + 131980))) CX1 eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK.
clear CX1.
st1.
rewrite le4_swrap_succ by lia.
assert (VR : 0 <= u32 (c + 1) < 2^32) by (unfold u32; Z.div_mod_to_equations; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_mmap_counter st3 mX (u32 (c + 1)) MR3 VR) as MR4; gw_expose_fam RATP end.
clear MR3.
rraw_store_finish0 ((RATP + 131980)) (le4 (wz (u32 (c + 1)))) MU WM SOK.
assert (E4 : mm_st4 st2 nd mt = upd_ctx (set_mmap_counter (u32 (c + 1))) st3).
{ unfold mm_st4, st3, upd_ctx. change (ctx (upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2)) with (ctx st2). rewrite HC. reflexivity. }
rewrite <- E4 in MR4.
assert (C4' : c_mmap_counter (ctx (mm_st4 st2 nd mt)) = u32 (c + 1)) by (rewrite E4; reflexivity).

step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (J : forall (a2v : word) (mn : Z), mn = (if cnt <? d then cnt else d) -> a2v = Z_to_bv 64 mn ->
evt segs (fun ms' => exists (a3' a4' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G)
(Z_to_bv 64 xa) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 (mm_ai cnt size)) a3' a4' a5 a6 a7
(Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 (RATP + 131960)) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x708)) fc None m' (seg_rom segs)
/\ munch [(G, G + 40); ((RATP + 131980), (RATP + 131984))]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rmrep (mm_st4 st2 nd mt) m' /\ c_mmap_counter (ctx (mm_st4 st2 nd mt)) = u32 (c + 1))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 xa) (Z_to_bv 64 d) a2v (Z_to_bv 64 nd) (Z_to_bv 64 (bv_swrap 32 c + 1)) a5 a6 a7
(Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 (RATP + 131960)) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x6f4)) fc None mX (seg_rom segs))) end.
{ intros a2v mn Hmn ->.
assert (MNR : 0 <= mn <= cnt /\ mn <= d) by (rewrite Hmn; destruct (Z.ltb_spec cnt d); lia).

step. rewrite ?(unsigned_lit mn) by lia. step. step. step. step.
replace (cnt + -1) with (cnt - 1) by lia.
assert (AI : mm_ai cnt size = (if mn =? 0 then 0 else mn - 1)).
{ unfold mm_ai. change (4096 - UNIT) with 4080. fold d. rewrite Hmn.
destruct (Z.ltb_spec cnt d) as [LT|GE].
- replace (cnt - 1 <? d - 1) with true by (symmetry; apply Z.ltb_lt; lia).
replace (cnt - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
replace (cnt =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
- replace (cnt - 1 <? d - 1) with false by (symmetry; apply Z.ltb_ge; lia).
destruct (Z.eqb_spec d 0) as [E0|NE0].
+ rewrite E0. reflexivity.
+ replace (d - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
assert (EA2 : Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 mn) (Z_to_bv 64 (mn + -1))) + -1))) (bv_unsigned (Z_to_bv 64 (mn + -1))))
= Z_to_bv 64 (mm_ai cnt size)).
{ rewrite AI. unfold v_sltu, c_ltu, bv_ltu. rewrite (unsigned_lit mn) by lia.
destruct (Z.eqb_spec mn 0) as [E0|NE0].
- rewrite E0. change (bv_unsigned (Z_to_bv 64 (0 + -1))) with (2^64 - 1). cbn [Z.ltb]. reflexivity.
- rewrite (unsigned_lit (mn + -1)) by lia. replace (mn <? mn + -1) with false by (symmetry; apply Z.ltb_ge; lia).
change (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0) + -1))) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones_low; [f_equal; lia| lia|].
destruct (Z.eq_dec (mn + -1) 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
rewrite EA2.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [gw_exact MU|]. split; [gw_exact WM|]. split; [assumption|]. split; [gw_exact MR4| gw_exact C4']. }
if_cases K1; zify_cond K1; rewrite ?(wz_unsigned cnt), ?unsigned_lit in K1 by lia.
-
eapply J; [reflexivity|]. replace (cnt <? d) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
-
step. eapply J; [reflexivity|]. replace (cnt <? d) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
End MMOK.

End RC__1.

End G.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w QTyG.Mq0.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QCa8.Mq4.
Import QDXD.Mq2.
Import QkTt.Mq3.
Import QkTt.Mq4.
Import QDXD.Mq1.
Import Qy8Z.Mqa.
Import QkTt.Mq5.
Import Qy8Z.Mq1.
Import QQRC.Mq4.
Import QQRC.Mqc.
Import Qy8Z.Mq9.
Import QROt.Mq3.
Import QZxv.Mqo.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rvm_wait_entry : Z).
Variables (w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 : Z).
Variables (hi_14 hi_18 hi_114 hi_121 hi_130 hi_136 hi_148 hi_218 hi_311 : bv 20).
Variables (lo_15 lo_19 lo_116 lo_122 lo_131 lo_137 lo_149 lo_220 lo_313 : bv 12).
Variables (joff_427 joff_552 : bv 21).
Variables (e_197bc : Z).
Hypothesis CODE : code_at segs base (alloc_slot_code w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 2212.
Let rmmap_entry := (rvm_wait_entry + 4)%Z.
Hypothesis D_14 : decode_any (Z_to_bv 32 w_14) = Some (Auipc 10 hi_14, 4%Z).
Hypothesis E_14 : is_ecall (Z_to_bv 32 w_14) = false.
Hypothesis D_15 : decode_any (Z_to_bv 32 w_15) = Some (Load SZ8 true 20 10 lo_15, 4%Z).
Hypothesis E_15 : is_ecall (Z_to_bv 32 w_15) = false.
Hypothesis D_18 : decode_any (Z_to_bv 32 w_18) = Some (Auipc 11 hi_18, 4%Z).
Hypothesis E_18 : is_ecall (Z_to_bv 32 w_18) = false.
Hypothesis D_19 : decode_any (Z_to_bv 32 w_19) = Some (OpImm ALU_ADD 22 11 lo_19, 4%Z).
Hypothesis E_19 : is_ecall (Z_to_bv 32 w_19) = false.
Hypothesis D_114 : decode_any (Z_to_bv 32 w_114) = Some (Auipc 11 hi_114, 4%Z).
Hypothesis E_114 : is_ecall (Z_to_bv 32 w_114) = false.
Hypothesis D_116 : decode_any (Z_to_bv 32 w_116) = Some (OpImm ALU_ADD 11 11 lo_116, 4%Z).
Hypothesis E_116 : is_ecall (Z_to_bv 32 w_116) = false.
Hypothesis D_121 : decode_any (Z_to_bv 32 w_121) = Some (Auipc 10 hi_121, 4%Z).
Hypothesis E_121 : is_ecall (Z_to_bv 32 w_121) = false.
Hypothesis D_122 : decode_any (Z_to_bv 32 w_122) = Some (OpImm ALU_ADD 25 10 lo_122, 4%Z).
Hypothesis E_122 : is_ecall (Z_to_bv 32 w_122) = false.
Hypothesis D_130 : decode_any (Z_to_bv 32 w_130) = Some (Auipc 11 hi_130, 4%Z).
Hypothesis E_130 : is_ecall (Z_to_bv 32 w_130) = false.
Hypothesis D_131 : decode_any (Z_to_bv 32 w_131) = Some (Load SZ8 true 11 11 lo_131, 4%Z).
Hypothesis E_131 : is_ecall (Z_to_bv 32 w_131) = false.
Hypothesis D_136 : decode_any (Z_to_bv 32 w_136) = Some (Auipc 13 hi_136, 4%Z).
Hypothesis E_136 : is_ecall (Z_to_bv 32 w_136) = false.
Hypothesis D_137 : decode_any (Z_to_bv 32 w_137) = Some (OpImm ALU_ADD 13 13 lo_137, 4%Z).
Hypothesis E_137 : is_ecall (Z_to_bv 32 w_137) = false.
Hypothesis D_148 : decode_any (Z_to_bv 32 w_148) = Some (Auipc 13 hi_148, 4%Z).
Hypothesis E_148 : is_ecall (Z_to_bv 32 w_148) = false.
Hypothesis D_149 : decode_any (Z_to_bv 32 w_149) = Some (OpImm ALU_ADD 13 13 lo_149, 4%Z).
Hypothesis E_149 : is_ecall (Z_to_bv 32 w_149) = false.
Hypothesis D_218 : decode_any (Z_to_bv 32 w_218) = Some (Auipc 13 hi_218, 4%Z).
Hypothesis E_218 : is_ecall (Z_to_bv 32 w_218) = false.
Hypothesis D_220 : decode_any (Z_to_bv 32 w_220) = Some (OpImm ALU_ADD 13 13 lo_220, 4%Z).
Hypothesis E_220 : is_ecall (Z_to_bv 32 w_220) = false.
Hypothesis D_311 : decode_any (Z_to_bv 32 w_311) = Some (Auipc 14 hi_311, 4%Z).
Hypothesis E_311 : is_ecall (Z_to_bv 32 w_311) = false.
Hypothesis D_313 : decode_any (Z_to_bv 32 w_313) = Some (OpImm ALU_ADD 14 14 lo_313, 4%Z).
Hypothesis E_313 : is_ecall (Z_to_bv 32 w_313) = false.
Hypothesis D_427 : decode_any (Z_to_bv 32 w_427) = Some (Jal 1 joff_427, 4%Z).
Hypothesis E_427 : is_ecall (Z_to_bv 32 w_427) = false.
Hypothesis D_552 : decode_any (Z_to_bv 32 w_552) = Some (Jal 1 joff_552, 4%Z).
Hypothesis E_552 : is_ecall (Z_to_bv 32 w_552) = false.
Hypothesis ANCH_15 : gw_anch (Z.shiftl (bv_signed hi_14) 12 + (base + 56) + bv_signed lo_15)%Z RGOT_SSP.
Hypothesis ANCH_19 : gw_anch (Z.shiftl (bv_signed hi_18) 12 + (base + 72) + bv_signed lo_19)%Z (RATP + 131960).
Hypothesis ANCH_116 : gw_anch (Z.shiftl (bv_signed hi_114) 12 + (base + 456) + bv_signed lo_116)%Z RDEBRUIJN.
Hypothesis ANCH_122 : gw_anch (Z.shiftl (bv_signed hi_121) 12 + (base + 484) + bv_signed lo_122)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_131 : gw_anch (Z.shiftl (bv_signed hi_130) 12 + (base + 520) + bv_signed lo_131)%Z (RATP + 131776).
Hypothesis ANCH_137 : gw_anch (Z.shiftl (bv_signed hi_136) 12 + (base + 544) + bv_signed lo_137)%Z (RDEBRUIJN + 128).
Hypothesis ANCH_149 : gw_anch (Z.shiftl (bv_signed hi_148) 12 + (base + 592) + bv_signed lo_149)%Z (RDEBRUIJN + 155).
Hypothesis ANCH_220 : gw_anch (Z.shiftl (bv_signed hi_218) 12 + (base + 872) + bv_signed lo_220)%Z RDEBRUIJN.
Hypothesis ANCH_313 : gw_anch (Z.shiftl (bv_signed hi_311) 12 + (base + 1244) + bv_signed lo_313)%Z (RDEBRUIJN + 32).
Hypothesis LINK_427 : gw_anch (base + 1708 + bv_signed joff_427)%Z (rmmap_entry + 0)%Z.
Hypothesis LINK_552 : gw_anch (base + 2208 + bv_signed joff_552)%Z (e_197bc + 0)%Z.
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
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rta_frame : ltac:(gw_rebind_ty (@QROt.Mq3.rta_frame RC__) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QROt.Mq3.rta_frame RC__) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QZxv.Mqo.rta_frame RC__) (@rta_frame) (gw_ent (@QROt.Mq3.rta_frame RC__) (@rta_frame) gw_tbl_0)).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QZxv.Mqo.rarea_rep segs) (@rarea_rep) (gw_ent (@QROt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mqc.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_1))))))))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QZxv.Mqo.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QROt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mqc.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_2))))))))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QZxv.Mqo.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QROt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mqc.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_3))))))))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QZxv.Mqo.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QROt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mqc.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_4))))))))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QZxv.Mqo.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QROt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mqc.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_5))))))))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QZxv.Mqo.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QROt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mqc.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_6))))))))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QZxv.Mqo.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QROt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mqc.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_7))))))))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QZxv.Mqo.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QROt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mqc.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_8))))))))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QZxv.Mqo.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QROt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mqc.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_9))))))))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QZxv.Mqo.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QROt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mqc.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_10))))))))))))))).

Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).
Definition rmrep_ctx_ext : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_ctx_ext) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_ctx_ext)).
Definition rarea_rep_ext : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_rep_ext) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_rep_ext)).
Definition rgroup_rep_ext : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rgroup_rep_ext) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rgroup_rep_ext)).
Definition rshadow_rep_ext : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rshadow_rep_ext) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rshadow_rep_ext)).
Definition rmrep_transport_high : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_transport_high) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_transport_high)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmeta_slot_bounds : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmeta_slot_bounds) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmeta_slot_bounds)).
Definition rmrep_ctx_frameW : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_ctx_frameW) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_ctx_frameW)).

Ltac rmchunk MR MSq CH :=
pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
rewrite ?get_meta_rec_put_same in CH;
rewrite ?conc_put_meta, ?pw_put_meta in CH;
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen
m_set_prev m_set_next m_set_mem m_set_avail m_set_freed] in CH;
unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.

Ltac rmeta_open cq MUq WMq :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(cq, cq + 40)]%Z mX) as MUq;
pose proof (wmono_refl segs mX) as WMq end.
#[using="RDEBRUIJN RGOT_SSP e_197bc rvm_wait_entry rmmap_entry RATP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 D_114 E_114 D_116 E_116 D_121 E_121 D_122 E_122 D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 D_218 E_218 D_220 E_220 D_311 E_311 D_313 E_313 D_427 E_427 D_552 E_552 ANCH_15 ANCH_19 ANCH_116 ANCH_122 ANCH_131 ANCH_137 ANCH_149 ANCH_220 ANCH_313 LINK_427 LINK_552 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rmmap_entry"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_1 LAY_win_2 LAY_ref_reserved rmmap_entry"] Lemma rmrep_set_free_head : forall st m v,
rmrep st m ->
rmrep (upd_ctx (set_free_meta_head v) st) (write_to_mem m (wa ((RATP + 131984))) (le8 (pw st v))).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_1 LAY_win_2 LAY_ref_reserved rmmap_entry RATP segs. gw_expose_fam RATP.
intros st m v MR. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
pose proof (length_le8 (pw st v)) as L8.
pose proof (munch_write [((RATP + 131984), (RATP + 131992))] m m ((RATP + 131984)) (le8 (pw st v)) (munch_refl _ m)
ltac:(gw_expose_fam RATP; lia) ltac:(rewrite L8; gw_expose_fam RATP; lia) ltac:(rewrite L8; cbn [inside]; lia)) as MU.
pose proof (wmono_write segs m m (wa ((RATP + 131984))) (le8 (pw st v)) (wmono_refl segs m)) as WM.
eapply (rmrep_ctx_frameW st (upd_ctx (set_free_meta_head v) st) m _ _ MR MU WM); try reflexivity.
- intros lo hi [E|[]]; inversion E; subst; gw_expose_fam RATP; lia.
- left.
pose proof (rw_cells_write segs m (RATP + 131968) (ctx_head_cells st) 16 (C8 (pw st (c_free_meta_head (ctx st)))) (C8 (pw st v)) X1 eq_refl eq_refl I) as W.
cbn [cbytes cell_upd ctx_head_cells Nat.eqb Z.of_nat Pos.of_succ_nat Pos.succ] in W.
unfold ctx_head_cells, ctx in *. cbn [s_ctx upd_ctx set_free_meta_head c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
gw_exact W.
- right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; gw_expose_fam RATP; lia].
- right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; gw_expose_fam RATP; lia].
- right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; gw_expose_fam RATP; lia].
- right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; gw_expose_fam RATP; lia].
- right. split; [| intros lo hi [E|[]]; inversion E; subst; gw_expose_fam RATP; lia].
unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx set_free_meta_head c_seq c_brk]. reflexivity.
Qed.

#[using="Type"] Lemma rmrep_extW : forall stX stY m,
rmrep stX m ->
s_regions stY = s_regions stX -> ctx stY = ctx stX -> (forall q, get_meta_rec stY q = get_meta_rec stX q) ->
s_areas stY = s_areas stX -> s_groups stY = s_groups stX -> (forall rid, get_shadow stY rid = get_shadow stX rid) ->
s_reserved stY = s_reserved stX ->
rmrep stY m.
Proof. clear - segs.
intros stX stY m (WF & CX & GL & AR & GR & SH) ER EC EM EA EG ES ERs.
assert (Hconc : forall q, conc stY q = conc stX q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
split; [|split; [|split; [gw_exact GL|split; [|split]]]].
- unfold rregions_wf. rewrite ER, EA, EG, ERs. gw_exact WF.
- eapply rmrep_ctx_ext; [gw_exact EC| gw_exact Hconc| gw_exact CX].
- intros a ar Ha. rewrite EA in Ha. eapply rarea_rep_ext; [gw_exact Hconc| intros; apply EM| exact (AR a ar Ha)].
- intros b gh Hb. rewrite EG in Hb. eapply rgroup_rep_ext; [gw_exact Hconc| exact (GR b gh Hb)].
- intros rid r Hr Hk. rewrite ER in Hr. eapply rshadow_rep_ext; [apply ES| exact (SH rid r Hr Hk)].
Qed.
End RC__1.

Ltac rraw_store_finishF A bs' FR MU WM SOK :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); (gw_expose_fam RATP; unfold wa); f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by first [reflexivity | (cbn; lia)];
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
apply (rw_cells_frame segs mX _ _ A bs') in FR; [| gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; cbn [cells_size csize Nat.add]; lia];
apply (munch_write _ _ mX A bs') in MU; [| gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; cbn [inside]; lia];
apply (wmono_write segs _ mX (wa A) bs') in WM;
lazymatch goal with HI : mem_inv segs mX |- _ =>
apply (mem_inv_store segs mX (wa A) bs') in HI;
[| first [ gw_exact SOK | rewrite <- ?L; replace (wa A) with a by ((gw_expose_fam RATP; unfold wa); f_equal; lia); gw_exact SOK ] ]
end;
clear L SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
end.
Section RC__2.

Section FAILM.
Variables (st : mstate) (mt : aptr).
Let G := conc st mt.
Hypothesis MST : meta_slot st mt.

Hypothesis FL : forall h, c_free_meta_head (ctx st) = Some h ->
meta_slot st h /\ h <> mt /\ exists p, m_prev (get_meta_rec st h) = Some p /\ meta_slot st p /\ p <> mt.

Definition rfailW (spv : Z) : list (Z * Z) :=
(spv - 144, spv) :: (G, G + 40) :: ((RATP + 131984), (RATP + 131992))
:: match c_free_meta_head (ctx st) with
| Some h => (conc st h, conc st h + 40)
:: match m_prev (get_meta_rec st h) with Some p => [(conc st p, conc st p + 40)] | None => [] end
| None => []
end.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmmap_entry MST FL"] Lemma rfailm1_walk :
forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc m junk,
rmrep st m -> mem_inv segs m ->
rw_cells segs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
alloc_ceiling <= bv_unsigned sp - 144 ->
evt segs (fun ms' => exists (a1' s6' : word) m' junk',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (Z_to_bv 64 (-1)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x860)) fc None m' (seg_rom segs)
/\ rw_cells segs m' (bv_unsigned sp + -144) (rta_frame junk' s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav)
/\ munch (rfailW (bv_unsigned sp)) m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rmrep (as_fm_st st mt) m')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (RATP + 131960)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x458)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmmap_entry MST FL segs base RATP st mt G. gw_expose_fam RATP. try gw_hide G; try gw_hide mt; try gw_hide st.
intros until junk. intros MR MI FR SPC.
pose proof (wmono_refl segs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
unfold rfailW. (gw_expose_fam RATP; unfold alloc_ceiling, rta_frame in *).

assert (PRE : forall W, In (bv_unsigned sp - 144, bv_unsigned sp) W -> In (G, G + 40) W ->
evt segs (fun ms' => exists m' junk',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (Z_to_bv 64 (-1)) (pw st (c_free_meta_head (ctx st))) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (RATP + 131960)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x4b4)) fc None m' (seg_rom segs)
/\ rw_cells segs m' (bv_unsigned sp + -144) ([CB 48 junk'; C8 rc_canary; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav])
/\ munch W m m' /\ wmono segs m m' /\ mem_inv segs m' /\ rmrep (put_meta mt meta0 st) m')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (RATP + 131960)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x458)) fc None m (seg_rom segs))).
{ intros W HW1 HW2.
pose proof MR as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. cbv zeta in CX1. gw_expose_fam RATP.
rmchunk MR MST CH. fold G in CH.

lazymatch type of CH with rw_cells segs m G [?c0; ?c1; ?c2; C4 ?av; C4 ?fr; ?c5] =>
assert (CH' : rw_cells segs m G [c0; c1; c2; CB 8 (le4 av ++ le4 fr); c5]);
[ eapply rw_cells_congr; [| | | gw_exact CH]; [cbn [cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity| reflexivity| cbn [cells_wf cell_wf]; rewrite length_app, !length_le4; tauto]
| clear CH ] end.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MUa.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs.

st1. st1. st1. st1. st1.
lazymatch goal with WMs : wmono segs m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRs : rmrep st mX) by (eapply rmrep_transport_high; [gw_exact MR | gw_exact MUs | gw_exact WMs | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
clear MUs.
rmeta_open G MUb WMb.

step. st1. step. st1. step. st1. step. st1. step. st1.

step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step. step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.

step.
lazymatch goal with H : rw_cells segs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR0 : rmrep (put_meta mt meta0 st) mX);
[ eapply rmrep_put_meta_frame; [gw_exact MRs| gw_exact MST| gw_exact MUb| gw_exact WMb|];
eapply rw_cells_congr; [| | | gw_exact H]; [cbn [cells_bytes cbytes]; reflexivity| reflexivity| cbn; tauto]
| clear H MUb WMb ] end.
lazymatch goal with H : rw_cells segs ?mX (bv_unsigned sp + -144) (CB 8 ?j8 :: _) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (FR' : rw_cells segs mX (bv_unsigned sp + -144)
([CB 48 (j8 ++ cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]); C8 rc_canary; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]));
[ destruct H as [[WF BA] WR]; cbn [cells_wf cell_wf] in WF; destruct WF as [L8 WF'];
split; [split; [cbn [cells_wf cell_wf]; rewrite length_app, L8; cbn; tauto| cbn [cells_bytes cbytes] in BA |- *; rewrite <- !app_assoc; gw_exact BA]
| cbn [cells_size csize] in WR |- *; gw_exact WR]
| clear H ] end.
apply evt_done. do 2 eexists. split; [reflexivity|]. split; [gw_exact FR'|].
split. { eapply munch_weaken; [| gw_exact MUa]. intros y Hy. cbn. split; [| split; [|exact I]]; eapply (outside_In _ y); eauto. }
split; [assumption|]. split; [assumption| gw_exact MR0]. }
destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH.
-
destruct (FL h eq_refl) as (MSh & NEh & p & HP & MSp & NEp). rewrite HP.
pose proof (rmeta_slot_bounds st m h MR MSh) as (Hpos & HC' & HI & _ & _).
pose proof (rmeta_slot_bounds st m p MR MSp) as (Ppos & PC & PI & _ & _).
eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); ((RATP + 131984), (RATP + 131992)); (conc st h, conc st h + 40); (conc st p, conc st p + 40)]%Z); cbn; tauto|]. cbv beta.
intros ms' (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0). clear PRE WM.
set (st0 := put_meta mt meta0 st) in *.
assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; gw_exact MST).
assert (MSh0 : meta_slot st0 h) by (apply meta_slot_put_meta; gw_exact MSh).
assert (MSp0 : meta_slot st0 p) by (apply meta_slot_put_meta; gw_exact MSp).
unfold pw. cbn [oconc]. unfold wz.

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.

rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
change (conc st mt) with G in CH.
rmeta_open G MUa WMa.
st1.
lazymatch goal with H : rw_cells segs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep (put_meta mt (mkMeta None (Some h) None 0 0 0 0 0 0) st0) mX);
[ eapply rmrep_put_meta_frame; [gw_exact MR0| gw_exact MSm0| gw_exact MUa| gw_exact WMa|];
eapply rw_cells_congr; [| | | gw_exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 h) with (conc st h); reflexivity
| clear MUa WMa H ] end.
set (st1 := put_meta mt _ st0) in MR1.
assert (MSm1 : meta_slot st1 mt) by (apply meta_slot_put_meta; gw_exact MSm0).
assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; gw_exact MSh0).
assert (MSp1 : meta_slot st1 p) by (apply meta_slot_put_meta; gw_exact MSp0).

rmchunk MR1 MSh1 CH. unfold st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
rewrite HP in CH. cbn [oconc] in CH.
step. clear CH.

rmchunk MR1 MSm1 CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. change (meta_word _) with 0 in CH.
change (conc st0 mt) with G in CH. change (conc st mt) with G in CH.
rmeta_open G MUb WMb.
st1.
lazymatch goal with H : rw_cells segs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep (put_meta mt (mkMeta (Some p) (Some h) None 0 0 0 0 0 0) st1) mX);
[ eapply rmrep_put_meta_frame; [gw_exact MR1| gw_exact MSm1| gw_exact MUb| gw_exact WMb|];
eapply rw_cells_congr; [| | | gw_exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; reflexivity
| clear MUb WMb H ] end.
set (st2 := put_meta mt _ st1) in MR2.
assert (MSm2 : meta_slot st2 mt) by (apply meta_slot_put_meta; gw_exact MSm1).
assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; gw_exact MSh1).
assert (MSp2 : meta_slot st2 p) by (apply meta_slot_put_meta; gw_exact MSp1).

rmchunk MR2 MSp2 CH. unfold st2, st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
rmeta_open (conc st p) MUc WMc.
st1.
lazymatch goal with H : rw_cells segs ?mX (conc st p) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR3 : rmrep (put_meta p (m_set_next (Some mt) (get_meta_rec st p)) st2) mX);
[ eapply rmrep_put_meta_frame; [gw_exact MR2| gw_exact MSp2| gw_exact MUc| gw_exact WMc|];
eapply rw_cells_congr; [| | | gw_exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_next oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
change (conc st2 mt) with G; reflexivity
| clear MUc WMc H ] end.
set (st3 := put_meta p _ st2) in MR3.
assert (MSm3 : meta_slot st3 mt) by (apply meta_slot_put_meta; gw_exact MSm2).
assert (MSh3 : meta_slot st3 h) by (apply meta_slot_put_meta; gw_exact MSh2).

rmchunk MR3 MSm3 CH. unfold st3 in CH. rewrite get_meta_rec_put_other in CH by (intros E; exact (NEp (eq_sym E))).
unfold st2 in CH. rewrite get_meta_rec_put_same in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
change (conc st mt) with G in CH.
step. clear CH.

rmchunk MR3 MSh3 CH.
rmeta_open (conc st h) MUd WMd.
st1.
lazymatch goal with H : rw_cells segs ?mX (conc st h) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR4 : rmrep (put_meta h (m_set_prev (Some mt) (get_meta_rec st3 h)) st3) mX);
[ eapply rmrep_put_meta_frame; [gw_exact MR3| gw_exact MSh3| gw_exact MUd| gw_exact WMd|];
eapply rw_cells_congr; [| | | gw_exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_prev oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
change (conc st3 mt) with G; reflexivity
| clear MUd WMd H ] end.

step.
apply evt_done. do 4 eexists. split; [reflexivity|]. split; [gw_exact FR1|].
split; [gw_exact MU|]. split; [gw_exact WM1|]. split; [assumption|].
unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
unfold as_fm_link. rewrite get_meta_rec_put_other by congruence. rewrite HP. cbv zeta.
eapply (rmrep_extW _ _ _ MR4); try reflexivity.
intros q. unfold st3, st2, st1, st0, upd_meta.
destruct (decide (q = h)) as [->|NQh].
{ rewrite !get_meta_rec_put_same. f_equal.
destruct (decide (h = p)) as [<-|NHp].
- rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity.
- rewrite !get_meta_rec_put_other by congruence. reflexivity. }
rewrite !(get_meta_rec_put_other _ h _ q) by congruence.
destruct (decide (q = p)) as [->|NQp].
{ rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity. }
rewrite !(get_meta_rec_put_other _ p _ q) by congruence.
destruct (decide (q = mt)) as [->|NQm].
{ rewrite !get_meta_rec_put_same. reflexivity. }
rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
-
eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); ((RATP + 131984), (RATP + 131992))]%Z); cbn; tauto|]. cbv beta.
intros ms' (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0). clear PRE WM.
set (st0 := put_meta mt meta0 st) in *.
assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; gw_exact MST).
unfold pw. cbn [oconc]. unfold wz.

step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.

rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
change (conc st mt) with G in CH.
rmeta_open G MUa WMa.
st1. st1.
lazymatch goal with H : rw_cells segs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep (put_meta mt (mkMeta (Some mt) (Some mt) None 0 0 0 0 0 0) st0) mX);
[ eapply rmrep_put_meta_frame; [gw_exact MR0| gw_exact MSm0| gw_exact MUa| gw_exact WMa|];
eapply rw_cells_congr; [| | | gw_exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 mt) with G; reflexivity
| clear MUa WMa H ] end.
set (st1 := put_meta mt _ st0) in MR1.

step.
pose proof MR1 as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. cbv zeta in CX1. gw_expose_fam RATP.
pose proof (rw_cells_store_ok_at segs _ _ _ 16 (C8 (pw st1 (c_free_meta_head (ctx st1)))) 8 (Z_to_bv 64 ((RATP + 131984))) CX1 eq_refl eq_refl
ltac:(unfold wa; f_equal; lia)) as SOK. clear CX1.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_free_head st1 mX (Some mt) MR1) as MR2; gw_expose_fam RATP end.
unfold pw in MR2. cbn [oconc] in MR2. change (conc st1 mt) with G in MR2.
rraw_store_finishF ((RATP + 131984)) (le8 (wz G)) FR1 MU WM1 SOK.

step.
apply evt_done. do 4 eexists. split; [reflexivity|]. split; [gw_exact FR1|].
split; [gw_exact MU|]. split; [gw_exact WM1|]. split; [assumption|].
unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
unfold as_fm_single. cbn [set_head].
eapply (rmrep_extW _ _ _ MR2); try reflexivity.
intros q. unfold st1, st0, upd_meta. rewrite !rec_upd_ctx.
destruct (decide (q = mt)) as [->|NQm].
{ rewrite !get_meta_rec_put_same. reflexivity. }
rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmmap_entry MST FL"] Lemma rfailm2_walk :
forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc m junk,
rmrep st m -> mem_inv segs m ->
rw_cells segs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
alloc_ceiling <= bv_unsigned sp - 144 ->
evt segs (fun ms' => exists (s6' : word) m' junk',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x860)) fc None m' (seg_rom segs)
/\ rw_cells segs m' (bv_unsigned sp + -144) (rta_frame junk' s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav)
/\ munch (rfailW (bv_unsigned sp)) m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rmrep (as_fm_st st mt) m')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (RATP + 131960)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x7d8)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmmap_entry MST FL segs base RATP st mt G. gw_expose_fam RATP. try gw_hide G; try gw_hide mt; try gw_hide st.
intros until junk. intros MR MI FR SPC.
pose proof (wmono_refl segs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
unfold rfailW. (gw_expose_fam RATP; unfold alloc_ceiling, rta_frame in *).

assert (PRE : forall W, In (bv_unsigned sp - 144, bv_unsigned sp) W -> In (G, G + 40) W ->
evt segs (fun ms' => exists m' junk',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (pw st (c_free_meta_head (ctx st))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (RATP + 131960)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x830)) fc None m' (seg_rom segs)
/\ rw_cells segs m' (bv_unsigned sp + -144) ([CB 48 junk'; C8 rc_canary; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav])
/\ munch W m m' /\ wmono segs m m' /\ mem_inv segs m' /\ rmrep (put_meta mt meta0 st) m')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (RATP + 131960)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x7d8)) fc None m (seg_rom segs))).
{ intros W HW1 HW2.
pose proof MR as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. cbv zeta in CX1. gw_expose_fam RATP.
rmchunk MR MST CH. fold G in CH.

lazymatch type of CH with rw_cells segs m G [?c0; ?c1; ?c2; C4 ?av; C4 ?fr; ?c5] =>
assert (CH' : rw_cells segs m G [c0; c1; c2; CB 8 (le4 av ++ le4 fr); c5]);
[ eapply rw_cells_congr; [| | | gw_exact CH]; [cbn [cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity| reflexivity| cbn [cells_wf cell_wf]; rewrite length_app, !length_le4; tauto]
| clear CH ] end.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MUa.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs.

st1. st1. st1. st1. st1.
lazymatch goal with WMs : wmono segs m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRs : rmrep st mX) by (eapply rmrep_transport_high; [gw_exact MR | gw_exact MUs | gw_exact WMs | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
clear MUs.
rmeta_open G MUb WMb.

step. st1. step. st1. step. st1. step. st1. step. st1.

step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.

step.
lazymatch goal with H : rw_cells segs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR0 : rmrep (put_meta mt meta0 st) mX);
[ eapply rmrep_put_meta_frame; [gw_exact MRs| gw_exact MST| gw_exact MUb| gw_exact WMb|];
eapply rw_cells_congr; [| | | gw_exact H]; [cbn [cells_bytes cbytes]; reflexivity| reflexivity| cbn; tauto]
| clear H MUb WMb ] end.
lazymatch goal with H : rw_cells segs ?mX (bv_unsigned sp + -144) (CB 8 ?j8 :: _) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (FR' : rw_cells segs mX (bv_unsigned sp + -144)
([CB 48 (j8 ++ cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]); C8 rc_canary; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]));
[ destruct H as [[WF BA] WR]; cbn [cells_wf cell_wf] in WF; destruct WF as [L8 WF'];
split; [split; [cbn [cells_wf cell_wf]; rewrite length_app, L8; cbn; tauto| cbn [cells_bytes cbytes] in BA |- *; rewrite <- !app_assoc; gw_exact BA]
| cbn [cells_size csize] in WR |- *; gw_exact WR]
| clear H ] end.
apply evt_done. do 2 eexists. split; [reflexivity|]. split; [gw_exact FR'|].
split. { eapply munch_weaken; [| gw_exact MUa]. intros y Hy. cbn. split; [| split; [|exact I]]; eapply (outside_In _ y); eauto. }
split; [assumption|]. split; [assumption| gw_exact MR0]. }
destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH.
-
destruct (FL h eq_refl) as (MSh & NEh & p & HP & MSp & NEp). rewrite HP.
pose proof (rmeta_slot_bounds st m h MR MSh) as (Hpos & HC' & HI & _ & _).
pose proof (rmeta_slot_bounds st m p MR MSp) as (Ppos & PC & PI & _ & _).
eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); ((RATP + 131984), (RATP + 131992)); (conc st h, conc st h + 40); (conc st p, conc st p + 40)]%Z); cbn; tauto|]. cbv beta.
intros ms' (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0). clear PRE WM.
set (st0 := put_meta mt meta0 st) in *.
assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; gw_exact MST).
assert (MSh0 : meta_slot st0 h) by (apply meta_slot_put_meta; gw_exact MSh).
assert (MSp0 : meta_slot st0 p) by (apply meta_slot_put_meta; gw_exact MSp).
unfold pw. cbn [oconc]. unfold wz.

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.

rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
change (conc st mt) with G in CH.
rmeta_open G MUa WMa.
st1.
lazymatch goal with H : rw_cells segs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep (put_meta mt (mkMeta None (Some h) None 0 0 0 0 0 0) st0) mX);
[ eapply rmrep_put_meta_frame; [gw_exact MR0| gw_exact MSm0| gw_exact MUa| gw_exact WMa|];
eapply rw_cells_congr; [| | | gw_exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 h) with (conc st h); reflexivity
| clear MUa WMa H ] end.
set (st1 := put_meta mt _ st0) in MR1.
assert (MSm1 : meta_slot st1 mt) by (apply meta_slot_put_meta; gw_exact MSm0).
assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; gw_exact MSh0).
assert (MSp1 : meta_slot st1 p) by (apply meta_slot_put_meta; gw_exact MSp0).

rmchunk MR1 MSh1 CH. unfold st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
rewrite HP in CH. cbn [oconc] in CH.
step. clear CH.

rmchunk MR1 MSm1 CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. change (meta_word _) with 0 in CH.
change (conc st0 mt) with G in CH. change (conc st mt) with G in CH.
rmeta_open G MUb WMb.
st1.
lazymatch goal with H : rw_cells segs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep (put_meta mt (mkMeta (Some p) (Some h) None 0 0 0 0 0 0) st1) mX);
[ eapply rmrep_put_meta_frame; [gw_exact MR1| gw_exact MSm1| gw_exact MUb| gw_exact WMb|];
eapply rw_cells_congr; [| | | gw_exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; reflexivity
| clear MUb WMb H ] end.
set (st2 := put_meta mt _ st1) in MR2.
assert (MSm2 : meta_slot st2 mt) by (apply meta_slot_put_meta; gw_exact MSm1).
assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; gw_exact MSh1).
assert (MSp2 : meta_slot st2 p) by (apply meta_slot_put_meta; gw_exact MSp1).

rmchunk MR2 MSp2 CH. unfold st2, st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
rmeta_open (conc st p) MUc WMc.
st1.
lazymatch goal with H : rw_cells segs ?mX (conc st p) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR3 : rmrep (put_meta p (m_set_next (Some mt) (get_meta_rec st p)) st2) mX);
[ eapply rmrep_put_meta_frame; [gw_exact MR2| gw_exact MSp2| gw_exact MUc| gw_exact WMc|];
eapply rw_cells_congr; [| | | gw_exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_next oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
change (conc st2 mt) with G; reflexivity
| clear MUc WMc H ] end.
set (st3 := put_meta p _ st2) in MR3.
assert (MSm3 : meta_slot st3 mt) by (apply meta_slot_put_meta; gw_exact MSm2).
assert (MSh3 : meta_slot st3 h) by (apply meta_slot_put_meta; gw_exact MSh2).

rmchunk MR3 MSm3 CH. unfold st3 in CH. rewrite get_meta_rec_put_other in CH by (intros E; exact (NEp (eq_sym E))).
unfold st2 in CH. rewrite get_meta_rec_put_same in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
change (conc st mt) with G in CH.
step. clear CH.

step.
rmchunk MR3 MSh3 CH.
rmeta_open (conc st h) MUd WMd.
st1.
lazymatch goal with H : rw_cells segs ?mX (conc st h) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR4 : rmrep (put_meta h (m_set_prev (Some mt) (get_meta_rec st3 h)) st3) mX);
[ eapply rmrep_put_meta_frame; [gw_exact MR3| gw_exact MSh3| gw_exact MUd| gw_exact WMd|];
eapply rw_cells_congr; [| | | gw_exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_prev oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
change (conc st3 mt) with G; reflexivity
| clear MUd WMd H ] end.

step.
apply evt_done. do 3 eexists. split; [reflexivity|]. split; [gw_exact FR1|].
split; [gw_exact MU|]. split; [gw_exact WM1|]. split; [assumption|].
unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
unfold as_fm_link. rewrite get_meta_rec_put_other by congruence. rewrite HP. cbv zeta.
eapply (rmrep_extW _ _ _ MR4); try reflexivity.
intros q. unfold st3, st2, st1, st0, upd_meta.
destruct (decide (q = h)) as [->|NQh].
{ rewrite !get_meta_rec_put_same. f_equal.
destruct (decide (h = p)) as [<-|NHp].
- rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity.
- rewrite !get_meta_rec_put_other by congruence. reflexivity. }
rewrite !(get_meta_rec_put_other _ h _ q) by congruence.
destruct (decide (q = p)) as [->|NQp].
{ rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity. }
rewrite !(get_meta_rec_put_other _ p _ q) by congruence.
destruct (decide (q = mt)) as [->|NQm].
{ rewrite !get_meta_rec_put_same. reflexivity. }
rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
-
eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); ((RATP + 131984), (RATP + 131992))]%Z); cbn; tauto|]. cbv beta.
intros ms' (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0). clear PRE WM.
set (st0 := put_meta mt meta0 st) in *.
assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; gw_exact MST).
unfold pw. cbn [oconc]. unfold wz.

step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.

rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
change (conc st mt) with G in CH.
rmeta_open G MUa WMa.
st1. st1.
lazymatch goal with H : rw_cells segs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep (put_meta mt (mkMeta (Some mt) (Some mt) None 0 0 0 0 0 0) st0) mX);
[ eapply rmrep_put_meta_frame; [gw_exact MR0| gw_exact MSm0| gw_exact MUa| gw_exact WMa|];
eapply rw_cells_congr; [| | | gw_exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 mt) with G; reflexivity
| clear MUa WMa H ] end.
set (st1 := put_meta mt _ st0) in MR1.

step.
pose proof MR1 as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. cbv zeta in CX1. gw_expose_fam RATP.
pose proof (rw_cells_store_ok_at segs _ _ _ 16 (C8 (pw st1 (c_free_meta_head (ctx st1)))) 8 (Z_to_bv 64 ((RATP + 131984))) CX1 eq_refl eq_refl
ltac:(unfold wa; f_equal; lia)) as SOK. clear CX1.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_free_head st1 mX (Some mt) MR1) as MR2; gw_expose_fam RATP end.
unfold pw in MR2. cbn [oconc] in MR2. change (conc st1 mt) with G in MR2.
rraw_store_finishF ((RATP + 131984)) (le8 (wz G)) FR1 MU WM1 SOK.

step.
apply evt_done. do 3 eexists. split; [reflexivity|]. split; [gw_exact FR1|].
split; [gw_exact MU|]. split; [gw_exact WM1|]. split; [assumption|].
unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
unfold as_fm_single. cbn [set_head].
eapply (rmrep_extW _ _ _ MR2); try reflexivity.
intros q. unfold st1, st0, upd_meta. rewrite !rec_upd_ctx.
destruct (decide (q = mt)) as [->|NQm].
{ rewrite !get_meta_rec_put_same. reflexivity. }
rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
Qed.
End FAILM.

End RC__2.

End G.
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w QDUx.Mq0 Q9Ay.Mq3 Q9Ay.Mq4 Q9Ay.Mq5 Q9Ay.Mq6 Q9Ay.Mq7 Q9Ay.Mq8 QJE4.Mq3.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QCa8.Mq4.
Import QDXD.Mq2.
Import QkTt.Mq3.
Import QkTt.Mq4.
Import Q8QT.Mq2.
Import QDXD.Mq1.
Import Qy8Z.Mqa.
Import QkTt.Mq5.
Import QCa8.Mq3.
Import Qy8Z.Mq8.
Import Q8l1.Mq8.
Import Qy8Z.Mq9.
Import QQRC.Mq9.
Import Qy8Z.Mq1.
Import QQRC.Mq4.
Import QQRC.Mqc.
Import QROt.Mq3.
Import QZxv.Mqo.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac amo_step AMO ::= g_amo_step AMO. Local Ltac mkr__amo_step_2 AMO := g_amo_step AMO.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rvm_wait_entry : Z).
Variables (w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 : Z).
Variables (hi_14 hi_18 hi_114 hi_121 hi_130 hi_136 hi_148 hi_218 hi_311 : bv 20).
Variables (lo_15 lo_19 lo_116 lo_122 lo_131 lo_137 lo_149 lo_220 lo_313 : bv 12).
Variables (joff_427 joff_552 : bv 21).
Variables (e_197bc : Z).
Hypothesis CODE : code_at segs base (alloc_slot_code w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 2212.
Hypothesis D_14 : decode_any (Z_to_bv 32 w_14) = Some (Auipc 10 hi_14, 4%Z).
Hypothesis E_14 : is_ecall (Z_to_bv 32 w_14) = false.
Hypothesis D_15 : decode_any (Z_to_bv 32 w_15) = Some (Load SZ8 true 20 10 lo_15, 4%Z).
Hypothesis E_15 : is_ecall (Z_to_bv 32 w_15) = false.
Hypothesis D_18 : decode_any (Z_to_bv 32 w_18) = Some (Auipc 11 hi_18, 4%Z).
Hypothesis E_18 : is_ecall (Z_to_bv 32 w_18) = false.
Hypothesis D_19 : decode_any (Z_to_bv 32 w_19) = Some (OpImm ALU_ADD 22 11 lo_19, 4%Z).
Hypothesis E_19 : is_ecall (Z_to_bv 32 w_19) = false.
Hypothesis D_114 : decode_any (Z_to_bv 32 w_114) = Some (Auipc 11 hi_114, 4%Z).
Hypothesis E_114 : is_ecall (Z_to_bv 32 w_114) = false.
Hypothesis D_116 : decode_any (Z_to_bv 32 w_116) = Some (OpImm ALU_ADD 11 11 lo_116, 4%Z).
Hypothesis E_116 : is_ecall (Z_to_bv 32 w_116) = false.
Hypothesis D_121 : decode_any (Z_to_bv 32 w_121) = Some (Auipc 10 hi_121, 4%Z).
Hypothesis E_121 : is_ecall (Z_to_bv 32 w_121) = false.
Hypothesis D_122 : decode_any (Z_to_bv 32 w_122) = Some (OpImm ALU_ADD 25 10 lo_122, 4%Z).
Hypothesis E_122 : is_ecall (Z_to_bv 32 w_122) = false.
Hypothesis D_130 : decode_any (Z_to_bv 32 w_130) = Some (Auipc 11 hi_130, 4%Z).
Hypothesis E_130 : is_ecall (Z_to_bv 32 w_130) = false.
Hypothesis D_131 : decode_any (Z_to_bv 32 w_131) = Some (Load SZ8 true 11 11 lo_131, 4%Z).
Hypothesis E_131 : is_ecall (Z_to_bv 32 w_131) = false.
Hypothesis D_136 : decode_any (Z_to_bv 32 w_136) = Some (Auipc 13 hi_136, 4%Z).
Hypothesis E_136 : is_ecall (Z_to_bv 32 w_136) = false.
Hypothesis D_137 : decode_any (Z_to_bv 32 w_137) = Some (OpImm ALU_ADD 13 13 lo_137, 4%Z).
Hypothesis E_137 : is_ecall (Z_to_bv 32 w_137) = false.
Hypothesis D_148 : decode_any (Z_to_bv 32 w_148) = Some (Auipc 13 hi_148, 4%Z).
Hypothesis E_148 : is_ecall (Z_to_bv 32 w_148) = false.
Hypothesis D_149 : decode_any (Z_to_bv 32 w_149) = Some (OpImm ALU_ADD 13 13 lo_149, 4%Z).
Hypothesis E_149 : is_ecall (Z_to_bv 32 w_149) = false.
Hypothesis D_218 : decode_any (Z_to_bv 32 w_218) = Some (Auipc 13 hi_218, 4%Z).
Hypothesis E_218 : is_ecall (Z_to_bv 32 w_218) = false.
Hypothesis D_220 : decode_any (Z_to_bv 32 w_220) = Some (OpImm ALU_ADD 13 13 lo_220, 4%Z).
Hypothesis E_220 : is_ecall (Z_to_bv 32 w_220) = false.
Hypothesis D_311 : decode_any (Z_to_bv 32 w_311) = Some (Auipc 14 hi_311, 4%Z).
Hypothesis E_311 : is_ecall (Z_to_bv 32 w_311) = false.
Hypothesis D_313 : decode_any (Z_to_bv 32 w_313) = Some (OpImm ALU_ADD 14 14 lo_313, 4%Z).
Hypothesis E_313 : is_ecall (Z_to_bv 32 w_313) = false.
Hypothesis D_427 : decode_any (Z_to_bv 32 w_427) = Some (Jal 1 joff_427, 4%Z).
Hypothesis E_427 : is_ecall (Z_to_bv 32 w_427) = false.
Hypothesis D_552 : decode_any (Z_to_bv 32 w_552) = Some (Jal 1 joff_552, 4%Z).
Hypothesis E_552 : is_ecall (Z_to_bv 32 w_552) = false.
Hypothesis ANCH_15 : gw_anch (Z.shiftl (bv_signed hi_14) 12 + (base + 56) + bv_signed lo_15)%Z RGOT_SSP.
Hypothesis ANCH_19 : gw_anch (Z.shiftl (bv_signed hi_18) 12 + (base + 72) + bv_signed lo_19)%Z (RATP + 131960).
Hypothesis ANCH_116 : gw_anch (Z.shiftl (bv_signed hi_114) 12 + (base + 456) + bv_signed lo_116)%Z RDEBRUIJN.
Hypothesis ANCH_122 : gw_anch (Z.shiftl (bv_signed hi_121) 12 + (base + 484) + bv_signed lo_122)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_131 : gw_anch (Z.shiftl (bv_signed hi_130) 12 + (base + 520) + bv_signed lo_131)%Z (RATP + 131776).
Hypothesis ANCH_137 : gw_anch (Z.shiftl (bv_signed hi_136) 12 + (base + 544) + bv_signed lo_137)%Z (RDEBRUIJN + 128).
Hypothesis ANCH_149 : gw_anch (Z.shiftl (bv_signed hi_148) 12 + (base + 592) + bv_signed lo_149)%Z (RDEBRUIJN + 155).
Hypothesis ANCH_220 : gw_anch (Z.shiftl (bv_signed hi_218) 12 + (base + 872) + bv_signed lo_220)%Z RDEBRUIJN.
Hypothesis ANCH_313 : gw_anch (Z.shiftl (bv_signed hi_311) 12 + (base + 1244) + bv_signed lo_313)%Z (RDEBRUIJN + 32).
Hypothesis LINK_427 : gw_anch (base + 1708 + bv_signed joff_427)%Z (rvm_wait_entry + 4)%Z.
Hypothesis LINK_552 : gw_anch (base + 2208 + bv_signed joff_552)%Z (e_197bc + 0)%Z.
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
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rt1_regs : ltac:(gw_rebind_ty (@QZxv.Mqo.rt1_regs RATP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QZxv.Mqo.rt1_regs RATP) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QZxv.Mqo.rt1_regs RATP) (@rt1_regs) gw_tbl_0).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QZxv.Mqo.rarea_rep segs) (@rarea_rep) (gw_ent (@QROt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mqc.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8l1.Mq8.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_1))))))))))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QZxv.Mqo.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QROt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mqc.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8l1.Mq8.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_2))))))))))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QZxv.Mqo.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QROt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mqc.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8l1.Mq8.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_3))))))))))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QZxv.Mqo.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QROt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mqc.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8l1.Mq8.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_4))))))))))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QZxv.Mqo.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QROt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mqc.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8l1.Mq8.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_5))))))))))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QZxv.Mqo.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QROt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mqc.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8l1.Mq8.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_6))))))))))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QZxv.Mqo.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QROt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mqc.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8l1.Mq8.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_7))))))))))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QZxv.Mqo.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QROt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mqc.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8l1.Mq8.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_8))))))))))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QZxv.Mqo.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QROt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mqc.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8l1.Mq8.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_9))))))))))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QZxv.Mqo.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QROt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mqc.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8l1.Mq8.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_10))))))))))))))))).

Definition rsize_classes_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rsize_classes_read) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rsize_classes_read)).
Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).
Definition rmrep_group_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_group_read) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_group_read)).
Definition rmrep_set_active : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_set_active) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_set_active)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmrep_bounces_read : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_bounces_read) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_bounces_read)).
Definition rmeta_slot_bounds : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmeta_slot_bounds) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmeta_slot_bounds)).
Definition rgroup_bounds : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rgroup_bounds) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rgroup_bounds)).

Definition rmrep_set_bounce : ltac:(gw_ctx_fold_ty2 (@QQRC.Mqc.rmrep_set_bounce) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mqc.rmrep_set_bounce)).
Definition rconc_meta_inj : ltac:(gw_ctx_fold_ty2 (@QQRC.Mqc.rconc_meta_inj) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mqc.rconc_meta_inj)).
Definition rmrep_set_group_ai : ltac:(gw_ctx_fold_ty2 (@QQRC.Mqc.rmrep_set_group_ai) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mqc.rmrep_set_group_ai)).
Ltac rraw_store_finish0 A bs' MU WM SOK :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); (gw_expose_fam RATP; unfold wa); f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
apply (munch_write _ _ mX A bs') in MU; [| gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; cbn [inside]; lia];
apply (wmono_write segs _ mX (wa A) bs') in WM;
lazymatch goal with HI : mem_inv segs mX |- _ =>
apply (mem_inv_store segs mX (wa A) bs') in HI;
[| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by ((gw_expose_fam RATP; unfold wa); f_equal; lia); exact SOK ] ]
end;
clear L SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
end.
Ltac rmchunk MR MSq CH :=
pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
rewrite ?get_meta_rec_put_same in CH;
rewrite ?conc_put_meta, ?pw_put_meta in CH;
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen
m_set_prev m_set_next m_set_mem m_set_avail m_set_freed] in CH;
unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.

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
Ltac rmeta_open cq MUq WMq :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(cq, cq + 40)]%Z mX) as MUq;
pose proof (wmono_refl segs mX) as WMq end.
#[using="RDEBRUIJN RGOT_SSP e_197bc rvm_wait_entry RATP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 D_114 E_114 D_116 E_116 D_121 E_121 D_122 E_122 D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 D_218 E_218 D_220 E_220 D_311 E_311 D_313 E_313 D_427 E_427 D_552 E_552 ANCH_15 ANCH_19 ANCH_116 ANCH_122 ANCH_131 ANCH_137 ANCH_149 ANCH_220 ANCH_313 LINK_427 LINK_552 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := first [clear - hs segs base w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_14 hi_18 hi_114 hi_121 hi_130 hi_136 hi_148 hi_218 hi_311 lo_15 lo_19 lo_116 lo_122 lo_131 lo_137 lo_149 lo_220 lo_313 joff_427 joff_552 RDEBRUIJN RGOT_SSP e_197bc rvm_wait_entry RATP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 D_114 E_114 D_116 E_116 D_121 E_121 D_122 E_122 D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 D_218 E_218 D_220 E_220 D_311 E_311 D_313 E_313 D_427 E_427 D_552 E_552 ANCH_15 ANCH_19 ANCH_116 ANCH_122 ANCH_131 ANCH_137 ANCH_149 ANCH_220 ANCH_313 LINK_427 LINK_552 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ | clear - hs segs base w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_14 hi_18 hi_114 hi_121 hi_130 hi_136 hi_148 hi_218 hi_311 lo_15 lo_19 lo_116 lo_122 lo_131 lo_137 lo_149 lo_220 lo_313 joff_427 joff_552 RDEBRUIJN RGOT_SSP e_197bc rvm_wait_entry RATP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 D_114 E_114 D_116 E_116 D_121 E_121 D_122 E_122 D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 D_218 E_218 D_220 E_220 D_311 E_311 D_313 E_313 D_427 E_427 D_552 E_552 ANCH_15 ANCH_19 ANCH_116 ANCH_122 ANCH_131 ANCH_137 ANCH_149 ANCH_220 ANCH_313 LINK_427 LINK_552 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay].

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

#[using="Type"] Lemma lw_slli52_srli58_sc mq : mw_ok mq ->
Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (sx32 (Z_to_bv 64 (meta_word mq)))) 52))) 58)
= Z_to_bv 64 (m_sizeclass mq).
Proof. clear - mq.
intros MWq. pose proof (meta_word_range _ MWq) as WR. pose proof MWq as (LI & FB & SCR & ML).
f_equal. unfold sx32. rewrite (unsigned_lit (meta_word mq)) by lia.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
rewrite swrap32_eq'.
unfold meta_word.
Z.div_mod_to_equations. nia.
Qed.

Section AVZ.
Variables (st : mstate) (m : mem) (g b : aptr) (gh : ghdr) (sc0 : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.
Let ai := g_active_idx gh.
Let act := mask_upto ai.
Let mask := Z.land f act.
Let st4 := upd_meta g (fun r => m_set_avail (Z.land f act) (m_set_freed (Z.ldiff f act) r)) st.
Let st5 := decay_bounces (m_sizeclass mr) st4.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hgh : (s_groups st) !! b = Some gh.
Hypothesis AI : 0 <= ai <= 31.
Hypothesis FR32 : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.
Hypothesis MASK : mask <> 0.
Hypothesis BNC : forall i, 0 <= bounces st i < 256.
Hypothesis SC0 : 0 <= sc0 < 48.

#[using="RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved RC__ mr MR MSL AV0"] Lemma ravz_pre_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 gw : word) F fc,
bv_unsigned gw = G -> mem_inv segs m ->
evt segs (fun ms' =>
ms' = MS (rt1_regs sc0 ra sp gp tp t0 t1 t2 s1 gw (wz 0) a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x128)) fc None m (seg_rom segs))
(MS (rt1_regs sc0 ra sp gp tp t0 t1 t2 s1 gw a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x11c)) fc None m (seg_rom segs)).
Proof. clear - RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved RC__ mr MR MSL AV0 segs base RATP st m g b gh sc0 G f ai act mask st4 st5 Hmem Hgh AI FR32 MW MASK BNC SC0. gw_expose_fam RATP. first [clear SC0 | gw_hide SC0 | idtac]; first [clear BNC | gw_hide BNC | idtac]; first [clear MASK | gw_hide MASK | idtac]; first [clear MW | gw_hide MW | idtac]; first [clear FR32 | gw_hide FR32 | idtac]; first [clear AI | gw_hide AI | idtac]; first [clear Hgh | gw_hide Hgh | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear st5 | gw_hide st5 | idtac]; first [clear st4 | gw_hide st4 | idtac]; first [clear mask | gw_hide mask | idtac]; first [clear act | gw_hide act | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear f | gw_hide f | idtac]; try gw_hide G; first [clear sc0 | gw_hide sc0 | idtac]; first [clear gh | gw_hide gh | idtac]; first [clear b | gw_hide b | idtac]; try gw_hide g; try gw_hide m; try gw_hide st.
intros until fc. intros HG MI. unfold rt1_regs.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
gw_expose_fam RATP.
rmchunk MR MSL CH. fold mr in CH. rewrite AV0 in CH. fold G in CH. rewrite <- HG in CH.
step. step. if_cases K0; zify_cond K0. 2:{ exfalso. apply K0. reflexivity. }
apply evt_done. reflexivity.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved b MR MSL AV0 Hmem Hgh AI FR32 MW MASK BNC SC0"] Lemma ravz_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 gw : word) F fc,
bv_unsigned gw = G -> mem_inv segs m ->
evt segs (fun ms' => exists (a2' a3' a4' a5' a6' a7' : word) m',
ms' = MS (rt1_regs sc0 ra sp gp tp t0 t1 t2 s1 gw (wz (sxv mask)) a2' a3' a4' a5' a6' a7' s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x1a0)) fc None m' (seg_rom segs)
/\ munch [(G, G + 40); ((RATP + 132848), (RATP + 132880))]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rmrep st5 m')
(MS (rt1_regs sc0 ra sp gp tp t0 t1 t2 s1 gw a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x128)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved b MR MSL AV0 Hmem Hgh AI FR32 MW MASK BNC SC0 segs base RATP st m g gh sc0 G mr f ai act mask st4 st5. gw_expose_fam RATP. try gw_hide st5; try gw_hide st4; try gw_hide mask; try gw_hide act; try gw_hide ai; try gw_hide f; try gw_hide mr; try gw_hide G; first [clear sc0 | gw_hide sc0 | idtac]; try gw_hide gh; try gw_hide g; try gw_hide m; try gw_hide st.
intros until fc. intros HG MI. unfold rt1_regs.
pose proof (munch_refl [(G, G + 40); ((RATP + 132848), (RATP + 132880))]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & G4 & G24). fold G in Gpos, GC, GI, G4, G24.
pose proof (meta_word_range _ MW) as MWR.
assert (AMO : amo_aligned AW (Z_to_bv 64 (bv_unsigned gw + 28)) = true).
{ apply amo_aligned_intro; [unfold alloc_ceiling in GC; lia|]. rewrite HG. clear - G4 RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved segs base RATP. Z.div_mod_to_equations. lia. }
clear G4 G24.
(gw_expose_fam RATP; unfold alloc_ceiling in *).
rmchunk MR MSL CH. fold mr in CH. rewrite AV0, Hmem in CH. cbn [oconc] in CH. fold G in CH. rewrite <- HG in CH. fold f in CH.

step.
destruct (rmrep_group_read st _ b gh MR Hgh) as (_ & w8 & RD8 & L8). unfold wa in RD8.
pose proof (bv_unsigned_in_range _ w8) as W8R. change (bv_modulus 8) with 256 in W8R.
step.

step. step.
assert (W8M : bv_unsigned w8 mod 32 = ai).
{ unfold ai. rewrite <- L8. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. }
unfold zxb. rewrite (unsigned_lit (bv_unsigned w8)) by lia.
rewrite (sllw2_word (bv_unsigned w8)) by lia. rewrite W8M.
set (y := 2 ^ (ai + 1)).

step. step. rewrite negw_word.

pose proof (sxv_range f) as RF. pose proof (sxv_range (- y)) as RY. pose proof (sxv_range (y - 1)) as RY1.
step. rewrite sx32_wz_sxv by lia.
step. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite sxv_land.

clear CH. rmeta_open G MUa WMa. rewrite <- HG in MUa.
rmchunk MR MSL CH. fold mr in CH. rewrite AV0, Hmem in CH. cbn [oconc] in CH. fold G in CH. rewrite <- HG in CH. fold f in CH.
amo_step AMO. rewrite ?sx32_wz_sxv by lia.
step. if_false.
amo_step AMO.
step. if_false.
step. rewrite ?sextw_sxv, ?sextw_sxv', ?sextw_sxv0, ?sextw_sxv1. step. if_false.

step. rewrite addiw_m1_word.
step. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite sxv_land.
step.

assert (AI31 : Z.land ai 31 = ai).
{ change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
assert (ACT : act = y - 1) by (unfold act, mask_upto, y; reflexivity).
assert (E1 : Z.land f (- y) = Z.ldiff f (y - 1)) by (unfold y; apply land_neg_pow2; lia).
assert (Ypos : 0 < y) by (unfold y; apply Z.pow_pos_nonneg; lia).
pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)) as R1.
pose proof (ldiff_le f (y - 1) ltac:(lia) ltac:(lia)) as R2.
pose proof (Z.ldiff_nonneg f (y - 1)) as R3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR4 : rmrep st4 mX) end.
{ rewrite HG in MUa, CH. unfold st4. rewrite upd_meta_put, ACT. eapply rmrep_put_meta_frame; [gw_exact MR | gw_exact MSL | gw_exact MUa | gw_exact WMa |].
eapply rw_cells_congr; [ | | | gw_exact CH]; [ | reflexivity | cbn; tauto].
unfold meta_cells, pw. cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail m_set_freed oconc].
rewrite meta_word_upd_af. fold mr f. rewrite Hmem, E1. cbn [oconc]. rewrite !le4_sxv by lia. reflexivity. }
clear MUa WMa.

step. if_cases K1; zify_cond K1.
2:{ exfalso. apply MASK. unfold mask. rewrite ACT. apply (proj1 (sxv_zero (Z.land f (y - 1)) ltac:(lia))).
rewrite ?wz_unsigned in K1 by (apply sxv_range). first [gw_exact K1 | change 18446744073709551615 with (Z.ones 64) in K1; rewrite Z.land_ones in K1 by lia; rewrite Z.mod_small in K1 by apply sxv_range; gw_exact K1]. }
clear K1.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (HRW : ov_read_bytes segs mX (wa (bv_unsigned gw + 32)) 4 = Some (le4 (Z_to_bv 64 (meta_word mr))))
by (destruct CH as [[_ B] _]; rewrite (bytes_at_ov_read segs mX (bv_unsigned gw) _ 32 4 B) by (cbn; lia); reflexivity) end.
step. step. step.
rewrite (lw_slli52_srli58_sc mr MW).
pose proof MW as (_ & _ & SCR & _). fold mr in SCR.
set (sc := m_sizeclass mr) in *.

step. step. step. if_cases K2; zify_cond K2; change 18446744073709551615 with (Z.ones 64) in K2; rewrite Z.land_ones in K2 by lia.
-
assert (NR : (7 <=? sc) && (sc <? 39) = false).
{ destruct (Z.lt_ge_cases sc 7); [apply Bool.andb_false_intro1; apply Z.leb_gt; lia|].
apply Bool.andb_false_intro2. apply Z.ltb_ge. rewrite Z.mod_small in K2 by lia. lia. }
apply evt_done. cbv beta. do 7 eexists. split; [rewrite <- ACT; reflexivity|].
split; [rewrite ?HG in MU; gw_exact MU|]. split; [gw_exact WM|]. split; [assumption|].
unfold st5. rewrite decay_bounces_eq. fold sc. rewrite NR. cbn [andb]. gw_exact MR4.
-
assert (SC7 : 7 <= sc) by (destruct (Z.le_gt_cases 7 sc); [assumption| exfalso; clear - K2 H SCR RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved segs base RATP; Z.div_mod_to_equations; lia]).
rewrite Z.mod_small in K2 by lia.
assert (IR : (7 <=? sc) && (sc <? 39) = true) by (apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).

step.
pose proof (rmrep_bounces_read st4 _ (sc - 7) (wa ((RATP + 132848) + (sc - 7))) MR4 ltac:(lia) eq_refl) as RDB.
change (bounces st4 (sc - 7)) with (bounces st (sc - 7)) in RDB.
pose proof (BNC (sc - 7)) as BR.
step. rewrite ?zxb_b8 by lia.

step. if_cases K3; zify_cond K3; rewrite ?(wz_unsigned (bounces st (sc - 7))), ?unsigned_lit in K3 by lia.
+
apply evt_done. cbv beta. do 7 eexists. split; [rewrite <- ACT; reflexivity|].
split; [rewrite ?HG in MU; gw_exact MU|]. split; [gw_exact WM|]. split; [assumption|].
unfold st5. rewrite decay_bounces_eq. fold sc. rewrite IR. change (bounces st4 (sc - 7)) with (bounces st (sc - 7)).
replace (bounces st (sc - 7) =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb negb]. gw_exact MR4.
+
step. rewrite ?(wz_unsigned (bounces st (sc - 7))) by lia.
pose proof MR4 as (_ & (_ & _ & _ & _ & X5 & _) & _).
pose proof (u8arr_store_ok segs _ _ _ (sc - 7) (Z_to_bv 64 ((RATP + 131960) + (sc + -7) + 888)) X5
ltac:(rewrite bouncess_length; lia) ltac:((gw_expose_fam RATP; unfold wa); f_equal; lia)) as SOK. clear X5 RDB.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_bounce st4 mX (sc - 7) (bounces st (sc - 7) - 1) MR4 ltac:(lia)) as MR5; gw_expose_fam RATP end.
rraw_store_finish0 ((RATP + 132848) + (sc - 7)) [b8 (bounces st (sc - 7) - 1)] MU WM SOK.
apply evt_done. cbv beta. do 7 eexists. split; [rewrite <- ACT; reflexivity|].
split; [rewrite ?HG in MU; gw_exact MU|].
split; [gw_exact WM|]. split; [assumption|].
unfold st5. rewrite decay_bounces_eq. fold sc. rewrite IR. change (bounces st4 (sc - 7)) with (bounces st (sc - 7)).
replace (bounces st (sc - 7) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. gw_exact MR5.
Qed.
End AVZ.

Section SPANLOOP.
Variables (size : Z).
Hypothesis SZ : 16 <= size < 2^20.

#[using="w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE SZ"] Lemma rspan_loop_walk : forall (F : nat) (c span : Z)
(ra sp gp tp t1 t2 s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
0 <= c -> 0 <= span -> span + size * (Z.of_nat F + 2) < 2^31 -> c + 1 + Z.of_nat F < 2^31 ->
span_exit F span size = true -> mem_inv segs m ->
evt segs (fun ms' => exists (t0' t1' a6' : word),
ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 a0 a1 a2 a3 (wz (span_loop F (c + 1) span size)) (wz size) a6' (Z_to_bv 64 4096) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (base + 0x530)) fc None m (seg_rom segs))
(MS (mkR ra sp gp tp (wz span) t1 t2 s0 s1 a0 a1 a2 a3 (wz c) (wz size) (wz (span + size - 1)) (Z_to_bv 64 4096) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (base + 0x51c)) fc None m (seg_rom segs)).
Proof. clear - w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE SZ segs base size. try gw_hide size.
induction F as [|F IH]; intros until m; intros C0 S0 SB CB EX MI; [discriminate|].
cbn [span_exit] in EX. cbn [span_loop].
rewrite Nat2Z.inj_succ in SB, CB.
pose proof (lxor_range31 span (span + size - 1) ltac:(lia) ltac:(lia)) as XR.

step. rewrite ?wz_unsigned by lia.
step. rewrite ?wz_unsigned by lia.
replace (Z_to_bv 64 (bv_swrap 32 (span + size))) with (wz (span + size)) by (rewrite swrap_word, sxv_small by lia; reflexivity).
step. rewrite ?wz_unsigned by lia.
replace (Z_to_bv 64 (bv_swrap 32 (c + 1))) with (wz (c + 1)) by (rewrite swrap_word, sxv_small by lia; reflexivity).
step. rewrite ?wz_unsigned by lia.
replace (Z_to_bv 64 (bv_swrap 32 (span + size - 1 + size))) with (wz (span + size + size - 1)) by (rewrite swrap_word, sxv_small by lia; unfold wz; f_equal; lia).
rewrite (Z.lxor_comm (span + size - 1) span).

step. if_cases K.
-
assert (LT : Z.lxor span (span + size - 1) < 4096).
{ unfold bv_lts, wz in K. rewrite !signed_wz_small in K by lia. apply Z.ltb_lt in K. gw_exact K. }
replace (Z.lxor span (span + size - 1) <? 4096) with true in EX |- * by (symmetry; apply Z.ltb_lt; gw_exact LT).
replace (c + 2) with (c + 1 + 1) by lia.
eapply (IH (c + 1) (span + size)); try assumption; try lia.
- assert (GE : ~ Z.lxor span (span + size - 1) < 4096).
{ intros LT. unfold bv_lts, wz in K. rewrite !signed_wz_small in K by lia. apply Z.ltb_ge in K. lia. }
replace (Z.lxor span (span + size - 1) <? 4096) with false by (symmetry; apply Z.ltb_ge; lia).
apply evt_done. do 3 eexists. reflexivity.
Qed.
End SPANLOOP.
#[using="Type"] Lemma ai_byte_land224 w v : 0 <= w -> 0 <= v ->
Z.land ((Z.lor (Z.land v 31) (Z.land w 224)) mod 256) 31 = Z.land v 31.
Proof. clear - w v.
intros Hw Hv. apply Z.bits_inj'. intros n Hn.
change 256 with (2^8). change 31 with (Z.ones 5).
rewrite !Z.land_spec, Z.testbit_mod_pow2, Z.lor_spec, !Z.land_spec, !Z.testbit_ones by lia.
replace 224 with (Z.shiftl 7 5) by first [reflexivity | (cbn; lia)].
destruct (Z.ltb_spec n 5).
- rewrite Z.shiftl_spec_low by lia. replace (n <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia). cbn [andb]. rewrite !andb_true_r, andb_false_r, orb_false_r. reflexivity.
- replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia). cbn [andb]. rewrite !andb_false_r. reflexivity.
Qed.

Section ACT.
Variables (st : mstate) (m : mem) (g b : aptr) (gh : ghdr) (sc mask : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let ai0 := g_active_idx gh.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hgh : (s_groups st) !! b = Some gh.
Hypothesis AI0 : 0 <= ai0 <= 31.
Hypothesis MASKR : 0 <= mask < 2^32.

Ltac ract_prefix CH w8 :=
rmchunk MR MSL CH; fold mr G in CH; fold G in CH; rewrite Hmem in CH; cbn [oconc] in CH;
step;
let RD8 := fresh "RD8" in let L8 := fresh "L8" in
destruct (rmrep_group_read st _ b gh MR Hgh) as (_ & w8 & RD8 & L8); unfold wa in RD8;
let W8R := fresh "W8R" in
pose proof (bv_unsigned_in_range _ w8) as W8R; change (bv_modulus 8) with 256 in W8R;
step;
let W8M := fresh "W8M" in
assert (W8M : bv_unsigned w8 mod 32 = ai0) by (unfold ai0; rewrite <- L8; change 31 with (Z.ones 5); rewrite Z.land_ones by lia; reflexivity);
step; unfold zxb; rewrite (unsigned_lit (bv_unsigned w8)) by lia; rewrite (sllw2_word (bv_unsigned w8)) by lia; rewrite W8M;
step; rewrite addiw_m1_word; change (2 ^ (ai0 + 1) - 1) with (mask_upto ai0);
step; rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range); rewrite sxv_land.

#[using="RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved RC__ b mr MR MSL Hmem Hgh AI0 MASKR"] Lemma ract_skip_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc,
Z.land mask (mask_upto ai0) <> 0 -> mem_inv segs m ->
evt segs (fun ms' => exists (a1' a2' a3' a4' : word),
ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1' a2' a3' a4' a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (base + 0x11c)) fc None m (seg_rom segs))
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 (wz (sxv mask)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (base + 0xf4)) fc None m (seg_rom segs)).
Proof. clear - RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved RC__ b mr MR MSL Hmem Hgh AI0 MASKR segs base RATP st m g gh sc mask G ai0 SC. gw_expose_fam RATP. first [clear SC | gw_hide SC | idtac]; try gw_hide ai0; try gw_hide G; try gw_hide mask; first [clear sc | gw_hide sc | idtac]; try gw_hide gh; try gw_hide g; try gw_hide m; try gw_hide st.
intros until fc. intros NZ MI. unfold rt1_regs.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
pose proof (rgroup_bounds st m b gh MR Hgh) as (B0 & BC & BI & _).
pose proof (sxv_range mask) as RM. pose proof (sxv_range (mask_upto ai0)) as RU.
gw_expose_fam RATP.
ract_prefix CH w8.
pose proof (QDUx.Mqb.mask_upto_range ai0 AI0) as MUR.
pose proof (land_upper (mask_upto ai0) mask ltac:(lia) ltac:(lia)) as LR.
step. if_cases K; zify_cond K.
2:{ exfalso. apply NZ. rewrite Z.land_comm. apply (proj1 (sxv_zero (Z.land (mask_upto ai0) mask) ltac:(lia))).
rewrite ?wz_unsigned in K by (apply sxv_range).
first [gw_exact K | change 18446744073709551615 with (Z.ones 64) in K; rewrite Z.land_ones in K by lia; rewrite Z.mod_small in K by apply sxv_range; gw_exact K]. }
apply evt_done. do 4 eexists. reflexivity.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved b MR MSL SC Hmem Hgh AI0"] Lemma ract_next_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (mn : aptr),
Z.land mask (mask_upto ai0) = 0 -> m_next mr = Some mn -> mn <> g -> meta_slot st mn -> mem_inv segs m ->
evt segs (fun ms' => exists (a1' a2' a3' a4' : word) m',
ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st mn)) a1' a2' a3' a4' a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (base + 0x11c)) fc None m' (seg_rom segs)
/\ munch [((RATP + 132048) + 8 * sc, (RATP + 132048) + 8 * sc + 8)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rmrep (set_active sc (Some mn) st) m')
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 (wz (sxv mask)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (base + 0xf4)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved b MR MSL SC Hmem Hgh AI0 segs base RATP st m g gh sc mask G mr ai0 MASKR. gw_expose_fam RATP. first [clear MASKR | gw_hide MASKR | idtac]; try gw_hide ai0; first [clear mr | gw_hide mr | idtac]; try gw_hide G; try gw_hide mask; try gw_hide sc; try gw_hide gh; try gw_hide g; try gw_hide m; try gw_hide st.
intros until mn. intros ZR GN NEn MSn MI. unfold rt1_regs.
pose proof (munch_refl [((RATP + 132048) + 8 * sc, (RATP + 132048) + 8 * sc + 8)]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
pose proof (rmeta_slot_bounds st m mn MR MSn) as (Npos & NC & NI & _ & _).
pose proof (rgroup_bounds st m b gh MR Hgh) as (B0 & BC & BI & _).
assert (NEG : conc st mn <> G) by (intros E; apply NEn; eapply rconc_meta_inj; [gw_exact MR| gw_exact MSL| gw_exact MSn| gw_exact E]).
pose proof (sxv_range mask) as RM. pose proof (sxv_range (mask_upto ai0)) as RU.
gw_expose_fam RATP.
ract_prefix CH w8.
pose proof (QDUx.Mqb.mask_upto_range ai0 AI0) as MUR.
step. if_cases K; zify_cond K.
{ exfalso. apply K. rewrite (Z.land_comm (mask_upto ai0) mask), ZR. reflexivity. }
clear K.

rewrite GN in CH. cbn [oconc] in CH.
step.

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. apply NEG. gw_exact K. } clear K.

clear CH.
pose proof MR as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok segs _ _ (actives st) sc (Z_to_bv 64 ((RATP + 132048) + 8 * sc)) ACTS
ltac:(rewrite actives_length; lia) ltac:((gw_expose_fam RATP; unfold wa); f_equal; lia)) as SOK. clear ACTS.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st mX sc (Some mn) MR SC) as MR2; gw_expose_fam RATP end.
rraw_store_finish0 ((RATP + 132048) + 8 * sc) (le8 (pw st (Some mn))) MU WM SOK.

step.
apply evt_done. do 5 eexists. split; [reflexivity|].
split; [gw_exact MU|]. split; [gw_exact WM|]. split; [assumption| gw_exact MR2].
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 ROM_reservedZ LAY_ref_reserved ai0 MR MSL Hgh AI0"] Lemma rspan_tail_walk :
forall (ra sp gp tp t0 t1 t2 s1 a3 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (cnt2 wv : Z),
1 <= cnt2 <= 32 -> 0 <= wv < 256 ->
(forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
g_meta gh = Some g -> m_avail mr = 0 -> mem_inv segs m ->
evt segs (fun ms' => exists (a1' a2' a4' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 G) a1' a2' a3 a4' a5 a6 a7 s2 s3 (Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 ((RATP + 132048) + 8 * sc))
(Z_to_bv 64 (RATP + 131960)) (Z_to_bv 64 ((RATP + 131960) + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (base + 0x128)) fc None m' (seg_rom segs)
/\ munch [(conc st b, conc st b + 9)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rmrep (set_group_active_idx b (cnt2 - 1) st) m')
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 G) (Z_to_bv 64 (conc st b)) (Z_to_bv 64 wv) a3 (Z_to_bv 64 cnt2) a5 a6 a7 s2 s3 (Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 ((RATP + 132048) + 8 * sc))
(Z_to_bv 64 (RATP + 131960)) (Z_to_bv 64 ((RATP + 131960) + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (base + 0x540)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 ROM_reservedZ LAY_ref_reserved ai0 MR MSL Hgh AI0 segs base RATP st m g b gh sc mask G mr SC Hmem MASKR. gw_expose_fam RATP. first [clear MASKR | gw_hide MASKR | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear SC | gw_hide SC | idtac]; try gw_hide mr; try gw_hide G; first [clear mask | gw_hide mask | idtac]; first [clear sc | gw_hide sc | idtac]; try gw_hide gh; try gw_hide b; try gw_hide g; try gw_hide m; try gw_hide st.
intros until wv. intros C2R WVR UNK GM AV0 MI.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
pose proof (rgroup_bounds st m b gh MR Hgh) as (B0 & BC & BI & _).
pose proof MR as (_ & _ & _ & _ & GR & _). destruct (GR b gh Hgh) as (w8o & RWB & Hw8o). clear GR.
gw_expose_fam RATP.
pose proof (munch_refl [(conc st b, conc st b + 9)]%Z m) as MUb. pose proof (wmono_refl segs m) as WMb.

step. step. rewrite ?(unsigned_lit (cnt2 + -1)) by lia. step. rewrite ?(unsigned_lit wv) by lia. step.
pose proof (land_upper (cnt2 + -1) 31 ltac:(lia) ltac:(lia)) as L2.
pose proof (land_upper wv 224 ltac:(lia) ltac:(lia)) as L1.
rewrite ?(unsigned_lit (Z.land (cnt2 + -1) 31)), ?(unsigned_lit (Z.land wv 224)) by lia.
set (nbv := Z.lor _ _).

step. rewrite (le1_mod nbv). mem_after_store.
pose proof (Z.lor_nonneg (Z.land (cnt2 + -1) 31) (Z.land wv 224)) as NBpos.
pose proof (Z.mod_pos_bound nbv 256 ltac:(lia)) as NBR.
lazymatch goal with H : rw_cells segs ?mX (conc st b) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep (set_group_active_idx b (cnt2 - 1) st) mX);
[ eapply (rmrep_set_group_ai st m mX b g (g_active_idx gh) (cnt2 - 1) (b8 (nbv mod 256)) MR); [ | gw_exact UNK | gw_exact MUb | gw_exact WMb | | ]
| ] end.
{ rewrite Hgh. destruct gh as [gm gai]. cbn in GM |- *. subst gm. reflexivity. }
{ lazymatch goal with H : rw_cells segs _ (conc st b) _ |- _ => rewrite GM in H; exact H end. }
{ rewrite b8_unsigned by lia. subst nbv. replace (cnt2 - 1) with (cnt2 + -1) by lia. apply ai_byte_land224; lia. }

assert (EA2 : s_areas (set_group_active_idx b (cnt2 - 1) st) = s_areas st) by (unfold set_group_active_idx; destruct (get_group st b); reflexivity).
assert (ER2 : s_regions (set_group_active_idx b (cnt2 - 1) st) = s_regions st) by (unfold set_group_active_idx; destruct (get_group st b); reflexivity).
assert (EM2 : s_metas (set_group_active_idx b (cnt2 - 1) st) = s_metas st) by (unfold set_group_active_idx; destruct (get_group st b); reflexivity).
assert (MS2 : meta_slot (set_group_active_idx b (cnt2 - 1) st) g) by (eapply meta_slot_same_areas; [gw_exact EA2| gw_exact MSL]).
rmchunk MR2 MS2 CH.
replace (get_meta_rec (set_group_active_idx b (cnt2 - 1) st) g) with mr in CH by (unfold mr, get_meta_rec; rewrite EM2; reflexivity).
replace (conc (set_group_active_idx b (cnt2 - 1) st) g) with G in CH by (unfold G, conc, get_region; rewrite ER2; reflexivity).
rewrite AV0 in CH.
step. step. if_cases K2; zify_cond K2. { exfalso. apply K2. reflexivity. } step.
apply evt_done. do 4 eexists. split; [reflexivity|]. split; [gw_exact MUb|]. split; [gw_exact WMb|]. split; [assumption| gw_exact MR2].
Qed.

#[using="RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_311 lo_313 CODE D_311 E_311 D_313 E_313 ANCH_313 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved MR MSL Hmem Hgh AI0"] Lemma ract_span_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc,
Z.land mask (mask_upto ai0) = 0 -> m_next mr = Some g -> mw_ok mr -> 1 <= m_sizeclass mr < 48 ->
(forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
g_meta gh = Some g -> m_avail mr = 0 ->
mem_inv segs m ->
let sc' := m_sizeclass mr in
let cnt := ai0 + 2 in
let size := size_class sc' * UNIT in
let span := UNIT + size * cnt in
let cnt1 := span_loop 300 cnt span size in
let cnt2 := if m_last_idx mr + 1 <? cnt1 then m_last_idx mr + 1 else cnt1 in
evt segs (fun ms' => exists (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word) m',
ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 G) a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 ((RATP + 132048) + 8 * sc))
(Z_to_bv 64 (RATP + 131960)) (Z_to_bv 64 ((RATP + 131960) + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (base + 0x128)) fc None m' (seg_rom segs)
/\ munch [(conc st b, conc st b + 9)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rmrep (set_group_active_idx b (cnt2 - 1) st) m')
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 (wz (sxv mask)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (base + 0xf4)) fc None m (seg_rom segs)).
Proof. clear - RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_311 lo_313 CODE D_311 E_311 D_313 E_313 ANCH_313 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved MR MSL Hmem Hgh AI0 segs base RATP st m g b gh sc mask G mr ai0 SC MASKR. gw_expose_fam RATP; gw_expose_fam RDEBRUIJN. first [clear MASKR | gw_hide MASKR | idtac]; first [clear SC | gw_hide SC | idtac]; try gw_hide ai0; try gw_hide mr; try gw_hide G; try gw_hide mask; first [clear sc | gw_hide sc | idtac]; try gw_hide gh; try gw_hide b; try gw_hide g; try gw_hide m; try gw_hide st.
intros until fc. intros ZR GN MW SCR UNK GM AV0 MI sc' cnt size span cnt1 cnt2. unfold rt1_regs.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
pose proof (rgroup_bounds st m b gh MR Hgh) as (B0 & BC & BI & _).
pose proof (sxv_range mask) as RM. pose proof (sxv_range (mask_upto ai0)) as RU.
pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & _ & ML).
pose proof (size_class_range sc' ltac:(lia)) as SZR.
(gw_expose_fam RATP; gw_expose_fam RDEBRUIJN).
ract_prefix CH w8.
pose proof (QDUx.Mqb.mask_upto_range ai0 AI0) as MUR.
step. if_cases K; zify_cond K.
{ exfalso. apply K. rewrite (Z.land_comm (mask_upto ai0) mask), ZR. reflexivity. }
clear K.

rewrite GN, AV0 in CH. cbn [oconc] in CH. fold G in CH.
step.

step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.

step. rewrite (unsigned_lit (bv_unsigned w8)) by lia. rewrite L8. fold ai0. step. step. step. step.

assert (W5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64).
{ rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
step. rewrite ?(unsigned_lit (meta_word mr)) by lia. step. rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite (meta_word_sc2 mr MW). fold sc'.
step.
lazymatch goal with HI : mem_inv segs ?mc |- _ =>
pose proof (rsize_classes_read mc sc' HI ltac:(lia)) as SCRD; gw_expose_fam RDEBRUIJN end.
step. rewrite zx16_wz by lia. clear SCRD.
fold cnt.
assert (SZB : 16 <= size <= 131240) by (unfold size, UNIT; lia).
assert (CNB : 2 <= cnt <= 33) by (unfold cnt; lia).
assert (PR : 0 <= cnt * size <= 33 * 131240) by nia.
assert (EX : span_exit 300 span size = true) by (unfold span, size, cnt, UNIT; apply span_exit_ok; lia).
assert (SPB : span = cnt * size + 16) by (unfold span, UNIT; lia).
assert (Esz : size = size_class sc' * 16) by first [reflexivity | (cbn; lia)]. assert (Ecnt : cnt = ai0 + 2) by first [reflexivity | (cbn; lia)].
pose proof (span_loop_bounds 300 cnt span size) as CB. fold cnt1 in CB. change (Z.of_nat 300) with 300 in CB.
assert (Ec2 : cnt2 = (if m_last_idx mr + 1 <? cnt1 then m_last_idx mr + 1 else cnt1)) by first [reflexivity | (cbn; lia)].
assert (Ec1 : cnt1 = span_loop 300 cnt span size) by first [reflexivity | (cbn; lia)].
clearbody size cnt span cnt1 cnt2.

step. step. rewrite (unsigned_lit ai0), (Z.shiftl_mul_pow2 ai0) by lia. step.
step. rewrite (wz_unsigned (size_class sc')), (Z.shiftl_mul_pow2 (size_class sc')) by lia. change (2 ^ 4) with 16. rewrite <- Esz.

step. rewrite ?(unsigned_lit (ai0 * 16 + 48)), ?(wz_unsigned (size_class sc')) by lia.
replace ((ai0 * 16 + 48) * size_class sc') with (span + size - 16) by (rewrite SPB, Esz, Ecnt; lia).
step. rewrite ?(unsigned_lit size), ?(unsigned_lit cnt) by lia. replace (size * cnt) with (cnt * size) by lia.
step. rewrite ?(unsigned_lit (span + size - 16)) by lia. rewrite swrap_word, sxv_small by lia.
replace (span + size - 16 + 15) with (span + size - 1) by lia.
step. rewrite ?(unsigned_lit (cnt * size)) by lia. rewrite swrap_word, sxv_small by lia. rewrite <- SPB.
step.

eapply evt_cut.
{ change (Z_to_bv 64 (ai0 + 1)) with (wz (ai0 + 1)). change (Z_to_bv 64 size) with (wz size).
eapply (rspan_loop_walk size ltac:(lia) 300 (ai0 + 1) span); try assumption; try (change (Z.of_nat 300) with 300; lia). }
intros ms' (t0' & t1' & a6' & ->). replace (ai0 + 1 + 1) with cnt by lia. rewrite <- Ec1.

step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (meta_word_last_idx mr MW).
step.

step. if_cases K; zify_cond K; rewrite ?(wz_unsigned cnt1), ?unsigned_lit in K by lia.
- replace (wz cnt1) with (Z_to_bv 64 cnt2) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); [lia| reflexivity]).
assert (C2R : 1 <= cnt2 <= 32) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); lia). clear K.
eapply evt_mono. { eapply (rspan_tail_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc cnt2 (bv_unsigned w8)); [lia| lia| gw_exact UNK| gw_exact GM| gw_exact AV0| assumption]. }
cbv beta. intros ms2 (a1'' & a2'' & a4'' & m' & -> & MU & WM & MI' & MR'). do 10 eexists. split; [reflexivity|]. eauto.
-
step.
replace (Z_to_bv 64 (m_last_idx mr + 1)) with (Z_to_bv 64 cnt2) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); [reflexivity| f_equal; lia]).
assert (C2R : 1 <= cnt2 <= 32) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); lia). clear K.
eapply evt_mono. { eapply (rspan_tail_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc cnt2 (bv_unsigned w8)); [lia| lia| gw_exact UNK| gw_exact GM| gw_exact AV0| assumption]. }
cbv beta. intros ms2 (a1'' & a2'' & a4'' & m' & -> & MU & WM & MI' & MR'). do 10 eexists. split; [reflexivity|]. eauto.
Qed.
End ACT.

End RC__1.

End G.
End Mq8.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlQE QFkE QBeb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.

Import QWTl.Mq5.
Import QVbl.Mq3.
Import Q2qa.Mq1 QytA QlQE QFkE Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 Qy5Y.Mq6 QPjm.Mq2 QPjm.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.

Import QJE4.Mq0 QJE4.Mq1 QDUx.Mq3 QWTl.Mq1 QWTl.Mq2 QWTl.Mq3 QDUx.Mq2 Q9Ay.Mq9 QXxF QBeb Q6y7.Mq1.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QkTt.Mq3.
Import QkTt.Mq4.
Import Q8QT.Mq2.
Import Qy8Z.Mqa.
Import Qy8Z.Mq9.
Import QQRC.Mq5.
Import Qy8Z.Mq2.
Import QQRC.Mq6.
Import Q8l1.Mq5.
Import Q8l1.Mq6.
Import Q8l1.Mq7.
Import QROt.
Import QROt.Mq4.
Import QZxv.
Import Q8l1.
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
Variables (rerrno_loc_entry rsysret_entry rvm_wait_entry : Z).
Variables (w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 : Z).
Variables (hi_7 hi_10 hi_14 : bv 20).
Variables (lo_8 lo_12 lo_15 : bv 12).
Variables (joff_30 joff_98 joff_120 joff_173 joff_175 joff_181 : bv 21).
Variables (e_197bc e_24f80 : Z).
Hypothesis CODE : code_at segs base (alloc_meta_code w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 728.
Let ralloc_meta_entry := (base + 0)%Z.
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
Hypothesis LINK_98 : gw_anch (base + 392 + bv_signed joff_98)%Z (rvm_wait_entry + 4)%Z.
Hypothesis LINK_120 : gw_anch (base + 480 + bv_signed joff_120)%Z (rvm_wait_entry + 4)%Z.
Hypothesis LINK_173 : gw_anch (base + 692 + bv_signed joff_173)%Z (rvm_wait_entry + 240)%Z.
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
Hypothesis AL_rsysret_entry : gw_al rsysret_entry 4.
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rmprotect_post : ltac:(gw_rebind_ty (@Q8QT.Mq2.rmprotect_post segs RATP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q8QT.Mq2.rmprotect_post segs RATP) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@Q8QT.Mq2.rmprotect_post segs RATP) (@rmprotect_post) gw_tbl_0).
Definition rmmap_anon_post : ltac:(gw_rebind_ty (@Q8QT.Mq2.rmmap_anon_post segs RC__) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq2.rmmap_anon_post segs RC__) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@Q8QT.Mq2.rmmap_anon_post segs RC__) (@rmmap_anon_post) gw_tbl_1).
Definition rmmap_fixed_post : ltac:(gw_rebind_ty (@Q8QT.Mq2.rmmap_fixed_post segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq2.rmmap_fixed_post segs) constr:(gw_tbl_2)).
#[global] Arguments rmmap_fixed_post {X}%_type_scope R%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F fc%_bv_scope A%_Z_scope L%_Z_scope errv%_bv_scope lo%_Z_scope m%_function_scope a _.
Notation gw_tbl_3 := (gw_ent (@Q8QT.Mq2.rmmap_fixed_post segs) (@rmmap_fixed_post) gw_tbl_2).
Definition ralloc_fp : ltac:(gw_rebind_ty (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QQRC.Mq5.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QCa8.Mq5.ralloc_fp RATP) (@ralloc_fp) gw_tbl_3)).
Definition rauxv_ok : ltac:(gw_rebind_ty (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@Q8l1.Mq7.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QCa8.Mq5.rauxv_ok segs RATP RC__) (@rauxv_ok) gw_tbl_4)).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QZxv.rarea_rep segs) (@rarea_rep) (gw_ent (@QROt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QROt.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8l1.Mq7.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8l1.Mq6.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8l1.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq6.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq9.rarea_rep segs) (@rarea_rep) gw_tbl_5)))))))))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QZxv.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QROt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QROt.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8l1.Mq7.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8l1.Mq6.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8l1.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq6.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq9.rmrep_areas segs) (@rmrep_areas) gw_tbl_6)))))))))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QZxv.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QROt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QROt.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8l1.Mq7.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8l1.Mq6.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8l1.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq6.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_7)))))))))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QZxv.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QROt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QROt.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8l1.Mq7.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8l1.Mq6.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8l1.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq6.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_8)))))))))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QZxv.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QROt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QROt.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8l1.Mq7.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8l1.Mq6.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8l1.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq6.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq9.rgroup_rep segs) (@rgroup_rep) gw_tbl_9)))))))))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QZxv.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QROt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QROt.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8l1.Mq7.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8l1.Mq6.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8l1.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq6.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq9.rmrep_groups segs) (@rmrep_groups) gw_tbl_10)))))))))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@QZxv.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QROt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QROt.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8l1.Mq7.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8l1.Mq6.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8l1.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq6.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq9.rshadow_rep segs) (@rshadow_rep) gw_tbl_11)))))))))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@QZxv.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QROt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QROt.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8l1.Mq7.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8l1.Mq6.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8l1.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq6.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq9.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_12)))))))))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@QZxv.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QROt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QROt.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8l1.Mq7.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8l1.Mq6.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8l1.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq6.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_13)))))))))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_14)).
Notation gw_tbl_15 := (gw_ent (@QZxv.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QROt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QROt.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8l1.Mq7.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8l1.Mq6.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8l1.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq6.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_14)))))))))))))))).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_15)).
Notation gw_tbl_16 := (gw_ent (@QROt.Mq4.rpres_except segs) (@rpres_except) (gw_ent (@QROt.rpres_except segs) (@rpres_except) (gw_ent (@Q8l1.Mq6.rpres_except segs) (@rpres_except) (gw_ent (@Q8l1.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QQRC.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq3.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq9.rpres_except segs) (@rpres_except) gw_tbl_15))))))))).
Definition ram_post : ltac:(gw_rebind_ty (@QCa8.Mq5.ram_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ram_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_16)).
Notation gw_tbl_17 := (gw_ent (@QCa8.Mq5.ram_post segs RATP RGOT_SSP ref_reserved RC__) (@ram_post) gw_tbl_16).
Definition rimplT : ltac:(gw_rebind_ty (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_17)).
#[global] Arguments rimplT {R}%_type_scope o t s Q%_function_scope ms.
Notation gw_tbl_18 := (gw_ent (@QkTt.Mq3.rimplT segs RC__) (@rimplT) (gw_ent (@QCa8.Mq5.rimplT segs RC__) (@rimplT) gw_tbl_17)).
Definition ralloc_meta_stmt : ltac:(gw_rebind_ty (@QCa8.Mq5.ralloc_meta_stmt segs RATP RGOT_SSP ref_reserved ralloc_meta_entry RC__) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ralloc_meta_stmt segs RATP RGOT_SSP ref_reserved ralloc_meta_entry RC__) constr:(gw_tbl_18)).
Notation gw_tbl_19 := (gw_ent (@QCa8.Mq5.ralloc_meta_stmt segs RATP RGOT_SSP ref_reserved ralloc_meta_entry RC__) (@ralloc_meta_stmt) gw_tbl_18).
Definition rrepfoot : ltac:(gw_rebind_ty (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) constr:(gw_tbl_19)).
Notation gw_tbl_20 := (gw_ent (@Q8l1.Mq5.rrepfoot RATP RGOT_SSP) (@rrepfoot) (gw_ent (@Qy8Z.Mq2.rrepfoot RATP RGOT_SSP) (@rrepfoot) (gw_ent (@QkTt.Mq4.rrepfoot RATP RGOT_SSP) (@rrepfoot) (gw_ent (@QkTt.Mq3.rrepfoot RATP RGOT_SSP) (@rrepfoot) (gw_ent (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) (@rrepfoot) gw_tbl_19))))).
Definition ram_frame : ltac:(gw_rebind_ty (@QQRC.Mq5.ram_frame RC__) constr:(gw_tbl_20)) := ltac:(gw_rebind_tm (@QQRC.Mq5.ram_frame RC__) constr:(gw_tbl_20)).
Notation gw_tbl_21 := (gw_ent (@QROt.Mq4.ram_frame RC__) (@ram_frame) (gw_ent (@QROt.ram_frame RC__) (@ram_frame) (gw_ent (@Q8l1.Mq7.ram_frame RC__) (@ram_frame) (gw_ent (@Q8l1.Mq6.ram_frame RC__) (@ram_frame) (gw_ent (@Q8l1.Mq5.ram_frame RC__) (@ram_frame) (gw_ent (@QQRC.Mq5.ram_frame RC__) (@ram_frame) gw_tbl_20)))))).
Definition ram_entry_post : ltac:(gw_rebind_ty (@Q8l1.Mq7.ram_entry_post segs base RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_21)) := ltac:(gw_rebind_tm (@Q8l1.Mq7.ram_entry_post segs base RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_21)).
Notation gw_tbl_22 := (gw_ent (@Q8l1.Mq7.ram_entry_post segs base RATP RGOT_SSP ref_reserved RC__) (@ram_entry_post) gw_tbl_21).
Definition memcpy_post : ltac:(gw_rebind_ty (@QVbl.Mq3.memcpy_post segs) constr:(gw_tbl_22)) := ltac:(gw_rebind_tm (@QVbl.Mq3.memcpy_post segs) constr:(gw_tbl_22)).
Notation gw_tbl_23 := (gw_ent (@Q8l1.Mq7.memcpy_post segs) (@memcpy_post) (gw_ent (@QVbl.Mq3.memcpy_post segs) (@memcpy_post) gw_tbl_22)).
Definition ram_fp : ltac:(gw_rebind_ty (@QQRC.Mq5.ram_fp RATP) constr:(gw_tbl_23)) := ltac:(gw_rebind_tm (@QQRC.Mq5.ram_fp RATP) constr:(gw_tbl_23)).
Notation gw_tbl_24 := (gw_ent (@QROt.Mq4.ram_fp RATP) (@ram_fp) (gw_ent (@QROt.ram_fp RATP) (@ram_fp) (gw_ent (@Q8l1.Mq6.ram_fp RATP) (@ram_fp) (gw_ent (@Q8l1.Mq5.ram_fp RATP) (@ram_fp) (gw_ent (@QQRC.Mq5.ram_fp RATP) (@ram_fp) gw_tbl_23))))).
Definition ram_ret_post : ltac:(gw_rebind_ty (@QQRC.Mq5.ram_ret_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_24)) := ltac:(gw_rebind_tm (@QQRC.Mq5.ram_ret_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_24)).
Notation gw_tbl_25 := (gw_ent (@QROt.Mq4.ram_ret_post segs RATP RGOT_SSP ref_reserved RC__) (@ram_ret_post) (gw_ent (@QROt.ram_ret_post segs RATP RGOT_SSP ref_reserved RC__) (@ram_ret_post) (gw_ent (@Q8l1.Mq6.ram_ret_post segs RATP RGOT_SSP ref_reserved RC__) (@ram_ret_post) (gw_ent (@Q8l1.Mq5.ram_ret_post segs RATP RGOT_SSP ref_reserved RC__) (@ram_ret_post) (gw_ent (@QQRC.Mq5.ram_ret_post segs RATP RGOT_SSP ref_reserved RC__) (@ram_ret_post) gw_tbl_24))))).

Hypothesis rmprotect_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q8QT.Mq2.gw_all) (@Q8QT.Mq2.rmprotect_spec) rvm_wait_entry)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_25))) in exact T).
Hypothesis rmmap_anon_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q8QT.Mq2.gw_all) (@Q8QT.Mq2.rmmap_anon_spec) rvm_wait_entry)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_25))) in exact T).
Hypothesis rmmap_fixed_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q8QT.Mq2.gw_all) (@Q8QT.Mq2.rmmap_fixed_spec) rvm_wait_entry)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_25))) in exact T).
Arguments rmmap_fixed_spec {X}%_type_scope dec%_function_scope R%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope t0%_bv_scope t1%_bv_scope t2%_bv_scope s0%_bv_scope s1%_bv_scope a0%_bv_scope a1%_bv_scope a2%_bv_scope a3%_bv_scope a4%_bv_scope a5%_bv_scope a6%_bv_scope a7%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope t3%_bv_scope t4%_bv_scope t5%_bv_scope t6%_bv_scope F fc%_bv_scope m%_function_scope A%_Z_scope L%_Z_scope P%_Z_scope errv%_bv_scope lo%_Z_scope _%_function_scope _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
Hypothesis rconc_meta_inj : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQRC.Mq9.gw_all) (@QQRC.Mq9.rconc_meta_inj) (base + -984)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_25))) in let T := gw_fold_pcs T base (-984)%Z [0; 356; 740; 896; 936]%Z in exact T).
Hypothesis memcpy_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq3.memcpy_spec segs e_24f80) 3%nat in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_25))) in exact T).

Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).
Definition rreserved_disjoint : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint)).
Definition rreserved_disjoint1 : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint1) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint1)).
Definition rarea_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_conc) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_conc)).
Definition rgroup_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rgroup_conc) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rgroup_conc)).

Definition rimplT_undef : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_undef) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_undef)).
#[global] Arguments rimplT_undef {R}%_type_scope o w k%_function_scope s Q%_function_scope ms.
Definition rimplT_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_evt) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_evt)).
#[global] Arguments rimplT_evt {R}%_type_scope o t s Q%_function_scope P%_function_scope ms _ _%_function_scope.
Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rimplT_mmap_none : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_mmap_none) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_mmap_none)).
#[global] Arguments rimplT_mmap_none {R}%_type_scope o len%_Z_scope k%_function_scope s P%_function_scope Q%_function_scope ms _ _%_function_scope.
Definition rimplT_mmap_fixed : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_mmap_fixed) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_mmap_fixed)).
#[global] Arguments rimplT_mmap_fixed {R}%_type_scope o addr%_Z_scope len%_Z_scope k%_function_scope s P%_function_scope Q%_function_scope ms _ _%_function_scope.
Definition rimplT_mprotect : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_mprotect) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_mprotect)).
#[global] Arguments rimplT_mprotect {R}%_type_scope o addr%_Z_scope len%_Z_scope prot%_Z_scope k%_function_scope s P%_function_scope Q%_function_scope ms _ _%_function_scope.
Definition rimplT_brk0 : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_brk0) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_brk0)).
#[global] Arguments rimplT_brk0 {R}%_type_scope o k%_function_scope s P%_function_scope Q%_function_scope ms _ _%_function_scope.
Definition rimplT_brk : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_brk) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_brk)).
#[global] Arguments rimplT_brk {R}%_type_scope o req%_Z_scope k%_function_scope s P%_function_scope Q%_function_scope ms _ _ _%_function_scope.
Definition rpres_except_refl : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_refl) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_refl)).
Definition rfresh_image : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rfresh_image) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rfresh_image)).

Definition rrepfoot_area : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rrepfoot_area) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rrepfoot_area)).
Definition rmrep_transport_unowned : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_transport_unowned) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_transport_unowned)).
Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmrep_ctx_frameW : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_ctx_frameW) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_ctx_frameW)).

Definition rwview_ext : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq3.rwview_ext) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq3.rwview_ext)).
Definition rmrep_transport_agree' : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq3.rmrep_transport_agree') constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq3.rmrep_transport_agree')).

Definition rbytes_at_agree : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mqa.rbytes_at_agree) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mqa.rbytes_at_agree)).
Definition rwr_at_agree : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mqa.rwr_at_agree) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mqa.rwr_at_agree)).
Definition rrw_cells_agree : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mqa.rrw_cells_agree) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mqa.rrw_cells_agree)).
Definition rmrep_new_region : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mqa.rmrep_new_region) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mqa.rmrep_new_region)).

Definition ram_fp_alloc_fp : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq5.ram_fp_alloc_fp) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq5.ram_fp_alloc_fp)).
Definition ram_fp_not_errno : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq5.ram_fp_not_errno) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq5.ram_fp_not_errno)).
Definition ram_fp_same : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq5.ram_fp_same) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq5.ram_fp_same)).

Definition rrw_cells_of_zeros : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mq2.rrw_cells_of_zeros) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mq2.rrw_cells_of_zeros)).
Definition rfresh_page_avoids : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mq2.rfresh_page_avoids) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mq2.rfresh_page_avoids)).

Definition rmrep_agree_but_ctx : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq6.rmrep_agree_but_ctx) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq6.rmrep_agree_but_ctx)).
Definition rmrep_ctx_mid_agree : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq6.rmrep_ctx_mid_agree) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq6.rmrep_ctx_mid_agree)).
Definition rarea_in_live : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq6.rarea_in_live) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq6.rarea_in_live)).
Definition rgroup_in_live : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq6.rgroup_in_live) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq6.rgroup_in_live)).
Definition rimage_clear_of_ranges_free : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq6.rimage_clear_of_ranges_free) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq6.rimage_clear_of_ranges_free)).
Definition rmrep_grow_region : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq6.rmrep_grow_region) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq6.rmrep_grow_region)).
Definition rimpl_enode_dec_weaken : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq6.rimpl_enode_dec_weaken) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq6.rimpl_enode_dec_weaken)).
#[global] Arguments rimpl_enode_dec_weaken {A}%_type_scope n dec%_function_scope dec'%_function_scope G%_function_scope P%_function_scope ms _ _%_function_scope.

Definition ram_carve_walk : ltac:(gw_ctx_fold_ty2 (@Q8l1.Mq5.ram_carve_walk) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@Q8l1.Mq5.ram_carve_walk)).

Definition ram_deq : ltac:(gw_ctx_fold_ty2 (@Q8l1.Mq6.ram_deq) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@Q8l1.Mq6.ram_deq)).
Definition ram_take_walk : ltac:(gw_ctx_fold_ty2 (@Q8l1.Mq6.ram_take_walk) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@Q8l1.Mq6.ram_take_walk)).
Definition ram_disp0 : ltac:(gw_ctx_fold_ty2 (@Q8l1.Mq6.ram_disp0) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@Q8l1.Mq6.ram_disp0)).

Definition ram_entry : ltac:(gw_ctx_fold_ty2 (@Q8l1.Mq7.ram_entry) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@Q8l1.Mq7.ram_entry)).

Definition ram_disp_fin : ltac:(gw_ctx_fold_ty2 (@QROt.ram_disp_fin) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QROt.ram_disp_fin)).
Definition ram_to_mprotect : ltac:(gw_ctx_fold_ty2 (@QROt.ram_to_mprotect) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QROt.ram_to_mprotect)).
Definition ram_mp_ok0 : ltac:(gw_ctx_fold_ty2 (@QROt.ram_mp_ok0) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QROt.ram_mp_ok0)).
Definition ram_mp_fail : ltac:(gw_ctx_fold_ty2 (@QROt.ram_mp_fail) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QROt.ram_mp_fail)).

Definition ram_disp_dead : ltac:(gw_ctx_fold_ty2 (@QROt.Mq4.ram_disp_dead) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QROt.Mq4.ram_disp_dead)).
Definition ram_to_mmap : ltac:(gw_ctx_fold_ty2 (@QROt.Mq4.ram_to_mmap) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QROt.Mq4.ram_to_mmap)).
Definition ram_mm_fail : ltac:(gw_ctx_fold_ty2 (@QROt.Mq4.ram_mm_fail) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QROt.Mq4.ram_mm_fail)).
Definition ram_mm_ok : ltac:(gw_ctx_fold_ty2 (@QROt.Mq4.ram_mm_ok) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QROt.Mq4.ram_mm_ok)).

Definition ram_disp_untried : ltac:(gw_ctx_fold_ty2 (@QZxv.ram_disp_untried) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QZxv.ram_disp_untried)).
Definition ram_disp_live : ltac:(gw_ctx_fold_ty2 (@QZxv.ram_disp_live) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QZxv.ram_disp_live)).
Definition ram_brk0_node : ltac:(gw_ctx_fold_ty2 (@QZxv.ram_brk0_node) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QZxv.ram_brk0_node)).
Definition ram_brk_node_at : ltac:(gw_ctx_fold_ty2 (@QZxv.ram_brk_node_at) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QZxv.ram_brk_node_at)).
Definition ram_bu_mid : ltac:(gw_ctx_fold_ty2 (@QZxv.ram_bu_mid) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QZxv.ram_bu_mid)).
Definition ram_bu_ok : ltac:(gw_ctx_fold_ty2 (@QZxv.ram_bu_ok) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QZxv.ram_bu_ok)).
Definition ram_b_store : ltac:(gw_ctx_fold_ty2 (@QZxv.ram_b_store) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QZxv.ram_b_store)).
Definition ram_bl_ok : ltac:(gw_ctx_fold_ty2 (@QZxv.ram_bl_ok) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QZxv.ram_bl_ok)).
Definition ram_bl_fail : ltac:(gw_ctx_fold_ty2 (@QZxv.ram_bl_fail) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QZxv.ram_bl_fail)).
Definition ram_bu_fail : ltac:(gw_ctx_fold_ty2 (@QZxv.ram_bu_fail) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@QZxv.ram_bu_fail)).

Definition rAMpre_init : ltac:(gw_ctx_fold_ty2 (@Q8l1.rAMpre_init) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@Q8l1.rAMpre_init)).
Definition rAMI_init : ltac:(gw_ctx_fold_ty2 (@Q8l1.rAMI_init) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm2 (@Q8l1.rAMI_init)).
Notation RAMpre := (@AMpre_g ref_reserved rc_secret).
Notation ram_pre := (am_pre_g ref_reserved rc_secret).

Notation RMallocKit_A2__rbytes_at_agree := rbytes_at_agree (only parsing).
Notation RMallocKit_A2__rmrep_new_region := rmrep_new_region (only parsing).
Notation RMallocKit_A2__rrw_cells_agree := rrw_cells_agree (only parsing).
Notation RMallocKit_A2__rwr_at_agree := rwr_at_agree (only parsing).

#[using="RGOT_SSP rerrno_loc_entry e_197bc rsysret_entry rvm_wait_entry rmmap_entry rmprotect_entry e_24f80 RATP RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_7 E_7 D_8 E_8 D_10 E_10 D_12 E_12 D_14 E_14 D_15 E_15 D_30 E_30 D_98 E_98 D_120 E_120 D_173 E_173 D_175 E_175 D_181 E_181 ANCH_8 ANCH_12 ANCH_15 LINK_30 LINK_98 LINK_120 LINK_173 LINK_175 LINK_181 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rsysret_entry AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ ralloc_meta_entry rmmap_entry rmprotect_entry rmprotect_spec rmmap_anon_spec rmmap_fixed_spec rconc_meta_inj memcpy_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := first [clear - hs segs base w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 hi_7 hi_10 hi_14 lo_8 lo_12 lo_15 joff_30 joff_98 joff_120 joff_173 joff_175 joff_181 RGOT_SSP rerrno_loc_entry e_197bc rsysret_entry rvm_wait_entry rmmap_entry rmprotect_entry e_24f80 RATP RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_7 E_7 D_8 E_8 D_10 E_10 D_12 E_12 D_14 E_14 D_15 E_15 D_30 E_30 D_98 E_98 D_120 E_120 D_173 E_173 D_175 E_175 D_181 E_181 ANCH_8 ANCH_12 ANCH_15 LINK_30 LINK_98 LINK_120 LINK_173 LINK_175 LINK_181 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rsysret_entry AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ ralloc_meta_entry rmprotect_spec rmmap_anon_spec rmmap_fixed_spec rconc_meta_inj memcpy_spec | clear - hs segs base w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 hi_7 hi_10 hi_14 lo_8 lo_12 lo_15 joff_30 joff_98 joff_120 joff_173 joff_175 joff_181 RGOT_SSP rerrno_loc_entry e_197bc rsysret_entry rvm_wait_entry rmmap_entry rmprotect_entry e_24f80 RATP RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_7 E_7 D_8 E_8 D_10 E_10 D_12 E_12 D_14 E_14 D_15 E_15 D_30 E_30 D_98 E_98 D_120 E_120 D_173 E_173 D_175 E_175 D_181 E_181 ANCH_8 ANCH_12 ANCH_15 LINK_30 LINK_98 LINK_120 LINK_173 LINK_175 LINK_181 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rsysret_entry AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay ralloc_meta_entry rmprotect_spec rmmap_anon_spec rmmap_fixed_spec rconc_meta_inj memcpy_spec].

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

#[using="Type"] Lemma rmagree_of_pres C m m' : rpres_except C m m' -> magree C m m'.
Proof. clear - C m m'. intros P a Ha Hc. exact (proj1 (P a Ha Hc)). Qed.
#[using="Type"] Lemma rpres_of_magree C m m' : magree C m m' -> rpres_except C m m'.
Proof. clear - C m m'. intros A a Ha Hc. split; [exact (A a Ha Hc)|]. rewrite (rwview_ext m m' (wa a) (A a Ha Hc)). auto. Qed.

#[using="base rvm_wait_entry ralloc_meta_entry rmmap_entry rmprotect_entry"] Lemma rrw_cells_magree C m m' A cs :
rw_cells segs m A cs -> magree C m m' -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ~ C a) -> rw_cells segs m' A cs.
Proof. clear - base rvm_wait_entry ralloc_meta_entry rmmap_entry rmprotect_entry segs C m m' A cs.
intros H AG HC. pose proof (rw_cells_bound _ _ _ _ H). eapply RMallocKit_A2__rrw_cells_agree; [gw_exact H|]. intros a Ha. apply AG; [lia| apply HC; gw_exact Ha].
Qed.
#[using="base rvm_wait_entry ralloc_meta_entry rmmap_entry rmprotect_entry"] Lemma rbytes_at_magree C m m' A bs :
bytes_at segs m A bs -> magree C m m' -> (forall a, A <= a < A + Z.of_nat (length bs) -> ~ C a) -> bytes_at segs m' A bs.
Proof. clear - base rvm_wait_entry ralloc_meta_entry rmmap_entry rmprotect_entry segs C m m' A bs.
intros H AG HC. pose proof (bytes_at_bound _ _ _ _ H). eapply RMallocKit_A2__rbytes_at_agree; [gw_exact H|]. intros a Ha. apply AG; [lia| apply HC; gw_exact Ha].
Qed.
#[using="base rvm_wait_entry ralloc_meta_entry rmmap_entry rmprotect_entry"] Lemma rwr_at_magree C m m' A n :
wr_at segs m A n -> magree C m m' -> (forall a, A <= a < A + n -> ~ C a) -> 0 <= A -> A + n <= 2^64 -> wr_at segs m' A n.
Proof. clear - base rvm_wait_entry ralloc_meta_entry rmmap_entry rmprotect_entry segs C m m' A n. intros H AG HC H0 H1. eapply RMallocKit_A2__rwr_at_agree; [gw_exact H|]. intros a Ha. apply AG; [lia| apply HC; gw_exact Ha]. Qed.

#[using="base rvm_wait_entry ralloc_meta_entry rmmap_entry rmprotect_entry"] Lemma rauxv_ok_magree C m m' B :
rauxv_ok m B -> magree C m m' -> (forall a, C a -> a < B /\ ~ ((RATP + 131736) <= a < (RATP + 131744))) -> rauxv_ok m' B.
Proof. clear - base rvm_wait_entry ralloc_meta_entry rmmap_entry rmprotect_entry RATP C m m' B. gw_expose_fam RATP.
intros (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & AC & AL & RN & H) AG HC.
exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. split; [|split; [|split; [|gw_exact H]]].
- eapply rrw_cells_magree; [gw_exact AC| gw_exact AG|]. cbn. intros a Ha X. destruct (HC a X) as [_ Y]. apply Y. gw_exact Ha.
- eapply rbytes_at_magree; [gw_exact AL| gw_exact AG|]. intros a Ha X. destruct (HC a X) as [Y _].
unfold rauxv_list in Ha. rewrite u64s_length, map_length in Ha. cbn in Ha. lia.
- eapply rbytes_at_magree; [gw_exact RN| gw_exact AG|]. intros a Ha X. destruct (HC a X) as [Y _]. rewrite length_le8 in Ha. lia.
Qed.

Section ASM.
Variables (R : Type) (k : mstate -> optr -> QUZl.M R) (bail : QUZl.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word).
Hypothesis AMP : RAMpre st.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk segs m lo (bv_unsigned sp).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - RAM_STACK.
Hypothesis ERR : rw_cells segs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv segs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis KH : forall st1 mo s' ms',
ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
brk_link_ps st1 s' ->
rimplT o (k st1 mo) s' Q ms'.

Definition rFP (stX : mstate) (a : Z) : Prop := ralloc_fp (fun k => k <> RKGroup) stX lo (bv_unsigned sp) a \/ fresh_addr st a.

#[using="RNG_RATP"] Lemma rFP_am stX a : ram_fp stX lo (bv_unsigned sp) a -> rFP stX a.
Proof. clear - RNG_RATP stX a R k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st lo errv AMP MR TK BL AUX ST LO LOLE ERR MI TP KH. first [clear KH | gw_hide KH | idtac]; first [clear TP | gw_hide TP | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear LOLE | gw_hide LOLE | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear AMP | gw_hide AMP | idtac]; first [clear errv | gw_hide errv | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear st | gw_hide st | idtac]; first [clear m | gw_hide m | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear R | gw_hide R | idtac]. intros H. left. apply ram_fp_alloc_fp. gw_exact H. Qed.

#[using="base rvm_wait_entry RNG_RATP ralloc_meta_entry rmmap_entry rmprotect_entry RC__ TP"] Lemma rETP : errno_addr tp = RATP - 164.
Proof. clear - base rvm_wait_entry RNG_RATP ralloc_meta_entry rmmap_entry rmprotect_entry RC__ TP RATP R k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st lo errv AMP MR TK BL AUX ST LO LOLE ERR MI KH. gw_expose_fam RATP. first [clear KH | gw_hide KH | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear LOLE | gw_hide LOLE | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear AMP | gw_hide AMP | idtac]; first [clear errv | gw_hide errv | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear st | gw_hide st | idtac]; first [clear m | gw_hide m | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear R | gw_hide R | idtac]. rewrite TP, unsigned_lit by lia. reflexivity. Qed.

#[using="TK KH"] Lemma rfinish_K : forall (st1 : mstate) (mo : optr) (sX : PState) (m' : mem) (e : word)
(t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rv : word),
am_rel st st1 mo -> rmrep st1 m' -> mem_inv segs m' -> stk segs m' lo (bv_unsigned sp) ->
rw_cells segs m' (errno_addr tp) [C4 e] -> rauxv_ok m' (bv_unsigned sp) -> magree (rFP st1) m m' ->
brk_link_ps st1 sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
rv = pw st1 mo -> (mo = None -> e = Z_to_bv 64 12) ->
rimplT o (k st1 mo) sX Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom segs)).
Proof. clear - TK KH segs R k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st lo errv AMP MR BL AUX ST LO LOLE ERR MI TP. first [clear TP | gw_hide TP | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear LOLE | gw_hide LOLE | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear AMP | gw_hide AMP | idtac]; first [clear errv | gw_hide errv | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear st | gw_hide st | idtac]; first [clear m | gw_hide m | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear R | gw_hide R | idtac].
intros st1 mo sX m' e t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rv REL MR1 MI1 ST1 ERR1 AUX1 AG BL1 P1 P2 P3 -> E12.
apply KH; [| gw_exact BL1]. unfold ram_post. do 16 eexists. split; [reflexivity|].
split; [gw_exact MI1|]. split; [gw_exact ST1|]. split; [gw_exact ERR1|]. split; [gw_exact AUX1|]. split.
{ apply rpres_of_magree. gw_exact AG. }
split; [gw_exact MR1|]. split.
{ destruct TK as [T1 T2]. split; intros; rewrite (amr_shadow _ _ _ REL) in *; rewrite (amr_tick _ _ _ REL); eauto. }
repeat (split; [auto|]). gw_exact E12.
Qed.

#[using="base rvm_wait_entry ralloc_meta_entry rmmap_entry rmprotect_entry"] Lemma rFP_mono stX stY a :
(forall rid r, (s_regions stX) !! rid = Some r -> exists r', (s_regions stY) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
rFP stX a -> rFP stY a.
Proof. clear - base rvm_wait_entry ralloc_meta_entry rmmap_entry rmprotect_entry stX stY a R k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st lo errv AMP MR TK BL AUX ST LO LOLE ERR MI TP KH. first [clear KH | gw_hide KH | idtac]; first [clear TP | gw_hide TP | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear LOLE | gw_hide LOLE | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear AMP | gw_hide AMP | idtac]; first [clear errv | gw_hide errv | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear st | gw_hide st | idtac]; first [clear m | gw_hide m | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear R | gw_hide R | idtac].
intros HR [[X|[X|[X|(rid & r & Hr & K & X)]]]|X]; [left; left; gw_exact X| left; right; left; gw_exact X| left; right; right; left; gw_exact X| | right; gw_exact X].
destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L'). left. right. right. right. exists rid, r'. split; [gw_exact Hr'|]. split; [rewrite K'; gw_exact K|].
assert (RU : round_up_pg (r_len r) <= round_up_pg (r_len r')).
{ unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite !Z.land_ones by lia. Z.div_mod_to_equations. lia. }
unfold lr_lo in *. rewrite K', B'. lia.
Qed.

#[using="base rvm_wait_entry ralloc_meta_entry rmmap_entry rmprotect_entry"] Lemma rFP_same stX stY a : s_regions stY = s_regions stX -> rFP stX a -> rFP stY a.
Proof. clear - base rvm_wait_entry ralloc_meta_entry rmmap_entry rmprotect_entry stX stY a R k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st lo errv AMP MR TK BL AUX ST LO LOLE ERR MI TP KH. first [clear KH | gw_hide KH | idtac]; first [clear TP | gw_hide TP | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear LOLE | gw_hide LOLE | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear AMP | gw_hide AMP | idtac]; first [clear errv | gw_hide errv | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear st | gw_hide st | idtac]; first [clear m | gw_hide m | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear R | gw_hide R | idtac]. intros E. apply rFP_mono. intros rid r Hr. exists r. rewrite E. repeat split; auto; lia. Qed.

#[using="base RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved ralloc_meta_entry rmmap_entry rmprotect_entry AMP LO LOLE"] Lemma rFP_below stX a : rregions_wf stX -> rFP stX a -> a < bv_unsigned sp /\ ~ ((RATP + 131736) <= a < (RATP + 131744)).
Proof. clear - base RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved ralloc_meta_entry rmmap_entry rmprotect_entry AMP LO LOLE RATP stX a R k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st lo errv MR TK BL AUX ST ERR MI TP KH. gw_expose_fam RATP. first [clear KH | gw_hide KH | idtac]; try gw_hide TP; first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear errv | gw_hide errv | idtac]; first [clear lo | gw_hide lo | idtac]; try gw_hide st; first [clear m | gw_hide m | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear R | gw_hide R | idtac].
intros (_ & WR & _) [[X|[X|[X|(rid & r & Hr & K & X)]]]|X]; rewrite ?TP in X; (gw_expose_fam RATP; unfold RAM_STACK, alloc_ceiling in *);
rewrite ?unsigned_lit in X by lia; [lia| lia| lia| |].
- destruct (WR _ _ Hr) as (_ & _ & _ & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). pose proof (lr_lo_ge r). unfold alloc_ceiling in RBC. lia.
- pose proof (rfresh_image st a X (amp_reserved st AMP)). destruct X as [C _]. unfold alloc_ceiling in C. lia.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_win_2 LAY_win_4 LAY_ref_reserved LO TP"] Lemma rerrno_not_amfp stX a : rregions_wf stX -> ram_fp stX lo (bv_unsigned sp) a -> ~ (errno_addr tp <= a < errno_addr tp + 4).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_win_2 LAY_win_4 LAY_ref_reserved LO TP stX a R k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st lo errv AMP MR TK BL AUX ST LOLE ERR MI KH. first [clear KH | gw_hide KH | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear LOLE | gw_hide LOLE | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear AMP | gw_hide AMP | idtac]; first [clear errv | gw_hide errv | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear st | gw_hide st | idtac]; first [clear m | gw_hide m | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear R | gw_hide R | idtac]. intros WF X. rewrite TP. eapply ram_fp_not_errno; [gw_exact X| gw_exact WF| gw_exact LO]. Qed.

#[using="Type"] Lemma rbrk_am_took X q c : c_brk (ctx (am_took X q c)) = c_brk (ctx X). Proof. clear - X q c R k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st lo errv AMP MR TK BL AUX ST LO LOLE ERR MI TP KH. first [clear KH | gw_hide KH | idtac]; first [clear TP | gw_hide TP | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear LOLE | gw_hide LOLE | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear AMP | gw_hide AMP | idtac]; first [clear errv | gw_hide errv | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear st | gw_hide st | idtac]; first [clear m | gw_hide m | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear R | gw_hide R | idtac]. reflexivity. Qed.

#[using="Type"] Lemma ram_take_took {RR} (Xst : mstate) (pp : aptr) (kk : mstate -> optr -> QUZl.M RR) (bl : QUZl.M RR) :
am_take (upd_ctx (fun c => set_avail_meta (Some (aadd pp AREA_HDR)) (set_avail_meta_count NSLOTS c)) Xst) kk bl
= kk (am_took Xst (aadd pp AREA_HDR) 100) (Some (aadd pp AREA_HDR)).
Proof. clear - RR Xst pp kk bl R k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st lo errv AMP MR TK BL AUX ST LO LOLE ERR MI TP KH. first [clear KH | gw_hide KH | idtac]; first [clear TP | gw_hide TP | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear LOLE | gw_hide LOLE | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear AMP | gw_hide AMP | idtac]; first [clear errv | gw_hide errv | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear st | gw_hide st | idtac]; first [clear m | gw_hide m | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear R | gw_hide R | idtac]. reflexivity. Qed.
#[using="Type"] Lemma rconc_am_took X q c y : conc (am_took X q c) y = conc X y. Proof. clear - X q c y R k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st lo errv AMP MR TK BL AUX ST LO LOLE ERR MI TP KH. first [clear KH | gw_hide KH | idtac]; first [clear TP | gw_hide TP | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear LOLE | gw_hide LOLE | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear AMP | gw_hide AMP | idtac]; first [clear errv | gw_hide errv | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear st | gw_hide st | idtac]; first [clear m | gw_hide m | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear R | gw_hide R | idtac]. reflexivity. Qed.
#[using="Type"] Lemma rbrk_carve stY p : c_brk (ctx (carve_st stY p)) = c_brk (ctx stY).
Proof. clear - stY p R k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st lo errv AMP MR TK BL AUX ST LO LOLE ERR MI TP KH. first [clear KH | gw_hide KH | idtac]; first [clear TP | gw_hide TP | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear LOLE | gw_hide LOLE | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear AMP | gw_hide AMP | idtac]; first [clear errv | gw_hide errv | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear st | gw_hide st | idtac]; first [clear m | gw_hide m | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear R | gw_hide R | idtac].
unfold carve_st. cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail].
destruct (c_meta_area_tail (s_ctx stY)); reflexivity.
Qed.
#[using="Type"] Lemma rconc_carve stY p y : conc (carve_st stY p) y = conc stY y.
Proof. clear - stY p y R k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st lo errv AMP MR TK BL AUX ST LO LOLE ERR MI TP KH. first [clear KH | gw_hide KH | idtac]; first [clear TP | gw_hide TP | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear LOLE | gw_hide LOLE | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear AMP | gw_hide AMP | idtac]; first [clear errv | gw_hide errv | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear st | gw_hide st | idtac]; first [clear m | gw_hide m | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear R | gw_hide R | idtac]. unfold conc, get_region. rewrite carve_st_regions. reflexivity. Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ralloc_meta_entry rmmap_entry rmprotect_entry AMP TK LO LOLE TP KH"] Lemma rcarve_K : forall (stY : mstate) (p : aptr) (r : region) (mX : mem) (sX : PState) (junk : list byte) (e : word)
(x1 t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
AMI st stY ->
(s_regions stY) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
pgal (snd p) -> lr_lo r <= r_base r + snd p ->
(s_areas stY) !! p = None -> (forall j, 0 <= j < NSLOTS -> (s_metas stY) !! (aadd p (AREA_HDR + META_SIZE * j)) = None) ->
(forall tl, c_meta_area_tail (ctx stY) = Some tl -> is_Some ((s_areas stY) !! tl)) ->
1 <= c_avail_meta_area_count (ctx stY) < 2^64 ->
rmrep stY mX -> mem_inv segs mX -> bytes_at segs mX (conc stY p) (zeros 4096) -> wr_at segs mX (conc stY p) 4096 ->
rw_cells segs mX (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk segs mX lo (bv_unsigned sp + -64) ->
rw_cells segs mX (errno_addr tp) [C4 e] -> rauxv_ok mX (bv_unsigned sp) -> magree (rFP stY) m mX ->
brk_link_ps stY sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
rimplT o (k (am_took (carve_st stY p) (aadd p AREA_HDR) 100) (Some (aadd p AREA_HDR))) sX Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0x (Z_to_bv 64 (conc stY p)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x218)) fc None mX (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ralloc_meta_entry rmmap_entry rmprotect_entry AMP TK LO LOLE TP KH segs base RATP R k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st lo errv MR BL AUX ST ERR MI. gw_expose_fam RATP. first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear errv | gw_hide errv | idtac]; try gw_hide lo; try gw_hide st; first [clear m | gw_hide m | idtac]; try gw_hide fc; try gw_hide F; try gw_hide s11; try gw_hide s10; try gw_hide s9; try gw_hide s8; try gw_hide s7; try gw_hide s6; try gw_hide s5; try gw_hide s4; try gw_hide s3; try gw_hide s2; try gw_hide s1; try gw_hide s0; try gw_hide tp; try gw_hide gp; try gw_hide sp; try gw_hide ra; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear R | gw_hide R | idtac].
intros until t6. intros AI Hr NK S0 S1 SAL SLR ANone FRESH TL CNT MRX MIX ZB ZW FRX STX ERRX AUXX AGX BLX P1 P2 P3.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof MRX as (WFX & _).
eapply rimplT_evt.
{ eapply (ram_carve_walk sp gp tp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra s0 s1 s2 s3 s4 F fc mX junk lo stY p r);
first [gw_exact MRX | gw_exact MIX | gw_exact Hr | gw_exact NK | gw_exact S0 | gw_exact S1 | gw_exact SAL | gw_exact SLR | gw_exact ANone | gw_exact FRESH | gw_exact TL | gw_exact CNT
| exact (ami_secretr _ _ AI) | gw_exact ZB | gw_exact ZW | gw_exact FRX | gw_exact STX | gw_exact LO | lia]. }
intros ms2 RP. unfold ram_ret_post in RP.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m2 & -> & PE2 & WM2 & MI2 & ST2 & MR2).
pose proof (carve_st_regions stY p) as RC.
eapply rfinish_K.
- eapply (ram_rel_carve st stY p r AI); assumption.
- gw_exact MR2.
- gw_exact MI2.
- gw_exact ST2.
- eapply rrw_cells_magree; [gw_exact ERRX| apply rmagree_of_pres; gw_exact PE2|]. cbn. intros a Ha X.
apply (rerrno_not_amfp stY a WFX); [exact (proj1 (ram_fp_same stY _ lo _ a RC) X) | lia].
- eapply rauxv_ok_magree; [gw_exact AUXX| apply rmagree_of_pres; gw_exact PE2|]. intros a X. apply (rFP_below stY _ WFX). apply rFP_am. exact (proj1 (ram_fp_same stY _ lo _ a RC) X).
- assert (RA : s_regions (am_took (carve_st stY p) (aadd p AREA_HDR) 100) = s_regions stY) by (cbn; gw_exact RC).
eapply magree_trans; [gw_exact AGX| apply rmagree_of_pres; gw_exact PE2| intros a X; exact (rFP_same stY _ a RA X) | intros a X; apply rFP_am; refine (proj2 (ram_fp_same (carve_st stY p) _ lo _ a _) X); reflexivity].
- unfold brk_link_ps in *. rewrite rbrk_am_took, rbrk_carve. destruct (c_brk (ctx stY)) as [| |rid off]; auto.
rewrite rconc_am_took, rconc_carve. gw_exact BLX.
- gw_exact P1.
- gw_exact P2.
- gw_exact P3.
- unfold pw, oconc, wz. rewrite rconc_am_took, rconc_carve. rewrite (conc_aadd stY p AREA_HDR) by (rewrite Hr; eauto). reflexivity.
- intros X; discriminate X.
Qed.

#[using="base RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved ralloc_meta_entry rmmap_entry rmprotect_entry TP"] Lemma rrepfoot_low stY a : rregions_wf stY -> rrepfoot stY a -> a < alloc_ceiling /\ ~ (errno_addr tp <= a < errno_addr tp + 4).
Proof. clear - base RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved ralloc_meta_entry rmmap_entry rmprotect_entry TP stY a RATP RGOT_SSP R k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st lo errv AMP MR TK BL AUX ST LO LOLE ERR MI KH. gw_expose_fam RATP; gw_expose_fam RGOT_SSP. first [clear KH | gw_hide KH | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear LOLE | gw_hide LOLE | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear AMP | gw_hide AMP | idtac]; first [clear errv | gw_hide errv | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear st | gw_hide st | idtac]; first [clear m | gw_hide m | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear R | gw_hide R | idtac].
intros WF H. rewrite rETP. pose proof WF as (_ & WR & _ & WA & WG). unfold alloc_ceiling.
destruct H as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]; (gw_expose_fam RATP; gw_expose_fam RGOT_SSP); try lia.
- destruct C as (ak & ar & Hak & Hin). destruct (rarea_conc stY ak ar WF Hak) as (rra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & RB0 & RBAL & RBC).
destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). unfold alloc_ceiling in RBC. lia.
- destruct C as (b & gh & Hb & Hin). destruct (rgroup_conc stY b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & Al & RB0 & RBC).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). unfold alloc_ceiling in RBC. lia.
- destruct C as (rid & rg & v & Hrg & Krg & Hin & _). destruct (WR _ _ Hrg) as (_ & _ & _ & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). unfold alloc_ceiling in RBC. lia.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rerrno_loc_entry rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 joff_173 joff_175 CODE BASE4 BASER D_173 E_173 D_175 E_175 LINK_173 LINK_175 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmprotect_spec ralloc_meta_entry rmmap_entry rmprotect_entry AMP KH LO LOLE TK TP"] Lemma rfinish_path : forall (stY : mstate) (p : aptr) (r : region) (mX : mem) (sX : PState) (junk : list byte) (e : word)
(x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
AMI st stY -> c_avail_meta_areas (ctx stY) = Some p ->
(s_regions stY) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
pgal (snd p) -> lr_lo r <= r_base r + snd p ->
(s_areas stY) !! p = None -> (forall j, 0 <= j < NSLOTS -> (s_metas stY) !! (aadd p (AREA_HDR + META_SIZE * j)) = None) ->
(forall tl, c_meta_area_tail (ctx stY) = Some tl -> is_Some ((s_areas stY) !! tl)) ->
1 <= c_avail_meta_area_count (ctx stY) < 2^64 ->
rmrep stY mX -> mem_inv segs mX ->
rw_cells segs mX (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk segs mX lo (bv_unsigned sp + -64) ->
rw_cells segs mX (errno_addr tp) [C4 e] -> rauxv_ok mX (bv_unsigned sp) -> magree (rFP stY) m mX ->
brk_link_ps stY sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
rimplT o (am_finish stY true k bail) sX Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc stY p)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x2a8)) fc None mX (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rerrno_loc_entry rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 joff_173 joff_175 CODE BASE4 BASER D_173 E_173 D_175 E_175 LINK_173 LINK_175 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmprotect_spec ralloc_meta_entry rmmap_entry rmprotect_entry AMP KH LO LOLE TK TP segs base RATP R k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st lo errv MR BL AUX ST ERR MI. gw_expose_fam RATP. first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear MR | gw_hide MR | idtac]; try gw_hide errv; try gw_hide lo; try gw_hide st; try gw_hide m; try gw_hide fc; try gw_hide F; try gw_hide s11; try gw_hide s10; try gw_hide s9; try gw_hide s8; try gw_hide s7; try gw_hide s6; try gw_hide s5; try gw_hide s4; try gw_hide s3; try gw_hide s2; try gw_hide s1; try gw_hide s0; try gw_hide tp; try gw_hide gp; try gw_hide sp; try gw_hide ra; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; try gw_hide o; try gw_hide bail; try gw_hide k; first [clear R | gw_hide R | idtac].
intros until t6. intros AI AMA Hr NK S0 S1 SAL SLR ANone FRESH TL CNT MRX MIX FRX STX ERRX AUXX AGX BLX P1 P2 P3.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof LO as LO'. unfold alloc_ceiling in LO'.
pose proof MRX as (WFX & _ & (_ & _ & PGX & _) & _). pose proof WFX as (RS & WR & DJ & WA & WG).
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). unfold alloc_ceiling in RBC.
pose proof (conc_region' stY p r Hr) as Cp. pose proof (round_up_pg_ge (r_len r)) as RU. pose proof (lr_lo_ge r) as LRG.
assert (PAL : conc stY p mod 4096 = 0) by (rewrite Cp; unfold pgal in SAL; clear - RBAL SAL RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rerrno_loc_entry rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 joff_173 joff_175 CODE BASE4 BASER D_173 E_173 D_175 E_175 LINK_173 LINK_175 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmprotect_spec ralloc_meta_entry rmmap_entry rmprotect_entry segs base RATP; Z.div_mod_to_equations; lia).
assert (IMG : conc stY p + 4096 <= 0x10000 \/ RIMG_HI <= conc stY p) by (pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)); lia).
pose proof rETP as rETP'. pose proof TP as TPv. unfold wz in PGX.

unfold am_finish. rewrite AMA. unfold pgal in SAL. unfold PGSZ at 1. rewrite (proj2 (Z.eqb_eq _ _) SAL). cbn [negb].

eapply rimplT_evt.
{ apply (ram_to_mprotect (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc mX (conc stY p)). }
intros ms2 ->.
eapply (rimplT_mprotect o (conc stY p) PGSZ PROT_RW _ sX).
{ eapply rimpl_enode_dec_weaken; [| intros rsp a Hd; exact (dec_mprotect_rw_weaken _ _ rsp a Hd)].
unfold PGSZ, PROT_RW.
eapply rmprotect_spec with (lo := lo) (errv := e);
[ rewrite unsigned_lit by lia; gw_exact STX | gw_exact ERRX | gw_exact PGX | gw_exact MIX | reflexivity | reflexivity | reflexivity
| gw_exact PAL | reflexivity | lia | lia | lia | lia | ..]; rewrite ?rETP', ?TPv, ?unsigned_lit by lia; gw_expose_fam RATP; try lia. }
intros ans ms3 [MP G]. unfold rmprotect_post in MP.
destruct MP as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m3 & -> & MU3 & WM3 & MI3 & ST3 & ERR3 & PG3 & CASE).
rewrite unsigned_lit in MU3, ST3 by lia.
try g_ret_pc_any.

assert (FR3 : rw_cells segs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
{ eapply rw_cells_transport; [gw_exact FRX| gw_exact MU3| gw_exact WM3|]. rewrite rETP'. cbn. unfold alloc_ceiling in LO. lia. }
assert (MR3 : rmrep stY m3).
{ eapply rmrep_transport_unowned; [gw_exact MRX| gw_exact MU3| gw_exact WM3|].
intros lo' hi' y [E|[E|[E|[]]]] Hy; inversion E; subst lo' hi'.
- intros RFt. destruct (rrepfoot_low stY y WFX RFt). unfold alloc_ceiling in *. lia.
- intros RFt. destruct (rrepfoot_low stY y WFX RFt). lia.
- eapply (rfresh_page_avoids stY mX p r y MRX); try assumption; lia. }
assert (M23 : magree (rFP stY) mX m3).
{ eapply magree_of_munch; [gw_exact MU3|].
cbn. split; [| split; [| split; [| exact I]]]; intros x Hx.
- left. left. lia.
- left. right. left. rewrite TPv in Hx. gw_exact Hx.
- left. right. right. right. exists (fst p), r. split; [gw_exact Hr|]. split; [gw_exact NK|]. lia. }
assert (AG3 : magree (rFP stY) m m3) by (eapply magree_trans; [gw_exact AGX| gw_exact M23| intros a X; gw_exact X| intros a X; gw_exact X]).
assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)) by (eapply rauxv_ok_magree; [gw_exact AUXX| gw_exact M23| intros a X; exact (rFP_below stY a WFX X)]).
clear MU3 WM3.
destruct ans as [e'|b]; cbn in G.
-
cbn [range_val Q9A7.Mq0.munmap_ret Q9A7.Mq0.rg_errno] in *.
unfold mprotect_answer_ok, is_errno_form, neg_errno, TWO64, ENOSYS.
replace ((2 ^ 64 - e' =? 0) || ((2 ^ 64 - 4095 <=? 2 ^ 64 - e') && (2 ^ 64 - e' <? 2 ^ 64))) with true by (symmetry; apply orb_true_iff; right; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
replace ((2 ^ 64 - e' =? 0) || (2 ^ 64 - e' =? 2 ^ 64 - 38)) with false by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; lia).
cbn [negb].
eapply rimplT_evt.
{ eapply (ram_mp_fail sp gp tp u0 u1 u2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc stY p)) u3 u4 u5 u6 u7 u8 u9 s4x s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 _ ra s0 s1 s2 s3 s4 F fc m3 m3 junk lo e' stY);
first [gw_exact MR3 | gw_exact MI3 | gw_exact TPv | gw_exact ERR3 | gw_exact G | apply rpres_except_refl | apply wmono_refl | gw_exact FR3 | gw_exact ST3 | gw_exact LO | lia]. }
intros ms4 [RP ERR4]. unfold ram_ret_post in RP. cbn [ms_mem] in ERR4.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m4 & EQ & PE4 & WM4 & MI4 & ST4 & MR4).
rewrite EQ in ERR4 |- *. cbn [ms_mem] in ERR4.
eapply rfinish_K.
+ apply (ram_rel_none st stY AI).
+ gw_exact MR4.
+ gw_exact MI4.
+ gw_exact ST4.
+ gw_exact ERR4.
+ eapply rauxv_ok_magree; [gw_exact AUX3| apply rmagree_of_pres; gw_exact PE4| intros a X; exact (rFP_below stY a WFX (rFP_am stY a X))].
+ eapply magree_trans; [gw_exact AG3| apply rmagree_of_pres; gw_exact PE4| intros a X; gw_exact X| intros a X; exact (rFP_am stY a X)].
+ gw_exact BLX.
+ gw_exact P1.
+ gw_exact P2.
+ gw_exact P3.
+ reflexivity.
+ intros _. cbn in CASE. rewrite CASE. reflexivity.
-
subst b. cbn [range_val] in *.
unfold mprotect_answer_ok. cbn [Z.eqb orb negb].
rewrite (am_carve_eq stY p k bail), (ram_take_took (carve_st stY p) p k bail).
destruct CASE as [[_ ZB] ZW]. cbn [cells_bytes cbytes cells_size csize Nat.add app] in ZB, ZW. rewrite app_nil_r in ZB.
eapply rimplT_evt.
{ apply (ram_mp_ok0 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0 u1 u2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc stY p)) u3 u4 u5 u6 u7 u8 u9 (Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4x s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 (Z_to_bv 64 (base + 0x2b8)) F fc m3). }
intros ms4 ->.
eapply (rcarve_K stY p r m3 sX junk); first [gw_exact AI | gw_exact Hr | gw_exact NK | gw_exact S0 | gw_exact S1 | gw_exact SLR | gw_exact ANone | gw_exact FRESH | gw_exact TL | gw_exact CNT
| gw_exact MR3 | gw_exact MI3 | gw_exact ZB | gw_exact ZW | gw_exact FR3 | gw_exact ST3 | gw_exact ERR3 | gw_exact AUX3 | gw_exact AG3 | gw_exact BLX | gw_exact P1 | gw_exact P2 | gw_exact P3 | idtac].
unfold pgal. gw_exact SAL.
Qed.

#[using="Type"] Lemma rlive_ranges_same stA stB : s_regions stB = s_regions stA -> s_reserved stB = s_reserved stA -> live_ranges stB = live_ranges stA.
Proof. clear - stA stB R k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st lo errv AMP MR TK BL AUX ST LO LOLE ERR MI TP KH. first [clear KH | gw_hide KH | idtac]; first [clear TP | gw_hide TP | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear LOLE | gw_hide LOLE | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear AMP | gw_hide AMP | idtac]; first [clear errv | gw_hide errv | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear st | gw_hide st | idtac]; first [clear m | gw_hide m | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear R | gw_hide R | idtac]. intros E1 E2. unfold live_ranges. rewrite E1, E2. reflexivity. Qed.

#[using="base rvm_wait_entry ralloc_meta_entry rmmap_entry rmprotect_entry"] Lemma rfresh_of_ranges_free stY x L a :
s_regions stY = s_regions st -> s_reserved stY = s_reserved st ->
ranges_free (live_ranges stY) x L = true -> x + L <= alloc_ceiling -> x <= a < x + L -> fresh_addr st a.
Proof. clear - base rvm_wait_entry ralloc_meta_entry rmmap_entry rmprotect_entry stY x L a R k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st lo errv AMP MR TK BL AUX ST LO LOLE ERR MI TP KH. first [clear KH | gw_hide KH | idtac]; first [clear TP | gw_hide TP | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear LOLE | gw_hide LOLE | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear AMP | gw_hide AMP | idtac]; first [clear errv | gw_hide errv | idtac]; first [clear lo | gw_hide lo | idtac]; try gw_hide st; first [clear m | gw_hide m | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear R | gw_hide R | idtac].
intros E1 E2 RF XC Ha. split; [lia|]. rewrite (rlive_ranges_same st stY E1 E2) in RF.
eapply ranges_free_sub; [gw_exact RF| lia| lia| lia].
Qed.

#[using="base RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 ROM_reservedZ LAY_ref_reserved ralloc_meta_entry rmmap_entry rmprotect_entry"] Lemma rrepfoot_clear stY mY x L a :
rmrep stY mY -> ranges_free (live_ranges stY) x L = true -> rrepfoot stY a \/ rgrp_region_addr stY a -> ~ (x <= a < x + L).
Proof. clear - base RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 ROM_reservedZ LAY_ref_reserved ralloc_meta_entry rmmap_entry rmprotect_entry stY mY x L a RATP RGOT_SSP R k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st lo errv AMP MR TK BL AUX ST LO LOLE ERR MI TP KH. gw_expose_fam RATP; gw_expose_fam RGOT_SSP. first [clear KH | gw_hide KH | idtac]; first [clear TP | gw_hide TP | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear LOLE | gw_hide LOLE | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear AMP | gw_hide AMP | idtac]; first [clear errv | gw_hide errv | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear st | gw_hide st | idtac]; first [clear m | gw_hide m | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear R | gw_hide R | idtac].
intros MRY RF H. pose proof MRY as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
pose proof (clear_range_of_ranges_free stY x L RF) as CR.
assert (IMG : forall y, 0x10000 <= y < RIMG_HI -> ~ (x <= y < x + L)) by (intros y Hy; apply (rimage_clear_of_ranges_free stY x L y RS RF Hy)).
destruct H as [[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]|C]; (gw_expose_fam RATP; gw_expose_fam RGOT_SSP).
- apply IMG. lia.
- apply IMG. lia.
- apply IMG. lia.
- apply IMG. lia.
- destruct C as (ak & ar & Hak & Hin). destruct (WA ak ar Hak) as (rra & Hra & _).
eapply (CR (fst ak) rra a Hra). eapply rarea_in_live; eauto.
- destruct C as (b & gh & Hb & Hin). destruct (WG b gh Hb) as (rb & Hrb & _).
eapply (CR (fst b) rb a Hrb). eapply rgroup_in_live; eauto.
- destruct C as (rid & rg & v & Hrg & Krg & Hin & _). eapply (CR rid rg a Hrg). rewrite (lr_lo_group rg Krg). lia.
- apply IMG. lia.
- apply IMG. lia.
- destruct C as (rid & rg & Hrg & Krg & Hin). eapply (CR rid rg a Hrg). rewrite (lr_lo_group rg Krg). lia.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rerrno_loc_entry rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 joff_120 joff_173 joff_175 CODE BASE4 BASER D_120 E_120 D_173 E_173 D_175 E_175 LINK_120 LINK_173 LINK_175 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmprotect_spec rmmap_anon_spec ralloc_meta_entry rmmap_entry rmprotect_entry AMP TK LO LOLE TP KH"] Lemma rmmap_path : forall (stY : mstate) (mX : mem) (sX : PState) (junk : list byte) (e : word)
(x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
AMI st stY -> s_regions stY = s_regions st -> c_avail_meta_area_count (ctx stY) = 0 ->
0 <= c_meta_alloc_shift (ctx stY) <= 38 ->
(forall tl, c_meta_area_tail (ctx stY) = Some tl -> is_Some ((s_areas stY) !! tl)) ->
(forall q mr, (s_metas stY) !! q = Some mr -> meta_slot stY q) ->
ptrs_in (fun rid => (rid < s_next_rid stY)%N) stY ->
rmrep stY mX -> mem_inv segs mX ->
rw_cells segs mX (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk segs mX lo (bv_unsigned sp + -64) ->
rw_cells segs mX (errno_addr tp) [C4 e] -> rauxv_ok mX (bv_unsigned sp) -> magree (rFP stY) m mX ->
brk_link_ps stY sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
rimplT o (am_after_brk stY true k bail) sX Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x1b8)) fc None mX (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rerrno_loc_entry rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 joff_120 joff_173 joff_175 CODE BASE4 BASER D_120 E_120 D_173 E_173 D_175 E_175 LINK_120 LINK_173 LINK_175 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmprotect_spec rmmap_anon_spec ralloc_meta_entry rmmap_entry rmprotect_entry AMP TK LO LOLE TP KH segs base RATP R k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st lo errv MR BL AUX ST ERR MI. gw_expose_fam RATP. first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear MR | gw_hide MR | idtac]; try gw_hide errv; try gw_hide lo; try gw_hide st; try gw_hide m; try gw_hide fc; try gw_hide F; try gw_hide s11; try gw_hide s10; try gw_hide s9; try gw_hide s8; try gw_hide s7; try gw_hide s6; try gw_hide s5; try gw_hide s4; try gw_hide s3; try gw_hide s2; try gw_hide s1; try gw_hide s0; try gw_hide tp; try gw_hide gp; try gw_hide sp; try gw_hide ra; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; try gw_hide o; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear R | gw_hide R | idtac].
intros until t6. intros AI RGY ACNT SHR TL MK PTR MRX MIX FRX STX ERRX AUXX AGX BLX P1 P2 P3.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof LO as LO'. unfold alloc_ceiling in LO'. pose proof rETP as rETP'. pose proof TP as TPv.
pose proof MRX as (WFX & _). pose proof WFX as (RS & WR & DJ & WA & WG).
set (n := Z.shiftl 2 (c_meta_alloc_shift (ctx stY))).
assert (NR : 2 <= n <= 2^39).
{ unfold n. rewrite Z.shiftl_mul_pow2 by lia. split.
- rewrite <- (Z.mul_1_r 2) at 1. apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r with (b := 0); lia || (change 1 with (2^0); apply Z.pow_le_mono_r; lia).
- change (2^39) with (2 * 2^38). apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia. }
unfold am_after_brk. rewrite ACNT. cbn [Z.eqb]. fold n.

eapply rimplT_evt.
{ apply (ram_to_mmap (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc mX stY MRX ltac:(lia)). }
intros ms2 ->. fold n.
pose proof MRX as MR2. pose proof MIX as MI2. pose proof FRX as FR2. pose proof STX as ST2. pose proof ERRX as ERR2. pose proof AGX as AG2. pose proof AUXX as AUX2.
set (m2 := mX) in MR2, MI2, FR2, ST2, ERR2, AG2, AUX2 |- *.
clear MRX MIX FRX STX ERRX AUXX AGX.
eapply (rimplT_mmap_none o (n * PGSZ) _ sX).
{ unfold PGSZ. replace (Z_to_bv 64 (n * 4096)) with (Z_to_bv 64 (n * 4096)%Z) by first [reflexivity | (cbn; lia)].
eapply (rmmap_anon_spec true) with (lo := lo) (errv := e) (avoid := []);
[ rewrite unsigned_lit by lia; gw_exact ST2 | gw_exact ERR2 | gw_exact MI2 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ..];
rewrite ?rETP', ?TPv, ?unsigned_lit by lia; try lia. all: first [rewrite Q9A7.Mq0.alloc_ceiling_val; lia | unfold alloc_ceiling in *; lia]. }
intros ans ms3 MP. unfold rmmap_anon_post in MP.
destruct ans as [e'|x].
-
destruct MP as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m3 & -> & MU3 & WM3 & MI3 & ST3 & ERR3 & ER).
rewrite unsigned_lit in MU3, ST3 by lia.
try g_ret_pc_any.
cbn [mmap_val]. unfold mmap_answer_ok, is_errno_form, is_err, neg_errno, TWO64.
replace ((2 ^ 64 - 4095 <=? 2 ^ 64 - e') && (2 ^ 64 - e' <? 2 ^ 64)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
cbn [orb negb]. replace (2 ^ 64 - 4096 <? 2 ^ 64 - e') with true by (symmetry; apply Z.ltb_lt; lia).
assert (FR3 : rw_cells segs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
{ eapply rw_cells_transport; [gw_exact FR2| gw_exact MU3| gw_exact WM3|]. rewrite rETP'. cbn. lia. }
assert (MR3 : rmrep stY m3).
{ eapply rmrep_transport_unowned; [gw_exact MR2| gw_exact MU3| gw_exact WM3|].
intros lo' hi' y [E|[E|[]]] Hy; inversion E; subst lo' hi'; intros RFt; destruct (rrepfoot_low stY y WFX RFt); unfold alloc_ceiling in *; lia. }
assert (M23 : magree (rFP stY) m2 m3).
{ eapply magree_of_munch; [gw_exact MU3|]. cbn. split; [| split; [| exact I]]; intros y Hy; [left; left; lia|]. left. right. left. rewrite TPv in Hy. gw_exact Hy. }
assert (AG3 : magree (rFP stY) m m3) by (eapply magree_trans; [gw_exact AG2| gw_exact M23| intros a X; gw_exact X| intros a X; gw_exact X]).
assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)) by (eapply rauxv_ok_magree; [gw_exact AUX2| gw_exact M23| intros a X; exact (rFP_below stY a WFX X)]).
eapply rimplT_evt.
{ eapply (ram_mm_fail sp gp tp u0 u1 u2 (Z_to_bv 64 4096) (Z_to_bv 64 n) u3 u4 u5 u6 u7 u8 u9 s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 _ ra s0 s1 s2 s3 s4 F fc m3 m3 junk lo stY);
first [gw_exact MR3 | gw_exact MI3 | apply rpres_except_refl | apply wmono_refl | gw_exact FR3 | gw_exact ST3 | gw_exact LO | lia]. }
intros ms4 RP. unfold ram_ret_post in RP.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m4 & -> & PE4 & WM4 & MI4 & ST4 & MR4).
eapply rfinish_K.
+ apply (ram_rel_none st stY AI).
+ gw_exact MR4.
+ gw_exact MI4.
+ gw_exact ST4.
+ eapply rrw_cells_magree; [gw_exact ERR3| apply rmagree_of_pres; gw_exact PE4|]. cbn. intros a Ha X. apply (rerrno_not_amfp stY a WFX); [gw_exact X| lia].
+ eapply rauxv_ok_magree; [gw_exact AUX3| apply rmagree_of_pres; gw_exact PE4| intros a X; exact (rFP_below stY a WFX (rFP_am stY a X))].
+ eapply magree_trans; [gw_exact AG3| apply rmagree_of_pres; gw_exact PE4| intros a X; gw_exact X| intros a X; exact (rFP_am stY a X)].
+ gw_exact BLX.
+ gw_exact P1.
+ gw_exact P2.
+ gw_exact P3.
+ reflexivity.
+ intros _. rewrite ER. reflexivity.
-
destruct MP as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m2' & -> & MU3 & WM3 & MI3 & ST3 & ERR3 & AOK).
rewrite unsigned_lit in MU3, ST3 by lia.
try g_ret_pc_any.
cbn [mmap_val].
destruct (mmap_answer_ok (live_ranges stY) (n * PGSZ) x) eqn:VOK; cbn [negb]; [| apply rimplT_undef].

unfold mmap_addr_ok in AOK. apply andb_prop in AOK. destruct AOK as [AOK _]. apply andb_prop in AOK. destruct AOK as [AOK XC].
apply andb_prop in AOK. destruct AOK as [XA X0]. apply Z.eqb_eq in XA. apply Z.ltb_lt in X0. apply Z.leb_le in XC.
rewrite QWTl.Mq5.mmap_len_round_up in XC. first [rewrite Q9A7.Mq0.alloc_ceiling_val in XC | unfold alloc_ceiling in XC]. change page_size with 4096 in XA.
assert (LAL : round_up_pg (n * PGSZ) = n * PGSZ) by (apply round_up_pg_aligned; unfold PGSZ; apply Z.mod_mul; lia).
rewrite LAL in XC.
unfold mmap_answer_ok in VOK. rewrite LAL in VOK. apply orb_prop in VOK.
assert (RF : ranges_free (live_ranges stY) x (n * PGSZ) = true).
{ destruct VOK as [V|V]; [| apply andb_prop in V; destruct V as [_ V]; gw_exact V].
unfold is_errno_form, TWO64 in V. apply andb_prop in V. destruct V as [V _]. apply Z.leb_le in V. unfold PGSZ in XC. exfalso. lia. }
unfold is_err, TWO64. replace (2 ^ 64 - 4096 <? x) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ in XC; lia).
unfold new_region. cbv beta iota zeta delta [fst snd].
set (rid := s_next_rid stY).
pose proof (rAMI_new_region st stY RKMeta x (n * PGSZ) AI ltac:(discriminate) ltac:(unfold PGSZ; lia)) as (AI1 & RG1 & CQ1 & CN1).
unfold new_region in AI1, RG1, CQ1, CN1. cbn [fst snd] in AI1, RG1, CQ1, CN1. fold rid in AI1, RG1, CQ1, CN1 |- *.
set (st1 := set_next_rid (N.succ rid) _) in AI1, RG1, CQ1, CN1 |- *.
set (st2 := upd_ctx _ st1).
assert (E2 : st2 = mm_ok_st st1 rid n) by first [reflexivity | (cbn; lia)].

unfold Q9A7.Mq0.mmap_raw in ST3 |- *. rewrite QWTl.Mq5.mmap_len_round_up, LAL in ST3 |- *.
set (m3 := apply_unmaps m2' [(wa x, Z_to_bv 64 (n * PGSZ))]) in *.
assert (Hx1 : 0 <= x < 2^64) by (unfold PGSZ in XC; lia). assert (Hn1 : 0 <= n * PGSZ < 2^64) by (unfold PGSZ in *; lia). assert (Hxn : x + n * PGSZ <= 2^64) by (unfold PGSZ in *; lia).
assert (FR3 : rw_cells segs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
{ apply (rw_cells_unmaps_other segs m2' x (n * PGSZ) Hx1 Hn1 Hxn).
- eapply rw_cells_transport; [gw_exact FR2| gw_exact MU3| gw_exact WM3|]. cbn. lia.
- cbn. unfold PGSZ in *. lia. }
assert (ERR4 : rw_cells segs m3 (errno_addr tp) [C4 e]).
{ apply (rw_cells_unmaps_other segs m2' x (n * PGSZ) Hx1 Hn1 Hxn); [gw_exact ERR3|]. cbn. rewrite rETP'.
pose proof (rimage_clear_of_ranges_free stY x (n * PGSZ) ((RATP + -164)) RS RF ltac:(lia)).
pose proof (rimage_clear_of_ranges_free stY x (n * PGSZ) ((RATP + -161)) RS RF ltac:(lia)). unfold PGSZ in *. lia. }
assert (MI4 : mem_inv segs m3) by (apply (mem_inv_unmaps segs m2' x (n * PGSZ) Hx1 Hn1 Hxn); gw_exact MI3).
assert (MR2' : rmrep stY m2').
{ eapply rmrep_transport_unowned; [gw_exact MR2| gw_exact MU3| gw_exact WM3|].
intros lo' hi' y [E|[]] Hy; inversion E; subst lo' hi'; intros RFt; destruct (rrepfoot_low stY y WFX RFt); unfold alloc_ceiling in *; lia. }
assert (MR3 : rmrep stY m3).
{ eapply rmrep_transport_agree'; [gw_exact MR2'|]. intros y Hy HF. unfold m3. apply (unmaps_outside m2' x (n * PGSZ) Hx1 Hn1 Hxn).
rewrite wa_unsigned by lia. pose proof (rrepfoot_clear stY m2' x (n * PGSZ) y MR2' RF HF). lia. }
assert (MRn : rmrep st1 m3).
{ unfold st1. apply (RMallocKit_A2__rmrep_new_region stY m3 m3 x (n * PGSZ) RKMeta);
first [ gw_exact MR3
| eapply ptrs_in_mono; [| gw_exact PTR]; intros q Hq; cbn in Hq; intros ->; unfold rid in Hq; lia
| apply (ami_fresh _ _ AI); unfold rid; lia
| unfold alloc_ceiling; rewrite LAL; gw_exact XC
| rewrite LAL; gw_exact RF
| intros; reflexivity
| intros; discriminate
| unfold PGSZ in *; lia ]. }
assert (M23 : magree (rFP stY) m2 m3).
{ intros y Hy Hc. unfold m3. rewrite (unmaps_outside m2' x (n * PGSZ) Hx1 Hn1 Hxn).
- apply MU3. rewrite wa_unsigned by lia. cbn. split; [| exact I]. intros X. apply Hc. left. left. lia.
- rewrite wa_unsigned by lia. destruct (Z.lt_ge_cases y x); [lia|]. destruct (Z.lt_ge_cases y (x + n * PGSZ)); [| lia].
exfalso. apply Hc. right. eapply (rfresh_of_ranges_free stY x (n * PGSZ)); [gw_exact RGY| exact (ami_reserved _ _ AI)| gw_exact RF| unfold alloc_ceiling; gw_exact XC| lia]. }
assert (AG3 : magree (rFP stY) m m3) by (eapply magree_trans; [gw_exact AG2| gw_exact M23| intros a X; gw_exact X| intros a X; gw_exact X]).
assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)) by (eapply rauxv_ok_magree; [gw_exact AUX2| gw_exact M23| intros a X; exact (rFP_below stY a WFX X)]).
clearbody m3. clear MU3 WM3 MR2 MR2' MI3 ERR3.

eapply rimplT_evt.
{ eapply (ram_mm_ok sp gp tp u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 _ ra s0 s1 s2 s3 s4 F fc m3 m3 junk lo x n st1 st1 rid (mkRegion RKMeta x (n * PGSZ)));
first [gw_exact MRn | gw_exact MI4 | intros a X; gw_exact X | gw_exact RG1 | reflexivity | gw_exact XA | gw_exact X0 | apply rpres_except_refl | apply wmono_refl | gw_exact FR3 | gw_exact ST3 | gw_exact LO | idtac];
try (unfold alloc_ceiling, PGSZ in *; lia).
change (ctx st1) with (ctx stY). lia. }
intros ms4 (m4 & -> & PE4 & WM4 & MI5 & FR4 & ST4 & MR4).
pose proof MRn as (WFn & _).
assert (RG2 : forall q, (s_regions st2) !! q = if decide (q = rid) then Some (mkRegion RKMeta x (n * PGSZ)) else (s_regions stY) !! q).
{ intros q. change (s_regions st2) with (<[rid := mkRegion RKMeta x (n * PGSZ)]> (s_regions stY)).
destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. }
destruct (ami_fresh _ _ AI rid ltac:(unfold rid; lia)) as [FRr FRs].
replace (Z_to_bv 64 (x + 4096)) with (Z_to_bv 64 (conc st2 (rid, 4096))) by (change (conc st2 (rid, 4096)) with (conc st1 (rid, 4096)); rewrite CN1; reflexivity).
eapply (rfinish_path st2 (rid, 4096) (mkRegion RKMeta x (n * PGSZ)) m4 sX junk e).
+ unfold st2. apply (rAMI_ctx st st1 _ AI1).
* cbn. repeat split; reflexivity.
* cbn. exact (ami_secretr _ _ AI1).
* right. exists (rid, PGSZ), (mkRegion RKMeta x (n * PGSZ)). cbn [fst]. split; [reflexivity|]. split; [gw_exact RG1| cbn; discriminate].
* left. reflexivity.
+ reflexivity.
+ cbn [fst]. rewrite RG2. destruct (decide (rid = rid)); [reflexivity| congruence].
+ cbn. discriminate.
+ cbn. lia.
+ cbn [snd r_len]. rewrite LAL. unfold PGSZ. lia.
+ unfold pgal. reflexivity.
+ cbn. lia.
+ change (s_areas st2) with (s_areas stY). lazymatch goal with |- ?t = None => destruct t as [ar|] eqn:EA end; [| reflexivity].
exfalso. destruct (WA _ _ EA) as (rr & Hrr & _). cbn [fst] in Hrr. rewrite FRr in Hrr. discriminate.
+ intros j Hj. change (s_metas st2) with (s_metas stY). lazymatch goal with |- ?t = None => destruct t as [mr|] eqn:EM end; [| reflexivity].
exfalso. destruct (MK _ _ EM) as (a & ar & kk & Ha & Hk & Eq). destruct (WA _ _ Ha) as (rr & Hrr & _).
assert (Ef : fst a = rid) by (unfold aadd in Eq; cbn in Eq; inversion Eq; reflexivity). rewrite Ef, FRr in Hrr. discriminate.
+ intros tl Htl. change (s_areas st2) with (s_areas stY). apply TL. gw_exact Htl.
+ cbn. lia.
+ gw_exact MR4.
+ gw_exact MI5.
+ gw_exact FR4.
+ gw_exact ST4.
+ eapply rrw_cells_magree; [gw_exact ERR4| apply rmagree_of_pres; gw_exact PE4|]. cbn. intros a Ha X. apply (rerrno_not_amfp st1 a WFn); [gw_exact X| lia].
+ eapply rauxv_ok_magree; [gw_exact AUX3| apply rmagree_of_pres; gw_exact PE4| intros a X; exact (rFP_below st1 a WFn (rFP_am st1 a X))].
+ eapply magree_trans; [gw_exact AG3| apply rmagree_of_pres; gw_exact PE4| |].
* intros a X. eapply rFP_mono; [| gw_exact X]. intros q rq Hq. exists rq. rewrite RG2.
destruct (decide (q = rid)) as [->|NE]; [rewrite FRr in Hq; discriminate|]. repeat split; auto; lia.
* intros a X. eapply rFP_same; [| exact (rFP_am st1 a X)]. reflexivity.
+ unfold brk_link_ps in *. change (c_brk (ctx st2)) with (c_brk (ctx stY)).
destruct PTR as (_ & _ & _ & _ & _ & _ & PB & _).
destruct (c_brk (ctx stY)) as [| |rb ob]; auto. change (conc st2 (rb, ob)) with (conc st1 (rb, ob)). rewrite CQ1; [gw_exact BLX|]. cbn [fst]. unfold rid. lia.
+ gw_exact P1.
+ gw_exact P2.
+ gw_exact P3.
Qed.

#[using="base RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry LAY_win_1 LAY_win_2 LAY_ref_reserved ralloc_meta_entry rmmap_entry rmprotect_entry RC__"] Lemma rimage_range_clear stY x L : s_reserved stY = ref_reserved -> ranges_free (live_ranges stY) x L = true -> 0 < L ->
x + L <= 0x10000 \/ RIMG_HI <= x.
Proof. clear - base RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry LAY_win_1 LAY_win_2 LAY_ref_reserved ralloc_meta_entry rmmap_entry rmprotect_entry RC__ RIMG_HI ref_reserved stY x L R k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st lo errv AMP MR TK BL AUX ST LO LOLE ERR MI TP KH. gw_expose_win. first [clear KH | gw_hide KH | idtac]; first [clear TP | gw_hide TP | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear LOLE | gw_hide LOLE | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear AMP | gw_hide AMP | idtac]; first [clear errv | gw_hide errv | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear st | gw_hide st | idtac]; first [clear m | gw_hide m | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear R | gw_hide R | idtac].
intros RS RF HL. unfold live_ranges in RF. rewrite RS in RF. rewrite ?LAY_ref_reserved in RF.
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; right; left; reflexivity)). cbn in *. lia.
Qed.

#[using="RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rerrno_loc_entry rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 joff_120 joff_173 joff_175 CODE BASE4 BASER D_120 E_120 D_173 E_173 D_175 E_175 LINK_120 LINK_173 LINK_175 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_reservedZ LAY_ref_reserved ref_ro_addr_false rmprotect_spec rmmap_anon_spec ralloc_meta_entry rmmap_entry rmprotect_entry errv AMP TK LO LOLE ERR TP KH"] Lemma rbrk_live_path : forall (stI : mstate) (brid : N) (boff : Z) (m1 : mem) (junk : list byte) (e1 : word)
(x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
RAMpre stI -> AMI st stI -> s_regions stI = s_regions st -> brk_link_ps stI s ->
c_avail_meta_area_count (ctx stI) = 0 -> c_brk (ctx stI) = BrkLive brid boff ->
ptrs_in (fun rid => (rid < s_next_rid stI)%N) stI ->
rmrep stI m1 -> mem_inv segs m1 ->
rw_cells segs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk segs m1 lo (bv_unsigned sp + -64) ->
rw_cells segs m1 (errno_addr tp) [C4 e1] -> rauxv_ok m1 (bv_unsigned sp) -> magree (rFP stI) m m1 ->
rimplT o (let old := conc stI (brid, boff) in
let new := old + PGSZ in
SVis (EBrk new) (fun r =>
if negb (brk_answer_ok old new r) then bad_answer bail else
if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) stI) true k bail
else if negb (brk_pages_ok stI old PGSZ) then bad_answer bail
else
let st1 := upd_region brid (fun rg => mkRegion (r_kind rg) (r_base rg) (boff + PGSZ)) stI in
let st2 := upd_ctx (fun c => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (brid, boff)) (set_brk (BrkLive brid (boff + PGSZ)) c))) st1 in
am_after_brk st2 false k bail)) s Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x108)) fc None m1 (seg_rom segs)).
Proof. clear - RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rerrno_loc_entry rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 joff_120 joff_173 joff_175 CODE BASE4 BASER D_120 E_120 D_173 E_173 D_175 E_175 LINK_120 LINK_173 LINK_175 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_reservedZ LAY_ref_reserved ref_ro_addr_false rmprotect_spec rmmap_anon_spec ralloc_meta_entry rmmap_entry rmprotect_entry errv AMP TK LO LOLE ERR TP KH segs base RATP R k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st lo MR BL AUX ST MI. gw_expose_fam RATP. first [clear MI | gw_hide MI | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear MR | gw_hide MR | idtac]; try gw_hide lo; try gw_hide st; try gw_hide m; try gw_hide fc; try gw_hide F; try gw_hide s11; try gw_hide s10; try gw_hide s9; try gw_hide s8; try gw_hide s7; try gw_hide s6; try gw_hide s5; try gw_hide s4; try gw_hide s3; try gw_hide s2; try gw_hide s1; try gw_hide s0; try gw_hide tp; try gw_hide gp; try gw_hide sp; try gw_hide ra; first [clear Q | gw_hide Q | idtac]; try gw_hide s; try gw_hide o; try gw_hide bail; try gw_hide k; first [clear R | gw_hide R | idtac].
intros until t6. intros AMPI AI RGI BLI ACNT BRK PTRI MR1 MI1 FR1 ST1 ERR1 AUX1 AG1.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof LO as LO'. unfold alloc_ceiling in LO'. pose proof rETP as rETP'. pose proof TP as TPv.
pose proof MR1 as (WF1 & (HX1 & HX2 & HX3 & HX4 & HX5 & HX6) & _). pose proof WF1 as (RS & WR & DJ & WA & WG).
pose proof (amp_brk stI AMPI) as HB. rewrite BRK in HB. destruct HB as (r & Hr & Kr & Lr & OAL & O4 & FRA & UNQ).
pose proof (conc_region' stI (brid, boff) r Hr) as OLD. cbn [snd] in OLD.
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RFr). unfold alloc_ceiling in RBC. rewrite Lr in RBC.
assert (RUB : round_up_pg boff = boff) by (apply round_up_pg_aligned; unfold PGSZ in OAL; gw_exact OAL). rewrite RUB in RBC.
set (old := conc stI (brid, boff)) in *.
assert (TLI : forall tl, c_meta_area_tail (ctx stI) = Some tl -> is_Some ((s_areas stI) !! tl)) by (exact (amp_tail stI AMPI)).
assert (MKI : forall q mr, (s_metas stI) !! q = Some mr -> meta_slot stI q) by (exact (amp_mkeys stI AMPI)).
unfold brk_link_ps in BLI. rewrite BRK in BLI. fold old in BLI.
cbv zeta.

eapply rimplT_evt.
{ eapply (ram_disp_live _ gp tp t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI brid boff); [gw_exact MR1| gw_exact ACNT| gw_exact BRK| fold old; lia| fold old; unfold PGSZ; lia]. }
intros ms2 ->. fold old.
eapply (rimplT_brk o (old + PGSZ) _ s).
{ unfold PGSZ; lia. }
{ rewrite BLI. unfold PGSZ.
exact (ram_brk_node_at x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (old + 4096)) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960))
s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 (base + 0x12c) (or_introl eq_refl) old (old + 4096) ltac:(lia)). }
intros a ms3 ->. rewrite BLI. unfold brk_res, brk_mem, rbrk_regs. gw_addr_norm.
destruct a.
-
unfold brk_answer_ok. rewrite Z.eqb_refl. cbn [orb negb].
destruct (brk_pages_ok stI old PGSZ) eqn:BPO; cbn [negb]; [| apply rimplT_undef].
unfold brk_pages_ok in BPO. apply andb_prop in BPO. destruct BPO as [BPO RF]. apply andb_prop in BPO. destruct BPO as [_ OC]. apply Z.leb_le in OC.
unfold alloc_ceiling, PGSZ in OC. unfold PGSZ in RF.
assert (OALD : old mod 4096 = 0) by (rewrite OLD; rewrite Z.add_mod, RBAL by lia; unfold PGSZ in OAL; rewrite OAL; reflexivity).
rewrite (brk_new_pages_aligned old 4096) by (first [lia | gw_exact OALD | reflexivity]).
rewrite (rgr_eq stI brid r boff Hr).
set (stG := set_regions _ stI).
unfold PGSZ. rewrite (am_after_brk_false_eq stG _ (brid, boff) k bail) by (cbn; first [lia | reflexivity | unfold PGSZ in OAL; gw_exact OAL]).
rewrite am_carve_took, carve_st_brk_irrel.
set (stX := upd_ctx _ stG).

assert (Ho1 : 0 <= old < 2^64) by lia. assert (Hn1 : 0 <= 4096 < 2^64) by lia. assert (Hon : old + 4096 <= 2^64) by lia.
pose proof (rimage_range_clear stI old 4096 RS RF ltac:(lia)) as IMG.
set (m2 := apply_zeros m1 [(wa old, Z_to_bv 64 4096)]).
unfold ctx_head_cells in HX1. rewrite ACNT in HX1. unfold ctx_tail_cells, brk_word in HX6. rewrite BRK in HX6. fold old in HX6.
assert (HC2 : rw_cells segs m2 (RATP + 131968) ltac:(lazymatch type of HX1 with rw_cells _ _ _ ?cs => exact cs end))
by (apply (rw_cells_zeros_other segs m1 old 4096 Ho1 Hn1 Hon); [gw_exact HX1| cbn; gw_expose_fam RATP; lia]).
assert (TC2 : rw_cells segs m2 ((RATP + 132880)) [C1 (b8 (c_seq (ctx stI))); CB 7 (zeros 7); C8 (wz old)])
by (apply (rw_cells_zeros_other segs m1 old 4096 Ho1 Hn1 Hon); [gw_exact HX6| cbn; gw_expose_fam RATP; lia]).
assert (MI2 : mem_inv segs m2).
{ apply (mem_inv_zeros segs m1 old 4096 Ho1 Hn1 Hon MI1). intros y Hy. apply ref_ro_addr_false. lia. }
assert (FR2 : rw_cells segs m2 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra))
by (apply (rw_cells_zeros_other segs m1 old 4096 Ho1 Hn1 Hon); [gw_exact FR1| cbn; lia]).
assert (ST2 : stk segs m2 lo (bv_unsigned sp + -64)) by (apply (stk_zeros segs m1 old 4096 Ho1 Hn1 Hon); gw_exact ST1).
assert (ERR2 : rw_cells segs m2 (errno_addr tp) [C4 e1])
by (apply (rw_cells_zeros_other segs m1 old 4096 Ho1 Hn1 Hon); [gw_exact ERR1| cbn; rewrite rETP'; lia]).
pose proof (rw_cells_zeros_new segs m1 old 4096 Ho1 Hn1 Hon) as ZN. fold m2 in ZN.
assert (MU12 : munch [(old, old + 4096)]%Z m1 m2) by (apply (munch_zeros m1 old 4096 Ho1 Hn1 Hon); [apply munch_refl| cbn; lia]).
assert (WM12 : wmono segs m1 m2) by (apply (wmono_zeros segs m1 old 4096 Ho1 Hn1 Hon); apply wmono_refl).
assert (MR2 : rmrep stI m2).
{ eapply rmrep_transport_unowned; [gw_exact MR1| gw_exact MU12| gw_exact WM12|].
intros lo' hi' y [E|[]] Hy; inversion E; subst lo' hi'. intros RFt. apply (rrepfoot_clear stI m1 old 4096 y MR1 RF (or_introl RFt)). lia. }
assert (M12 : magree (rFP stI) m1 m2).
{ intros y Hy Hc. unfold m2. apply (zeros_outside m1 old 4096 Ho1 Hn1 Hon). rewrite wa_unsigned by lia.
destruct (Z.lt_ge_cases y old); [lia|]. destruct (Z.lt_ge_cases y (old + 4096)); [| lia].
exfalso. apply Hc. right. eapply (rfresh_of_ranges_free stI old 4096); [gw_exact RGI| exact (ami_reserved _ _ AI)| gw_exact RF| unfold alloc_ceiling; lia| lia]. }
clearbody m2.

eapply rimplT_evt.
{ eapply (ram_bl_ok _ gp tp t0 t1 t2 (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 _ s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 (old + 4096)); [lia | | | gw_exact MI2].
- unfold pw in HC2. cbn [oconc] in HC2. gw_exact HC2.
- unfold wz in TC2. gw_exact TC2. }
intros ms4 (m3 & -> & MU3 & WM3 & MI3 & HC3 & TC3). replace (old + 4096 - 4096) with old by lia.

pose proof (rAMI_grow st stI brid r boff AI Hr ltac:(rewrite Kr; discriminate) Lr) as (AIG & CQG & RG'). fold stG in AIG, CQG, RG'.
assert (MRG : rmrep stG m2).
{ unfold stG. apply (rmrep_grow_region stI m2 brid r boff MR2 Hr);
first [ rewrite Kr; discriminate
| gw_exact Lr
| unfold PGSZ in OAL; gw_exact OAL
| rewrite <- OLD; gw_exact RF
| exact (amp_rpos stI AMPI)
| intros q rq Hq NE KB; apply NE; exact (UNQ q rq Hq KB)
| unfold alloc_ceiling, PGSZ in *; lia ]. }
assert (PWX : forall q, pw stX q = pw stI q) by (intros [q|]; unfold pw, oconc; [change (conc stX q) with (conc stG q); rewrite CQG|]; reflexivity).
assert (PWG : forall q, pw stG q = pw stI q) by (intros [q|]; unfold pw, oconc; [rewrite CQG|]; reflexivity).
assert (CQX : forall q, conc stX q = conc stI q) by (intros q; change (conc stX q) with (conc stG q); apply CQG).
assert (MRX : rmrep stX m3).
{ eapply (rmrep_ctx_frameW stG stX m2 m3 _ MRG MU3 WM3); try reflexivity.
- intros lo' hi' [E|[E|[]]]; inversion E; subst; gw_expose_fam RATP; lia.
- left. unfold ctx_head_cells. rewrite !PWX.
cbn [ctx stX stG upd_ctx s_ctx set_regions set_avail_meta_area_count set_brk c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
change (s_ctx stI) with (ctx stI). unfold wz at 5. gw_exact HC3.
- right. split; [| intros lo' hi' [E|[E|[]]]; inversion E; subst; gw_expose_fam RATP; lia].
unfold actives. apply map_ext. intros i. rewrite PWX, PWG. reflexivity.
- right. split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; gw_expose_fam RATP; lia].
- right. split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; gw_expose_fam RATP; lia].
- right. split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; gw_expose_fam RATP; lia].
- left. unfold ctx_tail_cells, brk_word. cbn [ctx stX upd_ctx s_ctx set_avail_meta_area_count set_brk c_brk c_seq].
change (conc stX (brid, boff + 4096)) with (conc stG (brid, boff + 4096)).
rewrite CQG. rewrite (conc_region' stI (brid, boff + 4096) r Hr). cbn [snd]. unfold wz.
replace (r_base r + (boff + 4096)) with (old + 4096) by lia. change (s_ctx stI) with (ctx stI). gw_exact TC3. }

assert (M23 : magree (rFP stX) m2 m3).
{ eapply magree_of_munch; [gw_exact MU3|]. cbn. gw_expose_fam RATP. split; [| split; [| exact I]]; intros y Hy; left; right; right; left; gw_expose_fam RATP; lia. }
assert (ZN3 : rw_cells segs m3 old [CB (Z.to_nat 4096) (repeat (Z_to_bv 8 0) (Z.to_nat 4096))]).
{ eapply rw_cells_transport; [gw_exact ZN| gw_exact MU3| gw_exact WM3|]. cbn. gw_expose_fam RATP. lia. }
destruct ZN3 as [[_ ZB] ZW]. cbn [cells_bytes cbytes cells_size csize Nat.add app] in ZB, ZW. rewrite app_nil_r in ZB.
assert (FR3 : rw_cells segs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [gw_exact FR2| gw_exact MU3| gw_exact WM3|]; cbn; gw_expose_fam RATP; lia).
assert (ST3 : stk segs m3 lo (bv_unsigned sp + -64)) by (eapply stk_transport_disjoint; [gw_exact ST2| gw_exact MU3| gw_exact WM3|]; cbn; gw_expose_fam RATP; lia).
assert (ERR3 : rw_cells segs m3 (errno_addr tp) [C4 e1]) by (eapply rw_cells_transport; [gw_exact ERR2| gw_exact MU3| gw_exact WM3|]; cbn; rewrite rETP'; gw_expose_fam RATP; lia).
assert (AGX1 : forall y, rFP stI y -> rFP stX y).
{ intros y X. eapply rFP_mono; [| gw_exact X]. intros q rq Hq. destruct (ami_regions _ _ AI q rq) as (r0 & H0 & _); [rewrite <- RGI; gw_exact Hq|].
destruct (decide (q = brid)) as [->|NE].
- eexists. split; [gw_exact RG'|]. rewrite Hr in Hq. inversion Hq; subst. cbn. repeat split; lia.
- exists rq. change (s_regions stX) with (<[brid := mkRegion (r_kind r) (r_base r) (boff + 4096)]> (s_regions stI)). rewrite lookup_insert_ne by congruence. repeat split; auto; lia. }
assert (AG3 : magree (rFP stX) m m3).
{ eapply magree_trans; [| gw_exact M23| gw_exact AGX1| intros y X; gw_exact X]. eapply magree_trans; [gw_exact AG1| gw_exact M12| intros y X; gw_exact X| intros y X; gw_exact X]. }
assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)).
{ eapply rauxv_ok_magree; [gw_exact AUX1| |intros y X; exact (rFP_below stX y (proj1 MRX) X)].
eapply magree_trans; [gw_exact M12| gw_exact M23| gw_exact AGX1| intros y X; gw_exact X]. }
replace (Z_to_bv 64 old) with (Z_to_bv 64 (conc stX (brid, boff))) by (change (conc stX (brid, boff)) with (conc stG (brid, boff)); rewrite CQG; reflexivity).
eapply (rcarve_K stX (brid, boff) (mkRegion (r_kind r) (r_base r) (boff + 4096)) m3 _ junk e1);
first [gw_exact RG' | gw_exact MRX | gw_exact MI3 | gw_exact FR3 | gw_exact ST3 | gw_exact ERR3 | gw_exact AUX3 | gw_exact AG3 | reflexivity | idtac].
+ unfold stX. apply (rAMI_ctx st stG _ AIG).
* cbn. repeat split; reflexivity.
* cbn. exact (ami_secretr _ _ AIG).
* left. reflexivity.
* right. right. exists brid, (boff + 4096), (mkRegion (r_kind r) (r_base r) (boff + 4096)). split; [reflexivity|]. split; [gw_exact RG'|]. cbn. rewrite Kr. discriminate.
+ cbn. rewrite Kr. discriminate.
+ cbn. lia.
+ cbn [snd r_len]. rewrite round_up_pg_aligned; [lia|]. rewrite Z.add_mod, OAL by lia. reflexivity.
+ unfold pgal. unfold PGSZ in OAL. gw_exact OAL.
+ cbn [snd r_base]. unfold lr_lo. cbn [r_kind r_base]. rewrite Kr. unfold PGSZ in O4. lia.
+ change (s_areas stX) with (s_areas stI). apply (proj1 (FRA (brid, boff) eq_refl ltac:(cbn; lia))).
+ intros j Hj. change (s_metas stX) with (s_metas stI). apply (proj2 (FRA (aadd (brid, boff) (AREA_HDR + META_SIZE * j)) eq_refl ltac:(cbn; unfold AREA_HDR, META_SIZE; lia))).
+ intros tl Htl. change (s_areas stX) with (s_areas stI). apply TLI. gw_exact Htl.
+ cbn. lia.
+ change (conc stX (brid, boff)) with (conc stG (brid, boff)). rewrite CQG. fold old. gw_exact ZB.
+ change (conc stX (brid, boff)) with (conc stG (brid, boff)). rewrite CQG. fold old. gw_exact ZW.
+ unfold brk_link_ps. cbn [ctx stX upd_ctx s_ctx set_avail_meta_area_count set_brk c_brk ps_brk set_brk_ps].
rewrite CQX. rewrite (conc_region' stI (brid, boff + 4096) r Hr). cbn [snd]. unfold PGSZ. lia.
-
unfold brk_answer_ok. rewrite Z.eqb_refl.
replace (old =? old + PGSZ) with false by (symmetry; apply Z.eqb_neq; unfold PGSZ; lia). cbn [orb negb].
eapply rimplT_evt.
{ unfold PGSZ. eapply (ram_bl_fail _ gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI old); [gw_exact MR1| gw_exact ACNT| lia| lia| gw_exact MI1]. }
intros ms4 (m3 & -> & MU3 & WM3 & MI3 & MRD).
assert (M13 : magree (rFP stI) m1 m3).
{ eapply magree_of_munch; [gw_exact MU3|]. cbn. split; [| exact I]. intros y Hy. left. right. right. left. gw_expose_fam RATP. lia. }
eapply (rmmap_path (upd_ctx (set_brk BrkDead) stI) m3 s junk e1); first [gw_exact MRD | gw_exact MI3 | reflexivity | idtac].
+ apply (rAMI_ctx st stI _ AI); [cbn; repeat split; reflexivity| cbn; exact (ami_secretr _ _ AI)| left; reflexivity| right; left; reflexivity].
+ gw_exact RGI.
+ gw_exact ACNT.
+ change (ctx (upd_ctx (set_brk BrkDead) stI)) with (set_brk BrkDead (ctx stI)). cbn [c_meta_alloc_shift set_brk]. pose proof (amp_shift stI AMPI). lia.
+ gw_exact TLI.
+ gw_exact MKI.
+ pose proof PTRI as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10). apply rptrs_in_upd_ctx; cbn; try assumption; try reflexivity; try exact I.
+ eapply rw_cells_transport; [gw_exact FR1| gw_exact MU3| gw_exact WM3|]. cbn. gw_expose_fam RATP. lia.
+ eapply stk_transport_disjoint; [gw_exact ST1| gw_exact MU3| gw_exact WM3|]. cbn. gw_expose_fam RATP. lia.
+ eapply rw_cells_transport; [gw_exact ERR1| gw_exact MU3| gw_exact WM3|]. cbn. rewrite rETP'. gw_expose_fam RATP. lia.
+ eapply rauxv_ok_magree; [gw_exact AUX1| gw_exact M13| intros y X; exact (rFP_below stI y WF1 X)].
+ eapply (magree_trans (rFP stI) (rFP stI) _ m m1 m3 AG1 M13); intros y X; (eapply rFP_same; [| gw_exact X]); reflexivity.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rerrno_loc_entry rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 joff_98 joff_120 joff_173 joff_175 CODE BASE4 BASER D_98 E_98 D_120 E_120 D_173 E_173 D_175 E_175 LINK_98 LINK_120 LINK_173 LINK_175 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_ro_addr_false rmprotect_spec rmmap_anon_spec rmmap_fixed_spec ralloc_meta_entry rmmap_entry rmprotect_entry AMP ERR KH LO LOLE TK TP"] Lemma rbrk_untried_path : forall (stI : mstate) (m1 : mem) (junk : list byte) (e1 : word)
(x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
RAMpre stI -> AMI st stI -> s_regions stI = s_regions st ->
c_avail_meta_area_count (ctx stI) = 0 -> c_brk (ctx stI) = BrkUntried ->
ptrs_in (fun rid => (rid < s_next_rid stI)%N) stI ->
rmrep stI m1 -> mem_inv segs m1 ->
rw_cells segs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk segs m1 lo (bv_unsigned sp + -64) ->
rw_cells segs m1 (errno_addr tp) [C4 e1] -> rauxv_ok m1 (bv_unsigned sp) -> magree (rFP stI) m m1 ->
ps_m s = ps_m s ->
rimplT o (SVis (EBrk 0) (fun cur =>
if negb (brk0_answer_ok cur) then bad_answer bail else
let base_ := round_up_pg cur in
let new := base_ + 2 * PGSZ in
SVis (EBrk new) (fun r =>
if negb (brk_answer_ok cur new r) then bad_answer bail else
if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) stI) true k bail
else if negb (brk_pages_ok stI base_ (2 * PGSZ)) then bad_answer bail
else
SVis (EMmap base_ PGSZ PROT_NONE (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) (fun rg =>
if negb (mmap_fixed_answer_ok base_ rg) then bad_answer bail else
let '(st1, rid) := new_region RKBrk base_ (2 * PGSZ) stI in
let st2 := upd_ctx (fun c => set_avail_meta_area_count 1
(set_avail_meta_areas (Some (rid, PGSZ))
(set_brk (BrkLive rid (2 * PGSZ)) c))) st1 in
am_after_brk st2 false k bail)))) s Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x108)) fc None m1 (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rerrno_loc_entry rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 joff_98 joff_120 joff_173 joff_175 CODE BASE4 BASER D_98 E_98 D_120 E_120 D_173 E_173 D_175 E_175 LINK_98 LINK_120 LINK_173 LINK_175 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_ro_addr_false rmprotect_spec rmmap_anon_spec rmmap_fixed_spec ralloc_meta_entry rmmap_entry rmprotect_entry AMP ERR KH LO LOLE TK TP segs base RATP RGOT_SSP R k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st lo errv MR BL AUX ST MI. gw_expose_fam RATP; gw_expose_fam RGOT_SSP. first [clear MI | gw_hide MI | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear MR | gw_hide MR | idtac]; try gw_hide errv; try gw_hide lo; try gw_hide st; try gw_hide m; try gw_hide fc; try gw_hide F; try gw_hide s11; try gw_hide s10; try gw_hide s9; try gw_hide s8; try gw_hide s7; try gw_hide s6; try gw_hide s5; try gw_hide s4; try gw_hide s3; try gw_hide s2; try gw_hide s1; try gw_hide s0; try gw_hide tp; try gw_hide gp; try gw_hide sp; try gw_hide ra; first [clear Q | gw_hide Q | idtac]; try gw_hide s; try gw_hide o; try gw_hide bail; try gw_hide k; first [clear R | gw_hide R | idtac].
intros until t6. intros AMPI AI RGI ACNT BRK PTRI MR1 MI1 FR1 ST1 ERR1 AUX1 AG1 _.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof LO as LO'. unfold alloc_ceiling in LO'. pose proof rETP as rETP'. pose proof TP as TPv.
pose proof MR1 as (WF1 & (HX1 & HX2 & HX3 & HX4 & HX5 & HX6) & _). pose proof WF1 as (RS & WR & DJ & WA & WG).
assert (TLI : forall tl, c_meta_area_tail (ctx stI) = Some tl -> is_Some ((s_areas stI) !! tl)) by (exact (amp_tail stI AMPI)).
assert (MKI : forall q mr, (s_metas stI) !! q = Some mr -> meta_slot stI q) by (exact (amp_mkeys stI AMPI)).
unfold ctx_head_cells in HX1. rewrite ACNT in HX1. unfold ctx_tail_cells, brk_word in HX6. rewrite BRK in HX6.

eapply rimplT_evt.
{ eapply (ram_disp_untried _ gp tp t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI); [gw_exact MR1| gw_exact ACNT| gw_exact BRK]. }
intros ms2 ->.
eapply (rimplT_brk0 o _ s).
{ exact (ram_brk0_node x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 4095) a2 a3 a4 a5 a6 (Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960))
s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1). }
intros cur ms3 [-> CR]. unfold rbrk_regs.
destruct (brk0_answer_ok cur) eqn:B0; cbn [negb]; [| apply rimplT_undef].
unfold brk0_answer_ok, TWO64, PGSZ in B0. apply andb_prop in B0. destruct B0 as [B0 _]. apply andb_prop in B0. destruct B0 as [C0 CAL].
apply Z.ltb_lt in C0. apply Z.eqb_eq in CAL.
rewrite (round_up_pg_aligned cur CAL). cbv zeta. unfold PGSZ.
replace (2 * 4096) with 8192 by first [reflexivity | (cbn; lia)].

eapply rimplT_evt.
{ eapply (ram_bu_mid _ gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m1 cur); [lia| gw_exact CAL| unfold wz in HX6; gw_exact HX6| gw_exact MI1]. }
intros ms4 (a2' & m2 & -> & MU2 & WM2 & MI2 & TC2).
eapply (rimplT_brk o (cur + 8192) _ (set_brk_ps cur s)).
{ lia. }
{ exact (ram_brk_node_at x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 0) a2' a3 a4 a5 a6 (Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960))
s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 (base + 0x168) (or_intror eq_refl) cur (cur + 8192) ltac:(lia)). }
intros a ms5 ->. cbn [ps_brk set_brk_ps]. unfold brk_res, brk_mem, rbrk_regs. gw_addr_norm.

assert (FR2 : rw_cells segs m2 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [gw_exact FR1| gw_exact MU2| gw_exact WM2|]; cbn; gw_expose_fam RATP; lia).
assert (ST2 : stk segs m2 lo (bv_unsigned sp + -64)) by (eapply stk_transport_disjoint; [gw_exact ST1| gw_exact MU2| gw_exact WM2|]; cbn; gw_expose_fam RATP; lia).
assert (ERR2 : rw_cells segs m2 (errno_addr tp) [C4 e1]) by (eapply rw_cells_transport; [gw_exact ERR1| gw_exact MU2| gw_exact WM2|]; cbn; rewrite rETP'; gw_expose_fam RATP; lia).
assert (HC2 : rw_cells segs m2 (RATP + 131968) ltac:(lazymatch type of HX1 with rw_cells _ _ _ ?cs => exact cs end))
by (eapply rw_cells_transport; [gw_exact HX1| gw_exact MU2| gw_exact WM2|]; cbn; gw_expose_fam RATP; lia).
assert (M12 : magree (rFP stI) m1 m2).
{ eapply magree_of_munch; [gw_exact MU2|]. cbn. split; [| exact I]. intros y Hy. left. right. right. left. gw_expose_fam RATP. lia. }
destruct a.
-
unfold brk_answer_ok. rewrite Z.eqb_refl. cbn [orb negb].
destruct (brk_pages_ok stI cur 8192) eqn:BPO; cbn [negb]; [| apply rimplT_undef].
unfold brk_pages_ok in BPO. apply andb_prop in BPO. destruct BPO as [BPO RF]. apply andb_prop in BPO. destruct BPO as [_ OC]. apply Z.leb_le in OC.
unfold alloc_ceiling in OC.
rewrite (brk_new_pages_aligned cur 8192) by (first [lia | gw_exact CAL | reflexivity]).
pose proof (rimage_range_clear stI cur 8192 RS RF ltac:(lia)) as IMG.
assert (Hc1 : 0 <= cur < 2^64) by lia. assert (Hn1 : 0 <= 8192 < 2^64) by lia. assert (Hcn : cur + 8192 <= 2^64) by lia.
set (m3 := apply_zeros m2 [(wa cur, Z_to_bv 64 8192)]).
assert (HC3 : rw_cells segs m3 (RATP + 131968) ltac:(lazymatch type of HX1 with rw_cells _ _ _ ?cs => exact cs end))
by (apply (rw_cells_zeros_other segs m2 cur 8192 Hc1 Hn1 Hcn); [gw_exact HC2| cbn; gw_expose_fam RATP; lia]).
assert (TC3 : rw_cells segs m3 ((RATP + 132880)) [C1 (b8 (c_seq (ctx stI))); CB 7 (zeros 7); C8 (Z_to_bv 64 cur)])
by (apply (rw_cells_zeros_other segs m2 cur 8192 Hc1 Hn1 Hcn); [gw_expose_fam RATP; gw_exact TC2| cbn; gw_expose_fam RATP; lia]).
assert (MI3 : mem_inv segs m3) by (apply (mem_inv_zeros segs m2 cur 8192 Hc1 Hn1 Hcn MI2); intros y Hy; apply ref_ro_addr_false; lia).
assert (FR3 : rw_cells segs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)) by (apply (rw_cells_zeros_other segs m2 cur 8192 Hc1 Hn1 Hcn); [gw_exact FR2| cbn; lia]).
assert (ST3 : stk segs m3 lo (bv_unsigned sp + -64)) by (apply (stk_zeros segs m2 cur 8192 Hc1 Hn1 Hcn); gw_exact ST2).
assert (ERR3 : rw_cells segs m3 (errno_addr tp) [C4 e1]) by (apply (rw_cells_zeros_other segs m2 cur 8192 Hc1 Hn1 Hcn); [gw_exact ERR2| cbn; rewrite rETP'; lia]).
pose proof (rw_cells_zeros_new segs m2 cur 8192 Hc1 Hn1 Hcn) as ZN. fold m3 in ZN.
assert (M23 : magree (rFP stI) m2 m3).
{ intros y Hy Hc. unfold m3. apply (zeros_outside m2 cur 8192 Hc1 Hn1 Hcn). rewrite wa_unsigned by lia.
destruct (Z.lt_ge_cases y cur); [lia|]. destruct (Z.lt_ge_cases y (cur + 8192)); [| lia].
exfalso. apply Hc. right. eapply (rfresh_of_ranges_free stI cur 8192); [gw_exact RGI| exact (ami_reserved _ _ AI)| gw_exact RF| unfold alloc_ceiling; lia| lia]. }

assert (E23 : forall y, 0 <= y < 2^64 -> ~ (cur <= y < cur + 8192) -> m3 (wa y) = m2 (wa y)).
{ intros y Hy Hn. unfold m3. apply (zeros_outside m2 cur 8192 Hc1 Hn1 Hcn). rewrite wa_unsigned by lia. lia. }
clearbody m3.

eapply rimplT_evt.
{ eapply (ram_bu_ok _ gp tp t0 t1 t2 (Z_to_bv 64 0) a2' a3 a4 a5 a6 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ F fc m3 cur);
first [gw_exact TC3 | lia]. }
intros ms6 ->.
pose proof MI3 as MI4. pose proof FR3 as FR4. pose proof ST3 as ST4. pose proof TC3 as TC4. pose proof HC3 as HC4. pose proof ERR3 as ERR4.
eapply (rimplT_mmap_fixed o cur PGSZ _ (set_brk_ps (cur + 8192) (set_brk_ps cur s))).
{ unfold PGSZ. eapply (rmmap_fixed_spec (dec_mmap_fixed cur 4096) (fx_rel cur)) with (lo := lo) (errv := e1);
[ intros rsp fa Hd; exact (dec_mmap_fixed_shape cur 4096 rsp fa Hd)
| rewrite unsigned_lit by lia; gw_exact ST4 | gw_exact ERR4 | gw_exact MI4 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ..];
rewrite ?QWTl.Mq5.mmap_len_round_up, ?rETP', ?TPv, ?unsigned_lit by lia; try (change (round_up_pg 4096) with 4096); try lia. }
intros fa ms7 MP. unfold rmmap_fixed_post in MP.
destruct MP as (rr & u & u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m5 & REL & -> & MU5 & WM5 & MI5 & ST5 & ERR5).
rewrite QWTl.Mq5.mmap_len_round_up in MU5. change (round_up_pg 4096) with 4096 in MU5. rewrite unsigned_lit in MU5, ST5 by lia.
try g_ret_pc_any.

replace (mmap_fixed_answer_ok cur (fixed_val cur fa)) with true.
2:{ symmetry. unfold mmap_fixed_answer_ok, is_errno_form, fixed_val, neg_errno, TWO64.
destruct fa as [e|  |e]; cbn in REL.
- destruct REL as [RE _]. destruct (errno_of_Some _ _ RE) as [_ HE]. apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
- apply orb_true_iff. right. apply Z.eqb_refl.
- destruct REL as [RE _]. destruct (errno_of_Some _ _ RE) as [_ HE]. apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
cbn [negb].
unfold new_region. cbv beta iota zeta delta [fst snd].
set (rid := s_next_rid stI).
pose proof (rAMI_new_region st stI RKBrk cur 8192 AI ltac:(discriminate) ltac:(lia)) as (AI1 & RG1 & CQ1 & CN1).
unfold new_region in AI1, RG1, CQ1, CN1. cbn [fst snd] in AI1, RG1, CQ1, CN1. fold rid in AI1, RG1, CQ1, CN1 |- *.
set (st1 := set_next_rid (N.succ rid) _) in AI1, RG1, CQ1, CN1 |- *.
rewrite (am_after_brk_false_eq st1 _ (rid, 4096) k bail) by (cbn; first [lia | reflexivity]).
rewrite am_carve_took, carve_st_brk_irrel.
set (stX := upd_ctx _ st1).

assert (E45 : forall y, 0 <= y < 2^64 -> ~ (bv_unsigned sp - 64 - 80 <= y < bv_unsigned sp - 64) -> ~ (errno_addr tp <= y < errno_addr tp + 4) -> ~ (cur <= y < cur + 4096) -> m5 (wa y) = m3 (wa y)).
{ intros y Hy N1 N2 N3. apply MU5. rewrite wa_unsigned by lia. cbn. rewrite ?rETP' in *. repeat split; lia. }
assert (HC5 : rw_cells segs m5 (RATP + 131968) ltac:(lazymatch type of HX1 with rw_cells _ _ _ ?cs => exact cs end)).
{ eapply RMallocKit_A2__rrw_cells_agree; [gw_exact HC4|]. cbn. intros y Hy. apply E45; rewrite ?rETP'; gw_expose_fam RATP; lia. }
assert (TC5 : rw_cells segs m5 ((RATP + 132880)) [C1 (b8 (c_seq (ctx stI))); CB 7 (zeros 7); C8 (Z_to_bv 64 cur)]).
{ eapply RMallocKit_A2__rrw_cells_agree; [gw_exact TC4|]. cbn. intros y Hy. apply E45; rewrite ?rETP'; gw_expose_fam RATP; lia. }
assert (FR5 : rw_cells segs m5 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
{ eapply RMallocKit_A2__rrw_cells_agree; [gw_exact FR4|]. cbn. intros y Hy. apply E45; rewrite ?rETP'; lia. }
eapply rimplT_evt.
{ eapply (ram_b_store _ gp tp u0 u1 u2 _ u3 u4 u5 u6 u7 u8 u9 s4x s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m5 (cur + 8192));
first [gw_exact HC5 | gw_exact TC5 | gw_exact MI5 | lia]. }
intros ms8 (m6 & -> & MU6 & WM6 & MI6 & HC6 & TC6). replace (cur + 8192 - 4096) with (cur + 4096) by lia.
assert (FR6 : rw_cells segs m6 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [gw_exact FR5| gw_exact MU6| gw_exact WM6|]; cbn; gw_expose_fam RATP; lia).
destruct (ami_fresh _ _ AI rid ltac:(unfold rid; lia)) as [FRr FRs].

assert (E16 : forall y, 0 <= y < 2^64 ->
~ ((RATP + 132008) <= y < (RATP + 132016)) -> ~ ((RATP + 132888) <= y < (RATP + 132896)) -> ~ (lo <= y < bv_unsigned sp) -> ~ (errno_addr tp <= y < errno_addr tp + 4) -> ~ (cur <= y < cur + 8192) ->
m6 (wa y) = m1 (wa y)).
{ intros y Hy N0 N1 N2 N3 N4.
rewrite (MU6 (wa y)) by (rewrite wa_unsigned by lia; cbn; gw_expose_fam RATP; lia).
rewrite (E45 y Hy) by (rewrite ?rETP' in *; lia).
rewrite (E23 y Hy) by lia.
apply MU2. rewrite wa_unsigned by lia. cbn. gw_expose_fam RATP. lia. }
assert (MRn1 : rmrep st1 m1).
{ unfold st1. apply (RMallocKit_A2__rmrep_new_region stI m1 m1 cur 8192 RKBrk);
first [ gw_exact MR1
| eapply ptrs_in_mono; [| gw_exact PTRI]; intros q Hq; cbn in Hq; intros ->; unfold rid in Hq; lia
| gw_exact FRr | gw_exact FRs
| unfold alloc_ceiling; change (round_up_pg 8192) with 8192; lia
| change (round_up_pg 8192) with 8192; gw_exact RF
| intros; reflexivity
| intros; discriminate
| lia ]. }
assert (CQX : forall q, fst q <> rid -> conc stX q = conc stI q) by (intros q Hq; change (conc stX q) with (conc st1 q); apply CQ1; gw_exact Hq).
pose proof PTRI as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10).
assert (PWX : forall q, optr_in (fun r => (r < s_next_rid stI)%N) q -> pw stX q = pw stI q).
{ intros [q|] Hq; unfold pw, oconc; [rewrite CQX; [reflexivity|]|reflexivity]. cbn in Hq. unfold rid. lia. }
assert (MRX : rmrep stX m6).
{ apply (rmrep_agree_but_ctx st1 stX m1 m6 MRn1); try reflexivity.
- intros y Hy. apply E16; rewrite ?rETP'; gw_expose_fam RATP; lia.
- intros y Hy. apply E16; rewrite ?rETP'; gw_expose_fam RATP; lia.
- intros y Hy. apply E16; rewrite ?rETP'; (gw_expose_fam RGOT_SSP; gw_expose_fam RATP); lia.
- intros y Hy. apply E16; rewrite ?rETP'; gw_expose_fam RATP; lia.
- intros a ar Ha y Hy. change (s_areas st1) with (s_areas stI) in Ha.
destruct (rarea_conc stI a ar WF1 Ha) as (rra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & RBa & RBAa & RBCa).
destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa). destruct (rreserved_disjoint _ _ RFa) as (Da1 & _ & Da23 & Da2). unfold alloc_ceiling in RBCa.
rewrite (CQ1 a) in Hy by (intros E; rewrite E, FRr in Hra; discriminate).
apply E16; rewrite ?rETP'; gw_expose_fam RATP; try lia. apply (rrepfoot_clear stI m1 cur 8192 y MR1 RF). left. eapply rrepfoot_area; [gw_exact Ha| lia].
- intros b gh Hb y Hy. change (s_groups st1) with (s_groups stI) in Hb.
destruct (rgroup_conc stI b gh WF1 Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & Alb & RBb & RBCb).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RFb). destruct (rreserved_disjoint _ _ RFb) as (Db1 & _ & Db23 & Db2). unfold alloc_ceiling in RBCb.
pose proof (round_up_pg_ge (r_len rb)).
rewrite (CQ1 b) in Hy by (intros E; rewrite E, FRr in Hrb; discriminate).
apply E16; rewrite ?rETP'; gw_expose_fam RATP; try lia. apply (rrepfoot_clear stI m1 cur 8192 y MR1 RF). left. do 5 right. left. exists b, gh. split; [gw_exact Hb| lia].
- intros q rq Hq Kq y Hy.
assert (Hq' : (s_regions stI) !! q = Some rq).
{ change (s_regions st1) with (<[rid := mkRegion RKBrk cur 8192]> (s_regions stI)) in Hq.
destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq in Hq; inversion Hq; subst; discriminate| rewrite lookup_insert_ne in Hq by congruence; gw_exact Hq]. }
destruct (WR _ _ Hq') as (RB0 & _ & _ & RBC & RFq). destruct (rreserved_disjoint _ _ RFq) as (Dq1 & _ & Dq23 & Dq2). unfold alloc_ceiling in RBC.
apply E16; rewrite ?rETP'; gw_expose_fam RATP; try lia. apply (rrepfoot_clear stI m1 cur 8192 y MR1 RF). right. exists q, rq. auto.
-
destruct (rmrep_ctx_mid_agree st1 stX m1 m6 MRn1 ltac:(right; repeat split; reflexivity) eq_refl) as (X2 & X3 & X4 & X5).
{ intros y Hy. apply E16; rewrite ?rETP'; gw_expose_fam RATP; lia. }
split; [| split; [gw_exact X2| split; [gw_exact X3| split; [gw_exact X4| split; [gw_exact X5|]]]]].
+ unfold ctx_head_cells. rewrite !PWX by assumption.
cbn [ctx stX st1 upd_ctx s_ctx set_next_rid set_regions set_avail_meta_area_count set_brk c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
change (s_ctx stI) with (ctx stI). unfold pw in HC6 |- *. cbn [oconc] in HC6 |- *. unfold wz. gw_exact HC6.
+ unfold ctx_tail_cells, brk_word. cbn [ctx stX upd_ctx s_ctx set_avail_meta_area_count set_brk c_brk c_seq].
change (conc stX (rid, 8192)) with (conc st1 (rid, 8192)). rewrite CN1. change (s_ctx st1) with (ctx stI). unfold wz. gw_exact TC6. }

assert (ZP3 : rw_cells segs m3 (cur + 4096) [CB 4096 (zeros 4096)]).
{ destruct ZN as [[_ ZB0] ZW0]. cbn [cells_bytes cbytes cells_size csize app] in ZB0, ZW0. rewrite app_nil_r in ZB0. rewrite Nat.add_0_r in ZW0.
eapply (rrw_cells_of_zeros m3 cur 8192 4096); [gw_exact ZB0| gw_exact ZW0| split; [exact (zeros_length 4096)| exact I]| cbn [cells_bytes cbytes cells_size csize]; rewrite app_nil_r, Nat.add_0_r; reflexivity| lia| cbv; discriminate]. }
assert (ZP6 : rw_cells segs m6 (cur + 4096) [CB 4096 (zeros 4096)]).
{ eapply rw_cells_transport; [| gw_exact MU6| gw_exact WM6| cbn [cells_size csize]; rewrite ?Nat.add_0_r; cbn; gw_expose_fam RATP; lia].
eapply RMallocKit_A2__rrw_cells_agree; [gw_exact ZP3|].
cbn [cells_size csize]. rewrite ?Nat.add_0_r. cbn. intros y Hy. apply E45; rewrite ?rETP'; lia. }
destruct ZP6 as [[_ ZB] ZW]. cbn [cells_bytes cbytes cells_size csize app] in ZB, ZW. rewrite app_nil_r in ZB. rewrite Nat.add_0_r in ZW.
assert (ST6 : stk segs m6 lo (bv_unsigned sp + -64)) by (eapply stk_transport_disjoint; [gw_exact ST5| gw_exact MU6| gw_exact WM6|]; cbn; gw_expose_fam RATP; lia).
assert (ERR6 : rw_cells segs m6 (errno_addr tp) [C4 (sysret_errno rr e1)]) by (eapply rw_cells_transport; [gw_exact ERR5| gw_exact MU6| gw_exact WM6|]; cbn; rewrite rETP'; gw_expose_fam RATP; lia).
assert (FPX : forall y, rFP stI y -> rFP stX y).
{ intros y X. eapply rFP_mono; [| gw_exact X]. intros q rq Hq. exists rq.
change (s_regions stX) with (<[rid := mkRegion RKBrk cur 8192]> (s_regions stI)).
rewrite lookup_insert_ne by (intros ->; rewrite FRr in Hq; discriminate). repeat split; auto; lia. }
assert (M16 : magree (rFP stX) m1 m6).
{ intros y Hy Hc.
assert (~ ((RATP + 132008) <= y < (RATP + 132016))) by (intros X; apply Hc; left; right; right; left; gw_expose_fam RATP; lia).
assert (~ ((RATP + 132888) <= y < (RATP + 132896))) by (intros X; apply Hc; left; right; right; left; gw_expose_fam RATP; lia).
assert (~ (lo <= y < bv_unsigned sp)) by (intros X; apply Hc; left; left; gw_exact X).
assert (~ (errno_addr tp <= y < errno_addr tp + 4)) by (intros X; apply Hc; left; right; left; rewrite <- TPv; gw_exact X).
assert (~ (cur <= y < cur + 8192)).
{ intros X. apply Hc. right. eapply (rfresh_of_ranges_free stI cur 8192); [gw_exact RGI| exact (ami_reserved _ _ AI)| gw_exact RF| unfold alloc_ceiling; lia| gw_exact X]. }
apply E16; assumption. }
replace (Z_to_bv 64 (cur + 4096)) with (Z_to_bv 64 (conc stX (rid, 4096))) by (change (conc stX (rid, 4096)) with (conc st1 (rid, 4096)); rewrite CN1; reflexivity).
eapply (rcarve_K stX (rid, 4096) (mkRegion RKBrk cur 8192) m6 _ _ (sysret_errno rr e1));
first [gw_exact RG1 | gw_exact MRX | gw_exact MI6 | gw_exact FR6 | gw_exact ST6 | gw_exact ERR6 | reflexivity | idtac].
all: try (cbn [snd fst r_len r_base r_kind]; unfold pgal, lr_lo; cbn [r_kind r_base]; change (round_up_pg 8192) with 8192; first [discriminate | lia]).
+ unfold stX. apply (rAMI_ctx st st1 _ AI1).
* cbn. repeat split; reflexivity.
* cbn. exact (ami_secretr _ _ AI1).
* left. reflexivity.
* right. right. exists rid, 8192, (mkRegion RKBrk cur 8192). split; [reflexivity|]. split; [gw_exact RG1|]. cbn. discriminate.
+ change (s_areas stX) with (s_areas stI). lazymatch goal with |- ?t = None => destruct t as [ar|] eqn:EA end; [| reflexivity].
exfalso. destruct (WA _ _ EA) as (rr0 & Hrr & _). cbn [fst] in Hrr. rewrite FRr in Hrr. discriminate.
+ intros j Hj. change (s_metas stX) with (s_metas stI). lazymatch goal with |- ?t = None => destruct t as [mr|] eqn:EM end; [| reflexivity].
exfalso. destruct (MKI _ _ EM) as (a & ar & kk & Ha & Hk & Eq). destruct (WA _ _ Ha) as (rr0 & Hrr & _).
assert (Ef : fst a = rid) by (unfold aadd in Eq; cbn in Eq; inversion Eq; reflexivity). rewrite Ef, FRr in Hrr. discriminate.
+ intros tl Htl. change (s_areas stX) with (s_areas stI). apply TLI. gw_exact Htl.
+ cbn. lia.
+ change (conc stX (rid, 4096)) with (conc st1 (rid, 4096)). rewrite CN1. gw_exact ZB.
+ change (conc stX (rid, 4096)) with (conc st1 (rid, 4096)). rewrite CN1. gw_exact ZW.
+ eapply rauxv_ok_magree; [gw_exact AUX1| gw_exact M16| intros y X; exact (rFP_below stX y (proj1 MRX) X)].
+ eapply magree_trans; [gw_exact AG1| gw_exact M16| gw_exact FPX| intros y X; gw_exact X].
+ unfold brk_link_ps. cbn [ctx stX upd_ctx s_ctx set_avail_meta_area_count set_brk c_brk ps_brk set_brk_ps].
change (conc stX (rid, 8192)) with (conc st1 (rid, 8192)). rewrite CN1. reflexivity.
-
unfold brk_answer_ok. rewrite Z.eqb_refl.
replace (cur =? cur + 8192) with false by (symmetry; apply Z.eqb_neq; lia). cbn [orb negb].
eapply rimplT_evt.
{ eapply (ram_bu_fail _ gp tp t0 t1 t2 (Z_to_bv 64 0) a2' a3 a4 a5 a6 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ F fc m1 m2 stI cur);
first [gw_exact MR1 | gw_exact MU2 | gw_exact WM2 | gw_exact ACNT | gw_exact MI2 | reflexivity | gw_exact TC2 | lia]. }
intros ms6 (m3 & -> & MU3 & WM3 & MI3 & MRD).
assert (M23 : magree (rFP stI) m2 m3).
{ eapply magree_of_munch; [gw_exact MU3|]. cbn. split; [| exact I]. intros y Hy. left. right. right. left. gw_expose_fam RATP. lia. }
eapply (rmmap_path (upd_ctx (set_brk BrkDead) stI) m3 (set_brk_ps cur s) junk e1); first [gw_exact MRD | gw_exact MI3 | reflexivity | idtac].
+ apply (rAMI_ctx st stI _ AI); [cbn; repeat split; reflexivity| cbn; exact (ami_secretr _ _ AI)| left; reflexivity| right; left; reflexivity].
+ gw_exact RGI.
+ gw_exact ACNT.
+ change (ctx (upd_ctx (set_brk BrkDead) stI)) with (set_brk BrkDead (ctx stI)). cbn [c_meta_alloc_shift set_brk]. pose proof (amp_shift stI AMPI). lia.
+ gw_exact TLI.
+ gw_exact MKI.
+ pose proof PTRI as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10). apply rptrs_in_upd_ctx; cbn; try assumption; try reflexivity; try exact I.
+ eapply rw_cells_transport; [gw_exact FR2| gw_exact MU3| gw_exact WM3|]. cbn. gw_expose_fam RATP. lia.
+ eapply stk_transport_disjoint; [gw_exact ST2| gw_exact MU3| gw_exact WM3|]. cbn. gw_expose_fam RATP. lia.
+ eapply rw_cells_transport; [gw_exact ERR2| gw_exact MU3| gw_exact WM3|]. cbn. rewrite rETP'. gw_expose_fam RATP. lia.
+ eapply rauxv_ok_magree; [gw_exact AUX1| | intros y X; exact (rFP_below stI y WF1 X)].
eapply magree_trans; [gw_exact M12| gw_exact M23| intros y X; gw_exact X| intros y X; gw_exact X].
+ eapply (magree_trans (rFP stI) (rFP stI) _ m m1 m3 AG1); [eapply magree_trans; [gw_exact M12| gw_exact M23| intros y X; gw_exact X| intros y X; gw_exact X] | |];
intros y X; (eapply rFP_same; [| gw_exact X]); reflexivity.
Qed.

#[using="RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rerrno_loc_entry rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 joff_98 joff_120 joff_173 joff_175 CODE BASE4 BASER D_98 E_98 D_120 E_120 D_173 E_173 D_175 E_175 LINK_98 LINK_120 LINK_173 LINK_175 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_reservedZ LAY_ref_reserved ref_ro_addr_false rmprotect_spec rmmap_anon_spec rmmap_fixed_spec rconc_meta_inj ralloc_meta_entry rmmap_entry rmprotect_entry errv AMP TK LO LOLE ERR TP KH"] Lemma rbody_spec : forall (stI : mstate) (x1 t0 t1 t2 s1x s4x a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : mem) (junk : list byte) (e1 : word),
RAMpre stI -> AMI st stI -> s_regions stI = s_regions st -> brk_link_ps stI s ->
rmrep stI m1 -> mem_inv segs m1 ->
rw_cells segs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk segs m1 lo (bv_unsigned sp + -64) ->
rw_cells segs m1 (errno_addr tp) [C4 e1] -> rauxv_ok m1 (bv_unsigned sp) -> magree (rFP stI) m m1 ->
rimplT o (am_body stI k bail) s Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xb4)) fc None m1 (seg_rom segs)).
Proof. clear - RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rerrno_loc_entry rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 joff_98 joff_120 joff_173 joff_175 CODE BASE4 BASER D_98 E_98 D_120 E_120 D_173 E_173 D_175 E_175 LINK_98 LINK_120 LINK_173 LINK_175 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_reservedZ LAY_ref_reserved ref_ro_addr_false rmprotect_spec rmmap_anon_spec rmmap_fixed_spec rconc_meta_inj ralloc_meta_entry rmmap_entry rmprotect_entry errv AMP TK LO LOLE ERR TP KH segs base RATP R k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st lo MR BL AUX ST MI. gw_expose_fam RATP. first [clear MI | gw_hide MI | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear MR | gw_hide MR | idtac]; try gw_hide lo; try gw_hide st; first [clear m | gw_hide m | idtac]; try gw_hide fc; try gw_hide F; try gw_hide s11; try gw_hide s10; try gw_hide s9; try gw_hide s8; try gw_hide s7; try gw_hide s6; try gw_hide s5; try gw_hide s4; try gw_hide s3; try gw_hide s2; try gw_hide s1; try gw_hide s0; try gw_hide tp; try gw_hide gp; try gw_hide sp; try gw_hide ra; first [clear Q | gw_hide Q | idtac]; try gw_hide s; first [clear o | gw_hide o | idtac]; try gw_hide bail; try gw_hide k; first [clear R | gw_hide R | idtac].
intros until e1. intros AMPI AI RGI BLI MR1 MI1 FR1 ST1 ERR1 AUX1 AG1.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof MR1 as (WF1 & _).
unfold am_body.
destruct (c_free_meta_head (ctx stI)) as [h|] eqn:FMH.
-
pose proof (amp_fmh stI AMPI h FMH) as [HN0 HM0].
pose proof (amp_links stI AMPI) as [CLn CLp CLno CLs].
pose proof (CLs h HN0) as MSh.
pose proof (amp_fml stI AMPI h HM0 HN0) as (CL0 & FMn & FMp).
destruct (m_next (get_meta_rec stI h)) as [nx|] eqn:HN; [| exfalso; apply HN0; reflexivity].
destruct (m_prev (get_meta_rec stI h)) as [pv|] eqn:HP.
2:{ exfalso. pose proof (proj2 (CLno h) HP) as X. rewrite HN in X. discriminate. }
destruct (CLn h nx HN) as [PVn MSn]. destruct (CLp h pv HP) as [NXp MSp].
assert (SELF : nx = h <-> pv = h).
{ split; intros ->; [rewrite HP in PVn| rewrite HN in NXp]; congruence. }
eapply rimplT_evt.
{ eapply (ram_deq sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra s0 s1 s2 s3 s4 F fc m1 junk lo stI h nx pv);
first [gw_exact MR1 | gw_exact MI1 | gw_exact FMH | gw_exact MSh | gw_exact HN | gw_exact HP | gw_exact MSn | gw_exact MSp | gw_exact SELF | gw_exact FR1 | gw_exact ST1 | gw_exact LO | lia]. }
intros ms2 RP. unfold ram_ret_post in RP.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m2 & -> & PE2 & WM2 & MI2 & ST2 & MR2).
eapply rfinish_K.
+ eapply (ram_rel_deq st stI h nx pv AI); try assumption.
* rewrite <- FMH. symmetry. exact (proj1 (proj2 (ami_ctx _ _ AI))).
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). gw_exact HN.
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). gw_exact HP.
* eapply meta_slot_same_areas; [| gw_exact MSh]. symmetry. exact (ami_areas _ _ AI).
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). gw_exact CL0.
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact (FMn nx eq_refl).
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). intros X. apply (proj1 (CLno nx)) in X. rewrite PVn in X. discriminate.
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact (FMp pv eq_refl).
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). rewrite NXp. discriminate.
+ gw_exact MR2.
+ gw_exact MI2.
+ gw_exact ST2.
+ eapply rrw_cells_magree; [gw_exact ERR1| apply rmagree_of_pres; gw_exact PE2|]. cbn. intros a Ha X. apply (rerrno_not_amfp stI a WF1); [gw_exact X| lia].
+ eapply rauxv_ok_magree; [gw_exact AUX1| apply rmagree_of_pres; gw_exact PE2|]. intros a X. apply (rFP_below stI _ WF1). apply rFP_am. gw_exact X.
+ pose proof (sbl_regions _ _ (sbl_dequeue stI LFree h)) as RD.
eapply magree_trans; [gw_exact AG1| apply rmagree_of_pres; gw_exact PE2| intros a X; eapply rFP_same; [gw_exact RD| gw_exact X] | intros a X; apply rFP_am; eapply (proj2 (ram_fp_same _ _ lo _ a RD)); gw_exact X].
+ unfold brk_link_ps in *. rewrite (sbl_brk _ _ (sbl_dequeue stI LFree h)). destruct (c_brk (ctx stI)) as [| |rid off]; auto.
unfold conc, get_region. rewrite (sbl_regions _ _ (sbl_dequeue stI LFree h)). gw_exact BLI.
+ reflexivity.
+ reflexivity.
+ reflexivity.
+ unfold pw, oconc, wz, conc, get_region. rewrite (sbl_regions _ _ (sbl_dequeue stI LFree h)). reflexivity.
+ intros X; discriminate X.
-
destruct (Z.eqb_spec (c_avail_meta_count (ctx stI)) 0) as [CNT|CNT]; cbn [negb].
+
eapply rimplT_evt.
{ eapply (ram_disp0 _ gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (RATP + 131696)) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI); [gw_exact MR1| gw_exact FMH| gw_exact CNT]. }
intros ms2 ->.
assert (TLI : forall tl, c_meta_area_tail (ctx stI) = Some tl -> is_Some ((s_areas stI) !! tl)) by (exact (amp_tail stI AMPI)).
assert (MKI : forall q mr, (s_metas stI) !! q = Some mr -> meta_slot stI q) by (exact (amp_mkeys stI AMPI)).
assert (PTRI : ptrs_in (fun rid => (rid < s_next_rid stI)%N) stI).
{ apply (ami_ptrs _ _ AI); [| eapply ptrs_in_mono; [| exact (proj1 (amp_ptrs st AMP))]; intros q Hq; cbn in Hq; pose proof (ami_next _ _ AI); lia]. intros rid r Hr _.
destruct (N.lt_ge_cases rid (s_next_rid stI)) as [L|G]; [gw_exact L|]. destruct (ami_fresh _ _ AI rid G) as [X _]. rewrite X in Hr. discriminate. }
destruct (Z.eqb_spec (c_avail_meta_area_count (ctx stI)) 0) as [ACNT|ACNT]; cbn [andb].
*
destruct (c_brk (ctx stI)) as [| |brid boff] eqn:BRK; cbn [negb].
--
eapply (rbrk_untried_path stI m1 junk e1); first [gw_exact AMPI | gw_exact AI | gw_exact RGI | gw_exact ACNT | gw_exact BRK | gw_exact PTRI | gw_exact MR1 | gw_exact MI1 | gw_exact FR1 | gw_exact ST1 | gw_exact ERR1 | gw_exact AUX1 | gw_exact AG1 | reflexivity].
--
eapply rimplT_evt.
{ eapply (ram_disp_dead _ gp tp t0 t1 t2 s1x _ _ a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI); [gw_exact MR1| gw_exact ACNT| gw_exact BRK]. }
intros ms3 ->.
eapply (rmmap_path stI m1 s junk e1); first [gw_exact AI | gw_exact RGI | gw_exact ACNT | gw_exact TLI | gw_exact MKI | gw_exact PTRI | gw_exact MR1 | gw_exact MI1 | gw_exact FR1 | gw_exact ST1 | gw_exact ERR1 | gw_exact AUX1 | gw_exact AG1 | gw_exact BLI | reflexivity | idtac].
pose proof (amp_shift stI AMPI). lia.
--
eapply (rbrk_live_path stI brid boff m1 junk e1); first [gw_exact AMPI | gw_exact AI | gw_exact RGI | gw_exact BLI | gw_exact ACNT | gw_exact BRK | gw_exact PTRI | gw_exact MR1 | gw_exact MI1 | gw_exact FR1 | gw_exact ST1 | gw_exact ERR1 | gw_exact AUX1 | gw_exact AG1].
*
destruct (amp_avail_areas stI AMPI ACNT) as (p & r & AMA & Hr & NK & PAL & P0 & PLR & PHI & FRA).
pose proof (amp_acount stI AMPI) as ACR.
unfold am_after_brk. rewrite (proj2 (Z.eqb_neq _ _) ACNT).
eapply rimplT_evt.
{ eapply (ram_disp_fin _ gp tp t0 t1 t2 s1x _ _ a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI p r);
first [gw_exact MR1 | gw_exact ACNT | gw_exact AMA | gw_exact Hr | unfold pgal, PGSZ in *; gw_exact PAL | lia | idtac]. unfold PGSZ in *. lia. }
intros ms3 ->.
eapply (rfinish_path stI p r m1 s junk e1); first [gw_exact AI | gw_exact AMA | gw_exact Hr | gw_exact NK | gw_exact P0 | gw_exact PLR | gw_exact TLI | gw_exact MR1 | gw_exact MI1 | gw_exact FR1 | gw_exact ST1 | gw_exact ERR1 | gw_exact AUX1 | gw_exact AG1 | gw_exact BLI | reflexivity | idtac].
-- unfold PGSZ in PHI. lia.
-- unfold pgal. unfold PGSZ in PAL. gw_exact PAL.
-- apply (proj1 (FRA p eq_refl ltac:(lia))).
-- intros j Hj. apply (proj2 (FRA (aadd p (AREA_HDR + META_SIZE * j)) eq_refl ltac:(cbn; unfold AREA_HDR, META_SIZE; lia))).
-- lia.
+
destruct (amp_avail stI AMPI CNT) as (aa & ar & kk & Haa & AVM & K0 & K1 & MQ).
pose proof (amp_count stI AMPI) as CR.
assert (MSq : meta_slot stI (aadd aa (AREA_HDR + META_SIZE * kk))) by (exists aa, ar, kk; repeat split; auto; unfold NSLOTS in *; lia).
rewrite (am_take_eq stI k bail _ AVM).
eapply rimplT_evt.
{ eapply (ram_take_walk sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra s0 s1 s2 s3 s4 F fc m1 junk lo stI _);
first [gw_exact MR1 | gw_exact MI1 | gw_exact FMH | gw_exact CNT | gw_exact AVM | gw_exact MSq | gw_exact FR1 | gw_exact ST1 | gw_exact LO | unfold NSLOTS in CR; lia | lia]. }
intros ms2 RP. unfold ram_ret_post in RP.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m2 & -> & PE2 & WM2 & MI2 & ST2 & MR2).
eapply rfinish_K.
* eapply (ram_rel_take st stI _ AI).
-- rewrite <- AVM. symmetry. exact (proj1 (proj2 (proj2 (ami_ctx _ _ AI)))).
-- rewrite <- (ami_metas _ _ AI). gw_exact MQ.
-- eapply meta_slot_same_areas; [| gw_exact MSq]. symmetry. exact (ami_areas _ _ AI).
* gw_exact MR2.
* gw_exact MI2.
* gw_exact ST2.
* eapply rrw_cells_magree; [gw_exact ERR1| apply rmagree_of_pres; gw_exact PE2|]. cbn. intros a Ha X. apply (rerrno_not_amfp stI a WF1); [gw_exact X| lia].
* eapply rauxv_ok_magree; [gw_exact AUX1| apply rmagree_of_pres; gw_exact PE2|]. intros a X. apply (rFP_below stI _ WF1). apply rFP_am. gw_exact X.
* eapply magree_trans; [gw_exact AG1| apply rmagree_of_pres; gw_exact PE2| intros a X; eapply rFP_same; [| gw_exact X]; reflexivity | intros a X; apply rFP_am; eapply (proj2 (ram_fp_same _ _ lo _ a ltac:(reflexivity))); gw_exact X].
* unfold brk_link_ps in *. unfold ctx in BLI. cbn. destruct (c_brk (s_ctx stI)) as [| |rid off]; auto.
* reflexivity.
* reflexivity.
* reflexivity.
* unfold pw, oconc, wz. reflexivity.
* intros X; discriminate X.
Qed.

#[using="RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rerrno_loc_entry rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 hi_7 hi_10 hi_14 lo_8 lo_12 lo_15 joff_30 joff_98 joff_120 joff_173 joff_175 e_24f80 CODE BASE4 BASER D_7 E_7 D_8 E_8 D_10 E_10 D_12 E_12 D_14 E_14 D_15 E_15 D_30 E_30 D_98 E_98 D_120 E_120 D_173 E_173 D_175 E_175 ANCH_8 ANCH_12 ANCH_15 LINK_30 LINK_98 LINK_120 LINK_173 LINK_175 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_reservedZ LAY_ref_reserved ref_ro_addr_false rmprotect_spec rmmap_anon_spec rmmap_fixed_spec rconc_meta_inj memcpy_spec ralloc_meta_entry rmmap_entry rmprotect_entry lo errv AMP MR TK BL AUX ST LO LOLE ERR MI TP KH"] Lemma ralloc_meta_main : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
rimplT o (alloc_meta st k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom segs)).
Proof. clear - RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rerrno_loc_entry rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 hi_7 hi_10 hi_14 lo_8 lo_12 lo_15 joff_30 joff_98 joff_120 joff_173 joff_175 e_24f80 CODE BASE4 BASER D_7 E_7 D_8 E_8 D_10 E_10 D_12 E_12 D_14 E_14 D_15 E_15 D_30 E_30 D_98 E_98 D_120 E_120 D_173 E_173 D_175 E_175 ANCH_8 ANCH_12 ANCH_15 LINK_30 LINK_98 LINK_120 LINK_173 LINK_175 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_reservedZ LAY_ref_reserved ref_ro_addr_false rmprotect_spec rmmap_anon_spec rmmap_fixed_spec rconc_meta_inj memcpy_spec ralloc_meta_entry rmmap_entry rmprotect_entry lo errv AMP MR TK BL AUX ST LO LOLE ERR MI TP KH segs R k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st. gw_expose_fam RATP. try gw_hide st; try gw_hide m; try gw_hide fc; try gw_hide F; try gw_hide s11; try gw_hide s10; try gw_hide s9; try gw_hide s8; try gw_hide s7; try gw_hide s6; try gw_hide s5; try gw_hide s4; try gw_hide s3; try gw_hide s2; try gw_hide s1; try gw_hide s0; try gw_hide tp; try gw_hide gp; try gw_hide sp; try gw_hide ra; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear R | gw_hide R | idtac].
intros. pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof LO as LO'. unfold alloc_ceiling in LO'. pose proof rETP as rETP'. pose proof TP as TPv.
pose proof MR as (WF0 & _).
rewrite alloc_meta_eq. unfold ralloc_meta_entry.
eapply rimplT_evt.
{ eapply (ram_entry ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo st);
first [gw_exact MR | gw_exact MI | gw_exact AUX | gw_exact ST | gw_exact LO | exact (amp_init st AMP) | exact (amp_s_secret st AMP) | exact (amp_secret st AMP) | lia]. }
intros ms1 (x1 & u0 & u1 & u2 & s1x & s4x & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u9' & u10 & u11 & u12 & u13 & m1 & junk & -> & MU1 & WM1 & MI1 & FR1 & ST1 & MR1).
assert (M01 : magree (rFP (am_init_st st)) m m1).
{ eapply magree_of_munch; [gw_exact MU1|]. cbn. split; [| split; [| exact I]]; intros y Hy.
- left. left. lia.
- left. right. right. left. gw_expose_fam RATP. lia. }
eapply (rbody_spec (am_init_st st) x1 u0 u1 u2 s1x s4x u3 u4 u5 u6 u7 u8 u9 u9' u10 u11 u12 u13 m1 junk errv).
- exact (rAMpre_init st AMP).
- exact (rAMI_init st AMP).
- exact (ram_init_regions st).
- unfold brk_link_ps in *. rewrite ram_init_brk. destruct (c_brk (ctx st)) as [| |rid off]; auto. rewrite ram_init_conc. gw_exact BL.
- gw_exact MR1.
- gw_exact MI1.
- gw_exact FR1.
- gw_exact ST1.
- eapply rw_cells_transport; [gw_exact ERR| gw_exact MU1| gw_exact WM1|]. rewrite rETP'. cbn. gw_expose_fam RATP. lia.
- eapply rauxv_ok_magree; [gw_exact AUX| gw_exact M01| intros a X; exact (rFP_below (am_init_st st) a (proj1 MR1) X)].
- gw_exact M01.
Qed.
End ASM.

#[using="RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rerrno_loc_entry rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 hi_7 hi_10 hi_14 lo_8 lo_12 lo_15 joff_30 joff_98 joff_120 joff_173 joff_175 e_24f80 CODE BASE4 BASER D_7 E_7 D_8 E_8 D_10 E_10 D_12 E_12 D_14 E_14 D_15 E_15 D_30 E_30 D_98 E_98 D_120 E_120 D_173 E_173 D_175 E_175 ANCH_8 ANCH_12 ANCH_15 LINK_30 LINK_98 LINK_120 LINK_173 LINK_175 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_reservedZ LAY_ref_reserved ref_ro_addr_false rmprotect_spec rmmap_anon_spec rmmap_fixed_spec rconc_meta_inj memcpy_spec rmmap_entry rmprotect_entry"] Theorem ralloc_meta_spec : ralloc_meta_stmt ram_pre.
Proof. clear - RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rerrno_loc_entry rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 hi_7 hi_10 hi_14 lo_8 lo_12 lo_15 joff_30 joff_98 joff_120 joff_173 joff_175 e_24f80 CODE BASE4 BASER D_7 E_7 D_8 E_8 D_10 E_10 D_12 E_12 D_14 E_14 D_15 E_15 D_30 E_30 D_98 E_98 D_120 E_120 D_173 E_173 D_175 E_175 ANCH_8 ANCH_12 ANCH_15 LINK_30 LINK_98 LINK_120 LINK_173 LINK_175 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_reservedZ LAY_ref_reserved ref_ro_addr_false rmprotect_spec rmmap_anon_spec rmmap_fixed_spec rconc_meta_inj memcpy_spec rmmap_entry rmprotect_entry.
unfold ralloc_meta_stmt. intros.
eapply ralloc_meta_main; eassumption.
Qed.

End RC__1.

End G.
End Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3o5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.

Import Q2qa.Mq1 Q4J3.Mq1 Qy5Y.Mq4 Q4J3.Mq3 QlQE QPjm.Mq1.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QJE4.Mq4 Qy5Y.Mq6 QPjm.Mq2 Q4J3.Mq4 QPjm.Mq3 QFkE Q6y7 QDUx.Mq6 QJE4.Mq2 Q3o5.Mq0.
Import Q9A7.Mq0.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QkTt.Mq3.
Import QkTt.Mq4.
Import QCa8.Mq4.
Import Q8QT.Mq2.
Import Qy8Z.Mq3.
Import Qy8Z.Mq4.
Import Qy8Z.Mq5.
Import QZxv.Mqp.
Import Qy8Z.Mq6.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
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
Variables (rerrno_loc_entry rsysret_entry rvm_wait_entry rlock_entry runlock_entry : Z).
Variables (w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 : Z).
Variables (hi_21 hi_64 hi_85 hi_95 : bv 20).
Variables (lo_23 lo_71 lo_86 lo_96 : bv 12).
Variables (joff_89 joff_97 joff_99 joff_104 : bv 21).
Hypothesis CODE : code_at segs base (free_code w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 460.
Let rfree_entry := (base + 0)%Z.
Let rmunmap_entry := (rvm_wait_entry + 524)%Z.
Hypothesis D_21 : decode_any (Z_to_bv 32 w_21) = Some (Auipc 14 hi_21, 4%Z).
Hypothesis E_21 : is_ecall (Z_to_bv 32 w_21) = false.
Hypothesis D_23 : decode_any (Z_to_bv 32 w_23) = Some (OpImm ALU_ADD 14 14 lo_23, 4%Z).
Hypothesis E_23 : is_ecall (Z_to_bv 32 w_23) = false.
Hypothesis D_64 : decode_any (Z_to_bv 32 w_64) = Some (Auipc 14 hi_64, 4%Z).
Hypothesis E_64 : is_ecall (Z_to_bv 32 w_64) = false.
Hypothesis D_71 : decode_any (Z_to_bv 32 w_71) = Some (Load SZ1 false 17 14 lo_71, 4%Z).
Hypothesis E_71 : is_ecall (Z_to_bv 32 w_71) = false.
Hypothesis D_85 : decode_any (Z_to_bv 32 w_85) = Some (Auipc 11 hi_85, 4%Z).
Hypothesis E_85 : is_ecall (Z_to_bv 32 w_85) = false.
Hypothesis D_86 : decode_any (Z_to_bv 32 w_86) = Some (OpImm ALU_ADD 11 11 lo_86, 4%Z).
Hypothesis E_86 : is_ecall (Z_to_bv 32 w_86) = false.
Hypothesis D_89 : decode_any (Z_to_bv 32 w_89) = Some (Jal 1 joff_89, 4%Z).
Hypothesis E_89 : is_ecall (Z_to_bv 32 w_89) = false.
Hypothesis D_95 : decode_any (Z_to_bv 32 w_95) = Some (Auipc 10 hi_95, 4%Z).
Hypothesis E_95 : is_ecall (Z_to_bv 32 w_95) = false.
Hypothesis D_96 : decode_any (Z_to_bv 32 w_96) = Some (OpImm ALU_ADD 10 10 lo_96, 4%Z).
Hypothesis E_96 : is_ecall (Z_to_bv 32 w_96) = false.
Hypothesis D_97 : decode_any (Z_to_bv 32 w_97) = Some (Jal 1 joff_97, 4%Z).
Hypothesis E_97 : is_ecall (Z_to_bv 32 w_97) = false.
Hypothesis D_99 : decode_any (Z_to_bv 32 w_99) = Some (Jal 1 joff_99, 4%Z).
Hypothesis E_99 : is_ecall (Z_to_bv 32 w_99) = false.
Hypothesis D_104 : decode_any (Z_to_bv 32 w_104) = Some (Jal 1 joff_104, 4%Z).
Hypothesis E_104 : is_ecall (Z_to_bv 32 w_104) = false.
Hypothesis ANCH_23 : gw_anch (Z.shiftl (bv_signed hi_21) 12 + (base + 84) + bv_signed lo_23)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_71 : gw_anch (Z.shiftl (bv_signed hi_64) 12 + (base + 256) + bv_signed lo_71)%Z (RATP + 131731).
Hypothesis ANCH_86 : gw_anch (Z.shiftl (bv_signed hi_85) 12 + (base + 340) + bv_signed lo_86)%Z (RATP + 131960).
Hypothesis ANCH_96 : gw_anch (Z.shiftl (bv_signed hi_95) 12 + (base + 380) + bv_signed lo_96)%Z (RATP + 131960).
Hypothesis LINK_89 : gw_anch (base + 356 + bv_signed joff_89)%Z (rlock_entry + 0)%Z.
Hypothesis LINK_97 : gw_anch (base + 388 + bv_signed joff_97)%Z (runlock_entry + 0)%Z.
Hypothesis LINK_99 : gw_anch (base + 396 + bv_signed joff_99)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_104 : gw_anch (base + 416 + bv_signed joff_104)%Z (rvm_wait_entry + 524)%Z.
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
Hypothesis AL_rsysret_entry : gw_al rsysret_entry 4.
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

Definition rmunmap_post : ltac:(gw_rebind_ty (@Q8QT.Mq2.rmunmap_post segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q8QT.Mq2.rmunmap_post segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@Q8QT.Mq2.rmunmap_post segs) (@rmunmap_post) gw_tbl_0).
Definition rimplT : ltac:(gw_rebind_ty (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_1)).
#[global] Arguments rimplT {R}%_type_scope o t s Q%_function_scope ms.
Notation gw_tbl_2 := (gw_ent (@QkTt.Mq3.rimplT segs RC__) (@rimplT) (gw_ent (@QCa8.Mq5.rimplT segs RC__) (@rimplT) (gw_ent (@QZxv.Mqp.rimplT segs RC__) (@rimplT) gw_tbl_1))).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@Qy8Z.Mq4.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq3.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq3.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QZxv.Mqp.rpres_except segs) (@rpres_except) gw_tbl_2)))))).
Definition rfree_fp : ltac:(gw_rebind_ty (@QDXD.Mq2.rfree_fp RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rfree_fp RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@Qy8Z.Mq6.rfree_fp RATP) (@rfree_fp) (gw_ent (@Qy8Z.Mq4.rfree_fp RATP) (@rfree_fp) (gw_ent (@Qy8Z.Mq3.rfree_fp RATP) (@rfree_fp) (gw_ent (@QDXD.Mq2.rfree_fp RATP) (@rfree_fp) (gw_ent (@QZxv.Mqp.rfree_fp RATP) (@rfree_fp) gw_tbl_3))))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@Qy8Z.Mq6.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QZxv.Mqp.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_4))))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@Qy8Z.Mq6.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QZxv.Mqp.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_5))))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@Qy8Z.Mq6.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QZxv.Mqp.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_6))))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@Qy8Z.Mq6.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QZxv.Mqp.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_7))))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@Qy8Z.Mq6.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QZxv.Mqp.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_8))))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@Qy8Z.Mq6.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QZxv.Mqp.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_9))))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@Qy8Z.Mq6.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QZxv.Mqp.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_10))))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@Qy8Z.Mq6.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QZxv.Mqp.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_11))))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@Qy8Z.Mq6.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QZxv.Mqp.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_12))))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@Qy8Z.Mq6.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QZxv.Mqp.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_13))))))))))).
Definition rntf_q : ltac:(gw_rebind_ty (@QZxv.Mqp.rntf_q segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@QZxv.Mqp.rntf_q segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_14)).
Notation gw_tbl_15 := (gw_ent (@QZxv.Mqp.rntf_q segs RATP RGOT_SSP ref_reserved RC__) (@rntf_q) gw_tbl_14).
Definition rfhead_post : ltac:(gw_rebind_ty (@Qy8Z.Mq3.rfhead_post segs base RATP RGOT_SSP ref_reserved hi_64 RC__) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@Qy8Z.Mq3.rfhead_post segs base RATP RGOT_SSP ref_reserved hi_64 RC__) constr:(gw_tbl_15)).
Definition rftriv_post : ltac:(gw_rebind_ty (@Qy8Z.Mq4.rftriv_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@Qy8Z.Mq4.rftriv_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_15)).
Notation gw_tbl_16 := (gw_ent (@Qy8Z.Mq4.rftriv_post segs RATP RGOT_SSP ref_reserved RC__) (@rftriv_post) gw_tbl_15).
Definition rffin_post : ltac:(gw_rebind_ty (@Qy8Z.Mq5.rffin_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@Qy8Z.Mq5.rffin_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_16)).
Notation gw_tbl_17 := (gw_ent (@Qy8Z.Mq5.rffin_post segs RATP RGOT_SSP ref_reserved RC__) (@rffin_post) gw_tbl_16).
Definition rfmun_post : ltac:(gw_rebind_ty (@Qy8Z.Mq5.rfmun_post segs base RATP RGOT_SSP ref_reserved rvm_wait_entry RC__) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@Qy8Z.Mq5.rfmun_post segs base RATP RGOT_SSP ref_reserved rvm_wait_entry RC__) constr:(gw_tbl_17)).
Notation gw_tbl_18 := (gw_ent (@Qy8Z.Mq5.rfmun_post segs base RATP RGOT_SSP ref_reserved rvm_wait_entry RC__) (@rfmun_post) gw_tbl_17).
Definition runlock_post : ltac:(gw_rebind_ty (@QCa8.Mq4.runlock_post segs) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QCa8.Mq4.runlock_post segs) constr:(gw_tbl_18)).
Notation gw_tbl_19 := (gw_ent (@Qy8Z.Mq5.runlock_post segs) (@runlock_post) (gw_ent (@QCa8.Mq4.runlock_post segs) (@runlock_post) gw_tbl_18)).
Definition rrepfoot : ltac:(gw_rebind_ty (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) constr:(gw_tbl_19)).
Notation gw_tbl_20 := (gw_ent (@Qy8Z.Mq5.rrepfoot RATP RGOT_SSP) (@rrepfoot) (gw_ent (@QkTt.Mq4.rrepfoot RATP RGOT_SSP) (@rrepfoot) (gw_ent (@QkTt.Mq3.rrepfoot RATP RGOT_SSP) (@rrepfoot) (gw_ent (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) (@rrepfoot) gw_tbl_19)))).
Definition rget_meta_post : ltac:(gw_rebind_ty (@QCa8.Mq4.rget_meta_post segs) constr:(gw_tbl_20)) := ltac:(gw_rebind_tm (@QCa8.Mq4.rget_meta_post segs) constr:(gw_tbl_20)).
Notation gw_tbl_21 := (gw_ent (@Qy8Z.Mq3.rget_meta_post segs) (@rget_meta_post) (gw_ent (@QZxv.Mqp.rget_meta_post segs) (@rget_meta_post) (gw_ent (@QCa8.Mq4.rget_meta_post segs) (@rget_meta_post) gw_tbl_20))).

Hypothesis rmunmap_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q8QT.Mq2.gw_all) (@Q8QT.Mq2.rmunmap_spec) rvm_wait_entry)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_21))) in exact T).

Hypothesis roracle_ok_pres : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mqp.gw_all) (@QZxv.Mqp.roracle_ok_pres) (base + 732)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_21))) in let T := gw_fold_pcs T base (732)%Z [0; 100; 160; 184; 276; 312; 348; 356; 444; 452; 552; 604; 628; 648; 700; 724; 740; 896; 936]%Z in exact T).
Hypothesis rfree_fp_lt : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mqp.gw_all) (@QZxv.Mqp.rfree_fp_lt) (base + 732)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_21))) in let T := gw_fold_pcs T base (732)%Z [0; 100; 160; 184; 276; 312; 348; 356; 444; 452; 552; 604; 628; 648; 700; 724; 740; 896; 936]%Z in exact T).
Hypothesis rntf_implT : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mqp.gw_all) (@QZxv.Mqp.rntf_implT) (base + 732)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_21))) in let T := gw_fold_pcs T base (732)%Z [0; 100; 160; 184; 276; 312; 348; 356; 444; 452; 552; 604; 628; 648; 700; 724; 740; 896; 936]%Z in exact T).
Hypothesis sllw1_word' : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QCa8.Mq4.gw_all) (@QCa8.Mq4.sllw1_word') (base + 460)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_21))) in let T := gw_fold_pcs T base (460)%Z [0; 244]%Z in exact T).
Hypothesis rget_meta_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QCa8.Mq4.gw_all) (@QCa8.Mq4.rget_meta_spec) (base + 460)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_21))) in let T := gw_fold_pcs T base (460)%Z [0; 244]%Z in exact T).
Hypothesis runlock_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QCa8.Mq4.gw_all) (@QCa8.Mq4.runlock_spec) (base + 460)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_21))) in let T := gw_fold_pcs T base (460)%Z [0; 244]%Z in exact T).

Definition rmrep_shadow_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_shadow_read) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_shadow_read)).
Definition rreserved_disjoint : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint)).
Definition rreserved_disjoint1 : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint1) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint1)).
Definition rarea_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_conc) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_conc)).
Definition rgroup_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rgroup_conc) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rgroup_conc)).
Definition rwr_at_bytes_exist : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rwr_at_bytes_exist) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rwr_at_bytes_exist)).

Definition rimplT_ret : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_ret) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_ret)).
#[global] Arguments rimplT_ret {R}%_type_scope o r s Q%_function_scope ms _.
Definition rimplT_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_evt) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_evt)).
#[global] Arguments rimplT_evt {R}%_type_scope o t s Q%_function_scope P%_function_scope ms _ _%_function_scope.
Definition rimplT_bind : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_bind) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_bind)).
#[global] Arguments rimplT_bind {R}%_type_scope {S}%_type_scope o t f%_function_scope s Q1%_function_scope Q%_function_scope ms _ _%_function_scope.
Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rimplT_munmap : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_munmap) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_munmap)).
#[global] Arguments rimplT_munmap {R}%_type_scope o addr%_Z_scope len%_Z_scope k%_function_scope s P%_function_scope Q%_function_scope ms _ _%_function_scope.
Definition rpres_except_trans : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_trans) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_trans)).
Definition rpres_except_mono : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_mono) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_mono)).
Definition rpres_except_rw_cells : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_rw_cells) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_rw_cells)).

Definition rfree_fp_stack : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rfree_fp_stack) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rfree_fp_stack)).

Definition rimplT_guard : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq3.rimplT_guard) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq3.rimplT_guard)).
#[global] Arguments rimplT_guard {R}%_type_scope o t%_Z_scope c%_bool_scope k bail s Q%_function_scope ms _%_function_scope.
Definition rimplT_rd8 : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq3.rimplT_rd8) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq3.rimplT_rd8)).
#[global] Arguments rimplT_rd8 {R}%_type_scope o st q k%_function_scope s Q%_function_scope ms _.
Definition rimplT_rd16 : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq3.rimplT_rd16) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq3.rimplT_rd16)).
#[global] Arguments rimplT_rd16 {R}%_type_scope o st q k%_function_scope s Q%_function_scope ms _.
Definition rimplT_rd32 : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq3.rimplT_rd32) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq3.rimplT_rd32)).
#[global] Arguments rimplT_rd32 {R}%_type_scope o st q k%_function_scope s Q%_function_scope ms _.
Definition rimplT_if : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq3.rimplT_if) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq3.rimplT_if)).
#[global] Arguments rimplT_if {R}%_type_scope o c%_bool_scope t1 t2 s Q%_function_scope ms _%_function_scope _%_function_scope.
Definition rrdv_cur : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq3.rrdv_cur) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq3.rrdv_cur)).
Definition rrw_cells_agree' : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq3.rrw_cells_agree') constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq3.rrw_cells_agree')).
Definition rmrep_transport_agree' : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq3.rmrep_transport_agree') constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq3.rmrep_transport_agree')).
Definition rpres_except_of_munch_nw : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq3.rpres_except_of_munch_nw) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq3.rpres_except_of_munch_nw)).

Definition rfree_head : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mq3.rfree_head) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mq3.rfree_head)).

Definition rfree_triv : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mq4.rfree_triv) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mq4.rfree_triv)).
Definition rfree_tocall : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mq4.rfree_tocall) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mq4.rfree_tocall)).

Definition rfree_fin0 : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mq5.rfree_fin0) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mq5.rfree_fin0)).
Definition rfree_tomunmap : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mq5.rfree_tomunmap) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mq5.rfree_tomunmap)).
Definition rerrno_avoids_repfoot : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mq5.rerrno_avoids_repfoot) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mq5.rerrno_avoids_repfoot)).
Definition rfree_fin1 : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mq5.rfree_fin1) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mq5.rfree_fin1)).

Definition rfree_fp_hdr_st : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mq6.rfree_fp_hdr_st) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mq6.rfree_fp_hdr_st)).
Definition rmrep_drop_region : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mq6.rmrep_drop_region) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mq6.rmrep_drop_region)).
Definition rptrs_in_norid : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mq6.rptrs_in_norid) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mq6.rptrs_in_norid)).

#[using="rerrno_loc_entry rsysret_entry rvm_wait_entry rmunmap_entry rlock_entry runlock_entry RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_21 E_21 D_23 E_23 D_64 E_64 D_71 E_71 D_85 E_85 D_86 E_86 D_89 E_89 D_95 E_95 D_96 E_96 D_97 E_97 D_99 E_99 D_104 E_104 ANCH_23 ANCH_71 ANCH_86 ANCH_96 LINK_89 LINK_97 LINK_99 LINK_104 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rsysret_entry AL_rvm_wait_entry AL_rlock_entry AL_runlock_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rfree_entry rmunmap_entry rmunmap_spec roracle_ok_pres rfree_fp_lt rntf_implT sllw1_word' rget_meta_spec runlock_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := first [clear - hs segs base w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 hi_21 hi_64 hi_85 hi_95 lo_23 lo_71 lo_86 lo_96 joff_89 joff_97 joff_99 joff_104 rerrno_loc_entry rsysret_entry rvm_wait_entry rmunmap_entry rlock_entry runlock_entry RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_21 E_21 D_23 E_23 D_64 E_64 D_71 E_71 D_85 E_85 D_86 E_86 D_89 E_89 D_95 E_95 D_96 E_96 D_97 E_97 D_99 E_99 D_104 E_104 ANCH_23 ANCH_71 ANCH_86 ANCH_96 LINK_89 LINK_97 LINK_99 LINK_104 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rsysret_entry AL_rvm_wait_entry AL_rlock_entry AL_runlock_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rfree_entry rmunmap_spec roracle_ok_pres rfree_fp_lt rntf_implT sllw1_word' rget_meta_spec runlock_spec | clear - hs segs base w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 hi_21 hi_64 hi_85 hi_95 lo_23 lo_71 lo_86 lo_96 joff_89 joff_97 joff_99 joff_104 rerrno_loc_entry rsysret_entry rvm_wait_entry rmunmap_entry rlock_entry runlock_entry RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_21 E_21 D_23 E_23 D_64 E_64 D_71 E_71 D_85 E_85 D_86 E_86 D_89 E_89 D_95 E_95 D_96 E_96 D_97 E_97 D_99 E_99 D_104 E_104 ANCH_23 ANCH_71 ANCH_86 ANCH_96 LINK_89 LINK_97 LINK_99 LINK_104 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rsysret_entry AL_rvm_wait_entry AL_rlock_entry AL_runlock_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay rfree_entry rmunmap_spec roracle_ok_pres rfree_fp_lt rntf_implT sllw1_word' rget_meta_spec runlock_spec].

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

Definition rfree_end (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (LB' : list block) (m : mem) (errv : word) (s : PState)
(st' : mstate) (s' : PState) : machine_state -> Prop :=
fun ms' => s' = s /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
/\ rw_cells segs m' (errno_addr tp) [C4 errv]
/\ rmrep st' m'
/\ rpres_except (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st st' a \/ (RATP + -164) <= a < (RATP + -164 + 4)) m m'
/\ (forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r')
/\ (forall blk', In blk' LB' -> exists r', (s_regions st') !! (fst (blk_slot blk')) = Some r')
/\ c_brk (ctx st') = c_brk (ctx st)
/\ (forall brid boff, c_brk (ctx st) = BrkLive brid boff -> (s_regions st') !! brid = (s_regions st) !! brid).

#[using="base RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rfree_entry rmunmap_entry"] Lemma rerrno_not_free_fp st m lo (sp : Z) a : rmrep st m -> alloc_ceiling <= lo -> (RATP + -164) <= a < (RATP + -164 + 4) -> ~ rfree_fp st lo sp a.
Proof. clear - base RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rfree_entry rmunmap_entry RATP st m lo sp a. gw_expose_fam RATP.
intros MR LO Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold alloc_ceiling in LO.
intros [[A|[A|A]]|[A|A]].
- lia.
- gw_expose_fam RATP. lia.
- destruct A as (rid & r & Hr & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (lr_lo_ge r). lia.
- destruct A as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
- destruct A as (rid & r & v & Hr & _ & Hin & _). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
Qed.

#[using="base RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rfree_entry rmunmap_entry"] Lemma rmrep_after_munmap st2 rid r2 m4 m5 (slo shi : Z) :
rmrep (drop_region rid st2) m4 -> rmrep st2 m4 ->
(s_regions st2) !! rid = Some r2 -> r_kind r2 = RKGroup ->
munch [(slo, shi); ((RATP + -164), (RATP + -164 + 4)); (r_base r2, r_base r2 + round_up_pg (r_len r2))]%Z m4 m5 ->
alloc_ceiling <= slo ->
rmrep (drop_region rid st2) m5.
Proof. clear - base RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rfree_entry rmunmap_entry RATP st2 rid r2 m4 m5 slo shi RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros MRd MR Hr Kr MU LO. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold alloc_ceiling in LO.
pose proof (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). unfold alloc_ceiling in RBC.
eapply rmrep_transport_agree'; [gw_exact MRd|]. intros a Ha HF. apply MU. rewrite wa_unsigned by lia.
assert (LOW : a < alloc_ceiling /\ ~ ((RATP + -164) <= a < (RATP + -164 + 4)) /\ ~ (r_base r2 <= a < r_base r2 + round_up_pg (r_len r2))).
{ destruct HF as [HF|HF].
- split; [| split].
+ destruct HF as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
* gw_expose_fam RATP; lia. * gw_expose_fam RATP; lia. * gw_expose_fam RATP; lia. * gw_expose_fam RATP; lia.
* destruct C as (ak & ar & Hak & Hin). destruct (rarea_conc (drop_region rid st2) ak ar (proj1 MRd) Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & _ & _ & _ & RC). unfold alloc_ceiling in RC. lia.
* destruct C as (b & gh & Hb & Hin). destruct (rgroup_conc (drop_region rid st2) b gh (proj1 MRd) Hb) as (rb & Hrb & Cb & _ & _ & Sb1 & _ & _ & RC). unfold alloc_ceiling in RC. lia.
* destruct C as (k & rk & v & Hk & _ & Hin & _). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [_ Hk].
destruct (WR _ _ Hk) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
* gw_expose_fam RGOT_SSP; lia. * gw_expose_fam RATP; lia.
+ intros Hea. exact (rerrno_avoids_repfoot _ _ a MRd Hea HF).
+ intros Hin. destruct HF as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
* gw_expose_fam RATP; lia. * gw_expose_fam RATP; lia. * gw_expose_fam RATP; lia. * gw_expose_fam RATP; lia.
* destruct C as (ak & ar & Hak & Ha'). cbn [drop_region s_areas set_shadow set_regions] in Hak.
destruct (WA ak ar Hak) as (ra & Hra & Sa0 & Sa1 & _ & NK & ALR).
assert (NE : fst ak <> rid) by (intros E; rewrite E, Hr in Hra; assert (ra = r2) by congruence; subst; exact (NK Kr)).
rewrite (rconc_drop st2 rid ak NE) in Ha'. rewrite (conc_region' st2 ak ra Hra) in Ha'.
pose proof (lr_lo_group r2 Kr). destruct (DJ _ _ _ _ Hra Hr NE); lia.
* destruct C as (b & gh & Hb & Ha'). cbn [drop_region s_groups set_shadow set_regions] in Hb.
destruct (WG b gh Hb) as (rb & Hrb & Krb & Sb0 & Sb1 & _).
assert (NE : fst b <> rid).
{ intros E. pose proof (proj1 MRd) as (_ & _ & _ & _ & WG'). destruct (WG' b gh Hb) as (rb' & Hrb' & _).
cbn [drop_region s_regions set_shadow set_regions] in Hrb'. rewrite E, lookup_delete_eq in Hrb'. discriminate. }
rewrite (rconc_drop st2 rid b NE) in Ha'. rewrite (conc_region' st2 b rb Hrb) in Ha'.
pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
* destruct C as (k & rk & v & Hk & Kk & Ha' & _). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rk Kk). destruct (DJ _ _ _ _ Hk Hr ltac:(congruence)); lia.
* gw_expose_fam RGOT_SSP. lia.
* gw_expose_fam RATP. lia.
- destruct HF as (k & rk & Hk & Kk & Ha'). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
destruct (WR _ _ Hk) as (_ & _ & _ & RC & RFk). pose proof (rreserved_disjoint _ _ RFk) as (?&?&?&?). unfold alloc_ceiling in RC.
split; [lia|]. split; [lia|].
pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rk Kk). destruct (DJ _ _ _ _ Hk Hr ltac:(congruence)); lia. }
destruct LOW as (L1 & L2 & L3). cbn [outside]. split; [lia|]. split; [gw_exact L2|]. split; [gw_exact L3| exact I].
Qed.

#[using="Type"] Lemma byte_zero_list (x : byte) : bv_unsigned x = 0 -> [x] = [b8 0].
Proof. clear - x. intros Hx. f_equal. rewrite <- (definitions.Z_to_bv_bv_unsigned 8 x). rewrite Hx. reflexivity. Qed.

#[using="base rvm_wait_entry rfree_entry rmunmap_entry"] Lemma bytes4_range (x0 x1 x2 x3 : byte) :
0 <= bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3 < 2^32.
Proof. clear - base rvm_wait_entry rfree_entry rmunmap_entry x0 x1 x2 x3.
pose proof (bv_unsigned_in_range 8 x0). pose proof (bv_unsigned_in_range 8 x1).
pose proof (bv_unsigned_in_range 8 x2). pose proof (bv_unsigned_in_range 8 x3).
unfold bv_modulus in *. cbn [Z.pow_pos Pos.iter Z.mul Pos.mul] in *. lia.
Qed.

#[using="base rvm_wait_entry rfree_entry rmunmap_entry"] Lemma le4_of_bytes (x0 x1 x2 x3 : byte) :
le4 (wz (bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3)) = [x0; x1; x2; x3].
Proof. clear - base rvm_wait_entry rfree_entry rmunmap_entry x0 x1 x2 x3.
pose proof (bv_unsigned_in_range 8 x0). pose proof (bv_unsigned_in_range 8 x1).
pose proof (bv_unsigned_in_range 8 x2). pose proof (bv_unsigned_in_range 8 x3).
unfold bv_modulus in *. cbn [Z.pow_pos Pos.iter Z.mul Pos.mul] in *.
rewrite le4_bytes by lia. unfold b8.

f_equal; [|f_equal; [|f_equal; [|f_equal]]];
(apply bv_eq; rewrite Z_to_bv_unsigned;
match goal with |- bv_wrap 8 ?a = _ => change (bv_wrap 8 a) with (a mod 256)%Z end;
Z.div_mod_to_equations; lia).
Qed.

#[using="base rvm_wait_entry rfree_entry rmunmap_entry"] Lemma shiftr5_ge v : 0 <= v < 256 -> 5 <= Z.shiftr v 5 -> 160 <= v.
Proof. clear - base rvm_wait_entry rfree_entry rmunmap_entry v. intros Hv H. rewrite Z.shiftr_div_pow2 in H by lia. change (2^5) with 32 in H. Z.div_mod_to_equations. lia. Qed.
#[using="base rvm_wait_entry rfree_entry rmunmap_entry"] Lemma shiftr5_lt v : 0 <= v < 256 -> Z.shiftr v 5 < 5 -> v < 160.
Proof. clear - base rvm_wait_entry rfree_entry rmunmap_entry v. intros Hv H. rewrite Z.shiftr_div_pow2 in H by lia. change (2^5) with 32 in H. Z.div_mod_to_equations. lia. Qed.
#[using="base rvm_wait_entry rfree_entry rmunmap_entry"] Lemma shiftr5_range v : 0 <= v < 256 -> 0 <= Z.shiftr v 5 < 8.
Proof. clear - base rvm_wait_entry rfree_entry rmunmap_entry v. intros Hv. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. Z.div_mod_to_equations. lia. Qed.

Section FREE.
Variables (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis TP : tp = Z_to_bv 64 RATP.

#[using="RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rerrno_loc_entry rvm_wait_entry runlock_entry w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 hi_21 hi_64 hi_95 lo_23 lo_71 lo_96 joff_97 joff_99 joff_104 CODE BASE4 BASER D_21 E_21 D_23 E_23 D_64 E_64 D_71 E_71 D_95 E_95 D_96 E_96 D_97 E_97 D_99 E_99 D_104 E_104 ANCH_23 ANCH_71 ANCH_96 LINK_97 LINK_99 LINK_104 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved ref_wview_overlay ref_seg_rom_none ref_mrd_overlay rmunmap_spec roracle_ok_pres rfree_fp_lt rntf_implT sllw1_word' rget_meta_spec runlock_spec rfree_entry rmunmap_entry LO TP"] Theorem rlibc_free_implT : forall (ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (s : PState)
(st : mstate) (blk : block) (off : Z) (errv : word),
CINV st LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st (blk_slot blk) + UNIT * off ->
rmrep st m -> mem_inv segs m ->
stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 8192 ->
rw_cells segs m (errno_addr tp) [C4 errv] ->
a0 = Z_to_bv 64 (blk_addr blk) ->
rimplT m (free st (Some (aadd (blk_slot blk) (UNIT * off)))) s
(rfree_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st (lbrm LB blk) m errv s)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rfree_entry) fc None m (seg_rom segs)).
Proof. clear - RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rerrno_loc_entry rvm_wait_entry runlock_entry w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 hi_21 hi_64 hi_95 lo_23 lo_71 lo_96 joff_97 joff_99 joff_104 CODE BASE4 BASER D_21 E_21 D_23 E_23 D_64 E_64 D_71 E_71 D_95 E_95 D_96 E_96 D_97 E_97 D_99 E_99 D_104 E_104 ANCH_23 ANCH_71 ANCH_96 LINK_97 LINK_99 LINK_104 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved ref_wview_overlay ref_seg_rom_none ref_mrd_overlay rmunmap_spec roracle_ok_pres rfree_fp_lt rntf_implT sllw1_word' rget_meta_spec runlock_spec rfree_entry rmunmap_entry LO TP segs RATP gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB lo. gw_expose_fam RATP. try gw_hide lo; try gw_hide LB; try gw_hide fc; try gw_hide F; try gw_hide s11; try gw_hide s10; try gw_hide s9; try gw_hide s8; try gw_hide s7; try gw_hide s6; try gw_hide s5; try gw_hide s4; try gw_hide s3; try gw_hide s2; try gw_hide s1; try gw_hide s0; try gw_hide tp; try gw_hide gp.
intros until errv. intros C Hin Hoff HA MR MI ST SLO ERR A0.
pose proof (ci_ticks _ _ C) as TK.
pose proof (KINV_of_CINV _ _ C) as K0.
pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin) as BK.
pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk Hin) as BC.
destruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off' & O0 & OA & OS & OK & HK)) NG SZ].
assert (off' = off) as ->.
{ rewrite HA in OA. unfold UNIT in OA. lia. }
clear OA.
set (c0 := blk_slot blk) in *. set (pf := aadd c0 (UNIT * off)) in *. set (LB' := lbrm LB blk) in *.
pose proof (ci_gmetas _ _ C b g HB) as GO.
destruct (go_region _ _ _ GO) as (r & Hr & Kr & B0 & B16 & SPAN & TOP).
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF).
destruct BC as [(r0 & Hr0 & _ & A16 & AEND & AL & UNK) HD BB].
rewrite <- FB, Hr in Hr0. assert (r0 = r) by congruence. subst r0.
destruct (ki_slts _ _ _ K0 _ _ _ SL) as (GMg & Ec & _). fold c0 in Ec.
destruct HK as (v3 & lo8 & hi & C3 & V31 & C2 & C1 & OFF). fold c0 in C3, C2, C1, OFF.
cbn [aadd fst snd] in C3, C2, C1, OFF.

assert (Fp : fst pf = fst b) by (unfold pf; cbn; symmetry; gw_exact FB).
assert (Cp : conc st pf = r_base r + snd pf) by (apply conc_region'; rewrite Fp; gw_exact Hr).
assert (Cc : conc st c0 = r_base r + snd c0) by (apply conc_region'; rewrite <- FB; gw_exact Hr).
assert (Sp : snd pf = snd c0 + 16 * off) by (unfold pf, UNIT; cbn; lia).
assert (HAp : blk_addr blk = r_base r + snd pf) by (rewrite HA, Cc, Sp; unfold UNIT; lia).
assert (Sc : snd c0 = snd b + 16 + get_stride (get_meta_rec st g) * i).
{ rewrite Ec. rewrite (slot_start'_mem _ b i (go_mem _ _ _ GO)). cbn. unfold UNIT. lia. }
pose proof (go_stride _ _ _ GO) as [S16 SM]. pose proof (go_li _ _ _ GO) as LI.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (ETP : bv_unsigned tp + -164 = (RATP + -164)) by (rewrite TP; gw_expose_fam RATP; rewrite unsigned_lit by lia; first [reflexivity | lia]).
pose proof LO as LOv. unfold alloc_ceiling in LOv.

assert (SIM : (get_stride (get_meta_rec st g) * i) mod 16 = 0).
{ unfold UNIT in SM. rewrite Z.mul_mod, SM, Z.mul_0_l by lia. reflexivity. }
assert (SI0 : 0 <= get_stride (get_meta_rec st g) * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
assert (SIL : get_stride (get_meta_rec st g) * (i + 1) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
{ apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia. }
unfold sstart_of in SPAN. rewrite (go_mem _ _ _ GO) in SPAN. cbn [default id snd] in SPAN.
assert (P16m : snd pf mod 16 = 0).
{ rewrite Sp, Sc. set (si := get_stride (get_meta_rec st g) * i) in *. unfold UNIT, IB in *. clear - SIM B16 Hoff RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rerrno_loc_entry rvm_wait_entry runlock_entry w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 hi_21 hi_64 hi_95 lo_23 lo_71 lo_96 joff_97 joff_99 joff_104 CODE BASE4 BASER D_21 E_21 D_23 E_23 D_64 E_64 D_71 E_71 D_95 E_95 D_96 E_96 D_97 E_97 D_99 E_99 D_104 E_104 ANCH_23 ANCH_71 ANCH_96 LINK_97 LINK_99 LINK_104 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved ref_wview_overlay ref_seg_rom_none ref_mrd_overlay rmunmap_spec roracle_ok_pres rfree_fp_lt rntf_implT sllw1_word' rget_meta_spec runlock_spec rfree_entry rmunmap_entry segs RATP. Z.div_mod_to_equations. lia. }
assert (PHI : snd pf + 16 <= round_up_pg (r_len r)).
{ rewrite Sp, Sc. set (si := get_stride (get_meta_rec st g) * i) in *. set (stq := get_stride (get_meta_rec st g)) in *.
unfold UNIT, IB in *.
assert (16 * off + 16 <= stq) by (clear - OS SZ SM Hoff S16 RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rerrno_loc_entry rvm_wait_entry runlock_entry w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 hi_21 hi_64 hi_95 lo_23 lo_71 lo_96 joff_97 joff_99 joff_104 CODE BASE4 BASER D_21 E_21 D_23 E_23 D_64 E_64 D_71 E_71 D_95 E_95 D_96 E_96 D_97 E_97 D_99 E_99 D_104 E_104 ANCH_23 ANCH_71 ANCH_96 LINK_97 LINK_99 LINK_104 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved ref_wview_overlay ref_seg_rom_none ref_mrd_overlay rmunmap_spec roracle_ok_pres rfree_fp_lt rntf_implT sllw1_word' rget_meta_spec runlock_spec rfree_entry rmunmap_entry segs RATP; Z.div_mod_to_equations; lia).
rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. fold si in SIL. lia. }
assert (HAR : 0 <= r_base r + snd pf /\ r_base r + snd pf + 16 <= 2^64) by (unfold alloc_ceiling in RBC; pose proof (round_up_pg_ge (r_len r)); lia).
assert (DRr : r_base r + round_up_pg (r_len r) <= 0x10000 \/ RIMG_HI <= r_base r) by (apply (rreserved_disjoint1 _ _ RF); lia).

clear SIM SM B16 RBAL AL. change (frozen (snd pf mod 16 = 0)) in P16m.
assert (EB : aadd pf (- (UNIT * (lo8 + 256 * hi)) - UNIT) = b).
{ unfold aadd. apply injective_projections; cbn; [gw_exact Fp| unfold UNIT in *; lia]. }
destruct HB as [ai Hgh].

assert (Cb : conc st b = r_base r + snd b) by (apply conc_region'; gw_exact Hr).
pose proof (shiftr5_range v3) as SR5.
destruct (rmrep_shadow_read st m (fst c0) r (snd c0 + UNIT * off - 3) v3 MR ltac:(rewrite <- FB; gw_exact Hr) Kr ltac:(unfold UNIT, IB in *; lia) C3) as [_ V3R].

assert (RDB : forall q : aptr, fst q = fst b -> 0 <= snd q < round_up_pg (r_len r) ->
exists x : byte, bytes_at segs m (r_base r + snd q) [x] /\ rdv pans_mem m st q = bv_unsigned x).
{ intros q Fq Hq.
assert (Hrq : s_regions st !! fst q = Some r) by (rewrite Fq; gw_exact Hr).
destruct (SH _ r Hr Kr) as [WRr _].
assert (W1 : wr_at segs m (r_base r + snd q) 1).
{ destruct WRr as (W0 & Wn & W). split; [lia|]. split; [pose proof (round_up_pg_ge (r_len r)); unfold alloc_ceiling in RBC; lia|].
intros j Hj. replace (r_base r + snd q + j) with (r_base r + (snd q + j)) by lia. apply W. lia. }
destruct (rwr_at_bytes_exist m _ 1 W1 ltac:(lia) ltac:(pose proof (round_up_pg_ge (r_len r)); lia)) as (bs & L & B).
destruct bs as [|x [|]]; try discriminate. exists x. split; [gw_exact B|].
eapply (rrdv_cur m st m q r x MR Hrq Kr Hq); [intros; reflexivity| gw_exact B]. }

unfold free.
eapply (rimplT_bind m (free_hdr st pf) _ s
(fun r1 s' ms' => s' = s /\ r1 = Some (hdr_st st pf, g, i) /\
rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m (hdr_st st pf) g i (m_last_idx (get_meta_rec st g)) ms')).
{ unfold free_hdr, get_meta. apply rimplT_guard. intros _.
apply rimplT_rd16. apply rimplT_rd8. cbv zeta. apply rimplT_rd8.
rewrite (rdv_known m st (aadd pf (-4)) 0) by (cbn [aadd fst snd]; replace (snd pf + -4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia); gw_exact OK).
rewrite (rdv_known m st (aadd pf (-3)) v3) by (cbn [aadd fst snd]; replace (snd pf + -3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia); gw_exact C3).
rewrite (rdv_known m st (aadd pf (-2)) lo8) by (cbn [aadd fst snd]; replace (snd pf + -2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia); gw_exact C2).
rewrite (rdv_known m st (aadd (aadd pf (-2)) 1) hi) by (cbn [aadd fst snd]; replace (snd pf + -2 + 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia); gw_exact C1).
cbn [Z.eqb negb]. rewrite EB. unfold get_group. rewrite Hgh. cbn [g_meta].
apply rimplT_guard; intros G11. apply rimplT_guard; intros G12. apply rimplT_guard; intros G13. apply rimplT_guard; intros G14.
destruct (s_areas st !! area_of g) as [ar|] eqn:AR1; [| apply rimplT_guard; intros; discriminate].
apply rimplT_guard; intros G15. apply rimplT_guard; intros G16. apply rimplT_guard; intros G17. cbv beta.
unfold slot_start. rewrite (go_mem _ _ _ GO). cbv beta zeta.
apply Z.eqb_eq in G15. apply Z.leb_le in G12. apply negb_true_iff in G13. apply negb_true_iff in G14.
rewrite V31 in G12, G13, G14, G16.
set (e := aadd (aadd b (UNIT + get_stride (get_meta_rec st g) * Z.land v3 31)) (get_stride (get_meta_rec st g) - IB)).
assert (Fe : fst e = fst b) by first [reflexivity | (cbn; lia)].
assert (Se : snd e = snd b + 16 + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - 4).
{ unfold e. cbn [aadd snd]. rewrite V31. unfold UNIT, IB. lia. }

pose proof (go_sc _ _ _ GO) as GSC.
assert (WALK : forall r32 : Z,
(160 <= v3 -> Z.shiftr v3 5 = 5 /\ 5 <= r32 < 2^32
/\ bytes_at segs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - 4) (le4 (wz r32))
/\ bytes_at segs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - 5) [b8 0]) ->
(if 160 <=? v3 then r32 else Z.shiftr v3 5) <= conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (r_base r + snd pf) ->
bytes_at segs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (if 160 <=? v3 then r32 else Z.shiftr v3 5)) [b8 0] ->
bytes_at segs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB) [b8 0] ->
evt segs (fun ms' => s = s /\ Some (hdr_st st pf, g, i) = Some (hdr_st st pf, g, i) /\
rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m (hdr_st st pf) g i (m_last_idx (get_meta_rec st g)) ms')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rfree_entry) fc None m (seg_rom segs))).
{ intros r32 BIG RSVLE RB0r RE0.
eapply evt_mono.
{ eapply (rfree_head ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo st pf r g (mkGhdr (Some g) ai) ar v3 lo8 hi r32);
first [gw_exact MR | gw_exact MI | gw_exact TK | gw_exact ST | gw_exact LO | gw_exact Kr | idtac].
all: rewrite ?EB, ?V31.
- lia.
- rewrite Fp. gw_exact Hr.
- rewrite A0, HAp. apply unsigned_lit. lia.
- gw_exact P16m.
- rewrite Sp, Sc. lia.
- unfold pf in OFF |- *. cbn [aadd snd] in OFF |- *. lia.
- gw_exact PHI.
- replace (snd pf - 4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia). unfold pf; cbn [aadd fst]. gw_exact OK.
- replace (snd pf - 3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. gw_exact C3.
- replace (snd pf - 2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. gw_exact C2.
- replace (snd pf - 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. gw_exact C1.
- gw_exact Hgh.
- reflexivity.
- exact (go_slot _ _ _ GO).
- destruct (go_slot _ _ _ GO) as (a & ara & k & Ha & Hk & ->). destruct (WA a ara Ha) as (rg0 & _ & A00 & _). cbn. unfold AREA_HDR, META_SIZE. lia.
- exact (go_mem _ _ _ GO).
- gw_exact AR1.
- gw_exact G15.
- exact (go_avail _ _ _ GO).
- exact (go_freed _ _ _ GO).
- exact (proj2 (proj2 (proj2 (ki_cx _ _ _ K0)))).
- lia.
- rewrite (go_freeable _ _ _ GO). lia.
- lia.
- pose proof (go_maplen _ _ _ GO). lia.
- gw_exact G12.
- gw_exact G13.
- gw_exact G14.
- intros Hsc. apply Z.ltb_lt in Hsc. rewrite Hsc in G16. apply andb_true_iff in G16. destruct G16 as [G16a G16b].
apply Z.leb_le in G16a. apply Z.ltb_lt in G16b. lia.
- intros Hsc. destruct (Z.ltb_spec (m_sizeclass (get_meta_rec st g)) 48); [lia|]. apply Z.eqb_eq in G16. gw_exact G16.
- intros Hml. destruct (Z.eqb_spec (m_maplen (get_meta_rec st g)) 0); [lia|]. cbn [negb] in G17. apply Z.leb_le in G17.
unfold UNIT in G17.
replace (m_maplen (get_meta_rec st g) * 4096) with (m_maplen (get_meta_rec st g) * 256 * 16) in G17 by lia.
rewrite Z.div_mul in G17 by lia. lia.
- lia.
- gw_exact S16.
- rewrite Cb, Sp, Sc. unfold UNIT, IB in *. lia.
- rewrite Cb. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold UNIT, IB in *. lia.
- gw_exact BIG.
- gw_exact RSVLE.
- gw_exact RB0r.
- gw_exact RE0.
- intros b' gh' Hb' Fb'. specialize (HD b' gh' Hb' ltac:(rewrite Fb', Fp; gw_exact FB)).
rewrite (conc_region' st b' r) in HD by (rewrite Fb', Fp; gw_exact Hr). unfold IB in HD.
clear - HD HAp SZ RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rerrno_loc_entry rvm_wait_entry runlock_entry w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 hi_21 hi_64 hi_95 lo_23 lo_71 lo_96 joff_97 joff_99 joff_104 CODE BASE4 BASER D_21 E_21 D_23 E_23 D_64 E_64 D_71 E_71 D_95 E_95 D_96 E_96 D_97 E_97 D_99 E_99 D_104 E_104 ANCH_23 ANCH_71 ANCH_96 LINK_97 LINK_99 LINK_104 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved ref_wview_overlay ref_seg_rom_none ref_mrd_overlay rmunmap_spec roracle_ok_pres rfree_fp_lt rntf_implT sllw1_word' rget_meta_spec runlock_spec rfree_entry rmunmap_entry segs RATP. lia.  }
intros ms' FP. split; [reflexivity|]. split; [reflexivity|]. unfold hdr_st. rewrite <- V31. gw_exact FP. }

assert (EQE : forall k, r_base r + snd (aadd e (- k)) = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - k).
{ intros k. cbn [aadd snd]. rewrite Se, Cb. unfold UNIT, IB. lia. }
assert (EQE0 : r_base r + snd e = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB).
{ rewrite Se, Cb. unfold UNIT, IB. lia. }
assert (ERNG : snd e + 1 <= round_up_pg (r_len r) /\ snd pf <= snd e /\ 16 <= snd e).
{ rewrite Se, Sp, Sc. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold UNIT, IB in *. lia. }
assert (DIFF : snd e - snd pf = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (r_base r + snd pf)).
{ rewrite Se, Cb. unfold UNIT, IB. lia. }

unfold get_nominal_size. apply rimplT_rd8. cbv zeta.
rewrite (rdv_known m st (aadd pf (-3)) v3) by (cbn [aadd fst snd]; replace (snd pf + -3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia); gw_exact C3).
apply rimplT_if; intros HR5.
-
apply Z.leb_le in HR5.
apply rimplT_guard; intros G20. apply Z.eqb_eq in G20.
apply rimplT_rd32.
destruct (RDB (aadd e (-4)) Fe ltac:(cbn [aadd snd]; lia)) as (x0 & BX0 & RX0). rewrite RX0.
destruct (RDB (aadd (aadd e (-4)) 1) Fe ltac:(cbn [aadd snd]; lia)) as (x1 & BX1 & RX1). rewrite RX1.
destruct (RDB (aadd (aadd e (-4)) 2) Fe ltac:(cbn [aadd snd]; lia)) as (x2 & BX2 & RX2). rewrite RX2.
destruct (RDB (aadd (aadd e (-4)) 3) Fe ltac:(cbn [aadd snd]; lia)) as (x3 & BX3 & RX3). rewrite RX3.
pose proof (bytes4_range x0 x1 x2 x3) as U32. pose proof (le4_of_bytes x0 x1 x2 x3) as LE4.
set (r32 := bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3) in *.
apply rimplT_guard; intros G21. apply Z.leb_le in G21.
apply rimplT_rd8. destruct (RDB (aadd e (-5)) Fe ltac:(cbn [aadd snd]; lia)) as (x5 & BX5 & RX5). rewrite RX5.
apply rimplT_guard; intros G25. apply Z.eqb_eq in G25.
apply rimplT_guard; intros G22. apply Z.leb_le in G22.
apply rimplT_rd8. destruct (RDB (aadd e (- r32)) Fe ltac:(cbn [aadd snd]; lia)) as (xc & BXc & RXc). rewrite RXc.
apply rimplT_guard; intros G23. apply Z.eqb_eq in G23.
apply rimplT_rd8. destruct (RDB e Fe ltac:(lia)) as (xe & BXe & RXe). rewrite RXe.
apply rimplT_guard; intros G24. apply Z.eqb_eq in G24.
apply rimplT_ret. rewrite V31.
specialize (SR5 V3R). pose proof (shiftr5_ge v3 V3R HR5) as V160.
assert (H160 : (160 <=? v3) = true) by (apply Z.leb_le; gw_exact V160).

apply (WALK r32).
+ intros _. split; [gw_exact G20|]. split; [lia|]. split.
* rewrite <- (EQE 4). rewrite LE4. change [x0; x1; x2; x3] with ([x0] ++ ([x1] ++ ([x2] ++ [x3]))).
apply bytes_at_app. split; [gw_exact BX0|]. apply bytes_at_app. split; [cbn [length Z.of_nat Pos.of_succ_nat]; cbn [aadd snd] in BX1 |- *; replace (r_base r + (snd e + -4) + 1) with (r_base r + (snd e + -4 + 1)) by lia; gw_exact BX1|].
apply bytes_at_app. split; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; cbn [aadd snd] in BX2, BX3 |- *.
-- replace (r_base r + (snd e + -4) + 1 + 1) with (r_base r + (snd e + -4 + 2)) by lia. gw_exact BX2.
-- replace (r_base r + (snd e + -4) + 1 + 1 + 1) with (r_base r + (snd e + -4 + 3)) by lia. gw_exact BX3.
* rewrite <- (EQE 5), <- (byte_zero_list x5 G25). gw_exact BX5.
+ rewrite H160, <- DIFF. gw_exact G22.
+ rewrite H160, <- (EQE r32), <- (byte_zero_list xc G23). gw_exact BXc.
+ rewrite <- EQE0, <- (byte_zero_list xe G24). gw_exact BXe.
-
apply Z.leb_gt in HR5.
apply rimplT_guard; intros G22. apply Z.leb_le in G22.
apply rimplT_rd8. destruct (RDB (aadd e (- Z.shiftr v3 5)) Fe ltac:(cbn [aadd snd]; lia)) as (xc & BXc & RXc). rewrite RXc.
apply rimplT_guard; intros G23. apply Z.eqb_eq in G23.
apply rimplT_rd8. destruct (RDB e Fe ltac:(lia)) as (xe & BXe & RXe). rewrite RXe.
apply rimplT_guard; intros G24. apply Z.eqb_eq in G24.
apply rimplT_ret. rewrite V31.
specialize (SR5 V3R). pose proof (shiftr5_lt v3 V3R HR5) as V160.
assert (H160 : (160 <=? v3) = false) by (apply Z.leb_gt; gw_exact V160).

apply (WALK 0).
+ intros H. exfalso. clear - H V160 RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rerrno_loc_entry rvm_wait_entry runlock_entry w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 hi_21 hi_64 hi_95 lo_23 lo_71 lo_96 joff_97 joff_99 joff_104 CODE BASE4 BASER D_21 E_21 D_23 E_23 D_64 E_64 D_71 E_71 D_95 E_95 D_96 E_96 D_97 E_97 D_99 E_99 D_104 E_104 ANCH_23 ANCH_71 ANCH_96 LINK_97 LINK_99 LINK_104 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved ref_wview_overlay ref_seg_rom_none ref_mrd_overlay rmunmap_spec roracle_ok_pres rfree_fp_lt rntf_implT sllw1_word' rget_meta_spec runlock_spec rfree_entry rmunmap_entry segs RATP. lia.
+ rewrite H160, <- DIFF. gw_exact G22.
+ rewrite H160, <- (EQE (Z.shiftr v3 5)), <- (byte_zero_list xc G23). gw_exact BXc.
+ rewrite <- EQE0, <- (byte_zero_list xe G24). gw_exact BXe. }

intros r1 s' ms1 (-> & -> & FH). cbv beta iota.
destruct FH as (x1 & x5 & x6 & x7 & junk & m1 & -> & PE1 & WM1 & MI1 & ST1 & FR1 & MR1).
set (st1 := hdr_st st pf) in *.
assert (TK1 : ticks_ok st1) by (unfold st1; apply ticks_ok_hdr_st; gw_exact TK).
assert (MSL1 : meta_slot st1 g) by (exact (go_slot _ _ _ GO)).
assert (HK123 : forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w).
{ intros k Hk. unfold pf; cbn [aadd fst snd].
assert (CS : k = 1 \/ k = 2 \/ k = 3) by lia.
destruct CS as [-> |[-> | ->]];
[exists hi; replace (snd c0 + UNIT * off - 1) with (snd c0 + UNIT * off - 1) by lia
|exists lo8|exists v3];
[rewrite <- C1 | rewrite <- C2 | rewrite <- C3]; f_equal; unfold UNIT; lia. }
assert (FP1 : forall a, rfree_fp st1 lo (bv_unsigned sp - 48) a -> rfree_fp st lo (bv_unsigned sp) a).
{ intros a Ha. eapply (rfree_fp_hdr_st st pf lo (bv_unsigned sp) (bv_unsigned sp - 48) a TK HK123); [lia| gw_exact Ha]. }
assert (ERR1 : rw_cells segs m1 (errno_addr tp) [C4 errv]).
{ eapply rpres_except_rw_cells; [gw_exact PE1 | gw_exact ERR |]. cbn [cells_size csize Nat.add]. intros a Ha.
rewrite ETP in Ha. eapply rerrno_not_free_fp; [gw_exact MR | gw_exact LO | lia]. }
assert (TF : Z.testbit (m_freed (get_meta_rec st g)) i = false).
{ destruct (Z.testbit (m_freed (get_meta_rec st g)) i) eqn:E; [exfalso; apply NFR; left; gw_exact E| reflexivity]. }
assert (TA : Z.testbit (m_avail (get_meta_rec st g)) i = false).
{ destruct (Z.testbit (m_avail (get_meta_rec st g)) i) eqn:E; [exfalso; apply NFR; right; gw_exact E| reflexivity]. }

assert (BLKR : forall stX blk', s_regions stX = s_regions st -> In blk' (lbrm LB blk) -> exists r', s_regions stX !! fst (blk_slot blk') = Some r').
{ intros stX blk' ERX Hb'. rewrite ERX. unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [Hb' _].
destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' Hb') as [(r' & Hr' & _) _ _]. exists r'. gw_exact Hr'. }
unfold free_tail. cbv zeta. change (get_meta_rec st1 g) with (get_meta_rec st g).
apply rimplT_guard. intros _.
apply rimplT_if; intros HC.
-
apply negb_true_iff in HC. apply orb_false_iff in HC. destruct HC as [Hfz Hall]. apply Z.eqb_neq in Hfz. apply Z.eqb_neq in Hall.
apply rimplT_ret.
eapply evt_mono.
{ eapply (rfree_triv ra sp gp tp t0 t1 t2 s0 s1 a0 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 junk lo st st1 g i);
first [gw_exact MR1 | gw_exact MI1 | gw_exact MSL1 | gw_exact TF | gw_exact TA | gw_exact Hfz | gw_exact Hall | gw_exact FR1 | gw_exact ST1 | gw_exact LO | reflexivity | idtac].
all: try exact (go_freed _ _ _ GO). all: try exact (go_avail _ _ _ GO). all: change (get_meta_rec st1 g) with (get_meta_rec st g); lia. }
intros ms' TPo. unfold rftriv_post in TPo.
destruct TPo as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & -> & PE' & WM' & MI' & ST' & MR').
split; [reflexivity|]. do 16 eexists. split; [reflexivity|].
split; [gw_exact MI'|]. split; [gw_exact ST'|].
split. { eapply rpres_except_rw_cells; [gw_exact PE' | gw_exact ERR1 |]. cbn [cells_size csize Nat.add]. intros a Ha.
rewrite ETP in Ha. eapply rerrno_not_free_fp; [gw_exact MR | gw_exact LO | lia]. }
split; [gw_exact MR'|].
split. { eapply rpres_except_mono; [eapply rpres_except_trans; [gw_exact PE1| gw_exact PE']|]. intros a Ha. left. gw_exact Ha. }
split; [intros rid r' H; gw_exact H|].
split; [intros blk' Hb'; apply (BLKR _ blk' eq_refl Hb')|].
split; reflexivity.
-

assert (HNT : m_freed (get_meta_rec st g) = 0 \/ Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) + bit i = mask_upto (m_last_idx (get_meta_rec st g))).
{ apply negb_false_iff in HC. apply orb_true_iff in HC. destruct HC as [HC|HC]; apply Z.eqb_eq in HC; auto. }
eapply rimplT_evt.
{ eapply (rfree_tocall ra sp gp tp t0 t1 t2 s0 s1 a0 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 st1 g i);
first [gw_exact MR1 | gw_exact MI1 | gw_exact MSL1 | gw_exact TF | gw_exact TA | gw_exact HNT | idtac].
all: try exact (go_freed _ _ _ GO). all: try exact (go_avail _ _ _ GO). all: change (get_meta_rec st1 g) with (get_meta_rec st g); lia. }
intros ms2 (y2 & y3 & y4 & y5 & y6 & y7 & ->).
assert (HLB : forall b', In b' LB' -> In b' LB /\ blk_slot b' <> blk_slot blk).
{ intros b' Hb'. unfold LB', lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [H1 H2]. split; [gw_exact H1|].
intros E. rewrite E, aptr_eqb_refl in H2. gw_exact H2. }
assert (K1 : KINV st1 LB' 0).
{ unfold st1. eapply (KINV_hdr_st st LB LB' 0 pf blk r C Hin); [| gw_exact HLB | rewrite Fp, FB; reflexivity | rewrite Fp; gw_exact Hr | symmetry; gw_exact HAp | gw_exact P16m].
unfold LB', lbrm. apply (KINV_filter_slot st LB 0 (fun s => negb (aptr_eqb s (blk_slot blk)))). gw_exact K0. }
assert (L1 : LPRE st1 LB' 0 g b i).
{ unfold LB', lbrm. apply (LPRE_intro st1 LB 0 g b i blk); [exact (ki_slts _ _ _ K0) | exists ai; gw_exact Hgh | gw_exact SL | gw_exact NFR | gw_exact NG | pose proof (go_sc _ _ _ GO); change (get_meta_rec st1 g) with (get_meta_rec st g); lia]. }
assert (Z1 : ZINV st1 []) by (unfold st1; apply ZINV_hdr_st; apply (ZINV_of_CINV _ _ C)).
assert (OOK1 : oracle_ok m m1 st1).
{ unfold st1. apply oracle_ok_hdr_st; [gw_exact TK|]. eapply (roracle_ok_pres m m m1 st lo (bv_unsigned sp) m); [apply oracle_ok_refl | gw_exact MR | gw_exact LO | gw_exact PE1]. }
change (wz (conc st g)) with (Z_to_bv 64 (conc st1 g)). change (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc st1 g)).
eapply (rntf_implT gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc m LB' lo LO);
[gw_exact K1 | gw_exact L1 | gw_exact Z1 | gw_exact MR1 | gw_exact MI1 | gw_exact OOK1 | rewrite unsigned_lit by lia; gw_exact ST1 | rewrite unsigned_lit by lia; unfold FUEL; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]; lia |].

intros st2 mi ms3 NQ. unfold rntf_q in NQ.
destruct NQ as (u0 & u1 & u2 & a0v & a1v & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m3 & -> & MI3 & ST3 & MR3 & PE3 & [c3 KI3] & ZI3 & FR3 & RES3 & OOK3).
rewrite unsigned_lit in ST3, PE3 by lia.
replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in PE3 by lia.
try g_ret_pc_any.
assert (PE13 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m m3).
{ eapply rpres_except_trans; [gw_exact PE1|]. eapply rpres_except_mono; [gw_exact PE3| gw_exact FP1]. }
assert (FR3' : rw_cells segs m3 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply rpres_except_rw_cells; [gw_exact PE3 | gw_exact FR1 |]. cbn [cells_size csize Nat.add length]. intros a Ha Hfp.
pose proof (rfree_fp_lt st1 m1 lo (bv_unsigned sp - 48) a MR1 LO ltac:(lia) Hfp). lia. }
assert (ERR3 : rw_cells segs m3 (errno_addr tp) [C4 errv]).
{ eapply rpres_except_rw_cells; [gw_exact PE3 | gw_exact ERR1 |]. cbn [cells_size csize Nat.add]. intros a Ha.
rewrite ETP in Ha. eapply rerrno_not_free_fp; [gw_exact MR1 | gw_exact LO | lia]. }
pose proof (nf_regions _ _ FR3) as ER3. change (s_regions st1) with (s_regions st) in ER3.
pose proof (nf_brk _ _ FR3) as EB3. change (ctx st1) with (ctx st) in EB3.
destruct mi as [[bm len]|].
+
cbv beta iota.
destruct RES3 as (-> & -> & LEN & SND & (r2 & Hr2 & Kr2 & Lr2) & NOG).
replace (negb (len =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; lia).
pose proof Hr2 as Hr2'. rewrite ER3 in Hr2'.
destruct (WR _ _ Hr2') as (R2B0 & R2AL & R2L & R2C & R2F). unfold alloc_ceiling in R2C.
assert (R2D : r_base r2 + round_up_pg (r_len r2) <= 0x10000 \/ RIMG_HI <= r_base r2) by (apply (rreserved_disjoint1 _ _ R2F); lia).
assert (CB2 : conc st2 bm = r_base r2) by (rewrite (conc_region' st2 bm r2 Hr2); lia).
pose proof (round_up_pg_ge (r_len r2)) as RU2.
eapply rimplT_evt.
{ eapply (rfree_tomunmap sp gp tp u0 u1 u2 s0 s1 u5 u6 u7 u8 u9 u10 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u11 u12 u13 u14 _ ra (wz (conc st2 bm)) _ _ F fc m3 junk lo len st2 errv);
first [gw_exact TP | gw_exact MR3 | gw_exact MI3 | gw_exact LEN | gw_exact FR3' | gw_exact ERR3 | gw_exact ST3 | gw_exact LO | lia]. }
intros ms4 FM. unfold rfmun_post in FM.
destruct FM as (w0 & w1 & w2 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m4 & -> & MU4 & WM4 & MI4 & ST4 & FR4 & ERR4 & MR4).
eapply (rimplT_munmap m (conc st2 bm) len _ s).
{ eapply rmunmap_spec.
- rewrite unsigned_lit by lia. gw_exact ST4.
- gw_exact ERR4.
- gw_exact MI4.
- unfold wz. reflexivity.
- unfold wz. reflexivity.
- lia.
- rewrite Lr2, mmap_len_round. lia.
- lia.
- rewrite unsigned_lit by lia. lia.
- rewrite ETP, unsigned_lit by lia. lia.
- rewrite Lr2, mmap_len_round, unsigned_lit by lia. lia.
- rewrite ETP, Lr2, mmap_len_round. lia.
- rewrite TP; gw_expose_fam RATP; rewrite unsigned_lit by lia. lia. }
intros a ms5 MP. cbv beta. unfold rmunmap_post in MP.
destruct MP as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m5 & -> & MU5 & _ & MI5 & ST5 & ERR5 & ERNG).
rewrite (munmap_ok_range_val a ltac:(destruct a; cbn in ERNG |- *; [lia| gw_exact Logic.I])).
apply rimplT_ret.
try g_ret_pc_any.
rewrite unsigned_lit in MU5, ST5 by lia. rewrite Lr2, mmap_len_round, ETP in MU5.

assert (AMC2 : amc (ctx st2) = amc (ctx st)) by (rewrite (nf_amc _ _ FR3); reflexivity).
assert (MP2 : ci_mptrs st2) by (eapply (ci_mptrs_frame st st2 (ci_mp _ _ C) AMC2); [rewrite (nf_areas _ _ FR3); reflexivity| gw_exact ER3]).
assert (NOG' : forall b' gh, s_groups st2 !! b' = Some gh -> fst b' <> fst bm) by (intros b' gh Hb'; exact (NOG b' gh Hb')).
pose proof (rptrs_in_norid st2 LB' c3 (fst bm) r2 m4 KI3 ZI3 MR4 Hr2 Kr2 NOG' MP2) as PTR.
pose proof (rmrep_drop_region st2 (fst bm) PTR m4 MR4) as MRd4.
assert (MRd5 : rmrep (drop_region (fst bm) st2) m5).
{ eapply (rmrep_after_munmap st2 (fst bm) r2 m4 m5); [gw_exact MRd4 | gw_exact MR4 | gw_exact Hr2 | gw_exact Kr2 | rewrite <- CB2; gw_exact MU5 | lia]. }
assert (FR5 : rw_cells segs m5 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply rrw_cells_agree'; [gw_exact FR4|]. cbn [cells_size csize Nat.add length]. intros x Hx. apply MU5. rewrite wa_unsigned by lia.
rewrite ?ETP. cbn [outside]. repeat split; lia. }
eapply evt_mono.
{ eapply (rfree_fin1 sp gp tp z0 z1 z2 s0 s1 (munmap_ret a) z3 z4 z5 z6 z7 z8 z9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z10 z11 z12 z13 _ ra (sx32 errv) (wz (conc st2 bm)) (wz len) (rg_errno a errv) F fc m5 junk lo (drop_region (fst bm) st2) errv);
first [gw_exact TP | gw_exact MRd5 | gw_exact MI5 | gw_exact FR5 | apply le4_sx32 | gw_exact ERR5 | gw_exact ST5 | gw_exact LO | lia]. }
intros ms' FIN. unfold rffin_post in FIN.
destruct FIN as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & m' & -> & MUf & WMf & MIf & STf & ERRf & MRf).
split; [reflexivity|]. do 16 eexists. split; [reflexivity|].
split; [gw_exact MIf|]. split; [gw_exact STf|]. split; [gw_exact ERRf|]. split; [gw_exact MRf|].
split.
{
assert (DR : forall x, r_base r2 <= x < r_base r2 + round_up_pg (r_len r2) -> DROPPED st (drop_region (fst bm) st2) x).
{ intros x Hx. exists (fst bm), r2. split; [gw_exact Hr2'|]. split; [| split; [gw_exact Kr2| gw_exact Hx]].
cbn [drop_region s_regions set_shadow set_regions]. apply lookup_delete_eq. }
eapply rpres_except_trans; [eapply rpres_except_mono; [gw_exact PE13| intros x Hx; left; gw_exact Hx]|].
eapply rpres_except_trans; [eapply (rpres_except_of_munch_nw _ _ m3 m4 MU4)|].
{ intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ (RATP + -164) <= a < (RATP + -164 + 4))); [| gw_exact NC].
cover_intervals ltac:(fun y Hy => left; apply rfree_fp_stack; lia). }
eapply rpres_except_trans; [eapply (rpres_except_of_munch_nw _ _ m4 m5 MU5)|].
{ intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ (RATP + -164) <= a < (RATP + -164 + 4))); [| gw_exact NC].
cover_intervals ltac:(fun y Hy => first [left; apply rfree_fp_stack; lia | right; right; lia | right; left; apply DR; lia]). }
eapply (rpres_except_of_munch_nw _ _ m5 m' MUf).
intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ (RATP + -164) <= a < (RATP + -164 + 4))); [| gw_exact NC].
cover_intervals ltac:(fun y Hy => first [left; apply rfree_fp_stack; lia | right; right; lia]). }
split.
{ intros rid r' H. cbn [drop_region s_regions set_shadow set_regions] in H. apply lookup_delete_Some in H. destruct H as [_ H]. rewrite <- ER3. gw_exact H. }
split.
{ intros blk' Hb'. pose proof (proj1 (List.Forall_forall _ _) (ki_blks _ _ _ KI3) blk' Hb') as BK'.
destruct BK' as [(g' & i' & bb & SL' & HB' & FB' & _) _ _].
destruct (go_region _ _ _ (ki_gmetas _ _ _ KI3 bb g' HB')) as (rr & Hrr & _).
exists rr. cbn [drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne; [rewrite <- FB'; gw_exact Hrr|].
intros E. destruct HB' as [ai' Hbb]. apply (NOG bb _ Hbb). rewrite E. gw_exact FB'. }
split; [gw_exact EB3|].
intros brid boff HB0. cbn [drop_region s_regions set_shadow set_regions ctx s_ctx].
rewrite <- EB3 in HB0. destruct (ki_bk _ _ _ KI3 brid boff HB0) as (rb & Hrb & Krb).
rewrite lookup_delete_ne; [rewrite ER3; reflexivity |].
intros E. rewrite <- E, Hr2 in Hrb. assert (rb = r2) by congruence. subst rb. rewrite Kr2 in Krb. discriminate.
+

cbv beta iota. cbn in RES3. subst a1v.
apply rimplT_ret.
eapply evt_mono.
{ eapply (rfree_fin0 sp gp tp u0 u1 u2 s0 s1 u5 u6 u7 u8 u9 u10 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u11 u12 u13 u14 _ ra a0v _ _ F fc m3 junk lo st2 errv);
first [gw_exact TP | gw_exact MR3 | gw_exact MI3 | gw_exact FR3' | gw_exact ERR3 | gw_exact ST3 | gw_exact LO | lia]. }
intros ms' FIN. unfold rffin_post in FIN.
destruct FIN as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & m' & -> & MUf & WMf & MIf & STf & ERRf & MRf).
split; [reflexivity|]. do 16 eexists. split; [reflexivity|].
split; [gw_exact MIf|]. split; [gw_exact STf|]. split; [gw_exact ERRf|]. split; [gw_exact MRf|].
split.
{ eapply rpres_except_trans; [eapply rpres_except_mono; [gw_exact PE13| intros x Hx; left; gw_exact Hx]|].
eapply (rpres_except_of_munch_nw _ _ m3 m' MUf).
intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st st2 a \/ (RATP + -164) <= a < (RATP + -164 + 4))); [| gw_exact NC].
cover_intervals ltac:(fun y Hy => left; apply rfree_fp_stack; lia). }
split; [intros rid r' H; rewrite <- ER3; gw_exact H|].
split; [intros blk' Hb'; apply (BLKR st2 blk' ER3 Hb')|].
split; [gw_exact EB3|].
intros brid boff _. rewrite ER3. reflexivity.
Qed.
End FREE.

End RC__1.

End G.
End Mqa.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkQT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkQT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlkP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlkP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QM7w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QM7w. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8QT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8QT.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCa8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCa8.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCa8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCa8.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDXD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDXD.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkTt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkTt.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkTt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkTt.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDXD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDXD.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy8Z.Mqa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkTt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkTt.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy8Z.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQRC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQRC.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQRC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQRC.Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy8Z.Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QROt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QROt.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZxv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZxv.Mqo.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenX StepGenX2 GwCallee GwApply GwFold.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G Require Import GwFamMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rvm_wait_entry : Z).
Variables (w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 : Z).
Variables (hi_14 hi_18 hi_114 hi_121 hi_130 hi_136 hi_148 hi_218 hi_311 : bv 20).
Variables (lo_15 lo_19 lo_116 lo_122 lo_131 lo_137 lo_149 lo_220 lo_313 : bv 12).
Variables (joff_427 joff_552 : bv 21).
Variables (e_197bc : Z).
Hypothesis CODE : code_at segs base (alloc_slot_code w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 2212.
Let rmmap_entry := (rvm_wait_entry + 4)%Z.
Hypothesis D_14 : decode_any (Z_to_bv 32 w_14) = Some (Auipc 10 hi_14, 4%Z).
Hypothesis E_14 : is_ecall (Z_to_bv 32 w_14) = false.
Hypothesis D_15 : decode_any (Z_to_bv 32 w_15) = Some (Load SZ8 true 20 10 lo_15, 4%Z).
Hypothesis E_15 : is_ecall (Z_to_bv 32 w_15) = false.
Hypothesis D_18 : decode_any (Z_to_bv 32 w_18) = Some (Auipc 11 hi_18, 4%Z).
Hypothesis E_18 : is_ecall (Z_to_bv 32 w_18) = false.
Hypothesis D_19 : decode_any (Z_to_bv 32 w_19) = Some (OpImm ALU_ADD 22 11 lo_19, 4%Z).
Hypothesis E_19 : is_ecall (Z_to_bv 32 w_19) = false.
Hypothesis D_114 : decode_any (Z_to_bv 32 w_114) = Some (Auipc 11 hi_114, 4%Z).
Hypothesis E_114 : is_ecall (Z_to_bv 32 w_114) = false.
Hypothesis D_116 : decode_any (Z_to_bv 32 w_116) = Some (OpImm ALU_ADD 11 11 lo_116, 4%Z).
Hypothesis E_116 : is_ecall (Z_to_bv 32 w_116) = false.
Hypothesis D_121 : decode_any (Z_to_bv 32 w_121) = Some (Auipc 10 hi_121, 4%Z).
Hypothesis E_121 : is_ecall (Z_to_bv 32 w_121) = false.
Hypothesis D_122 : decode_any (Z_to_bv 32 w_122) = Some (OpImm ALU_ADD 25 10 lo_122, 4%Z).
Hypothesis E_122 : is_ecall (Z_to_bv 32 w_122) = false.
Hypothesis D_130 : decode_any (Z_to_bv 32 w_130) = Some (Auipc 11 hi_130, 4%Z).
Hypothesis E_130 : is_ecall (Z_to_bv 32 w_130) = false.
Hypothesis D_131 : decode_any (Z_to_bv 32 w_131) = Some (Load SZ8 true 11 11 lo_131, 4%Z).
Hypothesis E_131 : is_ecall (Z_to_bv 32 w_131) = false.
Hypothesis D_136 : decode_any (Z_to_bv 32 w_136) = Some (Auipc 13 hi_136, 4%Z).
Hypothesis E_136 : is_ecall (Z_to_bv 32 w_136) = false.
Hypothesis D_137 : decode_any (Z_to_bv 32 w_137) = Some (OpImm ALU_ADD 13 13 lo_137, 4%Z).
Hypothesis E_137 : is_ecall (Z_to_bv 32 w_137) = false.
Hypothesis D_148 : decode_any (Z_to_bv 32 w_148) = Some (Auipc 13 hi_148, 4%Z).
Hypothesis E_148 : is_ecall (Z_to_bv 32 w_148) = false.
Hypothesis D_149 : decode_any (Z_to_bv 32 w_149) = Some (OpImm ALU_ADD 13 13 lo_149, 4%Z).
Hypothesis E_149 : is_ecall (Z_to_bv 32 w_149) = false.
Hypothesis D_218 : decode_any (Z_to_bv 32 w_218) = Some (Auipc 13 hi_218, 4%Z).
Hypothesis E_218 : is_ecall (Z_to_bv 32 w_218) = false.
Hypothesis D_220 : decode_any (Z_to_bv 32 w_220) = Some (OpImm ALU_ADD 13 13 lo_220, 4%Z).
Hypothesis E_220 : is_ecall (Z_to_bv 32 w_220) = false.
Hypothesis D_311 : decode_any (Z_to_bv 32 w_311) = Some (Auipc 14 hi_311, 4%Z).
Hypothesis E_311 : is_ecall (Z_to_bv 32 w_311) = false.
Hypothesis D_313 : decode_any (Z_to_bv 32 w_313) = Some (OpImm ALU_ADD 14 14 lo_313, 4%Z).
Hypothesis E_313 : is_ecall (Z_to_bv 32 w_313) = false.
Hypothesis D_427 : decode_any (Z_to_bv 32 w_427) = Some (Jal 1 joff_427, 4%Z).
Hypothesis E_427 : is_ecall (Z_to_bv 32 w_427) = false.
Hypothesis D_552 : decode_any (Z_to_bv 32 w_552) = Some (Jal 1 joff_552, 4%Z).
Hypothesis E_552 : is_ecall (Z_to_bv 32 w_552) = false.
Hypothesis ANCH_15 : gw_anch (Z.shiftl (bv_signed hi_14) 12 + (base + 56) + bv_signed lo_15)%Z RGOT_SSP.
Hypothesis ANCH_19 : gw_anch (Z.shiftl (bv_signed hi_18) 12 + (base + 72) + bv_signed lo_19)%Z (RATP + 131960).
Hypothesis ANCH_116 : gw_anch (Z.shiftl (bv_signed hi_114) 12 + (base + 456) + bv_signed lo_116)%Z RDEBRUIJN.
Hypothesis ANCH_122 : gw_anch (Z.shiftl (bv_signed hi_121) 12 + (base + 484) + bv_signed lo_122)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_131 : gw_anch (Z.shiftl (bv_signed hi_130) 12 + (base + 520) + bv_signed lo_131)%Z (RATP + 131776).
Hypothesis ANCH_137 : gw_anch (Z.shiftl (bv_signed hi_136) 12 + (base + 544) + bv_signed lo_137)%Z (RDEBRUIJN + 128).
Hypothesis ANCH_149 : gw_anch (Z.shiftl (bv_signed hi_148) 12 + (base + 592) + bv_signed lo_149)%Z (RDEBRUIJN + 155).
Hypothesis ANCH_220 : gw_anch (Z.shiftl (bv_signed hi_218) 12 + (base + 872) + bv_signed lo_220)%Z RDEBRUIJN.
Hypothesis ANCH_313 : gw_anch (Z.shiftl (bv_signed hi_311) 12 + (base + 1244) + bv_signed lo_313)%Z (RDEBRUIJN + 32).
Hypothesis LINK_427 : gw_anch (base + 1708 + bv_signed joff_427)%Z (rmmap_entry + 0)%Z.
Hypothesis LINK_552 : gw_anch (base + 2208 + bv_signed joff_552)%Z (e_197bc + 0)%Z.
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
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QZxv.Mqo.rarea_rep segs) (@rarea_rep) (gw_ent (@QROt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mqc.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_0))))))))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QZxv.Mqo.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QROt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mqc.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_1))))))))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QZxv.Mqo.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QROt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mqc.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_2))))))))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QZxv.Mqo.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QROt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mqc.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_3))))))))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QZxv.Mqo.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QROt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mqc.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_4))))))))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QZxv.Mqo.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QROt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mqc.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_5))))))))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QZxv.Mqo.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QROt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mqc.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_6))))))))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QZxv.Mqo.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QROt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mqc.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_7))))))))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QZxv.Mqo.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QROt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mqc.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_8))))))))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QZxv.Mqo.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QROt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mqc.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_9))))))))))))))).

Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmrep_bounces_read : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_bounces_read) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_bounces_read)).
Definition rmrep_seq_read : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_seq_read) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_seq_read)).
Definition rmrep_ctx_frameW : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_ctx_frameW) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_ctx_frameW)).

Definition rmrep_set_seq : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq4.rmrep_set_seq) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq4.rmrep_set_seq)).

Definition rmrep_set_bounce : ltac:(gw_ctx_fold_ty2 (@QQRC.Mqc.rmrep_set_bounce) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mqc.rmrep_set_bounce)).
Ltac rraw_store_finish0 A bs' MU WM SOK :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); (gw_expose_fam RATP; unfold wa); f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
apply (munch_write _ _ mX A bs') in MU; [| gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; cbn [inside]; lia];
apply (wmono_write segs _ mX (wa A) bs') in WM;
lazymatch goal with HI : mem_inv segs mX |- _ =>
apply (mem_inv_store segs mX (wa A) bs') in HI;
[| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by ((gw_expose_fam RATP; unfold wa); f_equal; lia); exact SOK ] ]
end;
clear L SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
end.

#[using="RDEBRUIJN RGOT_SSP e_197bc rvm_wait_entry rmmap_entry RATP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 D_114 E_114 D_116 E_116 D_121 E_121 D_122 E_122 D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 D_218 E_218 D_220 E_220 D_311 E_311 D_313 E_313 D_427 E_427 D_552 E_552 ANCH_15 ANCH_19 ANCH_116 ANCH_122 ANCH_131 ANCH_137 ANCH_149 ANCH_220 ANCH_313 LINK_427 LINK_552 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rmmap_entry"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := first [clear - hs segs base w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_14 hi_18 hi_114 hi_121 hi_130 hi_136 hi_148 hi_218 hi_311 lo_15 lo_19 lo_116 lo_122 lo_131 lo_137 lo_149 lo_220 lo_313 joff_427 joff_552 RDEBRUIJN RGOT_SSP e_197bc rvm_wait_entry rmmap_entry RATP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 D_114 E_114 D_116 E_116 D_121 E_121 D_122 E_122 D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 D_218 E_218 D_220 E_220 D_311 E_311 D_313 E_313 D_427 E_427 D_552 E_552 ANCH_15 ANCH_19 ANCH_116 ANCH_122 ANCH_131 ANCH_137 ANCH_149 ANCH_220 ANCH_313 LINK_427 LINK_552 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ | clear - hs segs base w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_14 hi_18 hi_114 hi_121 hi_130 hi_136 hi_148 hi_218 hi_311 lo_15 lo_19 lo_116 lo_122 lo_131 lo_137 lo_149 lo_220 lo_313 joff_427 joff_552 RDEBRUIJN RGOT_SSP e_197bc rvm_wait_entry rmmap_entry RATP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 D_114 E_114 D_116 E_116 D_121 E_121 D_122 E_122 D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 D_218 E_218 D_220 E_220 D_311 E_311 D_313 E_313 D_427 E_427 D_552 E_552 ANCH_15 ANCH_19 ANCH_116 ANCH_122 ANCH_131 ANCH_137 ANCH_149 ANCH_220 ANCH_313 LINK_427 LINK_552 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay].

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

Section SEQ.
Variables (sc : Z).
Hypothesis SC : 0 <= sc < 48.

Definition rseqW : list (Z * Z) := [((RATP + 132816), (RATP + 132881))]%Z.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rmmap_entry SC"] Lemma rbounce_walk :
forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) (m : mem),
rmrep st m -> 0 <= c_seq (ctx st) < 256 -> (forall i, 0 <= bounces st i < 256) -> (forall i, 0 <= unmap_seq st i < 256) ->
mem_inv segs m ->
evt segs (fun ms' => exists (t0' t1' a3' a5' a7' : word) m',
ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3' a4 a5' (wz (c_seq (ctx st))) a7' s2 s3 s4 s5 (Z_to_bv 64 (RATP + 131960)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x580)) fc None m' (seg_rom segs)
/\ a3' = Z_to_bv 64 (Z.b2z (is_bouncing sc st))
/\ munch rseqW m m' /\ wmono segs m m' /\ mem_inv segs m' /\ rmrep (account_bounce sc st) m')
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (RATP + 131960)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x2cc)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rmmap_entry SC segs base RATP sc. gw_expose_fam RATP. try gw_hide sc.
intros until m. intros MR SEQ BR USR MI.
pose proof (munch_refl rseqW m) as MU. pose proof (wmono_refl segs m) as WM. unfold rseqW in MU.
gw_expose_fam RATP.

assert (EXIT : forall stX mX (t0v t1v a3v a5v a6v a7v : word),
rmrep stX mX -> stX = account_bounce sc st -> mem_inv segs mX -> a3v = Z_to_bv 64 (Z.b2z (is_bouncing sc st)) ->
munch [((RATP + 132816), (RATP + 132881))]%Z m mX -> wmono segs m mX ->
evt segs (fun ms' => exists (t0' t1' a3' a5' a7' : word) m',
ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3' a4 a5' (wz (c_seq (ctx st))) a7' s2 s3 s4 s5 (Z_to_bv 64 (RATP + 131960)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x580)) fc None m' (seg_rom segs)
/\ a3' = Z_to_bv 64 (Z.b2z (is_bouncing sc st))
/\ munch [((RATP + 132816), (RATP + 132881))]%Z m m' /\ wmono segs m m' /\ mem_inv segs m' /\ rmrep (account_bounce sc st) m')
(MS (mkR ra sp gp tp t0v t1v t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3v a4 a5v a6v a7v s2 s3 s4 s5 (Z_to_bv 64 (RATP + 131960)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x57c)) fc None mX (seg_rom segs))).
{ intros stX mX t0v t1v a3v a5v a6v a7v MRX EX MIX -> MUX WMX.
pose proof (rmrep_seq_read stX mX (wa ((RATP + 132880))) MRX eq_refl) as RDS.
replace (wa ((RATP + 132880))) with (Z_to_bv 64 ((RATP + 132880))) in RDS by (unfold wa; f_equal; lia).
assert (SQX : c_seq (ctx stX) = c_seq (ctx st)).
{ rewrite EX. unfold account_bounce. destruct (sc_in_seq_range sc); [|reflexivity].
destruct (negb _ && _); [|reflexivity]. destruct (_ <? 100); reflexivity. }
rewrite SQX in RDS.
step. rewrite ?zxb_b8 by lia. clear RDS.
apply evt_done. do 6 eexists. split; [reflexivity|]. split; [reflexivity|].
split; [gw_exact MUX|]. split; [gw_exact WMX|]. split; [gw_exact MIX| rewrite <- EX; gw_exact MRX]. }

step. rewrite ?(unsigned_lit sc) by lia. step.
step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
{
assert (HO : sc_in_seq_range sc = false).
{ unfold sc_in_seq_range. destruct (Z.lt_ge_cases sc 7) as [L7|G7].
- replace (7 <=? sc) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
- rewrite swrap32_small in K by lia. change 18446744073709551615 with (Z.ones 64) in K. rewrite Z.land_ones, Z.mod_small in K by lia.
replace (sc <? 39) with false by (symmetry; apply Z.ltb_ge; lia). apply Bool.andb_false_r. }
step. step.
eapply EXIT; [gw_exact MR| | gw_exact MI| | gw_exact MU| gw_exact WM].
- unfold account_bounce. rewrite HO. reflexivity.
- unfold is_bouncing. rewrite HO. reflexivity. }
rewrite swrap32_small in K |- * by lia. change 18446744073709551615 with (Z.ones 64) in K. rewrite Z.land_ones in K by lia.
destruct (Z.lt_ge_cases sc 7) as [L7|G7].
{ exfalso. clear - K L7 SC RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rmmap_entry segs base RATP. Z.div_mod_to_equations. lia. }
rewrite Z.mod_small in K by lia.
assert (IN : sc_in_seq_range sc = true) by (unfold sc_in_seq_range; rewrite (proj2 (Z.leb_le 7 sc)), (proj2 (Z.ltb_lt sc 39)) by lia; reflexivity).

step. rewrite ?(unsigned_lit (sc + -7)) by lia.
pose proof (rmrep_bounces_read st m (sc - 7) (wa ((RATP + 132848) + (sc - 7))) MR ltac:(lia) eq_refl) as RDB.
replace (wa ((RATP + 132848) + (sc - 7))) with (Z_to_bv 64 ((RATP + 131960) + (sc + -7) + 888)) in RDB by (unfold wa; f_equal; lia).
pose proof (BR (sc - 7)) as BR7. pose proof (USR (sc - 7)) as USR7.
step. rewrite ?zxb_b8 by lia. clear RDB.
pose proof MR as (_ & (_ & _ & _ & US & _) & _).
pose proof (u8arr_read segs m _ (unmap_seqs st) (sc - 7) _ (Z_to_bv 64 ((RATP + 131960) + (sc + -7) + 856)) US (unmap_seqs_nth st (sc - 7) ltac:(lia)) ltac:(lia)
ltac:((gw_expose_fam RATP; unfold wa); f_equal; lia)) as RDU. clear US.
step. rewrite ?zxb_b8 by lia. clear RDU.

step. step.
set (nos := 100 <=? bounces st (sc - 7)).
assert (NOSE : is_bouncing sc st = nos) by (unfold is_bouncing; rewrite IN; reflexivity).
assert (A3 : Z_to_bv 64 (Z.lxor (bv_unsigned (v_sltiu (wz (bounces st (sc - 7))) 100)) 1) = Z_to_bv 64 (Z.b2z (is_bouncing sc st))).
{ rewrite NOSE. unfold v_sltiu, c_ltu, bv_ltu, nos. rewrite (wz_unsigned (bounces st (sc - 7))) by lia.
change (bv_wrap 64 100) with 100.
destruct (Z.ltb_spec (bounces st (sc - 7)) 100); destruct (Z.leb_spec 100 (bounces st (sc - 7))); try lia; reflexivity. }
rewrite A3. clear A3.
assert (AB : account_bounce sc st =
(if negb (unmap_seq st (sc - 7) =? 0) && (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10)
then if bounces st (sc - 7) + 1 <? 100 then set_bounce (sc - 7) (bounces st (sc - 7) + 1) st else set_bounce (sc - 7) 150 st
else st)) by (unfold account_bounce; rewrite IN; reflexivity).

step. if_cases K1; zify_cond K1; rewrite ?(wz_unsigned (unmap_seq st (sc - 7))) in K1 by lia.
{ eapply EXIT; [gw_exact MR| | gw_exact MI| reflexivity| gw_exact MU| gw_exact WM]. rewrite AB, K1. reflexivity. }

pose proof (rmrep_seq_read st m (wa ((RATP + 132880))) MR eq_refl) as RDS.
replace (wa ((RATP + 132880))) with (Z_to_bv 64 ((RATP + 132880))) in RDS by (unfold wa; f_equal; lia).
step. rewrite ?zxb_b8 by lia. clear RDS.
step. rewrite (wz_unsigned (c_seq (ctx st))), (wz_unsigned (unmap_seq st (sc - 7))) by lia.
step. step. if_cases K2; unfold bv_lts in K2; rewrite !signed_lit_small in K2 by lia.
{
apply Z.ltb_lt in K2.
apply evt_done. do 6 eexists. split; [reflexivity|]. split; [reflexivity|].
split; [gw_exact MU|]. split; [gw_exact WM|]. split; [gw_exact MI|].
rewrite AB. replace (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10) with false by (symmetry; apply Z.ltb_ge; lia).
rewrite Bool.andb_false_r. gw_exact MR. }
apply Z.ltb_ge in K2.
assert (AB2 : account_bounce sc st =
(if bounces st (sc - 7) + 1 <? 100 then set_bounce (sc - 7) (bounces st (sc - 7) + 1) st else set_bounce (sc - 7) 150 st)).
{ rewrite AB. replace (unmap_seq st (sc - 7) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
replace (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
clear AB K1 K2.
pose proof MR as (_ & (_ & _ & _ & _ & BA & _) & _).
pose proof (u8arr_store_ok segs _ _ (bouncess st) (sc - 7) (Z_to_bv 64 ((RATP + 131960) + (sc + -7) + 888)) BA
ltac:(rewrite bouncess_length; lia) ltac:((gw_expose_fam RATP; unfold wa); f_equal; lia)) as SOK. clear BA.

step. step. if_cases K3; zify_cond K3; rewrite ?(wz_unsigned (bounces st (sc - 7))), ?unsigned_lit in K3 by lia.
-
step. rewrite (wz_unsigned (bounces st (sc - 7))) by lia.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_bounce st mX (sc - 7) (bounces st (sc - 7) + 1) MR ltac:(lia)) as MR2; gw_expose_fam RATP end.
rraw_store_finish0 ((RATP + 132848) + (sc - 7)) [b8 (bounces st (sc - 7) + 1)] MU WM SOK.
eapply EXIT; [gw_exact MR2| | assumption| reflexivity| gw_exact MU| gw_exact WM].
rewrite AB2. replace (bounces st (sc - 7) + 1 <? 100) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
-
step. step. st1. rewrite (le1_lit 150) by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_bounce st mX (sc - 7) 150 MR ltac:(lia)) as MR2; gw_expose_fam RATP end.
rraw_store_finish0 ((RATP + 132848) + (sc - 7)) [b8 150] MU WM SOK.
eapply EXIT; [gw_exact MR2| | assumption| reflexivity| gw_exact MU| gw_exact WM].
rewrite AB2. replace (bounces st (sc - 7) + 1 <? 100) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_1 LAY_win_2 LAY_ref_reserved rmmap_entry"] Lemma rseq_walk :
forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) (m0 m : mem),
rmrep st m -> 0 <= c_seq (ctx st) < 256 -> mem_inv segs m ->
munch rseqW m0 m -> wmono segs m0 m ->
evt segs (fun ms' => exists (a6' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 31) a6' a7 s2 s3 s4 s5 (Z_to_bv 64 (RATP + 131960)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x5ac)) fc None m' (seg_rom segs)
/\ munch rseqW m0 m' /\ wmono segs m0 m' /\ mem_inv segs m' /\ rmrep (step_seq st) m')
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 (wz (c_seq (ctx st))) a7 s2 s3 s4 s5 (Z_to_bv 64 (RATP + 131960)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x580)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_1 LAY_win_2 LAY_ref_reserved rmmap_entry segs base RATP sc SC. gw_expose_fam RATP. first [clear SC | gw_hide SC | idtac]; try gw_hide sc.
intros until m. intros MR SEQ MI MU WM. unfold rseqW in *.
set (q := c_seq (ctx st)) in *.
pose proof MR as (_ & (_ & _ & _ & US & _ & C6) & _).
gw_expose_fam RATP. unfold ctx_tail_cells in C6.
replace ((RATP + 132880)) with (RATP + 132880) in C6 by first [reflexivity | (cbn; lia)]. replace ((RATP + 132816)) with (RATP + 132816) in US by first [reflexivity | (cbn; lia)].

assert (TL : forall (mj : mem) (stj : mstate) (ns : Z),
0 <= ns < 256 -> rmrep stj mj -> ctx_tail_cells stj = ctx_tail_cells st -> mem_inv segs mj ->
munch [((RATP + 132816), (RATP + 132881))]%Z m0 mj -> wmono segs m0 mj ->
evt segs (fun ms' => exists (a6' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 31) a6' a7 s2 s3 s4 s5 (Z_to_bv 64 (RATP + 131960)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x5ac)) fc None m' (seg_rom segs)
/\ munch [((RATP + 132816), (RATP + 132881))]%Z m0 m' /\ wmono segs m0 m' /\ mem_inv segs m' /\ rmrep (upd_ctx (set_seq ns) stj) m')
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 255) (Z_to_bv 64 ns) a7 s2 s3 s4 s5 (Z_to_bv 64 (RATP + 131960)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x5a4)) fc None mj (seg_rom segs))).
{ intros mj stj ns NS MRj CTj MIj MUj WMj.
pose proof MRj as (_ & (_ & _ & _ & _ & _ & C6j) & _). rewrite CTj in C6j. unfold ctx_tail_cells in C6j. gw_expose_fam RATP.
replace ((RATP + 132880)) with (RATP + 132880) in C6j by first [reflexivity | (cbn; lia)].
pose proof (rw_cells_store_ok_at segs _ _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 ((RATP + 132880))) C6j eq_refl eq_refl
ltac:(unfold wa; f_equal; lia)) as SOK.
clear C6j.

step. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_seq stj mX ns MRj NS) as MR1; gw_expose_fam RATP end.
rraw_store_finish0 ((RATP + 132880)) [b8 ns] MUj WMj SOK.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [gw_exact MUj|]. split; [gw_exact WMj|]. split; [assumption| gw_exact MR1]. }

step. step. if_cases K2; zify_cond K2; rewrite ?(wz_unsigned q), ?unsigned_lit in K2 by lia.
-
step. rewrite (wz_unsigned q) by lia.
eapply evt_mono; [eapply (TL m st (q + 1)); [lia| gw_exact MR| reflexivity| gw_exact MI| gw_exact MU| gw_exact WM]|].
intros ms' PO. rewrite (step_seq_eq st). fold q. replace (q =? 255) with false by (symmetry; apply Z.eqb_neq; lia). gw_exact PO.
-
pose proof (rw_cells_of_u8arr segs _ _ _ US) as USC. rewrite unmap_seqs_length in USC. clear US C6.
pose proof (munch_refl [((RATP + 132816), (RATP + 132848))]%Z m) as MUz. pose proof (wmono_refl segs m) as WMz.
step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (UZ : u8arr segs mX (RATP + 132816) (zeros 32));
[ apply (u8arr_of_rw_cells segs mX (RATP + 132816) 32);
lazymatch goal with H : rw_cells segs mX (RATP + 132816) _ |- _ =>
apply (rw_cells_congr segs mX (RATP + 132816) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [CB 32 (zeros 32)]); [reflexivity| reflexivity| cbn; split; [reflexivity| exact I]| gw_exact H] end |] end.
set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
pose proof MR as (_ & (_ & _ & _ & _ & _ & C6) & _). (gw_expose_fam RATP; unfold ctx_tail_cells in C6).
lazymatch goal with MUc : munch _ m ?mX, WMc : wmono segs m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRz : rmrep stz mX);
[ eapply (rmrep_ctx_frameW st stz _ mX _ MR MUc WMc); try reflexivity;
[ intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia
| right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia]
| right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia]
| right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia]
| left; unfold stz; rewrite unmap_seqs_empty; gw_expose_fam RATP; gw_exact UZ
| right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia]
| right; split; [| intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia];
unfold ctx_tail_cells, brk_word, ctx, stz; cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]; reflexivity ]
| clear MUc WMc ] end.

step. step.
lazymatch goal with MUc : munch _ m0 ?mX, WMc : wmono segs m0 ?mX, MIc : mem_inv segs ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
eapply evt_mono; [eapply (TL mX stz 1); [lia| gw_exact MRz| reflexivity| gw_exact MIc| gw_exact MUc| gw_exact WMc]|] end.
intros ms' PO. rewrite (step_seq_eq st). fold q. rewrite K2. cbn [Z.eqb Pos.eqb]. gw_exact PO.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rmmap_entry SC"] Lemma rmm_seq_walk :
forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) (m : mem),
rmrep st m -> 0 <= c_seq (ctx st) < 256 -> (forall i, 0 <= bounces st i < 256) -> (forall i, 0 <= unmap_seq st i < 256) ->
mem_inv segs m ->
evt segs (fun ms' => exists (t0' t1' a3' a6' a7' : word) m',
ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3' a4 (Z_to_bv 64 31) a6' a7' s2 s3 s4 s5 (Z_to_bv 64 (RATP + 131960)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x5ac)) fc None m' (seg_rom segs)
/\ a3' = Z_to_bv 64 (Z.b2z (is_bouncing sc st))
/\ munch rseqW m m' /\ wmono segs m m' /\ mem_inv segs m' /\ rmrep (step_seq (account_bounce sc st)) m')
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (RATP + 131960)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x2cc)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rmmap_entry SC segs base RATP sc. gw_expose_fam RATP. try gw_hide sc.
intros until m. intros MR SEQ BR USR MI.
eapply evt_cut; [eapply rbounce_walk; eassumption|].
cbv beta. intros ms' (t0' & t1' & a3' & a5' & a7' & m' & -> & A3 & MU & WM & MI' & MR').
assert (SEQ' : c_seq (ctx (account_bounce sc st)) = c_seq (ctx st)).
{ unfold account_bounce. destruct (sc_in_seq_range sc); [|reflexivity].
destruct (negb _ && _); [|reflexivity]. destruct (_ <? 100); reflexivity. }
rewrite <- SEQ'.
eapply evt_mono; [eapply (rseq_walk _ _ _ _ t0' t1'); [gw_exact MR'| rewrite SEQ'; gw_exact SEQ| gw_exact MI'| gw_exact MU| gw_exact WM]|].
cbv beta. intros ms'' (a6'' & m'' & -> & MU'' & WM'' & MI'' & MR'').
do 6 eexists. split; [reflexivity|]. subst a3'.
repeat (split; [first [reflexivity| assumption]|]). gw_exact MR''.
Qed.
End SEQ.

End RC__1.

End G.
