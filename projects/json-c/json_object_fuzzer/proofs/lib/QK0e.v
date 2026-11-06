(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqdR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVbl.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVbl.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQLG.Mq8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q91D.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q91D.Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQLG.Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q91D.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q91D.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQRC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQRC.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require G.T_shp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_shp.F_fmt_fp.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q91D.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q91D.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require G.T_pe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qbz7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qbz7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFau.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFau.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8l1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8l1.Mq1.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QROt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QROt.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq1.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= Q6q3.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= Q6q3.mkr__nia_1. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenX StepGenX2 GwCallee GwApply GwFold.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 : Z).
Variables (hi_22 hi_281 hi_332 hi_360 hi_371 hi_378 hi_395 hi_412 hi_426 hi_438 hi_453 hi_467 hi_473 hi_533 hi_543 : bv 20).
Variables (lo_25 lo_282 lo_333 lo_362 lo_372 lo_379 lo_396 lo_413 lo_427 lo_439 lo_454 lo_468 lo_474 lo_534 lo_545 : bv 12).
Variables (joff_81 joff_381 joff_383 joff_389 joff_530 joff_627 joff_639 joff_648 joff_655 joff_668 joff_680 joff_689 joff_701 joff_713 joff_722 joff_729 joff_742 joff_754 joff_762 joff_798 joff_883 joff_907 : bv 21).
Variables (G_102fd G_10741 G_107e0 G_11778 G_11858 G_118c0 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
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
Hypothesis D_371 : decode_any (Z_to_bv 32 w_371) = Some (Auipc 10 hi_371, 4%Z).
Hypothesis E_371 : is_ecall (Z_to_bv 32 w_371) = false.
Hypothesis D_372 : decode_any (Z_to_bv 32 w_372) = Some (OpImm ALU_ADD 10 10 lo_372, 4%Z).
Hypothesis E_372 : is_ecall (Z_to_bv 32 w_372) = false.
Hypothesis D_378 : decode_any (Z_to_bv 32 w_378) = Some (Auipc 10 hi_378, 4%Z).
Hypothesis E_378 : is_ecall (Z_to_bv 32 w_378) = false.
Hypothesis D_379 : decode_any (Z_to_bv 32 w_379) = Some (OpImm ALU_ADD 23 10 lo_379, 4%Z).
Hypothesis E_379 : is_ecall (Z_to_bv 32 w_379) = false.
Hypothesis D_381 : decode_any (Z_to_bv 32 w_381) = Some (Jal 1 joff_381, 4%Z).
Hypothesis E_381 : is_ecall (Z_to_bv 32 w_381) = false.
Hypothesis D_383 : decode_any (Z_to_bv 32 w_383) = Some (Jal 1 joff_383, 4%Z).
Hypothesis E_383 : is_ecall (Z_to_bv 32 w_383) = false.
Hypothesis D_389 : decode_any (Z_to_bv 32 w_389) = Some (Jal 1 joff_389, 4%Z).
Hypothesis E_389 : is_ecall (Z_to_bv 32 w_389) = false.
Hypothesis D_395 : decode_any (Z_to_bv 32 w_395) = Some (Auipc 12 hi_395, 4%Z).
Hypothesis E_395 : is_ecall (Z_to_bv 32 w_395) = false.
Hypothesis D_396 : decode_any (Z_to_bv 32 w_396) = Some (OpImm ALU_ADD 12 12 lo_396, 4%Z).
Hypothesis E_396 : is_ecall (Z_to_bv 32 w_396) = false.
Hypothesis D_412 : decode_any (Z_to_bv 32 w_412) = Some (Auipc 11 hi_412, 4%Z).
Hypothesis E_412 : is_ecall (Z_to_bv 32 w_412) = false.
Hypothesis D_413 : decode_any (Z_to_bv 32 w_413) = Some (OpImm ALU_ADD 11 11 lo_413, 4%Z).
Hypothesis E_413 : is_ecall (Z_to_bv 32 w_413) = false.
Hypothesis D_426 : decode_any (Z_to_bv 32 w_426) = Some (Auipc 11 hi_426, 4%Z).
Hypothesis E_426 : is_ecall (Z_to_bv 32 w_426) = false.
Hypothesis D_427 : decode_any (Z_to_bv 32 w_427) = Some (OpImm ALU_ADD 11 11 lo_427, 4%Z).
Hypothesis E_427 : is_ecall (Z_to_bv 32 w_427) = false.
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
Hypothesis D_530 : decode_any (Z_to_bv 32 w_530) = Some (Jal 1 joff_530, 4%Z).
Hypothesis E_530 : is_ecall (Z_to_bv 32 w_530) = false.
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
Hypothesis D_639 : decode_any (Z_to_bv 32 w_639) = Some (Jal 1 joff_639, 4%Z).
Hypothesis E_639 : is_ecall (Z_to_bv 32 w_639) = false.
Hypothesis D_648 : decode_any (Z_to_bv 32 w_648) = Some (Jal 1 joff_648, 4%Z).
Hypothesis E_648 : is_ecall (Z_to_bv 32 w_648) = false.
Hypothesis D_655 : decode_any (Z_to_bv 32 w_655) = Some (Jal 1 joff_655, 4%Z).
Hypothesis E_655 : is_ecall (Z_to_bv 32 w_655) = false.
Hypothesis D_668 : decode_any (Z_to_bv 32 w_668) = Some (Jal 1 joff_668, 4%Z).
Hypothesis E_668 : is_ecall (Z_to_bv 32 w_668) = false.
Hypothesis D_680 : decode_any (Z_to_bv 32 w_680) = Some (Jal 1 joff_680, 4%Z).
Hypothesis E_680 : is_ecall (Z_to_bv 32 w_680) = false.
Hypothesis D_689 : decode_any (Z_to_bv 32 w_689) = Some (Jal 1 joff_689, 4%Z).
Hypothesis E_689 : is_ecall (Z_to_bv 32 w_689) = false.
Hypothesis D_701 : decode_any (Z_to_bv 32 w_701) = Some (Jal 1 joff_701, 4%Z).
Hypothesis E_701 : is_ecall (Z_to_bv 32 w_701) = false.
Hypothesis D_713 : decode_any (Z_to_bv 32 w_713) = Some (Jal 1 joff_713, 4%Z).
Hypothesis E_713 : is_ecall (Z_to_bv 32 w_713) = false.
Hypothesis D_722 : decode_any (Z_to_bv 32 w_722) = Some (Jal 1 joff_722, 4%Z).
Hypothesis E_722 : is_ecall (Z_to_bv 32 w_722) = false.
Hypothesis D_729 : decode_any (Z_to_bv 32 w_729) = Some (Jal 1 joff_729, 4%Z).
Hypothesis E_729 : is_ecall (Z_to_bv 32 w_729) = false.
Hypothesis D_742 : decode_any (Z_to_bv 32 w_742) = Some (Jal 1 joff_742, 4%Z).
Hypothesis E_742 : is_ecall (Z_to_bv 32 w_742) = false.
Hypothesis D_754 : decode_any (Z_to_bv 32 w_754) = Some (Jal 1 joff_754, 4%Z).
Hypothesis E_754 : is_ecall (Z_to_bv 32 w_754) = false.
Hypothesis D_762 : decode_any (Z_to_bv 32 w_762) = Some (Jal 1 joff_762, 4%Z).
Hypothesis E_762 : is_ecall (Z_to_bv 32 w_762) = false.
Hypothesis D_798 : decode_any (Z_to_bv 32 w_798) = Some (Jal 1 joff_798, 4%Z).
Hypothesis E_798 : is_ecall (Z_to_bv 32 w_798) = false.
Hypothesis D_883 : decode_any (Z_to_bv 32 w_883) = Some (Jal 1 joff_883, 4%Z).
Hypothesis E_883 : is_ecall (Z_to_bv 32 w_883) = false.
Hypothesis D_907 : decode_any (Z_to_bv 32 w_907) = Some (Jal 1 joff_907, 4%Z).
Hypothesis E_907 : is_ecall (Z_to_bv 32 w_907) = false.
Hypothesis ANCH_25 : gw_anch (Z.shiftl (bv_signed hi_22) 12 + (base + 88) + bv_signed lo_25)%Z got_ssp.
Hypothesis ANCH_282 : gw_anch (Z.shiftl (bv_signed hi_281) 12 + (base + 1124) + bv_signed lo_282)%Z G_118c0.
Hypothesis ANCH_333 : gw_anch (Z.shiftl (bv_signed hi_332) 12 + (base + 1328) + bv_signed lo_333)%Z G_11778.
Hypothesis ANCH_362 : gw_anch (Z.shiftl (bv_signed hi_360) 12 + (base + 1440) + bv_signed lo_362)%Z G_102fd.
Hypothesis ANCH_372 : gw_anch (Z.shiftl (bv_signed hi_371) 12 + (base + 1484) + bv_signed lo_372)%Z G_102fd.
Hypothesis ANCH_379 : gw_anch (Z.shiftl (bv_signed hi_378) 12 + (base + 1512) + bv_signed lo_379)%Z G_10741.
Hypothesis ANCH_396 : gw_anch (Z.shiftl (bv_signed hi_395) 12 + (base + 1580) + bv_signed lo_396)%Z G_102fd.
Hypothesis ANCH_413 : gw_anch (Z.shiftl (bv_signed hi_412) 12 + (base + 1648) + bv_signed lo_413)%Z G_102fd.
Hypothesis ANCH_427 : gw_anch (Z.shiftl (bv_signed hi_426) 12 + (base + 1704) + bv_signed lo_427)%Z G_11858.
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
Hypothesis RNG_STATIC_SPLIT : gw_br STATIC_SPLIT 8.
Hypothesis LAY_lo_STATIC_SPLIT : gw_le 65536 STATIC_SPLIT.
Hypothesis AL_STATIC_SPLIT : gw_al STATIC_SPLIT 8.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis LAY_lo_got_ssp : gw_le 65536 got_ssp.
Hypothesis AL_got_ssp : gw_al got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis LAY_lo_ssp_guard : gw_le 65536 ssp_guard.
Hypothesis AL_ssp_guard : gw_al ssp_guard 8.
Hypothesis RNG_GLOBALS_TOP : gw_br GLOBALS_TOP 8.
Hypothesis LAY_lo_GLOBALS_TOP : gw_le 65536 GLOBALS_TOP.
Hypothesis AL_GLOBALS_TOP : gw_al GLOBALS_TOP 8.
Hypothesis LAY_STATIC_SPLIT_got_ssp : gw_le (STATIC_SPLIT + 8) got_ssp.
Hypothesis LAY_got_ssp_ssp_guard : gw_le (got_ssp + 8) ssp_guard.
Hypothesis LAY_ssp_guard_GLOBALS_TOP : gw_le (ssp_guard + 8) GLOBALS_TOP.
Hypothesis RNG_G_118c0 : gw_br G_118c0 116.
Hypothesis ROM_G_118c0 : ro_bytes segs G_118c0 [Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 10; Z_to_bv 8 10; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 3; Z_to_bv 8 10; Z_to_bv 8 7; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 27; Z_to_bv 8 9; Z_to_bv 8 11; Z_to_bv 8 24; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 6; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 6; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 14; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 11; Z_to_bv 8 13; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 2; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 14; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 14; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 14; Z_to_bv 8 0; Z_to_bv 8 0].
Hypothesis RNG_G_102fd : gw_br G_102fd 12.
Hypothesis ROM_G_102fd : ro_bytes segs G_102fd [Z_to_bv 8 45; Z_to_bv 8 43; Z_to_bv 8 32; Z_to_bv 8 32; Z_to_bv 8 32; Z_to_bv 8 48; Z_to_bv 8 88; Z_to_bv 8 48; Z_to_bv 8 120; Z_to_bv 8 0; Z_to_bv 8 125; Z_to_bv 8 0].
Hypothesis RNG_G_10741 : gw_br G_10741 12.
Hypothesis ROM_G_10741 : ro_bytes segs G_10741 [Z_to_bv 8 40; Z_to_bv 8 110; Z_to_bv 8 117; Z_to_bv 8 108; Z_to_bv 8 108; Z_to_bv 8 41; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Hypothesis RNG_G_107e0 : gw_br G_107e0 16.
Hypothesis ROM_G_107e0 : ro_bytes segs G_107e0 [Z_to_bv 8 48; Z_to_bv 8 49; Z_to_bv 8 50; Z_to_bv 8 51; Z_to_bv 8 52; Z_to_bv 8 53; Z_to_bv 8 54; Z_to_bv 8 55; Z_to_bv 8 56; Z_to_bv 8 57; Z_to_bv 8 65; Z_to_bv 8 66; Z_to_bv 8 67; Z_to_bv 8 68; Z_to_bv 8 69; Z_to_bv 8 70].
Hypothesis LAY_G_102fd_STATIC_SPLIT : gw_le (G_102fd + 12) STATIC_SPLIT.
Hypothesis LAY_G_10741_STATIC_SPLIT : gw_le (G_10741 + 12) STATIC_SPLIT.
Hypothesis LAY_G_107e0_STATIC_SPLIT : gw_le (G_107e0 + 16) STATIC_SPLIT.
Hypothesis LAY_G_118c0_STATIC_SPLIT : gw_le (G_118c0 + 116) STATIC_SPLIT.
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
Local Definition gw_tbl_1 := (gw_ent (@QROt.Mq0.wfile segs) wfile (gw_ent (@Q8l1.Mq1.wfile segs) wfile (gw_ent (@Q91D.Mq2.wfile segs) wfile (gw_ent (@QQLG.Mq7.wfile segs) wfile gw_tbl_0)))).
Definition ssp_cells : ltac:(gw_rebind_ty (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QROt.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q8l1.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_1))).
Definition va_area : ltac:(gw_rebind_ty (@Q91D.Mq3.va_area segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q91D.Mq3.va_area segs) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@QROt.Mq0.va_area segs) va_area (gw_ent (@Q8l1.Mq1.va_area segs) va_area (gw_ent (@Q91D.Mq3.va_area segs) va_area gw_tbl_2))).
Definition strnlen_post : ltac:(gw_rebind_ty (@Q91D.Mq6.strnlen_post segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q91D.Mq6.strnlen_post segs) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@QROt.Mq0.strnlen_post segs) strnlen_post (gw_ent (@Q91D.Mq6.strnlen_post segs) strnlen_post gw_tbl_3)).
Definition pop_arg_post : ltac:(gw_rebind_ty (@Q91D.Mq3.pop_arg_post segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q91D.Mq3.pop_arg_post segs) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@QROt.Mq0.pop_arg_post segs) pop_arg_post (gw_ent (@Q91D.Mq3.pop_arg_post segs) pop_arg_post gw_tbl_4)).
Definition sink_frame_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QROt.Mq0.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@Q8l1.Mq1.sink_frame_stmt segs) sink_frame_stmt gw_tbl_5)).
#[global] Arguments sink_frame_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope.
Definition sink_flags_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QROt.Mq0.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@Q8l1.Mq1.sink_flags_stmt segs) sink_flags_stmt gw_tbl_6)).
#[global] Arguments sink_flags_stmt {St}%_type_scope Fp%_Z_scope SINK%_function_scope.
Definition out_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QROt.Mq0.out_post segs got_ssp ssp_guard) out_post (gw_ent (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) out_post gw_tbl_7)).
#[global] Arguments out_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F fc%_bv_scope S%_Z_scope bs%_list_scope lo%_Z_scope canary%_bv_scope m%_function_scope _ _ _.
Definition out_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QROt.Mq0.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt gw_tbl_8)).
#[global] Arguments out_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope.
Definition fpcall_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QROt.Mq0.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) fpcall_post gw_tbl_9)).
#[global] Arguments fpcall_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F lo%_Z_scope canary%_bv_scope m%_function_scope _%_Z_scope _ _.
Definition fpcall_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QROt.Mq0.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt gw_tbl_10)).
#[global] Arguments fpcall_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUTFP%_function_scope c.
Definition arg_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QROt.Mq0.arg_ok segs) arg_ok (gw_ent (@Q8l1.Mq1.arg_ok segs) arg_ok gw_tbl_11)).
Definition args_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QROt.Mq0.args_ok segs) args_ok (gw_ent (@Q8l1.Mq1.args_ok segs) args_ok gw_tbl_12)).
Definition POST : ltac:(gw_rebind_ty (@QROt.Mq0.POST segs got_ssp ssp_guard) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QROt.Mq0.POST segs got_ssp ssp_guard) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@QROt.Mq0.POST segs got_ssp ssp_guard) POST gw_tbl_13).
#[global] Arguments POST {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F m0%_function_scope lo%_Z_scope canary%_bv_scope AP%_Z_scope _%_Z_scope _ _.
Definition lo_cells : ltac:(gw_rebind_ty (@QROt.Mq0.lo_cells ssp_guard) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@QROt.Mq0.lo_cells ssp_guard) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@QROt.Mq0.lo_cells ssp_guard) lo_cells gw_tbl_14).
Definition finv : ltac:(gw_rebind_ty (@QROt.Mq0.finv segs got_ssp ssp_guard) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QROt.Mq0.finv segs got_ssp ssp_guard) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@QROt.Mq0.finv segs got_ssp ssp_guard) finv gw_tbl_15).
Definition lo_cells14 : ltac:(gw_rebind_ty (@QROt.Mq0.lo_cells14 ssp_guard) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QROt.Mq0.lo_cells14 ssp_guard) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@QROt.Mq0.lo_cells14 ssp_guard) lo_cells14 gw_tbl_16).
Definition S_HEAD : ltac:(gw_rebind_ty (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_17)).
Local Definition gw_tbl_18 := (gw_ent (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD gw_tbl_17).
#[global] Arguments S_HEAD {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope fuel%_nat_scope.
Definition S_CONV : ltac:(gw_rebind_ty (@QROt.Mq0.S_CONV segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_CONV segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_18)).
Local Definition gw_tbl_19 := (gw_ent (@QROt.Mq0.S_CONV segs base got_ssp GLOBALS_TOP ssp_guard) S_CONV gw_tbl_18).
#[global] Arguments S_CONV {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_CV_D : ltac:(gw_rebind_ty (@QROt.Mq0.S_CV_D segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_CV_D segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_19)).
Local Definition gw_tbl_20 := (gw_ent (@QROt.Mq0.S_CV_D segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_D gw_tbl_19).
#[global] Arguments S_CV_D {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_CV_U : ltac:(gw_rebind_ty (@QROt.Mq0.S_CV_U segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_20)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_CV_U segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_20)).
Local Definition gw_tbl_21 := (gw_ent (@QROt.Mq0.S_CV_U segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_U gw_tbl_20).
#[global] Arguments S_CV_U {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_CV_C : ltac:(gw_rebind_ty (@QROt.Mq0.S_CV_C segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_21)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_CV_C segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_21)).
Local Definition gw_tbl_22 := (gw_ent (@QROt.Mq0.S_CV_C segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_C gw_tbl_21).
#[global] Arguments S_CV_C {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_CV_X : ltac:(gw_rebind_ty (@QROt.Mq0.S_CV_X segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_22)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_CV_X segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_22)).
Local Definition gw_tbl_23 := (gw_ent (@QROt.Mq0.S_CV_X segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_X gw_tbl_22).
#[global] Arguments S_CV_X {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_CV_S : ltac:(gw_rebind_ty (@QROt.Mq0.S_CV_S segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_23)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_CV_S segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_23)).
Local Definition gw_tbl_24 := (gw_ent (@QROt.Mq0.S_CV_S segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_S gw_tbl_23).
#[global] Arguments S_CV_S {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_CV_FP : ltac:(gw_rebind_ty (@QROt.Mq0.S_CV_FP segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_24)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_CV_FP segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_24)).
Local Definition gw_tbl_25 := (gw_ent (@QROt.Mq0.S_CV_FP segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_FP gw_tbl_24).
#[global] Arguments S_CV_FP {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Hypothesis strnlen_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q91D.Mq6.gw_all) (@Q91D.Mq6.strnlen_spec) e_2596c)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_25))) in exact T).
Hypothesis va_area_bound : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q91D.Mq3.gw_all) (@Q91D.Mq3.va_area_bound) (base + 3632)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_25))) in let T := gw_fold_pcs T base (3632)%Z [0]%Z in exact T).
Hypothesis pop_arg_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q91D.Mq3.gw_all) (@Q91D.Mq3.pop_arg_spec) (base + 3632)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_25))) in let T := gw_fold_pcs T base (3632)%Z [0]%Z in exact T).

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Notation d_fl := G.T_printf.d_fl.
Notation d_w := G.T_printf.d_w.
Notation d_p := G.T_printf.d_p.
Notation d_xp := G.T_printf.d_xp.
Notation d_t := G.T_printf.d_t.
Notation d_ty := G.T_printf.d_ty.

Definition zbytes_read : ltac:(gw_ctx_fold_ty (@QROt.Mq0.zbytes_read) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.zbytes_read)).
Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
Definition jt1_read_s : ltac:(gw_ctx_fold_ty (@QROt.Mq0.jt1_read_s) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.jt1_read_s)).
Definition jt1_read_d : ltac:(gw_ctx_fold_ty (@QROt.Mq0.jt1_read_d) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.jt1_read_d)).
Definition jt1_read_u : ltac:(gw_ctx_fold_ty (@QROt.Mq0.jt1_read_u) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.jt1_read_u)).
Definition jt1_read_x : ltac:(gw_ctx_fold_ty (@QROt.Mq0.jt1_read_x) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.jt1_read_x)).
Definition jt1_read_fp : ltac:(gw_ctx_fold_ty (@QROt.Mq0.jt1_read_fp) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.jt1_read_fp)).
Definition jt1_read_c : ltac:(gw_ctx_fold_ty (@QROt.Mq0.jt1_read_c) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.jt1_read_c)).
Definition implM_eq_ms : ltac:(gw_ctx_fold_ty (@QROt.Mq0.implM_eq_ms) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.implM_eq_ms)).
#[global] Arguments implM_eq_ms {St}%_type_scope {X}%_type_scope c s Q%_function_scope ms ms' _ _.
Definition sink_store : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_store) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_store)).
#[global] Arguments sink_store {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR m%_function_scope st a%_Z_scope bs%_list_scope _ _ _ _ _.
Definition sink_call : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_call) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_call)).
#[global] Arguments sink_call {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR Wc%_list_scope m%_function_scope m'%_function_scope st _ _ _ _ _.
Definition arg_ok_W : ltac:(gw_ctx_fold_ty (@QROt.Mq0.arg_ok_W) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.arg_ok_W)).
Definition lo_split : ltac:(gw_ctx_fold_ty (@QROt.Mq0.lo_split) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.lo_split)).
Definition lo_join : ltac:(gw_ctx_fold_ty (@QROt.Mq0.lo_join) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.lo_join)).
Definition pop_arg_callq : ltac:(gw_ctx_fold_ty (@QROt.Mq0.pop_arg_callq) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.pop_arg_callq)).
Ltac zl := unfold zlength in *; cbn [length] in *; lia.
Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.
Tactic Notation "callw" tactic3(tac) :=
lazymatch goal with
| |- evt ?segs_ _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ tac | post_call segs_ m ]
end.
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.
Ltac ienter := lazymatch goal with |- Ql2m.Mq3.implM _ _ _ _ _ => unfold Ql2m.Mq3.implM; apply impl_from_evt | |- QlEo_c1.Mq0.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.

Definition F_printf_core_common__Fok_trans : ltac:(gw_ctx_fold_ty (@QROt.Mq0.Fok_trans) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.Fok_trans)).
Notation F_printf_core_common__S_CONV := S_CONV (only parsing).
Notation F_printf_core_common__S_CV_C := S_CV_C (only parsing).
Notation F_printf_core_common__S_CV_D := S_CV_D (only parsing).
Notation F_printf_core_common__S_CV_FP := S_CV_FP (only parsing).
Notation F_printf_core_common__S_CV_S := S_CV_S (only parsing).
Notation F_printf_core_common__S_CV_U := S_CV_U (only parsing).
Notation F_printf_core_common__S_CV_X := S_CV_X (only parsing).
Notation F_printf_core_common__arg_ok_W := arg_ok_W (only parsing).
Notation F_printf_core_common__finv := finv (only parsing).
Definition F_printf_core_common__fmt_rng : ltac:(gw_ctx_fold_ty (@QROt.Mq0.fmt_rng) constr:(gw_tbl_25)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.fmt_rng)).
Notation F_printf_core_common__implM_eq_ms := implM_eq_ms (only parsing).
Notation F_printf_core_common__lo_cells14 := lo_cells14 (only parsing).
Notation F_printf_core_common__lo_join := lo_join (only parsing).
Notation F_printf_core_common__lo_split := lo_split (only parsing).
Notation F_printf_core_common__pop_arg_callq := pop_arg_callq (only parsing).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).

#[using="G_102fd G_10741 G_107e0 G_11778 G_11858 G_118c0 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_194bc e_194c8 e_197bc e_fwritex e_memset e_2596c e_memchr CODE BASE4 BASER D_22 E_22 D_25 E_25 D_81 E_81 D_281 E_281 D_282 E_282 D_332 E_332 D_333 E_333 D_360 E_360 D_362 E_362 D_371 E_371 D_372 E_372 D_378 E_378 D_379 E_379 D_381 E_381 D_383 E_383 D_389 E_389 D_395 E_395 D_396 E_396 D_412 E_412 D_413 E_413 D_426 E_426 D_427 E_427 D_438 E_438 D_439 E_439 D_453 E_453 D_454 E_454 D_467 E_467 D_468 E_468 D_473 E_473 D_474 E_474 D_530 E_530 D_533 E_533 D_534 E_534 D_543 E_543 D_545 E_545 D_627 E_627 D_639 E_639 D_648 E_648 D_655 E_655 D_668 E_668 D_680 E_680 D_689 E_689 D_701 E_701 D_713 E_713 D_722 E_722 D_729 E_729 D_742 E_742 D_754 E_754 D_762 E_762 D_798 E_798 D_883 E_883 D_907 E_907 ANCH_25 ANCH_282 ANCH_333 ANCH_362 ANCH_372 ANCH_379 ANCH_396 ANCH_413 ANCH_427 ANCH_439 ANCH_454 ANCH_468 ANCH_474 ANCH_534 ANCH_545 LINK_81 LINK_381 LINK_383 LINK_389 LINK_530 LINK_627 LINK_639 LINK_648 LINK_655 LINK_668 LINK_680 LINK_689 LINK_701 LINK_713 LINK_722 LINK_729 LINK_742 LINK_754 LINK_762 LINK_798 LINK_883 LINK_907 RNG_STATIC_SPLIT LAY_lo_STATIC_SPLIT AL_STATIC_SPLIT RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP AL_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 RNG_G_102fd ROM_G_102fd RNG_G_10741 ROM_G_10741 RNG_G_107e0 ROM_G_107e0 LAY_G_102fd_STATIC_SPLIT LAY_G_10741_STATIC_SPLIT LAY_G_107e0_STATIC_SPLIT LAY_G_118c0_STATIC_SPLIT RNG_G_11778 JTL_jt_11778_o1504 ROM_jt_11778_50 JTL_jt_11778_o1432 ROM_jt_11778_35 ROM_jt_11778_40 JTL_jt_11778_o1800 ROM_jt_11778_34 JTL_jt_11778_o1744 ROM_jt_11778_52 JTL_jt_11778_o1864 ROM_jt_11778_55 ROM_jt_11778_23 JTL_jt_11778_o1352 ROM_jt_11778_36 ROM_jt_11778_37 ROM_jt_11778_38 ROM_jt_11778_4 ROM_jt_11778_5 ROM_jt_11778_6 strnlen_spec va_area_bound pop_arg_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_22 hi_281 hi_332 hi_360 hi_371 hi_378 hi_395 hi_412 hi_426 hi_438 hi_453 hi_467 hi_473 hi_533 hi_543 lo_25 lo_282 lo_333 lo_362 lo_372 lo_379 lo_396 lo_413 lo_427 lo_439 lo_454 lo_468 lo_474 lo_534 lo_545 joff_81 joff_381 joff_383 joff_389 joff_530 joff_627 joff_639 joff_648 joff_655 joff_668 joff_680 joff_689 joff_701 joff_713 joff_722 joff_729 joff_742 joff_754 joff_762 joff_798 joff_883 joff_907 G_102fd G_10741 G_107e0 G_11778 G_11858 G_118c0 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_194bc e_194c8 e_197bc e_fwritex e_memset e_2596c e_memchr CODE BASE4 BASER D_22 E_22 D_25 E_25 D_81 E_81 D_281 E_281 D_282 E_282 D_332 E_332 D_333 E_333 D_360 E_360 D_362 E_362 D_371 E_371 D_372 E_372 D_378 E_378 D_379 E_379 D_381 E_381 D_383 E_383 D_389 E_389 D_395 E_395 D_396 E_396 D_412 E_412 D_413 E_413 D_426 E_426 D_427 E_427 D_438 E_438 D_439 E_439 D_453 E_453 D_454 E_454 D_467 E_467 D_468 E_468 D_473 E_473 D_474 E_474 D_530 E_530 D_533 E_533 D_534 E_534 D_543 E_543 D_545 E_545 D_627 E_627 D_639 E_639 D_648 E_648 D_655 E_655 D_668 E_668 D_680 E_680 D_689 E_689 D_701 E_701 D_713 E_713 D_722 E_722 D_729 E_729 D_742 E_742 D_754 E_754 D_762 E_762 D_798 E_798 D_883 E_883 D_907 E_907 ANCH_25 ANCH_282 ANCH_333 ANCH_362 ANCH_372 ANCH_379 ANCH_396 ANCH_413 ANCH_427 ANCH_439 ANCH_454 ANCH_468 ANCH_474 ANCH_534 ANCH_545 LINK_81 LINK_381 LINK_383 LINK_389 LINK_530 LINK_627 LINK_639 LINK_648 LINK_655 LINK_668 LINK_680 LINK_689 LINK_701 LINK_713 LINK_722 LINK_729 LINK_742 LINK_754 LINK_762 LINK_798 LINK_883 LINK_907 RNG_STATIC_SPLIT LAY_lo_STATIC_SPLIT AL_STATIC_SPLIT RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP AL_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 RNG_G_102fd ROM_G_102fd RNG_G_10741 ROM_G_10741 RNG_G_107e0 ROM_G_107e0 LAY_G_102fd_STATIC_SPLIT LAY_G_10741_STATIC_SPLIT LAY_G_107e0_STATIC_SPLIT LAY_G_118c0_STATIC_SPLIT RNG_G_11778 JTL_jt_11778_o1504 ROM_jt_11778_50 JTL_jt_11778_o1432 ROM_jt_11778_35 ROM_jt_11778_40 JTL_jt_11778_o1800 ROM_jt_11778_34 JTL_jt_11778_o1744 ROM_jt_11778_52 JTL_jt_11778_o1864 ROM_jt_11778_55 ROM_jt_11778_23 JTL_jt_11778_o1352 ROM_jt_11778_36 ROM_jt_11778_37 ROM_jt_11778_38 ROM_jt_11778_4 ROM_jt_11778_5 ROM_jt_11778_6 strnlen_spec va_area_bound pop_arg_spec.

#[using="RNG_G_11778"] Lemma gw_jt_rd_G_11778 : forall m k jt, mem_inv segs m -> (0 <= k /\ k + 4 <= 224)%Z -> ro_bytes segs (G_11778 + k) (le4 (Z_to_bv 64 jt)) ->
ov_read_bytes segs m (Z_to_bv 64 (k + G_11778)) 4 = Some (le4 (Z_to_bv 64 jt)).
Proof. clear - RNG_G_11778 segs G_11778. intros m k jt MI Hk ROM. pose proof RNG_G_11778 as R; unfold gw_br in R.
assert (RN : gw_br (G_11778 + k) 4) by (unfold gw_br; lia).
pose proof (ro_bytes_read segs m (G_11778 + k) 4 _ 0 4 MI ROM RN eq_refl) as RD.
rewrite Z.add_0_r in RD. replace (k + G_11778)%Z with (G_11778 + k)%Z by lia. exact RD. Qed.

Ltac gw_jt_all rd := repeat match goal with ROM : ro_bytes ?s (?A + ?k)%Z (le4 (Z_to_bv 64 ?jt)), MI : mem_inv ?s ?mc |- evt ?s _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with _ : ov_read_bytes s mc (Z_to_bv 64 (k + A)) 4 = _ |- _ => fail | _ => pose proof (rd mc k jt MI ltac:(lia) ROM) end end.
Ltac gw_jt_clear := repeat match goal with H : ov_read_bytes _ _ (Z_to_bv 64 (_ + _)) 4 = Some (le4 (Z_to_bv 64 _)) |- _ => clear H end.

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

Local Notation W := (QROt.Mq0.W Fp B BS q lo AP).
Local Notation Fok := (QROt.Mq0.Fok F).

Local Notation Fok_trans := (F_printf_core_common__Fok_trans F).

Local Notation hi_cells := (QROt.Mq0.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).

Local Notation finv := (F_printf_core_common__finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (F_printf_core_common__fmt_rng fmt HF).
Local Notation implM_eq_ms := (F_printf_core_common__implM_eq_ms (St:=St)).
Local Notation sink_store := (F_printf_core_common__sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common__sink_call (St:=St) Fp B BS SINK SFR).
Local Notation arg_ok_W := (F_printf_core_common__arg_ok_W Fp B BS q lo fmt AP slots).

Local Notation lo_cells14 := (F_printf_core_common__lo_cells14 AP nla nlt).
Local Notation lo_split := (F_printf_core_common__lo_split q AP nla nlt).
Local Notation lo_join := (F_printf_core_common__lo_join q AP nla nlt).
Local Notation pop_arg_callq := (F_printf_core_common__pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).

Local Notation S_CONV := (F_printf_core_common__S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Local Notation tregs := (QROt.Mq0.tregs Fp q gp tp A).

Local Notation S_CV_D := (F_printf_core_common__S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_U := (F_printf_core_common__S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Local Notation S_CV_X := (F_printf_core_common__S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_S := (F_printf_core_common__S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_FP := (F_printf_core_common__S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_C := (F_printf_core_common__S_CV_C (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Ltac hush := idtac.

Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).

Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
destruct H as (MI & MU & WM & FRhi & ST & BY & VAA & SSP1 & SSP2); unfold W in MU; unfold hi_cells in FRhi;
gw_expose got_ssp; gw_expose ssp_guard; unfold va_area in VAA;
gw_expose GLOBALS_TOP; unfold PC_DEPTH in LO, GLO;
try (let LT := fresh "LZB" in pose proof (zb_length fmt) as LT;
lazymatch goal with _ : length (zb fmt) = length fmt, _ : length (zb fmt) = length fmt |- _ => clear LT | _ => idtac end);
try (let LT := fresh "LU" in pose proof (u64s_length slots) as LT;
lazymatch goal with _ : length (u64s slots) = _, _ : length (u64s slots) = _ |- _ => clear LT | _ => idtac end);
unfold zlength in *; hush.
Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.
Ltac mk_finv := gw_expose got_ssp; gw_expose ssp_guard; unfold finv, W, hi_cells, va_area;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | hyp_cells] |]; split; [hyp|]; split; [hyp|]; split; hyp.
Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
Ltac zsto p := repeat (tryif at_pc p then fail else
lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).
Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
Ltac rd_fmt idx :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
let RD := fresh "RD" in let RG := fresh "RG" in
pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;

repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
end end.
Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal | (progress (rewrite ?Z.shiftl_0_l, ?Z.shiftr_0_l); lia) ].

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

Hypothesis HS_CV_D : S_CV_D.
Hypothesis HS_CV_U : S_CV_U.
Hypothesis HS_CV_X : S_CV_X.
Hypothesis HS_CV_S : S_CV_S.
Hypothesis HS_CV_FP : S_CV_FP.
Hypothesis HS_CV_C : S_CV_C.

#[using="Type"] Lemma slot_long : forall (slot : word) i, (bv_unsigned slot = i mod 2^64)%Z -> slot = Z_to_bv 64 (i mod 2^64).
Proof. clear - St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0 HS_CV_D HS_CV_U HS_CV_X HS_CV_S HS_CV_FP HS_CV_C. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac]; first [clear HS_CV_D | gw_hide HS_CV_D | idtac]; first [clear HS_CV_U | gw_hide HS_CV_U | idtac]; first [clear HS_CV_X | gw_hide HS_CV_X | idtac]; first [clear HS_CV_S | gw_hide HS_CV_S | idtac]; first [clear HS_CV_FP | gw_hide HS_CV_FP | idtac]; first [clear HS_CV_C | gw_hide HS_CV_C | idtac]. intros slot i E. rewrite <- E. symmetry. apply Z_to_bv_bv_unsigned. Qed.
#[using="Type"] Lemma slot_ulong : forall (slot : word) u, (bv_unsigned slot = u)%Z -> slot = Z_to_bv 64 u.
Proof. clear - St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0 HS_CV_D HS_CV_U HS_CV_X HS_CV_S HS_CV_FP HS_CV_C. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac]; first [clear HS_CV_D | gw_hide HS_CV_D | idtac]; first [clear HS_CV_U | gw_hide HS_CV_U | idtac]; first [clear HS_CV_X | gw_hide HS_CV_X | idtac]; first [clear HS_CV_S | gw_hide HS_CV_S | idtac]; first [clear HS_CV_FP | gw_hide HS_CV_FP | idtac]; first [clear HS_CV_C | gw_hide HS_CV_C | idtac]. intros slot u E. rewrite <- E. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Ltac fold_b2z :=
repeat match goal with |- context [Z.b2z ?b] =>
let v := eval vm_compute in (Z.b2z b) in
lazymatch v with 0%Z => change (Z.b2z b) with 0%Z | 1%Z => change (Z.b2z b) with 1%Z end end;
repeat match goal with |- context [Z.land ?a ?b] =>
lazymatch a with 0%Z => idtac | 1%Z => idtac end; lazymatch b with 0%Z => idtac | 1%Z => idtac end;
let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v end.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_332 lo_333 G_11778 STATIC_SPLIT jt_11778_o1504 jt_11778_o1432 jt_11778_o1800 jt_11778_o1744 jt_11778_o1864 jt_11778_o1352 CODE BASE4 BASER D_332 E_332 D_333 E_333 ANCH_333 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_11778 JTL_jt_11778_o1504 ROM_jt_11778_50 JTL_jt_11778_o1432 ROM_jt_11778_35 ROM_jt_11778_40 JTL_jt_11778_o1800 ROM_jt_11778_34 JTL_jt_11778_o1744 ROM_jt_11778_52 JTL_jt_11778_o1864 ROM_jt_11778_55 ROM_jt_11778_23 JTL_jt_11778_o1352 ROM_jt_11778_36 ROM_jt_11778_37 ROM_jt_11778_38 ROM_jt_11778_4 ROM_jt_11778_5 ROM_jt_11778_6 va_area_bound pop_arg_spec BS0 GLO HA HAP HF HS_CV_D HS_CV_FP HS_CV_S HS_CV_U HS_CV_X HS_CV_C HVA LO QHI SEP_B SEP_F SFL SFR VAHI"] Lemma L_CONV : S_CONV.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_332 lo_333 G_11778 STATIC_SPLIT jt_11778_o1504 jt_11778_o1432 jt_11778_o1800 jt_11778_o1744 jt_11778_o1864 jt_11778_o1352 CODE BASE4 BASER D_332 E_332 D_333 E_333 ANCH_333 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_11778 JTL_jt_11778_o1504 ROM_jt_11778_50 JTL_jt_11778_o1432 ROM_jt_11778_35 ROM_jt_11778_40 JTL_jt_11778_o1800 ROM_jt_11778_34 JTL_jt_11778_o1744 ROM_jt_11778_52 JTL_jt_11778_o1864 ROM_jt_11778_55 ROM_jt_11778_23 JTL_jt_11778_o1352 ROM_jt_11778_36 ROM_jt_11778_37 ROM_jt_11778_38 ROM_jt_11778_4 ROM_jt_11778_5 ROM_jt_11778_6 va_area_bound pop_arg_spec BS0 GLO HA HAP HF HS_CV_D HS_CV_FP HS_CV_S HS_CV_U HS_CV_X HS_CV_C HVA LO QHI SEP_B SEP_F SFL SFR VAHI St Fp B BS SINK TOPOK OUT OUTFP TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt TQ FRM0 A0.
intros fuel HH x1 x6 x7 x12 x13 x14 x23 x26 x28 x29 x30 x31 Ft fc m st i4 k c d a args pfx s2s za pl plp alo ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC1 FPC FRM FOK Hi4 Ht CT Hfl Hw Hp XP Hc.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.

cbn [args_ok] in AOK. destruct (skipn (Z.to_nat k) slots) as [|slot slots'] eqn:ESK; [destruct AOK|]. destruct AOK as [AOK1 AOK].
assert (NTH : nth_error slots (Z.to_nat k) = Some slot).
{ rewrite <- (Nat.add_0_r (Z.to_nat k)), <- nth_error_skipn, ESK. reflexivity. }
assert (ESK' : skipn (Z.to_nat (k + 1)) slots = slots').
{ replace (Z.to_nat (k + 1)) with (1 + Z.to_nat k)%nat by lia. rewrite <- skipn_skipn, ESK. reflexivity. }
rewrite <- ESK' in AOK.
destruct (lo_split _ _ _ _ _ _ _ _ _ _ LOW) as (LOW14 & ARGC & J128). gw_expose ssp_guard; unfold lo_cells14 in LOW14. clear LOW.
pose proof (land_bound' (d_fl d) 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB. rewrite (nzmask_eq (d_fl d)) in FLB by lia.
unfold conv. cbv zeta. unfold LEFT_ADJ, ZERO_PAD.
destruct CT as [[CT PS] | [CTL PS]]; rewrite PS.
{
pose proof (conv_type_cases _ _ CT) as CASES. pose proof (conv_type_range _ _ CT) as TR. pose proof (conv_type_ty _ _ CT) as TYS.

destruct a as [sv | iv | uv | dd | liv | luv];
[ destruct (Z.eqb_spec (d_ty d) T_PTR) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
| destruct (Z.eqb_spec (d_ty d) T_INT) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
| destruct (Z.eqb_spec (d_ty d) T_UINT) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
| destruct (Z.eqb_spec (d_ty d) T_DBL) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
| destruct (Z.eqb_spec (d_ty d) T_LONG) as [ETY|NTY]; [exfalso; unfold T_PTR, T_INT, T_UINT, T_DBL, T_LONG in TYS, ETY; lia | cbn [negb]; apply implM_unr_l]
| destruct (Z.eqb_spec (d_ty d) T_ULONG) as [ETY|NTY]; [exfalso; unfold T_PTR, T_INT, T_UINT, T_DBL, T_ULONG in TYS, ETY; lia | cbn [negb orb]; apply implM_unr_l] ].

1: assert (T115 : d_t d = 115%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL in CASES, ETY; lia).
2: destruct (Z.eqb_spec (d_t d) 99) as [T99 | N99].
3: assert (TDI : (d_t d = 100 \/ d_t d = 105)%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL in CASES, ETY; lia).
4: assert (TUX : (d_t d = 117 \/ (d_t d = 120 \/ d_t d = 88))%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL in CASES, ETY; lia).
5: assert (TFP : conv_type (d_t d) = Some T_DBL) by (rewrite <- ETY; exact CT).
5: pose proof (proj1 (conv_type_dbl _ TFP)) as TFR.
4: destruct TUX as [T117 | TX];
[ rewrite (proj2 (Z.eqb_eq _ _) T117) | replace (d_t d =? 117)%Z with false by (symmetry; apply Z.eqb_neq; lia) ].

all: assert (HFpR__ : (0 <= Fp < 2 ^ 64)%Z) by (first [ clear - N99 LU LZB VAHI HAP SEP_F GLO LO w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_332 lo_333 G_11778 STATIC_SPLIT jt_11778_o1504 jt_11778_o1432 jt_11778_o1800 jt_11778_o1744 jt_11778_o1864 jt_11778_o1352 CODE BASE4 BASER D_332 E_332 D_333 E_333 ANCH_333 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_11778 JTL_jt_11778_o1504 ROM_jt_11778_50 JTL_jt_11778_o1432 ROM_jt_11778_35 ROM_jt_11778_40 JTL_jt_11778_o1800 ROM_jt_11778_34 JTL_jt_11778_o1744 ROM_jt_11778_52 JTL_jt_11778_o1864 ROM_jt_11778_55 ROM_jt_11778_23 JTL_jt_11778_o1352 ROM_jt_11778_36 ROM_jt_11778_37 ROM_jt_11778_38 ROM_jt_11778_4 ROM_jt_11778_5 ROM_jt_11778_6 va_area_bound pop_arg_spec; lia | lia ]).
all: ienter; zs; (brf K; [ exfalso; lia | ]); zs; zs; zs; zs.
all: callx (eapply pop_arg_callq; [lia | exact APC | exact VAA | exact NTH | lia | exact ARGC | exact ST | exact MI | rewrite ETY; unfold T_PTR, T_INT, T_UINT, T_DBL, T_LONG, T_ULONG; lia]).
all: match goal with H : rw_cells _ _ (q + -544 + 112)%Z _ |- _ => rename H into ARGC'; rewrite ETY in ARGC'; cbn [pop_arg_lo pop_arg_hi Q91D.Mq3.T_PTR Q91D.Mq3.T_INT Q91D.Mq3.T_UINT Q91D.Mq3.T_DBL Q91D.Mq3.T_LONG Q91D.Mq3.T_ULONG T_PTR T_INT T_UINT T_DBL T_LONG T_ULONG Z.eqb Pos.eqb orb] in ARGC' end.
all: match goal with H : Fokd ?F1 ?F2, G : Fok ?F1 |- _ => pose proof (Fok_trans _ _ G H) as FOK2 end.
all: zs.
all: match goal with H : SINK ?mm _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (SFL _ _ H) as (fb & FLC & FB) end; zs; zs; zs; (brf K1; [ exfalso; lia | ]); clear FLC.
all: rd_fmt (i4 - 1)%Z; zs; fix_u8 (i4 - 1)%Z; rewrite Ht.
all: zsto (base + 0x504)%Z; change (Z.b2z (0 <? 0)) with 0%Z; rewrite Z.land_0_l; zs; (brf K2a; [ | exfalso; lia ]); zsto (base + 0x518)%Z; rewrite (nzmask_eq (d_fl d)) by lia; zs; brf K2;
[ apply (proj1 (fl_shl50 _ Hfl)) in K2; rewrite (proj2 (Z.eqb_eq _ _) K2); rewrite ?ift
| assert (K2' : Z.land (d_fl d) 8192 <> 0%Z) by (intros E; apply (proj2 (fl_shl50 _ Hfl)) in E; lia);
rewrite (proj2 (Z.eqb_neq _ _) K2'); rewrite ?iff; zs ].
all: zsto (base + 0x528)%Z; zs; (brf K3; [ exfalso; lia | ]); zsto (base + 0x53c)%Z.
all: replace (Z.shiftl (d_t d + -65) 2 + G_11778)%Z with (G_11778 + 4 * (d_t d - 65))%Z by (rewrite Z.shiftl_mul_pow2; lia).
all: first [ the_mi ltac:(fun M => pose proof (jt1_read_s _ _ M T115) as RD1)
| the_mi ltac:(fun M => pose proof (jt1_read_c _ _ M T99) as RD1)
| the_mi ltac:(fun M => pose proof (jt1_read_d _ _ M TDI) as RD1)
| the_mi ltac:(fun M => pose proof (jt1_read_u _ _ M T117) as RD1)
| the_mi ltac:(fun M => pose proof (jt1_read_x _ _ M TX) as RD1)
| the_mi ltac:(fun M => pose proof (jt1_read_fp _ _ M TFP) as RD1) ].
all: zs; zs; zs.

all: let s8v := getreg 24%Z in lazymatch s8v with Z_to_bv 64 ?f => set (fl' := f) in |- * end.
all: assert (Hfl' : (0 <= fl' < 131072)%Z) by (subst fl'; lia).
all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mm _) =>
lazymatch pc with
| (base + 0x5e0)%Z =>
rewrite <- (Z_to_bv_bv_unsigned slot) in ARGC';
pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
match goal with MUc : munch _ m0 mm |- _ =>
destruct (arg_ok_W _ _ _ _ AOK1 MUc) as (slack & STR & SRNG & SPAD & P0 & SD1 & SD2 & SD3 & SD4) end;
stmt (HS_CV_S fuel HH) as NX;
jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (fl10 := Z.land (d_fl d) (Z.lnot 65536))
(xp := d_xp d) (P := bv_unsigned slot) (s := sv) (slack := slack));
[ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
| zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact STR | exact SRNG | exact SPAD | exact P0 | exact SD1 | exact SD2 | exact SD3
| subst fl'; rewrite ?land_land_same; reflexivity ]
| (base + 0x708)%Z =>
destruct AOK1 as [Hiv Emod];
rewrite (sx32_int slot iv Hiv Emod) in ARGC';
pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
stmt (HS_CV_C fuel HH) as NX;
jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (flc := Z.land (d_fl d) (Z.lnot 65536)) (w := d_w d) (p := d_p d) (xp := d_xp d) (i := iv));
[ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
| zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP
| subst fl'; unfold ZERO_PAD; rewrite ?land_land_same; reflexivity ]
| (base + 0x598)%Z =>
destruct AOK1 as [Hiv Emod];
rewrite (sx32_int slot iv Hiv Emod) in ARGC';
pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
stmt (HS_CV_D fuel HH) as NX;
jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (i := iv));
[ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
| zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ]
| (base + 0x6d0)%Z =>
destruct AOK1 as [Huv Emod];
rewrite (zx32_uint slot uv Emod) in ARGC';
pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
stmt (HS_CV_U fuel HH) as NX;
jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := uv));
[ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
| zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ]
| (base + 0x748)%Z =>
destruct AOK1 as [Huv Emod];
rewrite (zx32_uint slot uv Emod) in ARGC';
pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
stmt (HS_CV_X fuel HH) as NX;
jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := uv) (t := d_t d));
[ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
| zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Huv | exact TX ]
| (base + 0x548)%Z =>
cbn [arg_ok] in AOK1; rewrite AOK1 in ARGC';
pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
unfold LEFT_ADJ, ZERO_PAD in FPC1;
first [ rewrite (proj2 (Z.eqb_eq _ _) K2) in FPC1 | rewrite (proj2 (Z.eqb_neq _ _) K2') in FPC1 ]; rewrite ?ift, ?iff in FPC1;
stmt (HS_CV_FP fuel HH) as NX;
jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (y := f128_of_d dd) (t := d_t d));
[ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | subst fl'; exact FPC1 | exact FPC | exact FRM | exact FOK2
| zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | apply f128_of_d_range | exact TFP ]
end end. }
{
pose proof (conv_type_l_ty _ _ CTL) as CASESL.
assert (TR : (100 <= d_t d <= 117)%Z) by lia.
destruct a as [sv | iv | uv | dd | liv | luv];
[ destruct (Z.eqb_spec (d_ty d) T_PTR) as [ETY|NTY]; [exfalso; unfold T_PTR, T_LONG, T_ULONG in CASESL, ETY; lia | cbn [negb]; apply implM_unr_l]
| destruct (Z.eqb_spec (d_ty d) T_INT) as [ETY|NTY]; [exfalso; unfold T_INT, T_LONG, T_ULONG in CASESL, ETY; lia | cbn [negb]; apply implM_unr_l]
| destruct (Z.eqb_spec (d_ty d) T_UINT) as [ETY|NTY]; [exfalso; unfold T_UINT, T_LONG, T_ULONG in CASESL, ETY; lia | cbn [negb]; apply implM_unr_l]
| destruct (Z.eqb_spec (d_ty d) T_DBL) as [ETY|NTY]; [exfalso; unfold T_DBL, T_LONG, T_ULONG in CASESL, ETY; lia | cbn [negb]; apply implM_unr_l]
| destruct (Z.eqb_spec (d_ty d) T_LONG) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
| destruct (Z.eqb_spec (d_ty d) T_ULONG) as [ETY|NTY]; [cbn [negb orb] | cbn [negb orb]; apply implM_unr_l] ].
1: assert (TDI : (d_t d = 100 \/ d_t d = 105)%Z) by (unfold T_LONG, T_ULONG in CASESL, ETY; lia).
2: assert (T117 : d_t d = 117%Z) by (unfold T_LONG, T_ULONG in CASESL, ETY; lia).
2: rewrite (proj2 (Z.eqb_eq _ _) T117); cbn [negb].

1: destruct TDI as [TD | TD]. 3: pose proof T117 as TD.
all: rewrite TD in Ht.
all: ienter; zs; (brf K; [ exfalso; lia | ]); zs; zs; zs; zs.
all: callx (eapply pop_arg_callq; [lia | exact APC | exact VAA | exact NTH | lia | exact ARGC | exact ST | exact MI | rewrite ETY; unfold T_PTR, T_INT, T_UINT, T_DBL, T_LONG, T_ULONG; lia]).
all: match goal with H : rw_cells _ _ (q + -544 + 112)%Z _ |- _ => rename H into ARGC'; rewrite ETY in ARGC'; cbn [pop_arg_lo pop_arg_hi Q91D.Mq3.T_PTR Q91D.Mq3.T_INT Q91D.Mq3.T_UINT Q91D.Mq3.T_DBL Q91D.Mq3.T_LONG Q91D.Mq3.T_ULONG T_PTR T_INT T_UINT T_DBL T_LONG T_ULONG Z.eqb Pos.eqb orb] in ARGC' end.
all: match goal with H : Fokd ?F1 ?F2, G : Fok ?F1 |- _ => pose proof (Fok_trans _ _ G H) as FOK2 end.
all: zs.
all: match goal with H : SINK ?mm _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (SFL _ _ H) as (fb & FLC & FB) end; zs; zs; zs; (brf K1; [ exfalso; lia | ]); clear FLC.
all: rd_fmt (i4 - 1)%Z; zs; fix_u8 (i4 - 1)%Z; rewrite Ht.
all: zsto (base + 0x504)%Z; fold_b2z; try zs; try ((brf K2a; [ | exfalso; lia ])); zsto (base + 0x518)%Z; rewrite (nzmask_eq (d_fl d)) by lia; zs; brf K2;
[ apply (proj1 (fl_shl50 _ Hfl)) in K2; rewrite (proj2 (Z.eqb_eq _ _) K2); rewrite ?ift
| assert (K2' : Z.land (d_fl d) 8192 <> 0%Z) by (intros E; apply (proj2 (fl_shl50 _ Hfl)) in E; lia);
rewrite (proj2 (Z.eqb_neq _ _) K2'); rewrite ?iff; zs ].
all: zsto (base + 0x528)%Z; zs; try ((brf K3; [ exfalso; lia | ])); zsto (base + 0x53c)%Z.
all: gw_jt_all gw_jt_rd_G_11778; zs; gw_jt_clear; zs; zs.
all: let s8v := getreg 24%Z in lazymatch s8v with Z_to_bv 64 ?f => set (fl' := f) in |- * end.
all: assert (Hfl' : (0 <= fl' < 131072)%Z) by (subst fl'; lia).
all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mm _) =>
lazymatch pc with
| (base + 0x598)%Z =>
destruct AOK1 as [Hiv Emod];
rewrite (slot_long slot liv Emod) in ARGC';
pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
stmt (HS_CV_D fuel HH) as NX;
jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (i := liv));
[ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
| zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ]
| (base + 0x6d0)%Z =>
destruct AOK1 as [Huv Emod];
rewrite (slot_ulong slot luv Emod) in ARGC';
pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
stmt (HS_CV_U fuel HH) as NX;
jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := luv));
[ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
| zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ]
end end.
}
Qed.
End PrintfCore.

End G.
