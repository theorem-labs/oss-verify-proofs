(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq4.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyjG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyjG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXxF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXxF.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTyG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTyG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXxF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXxF.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTyG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTyG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QM7w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QM7w. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNAo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNAo.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNAo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNAo. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHEA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHEA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3o5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3o5.
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8QT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8QT.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDXD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDXD.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy8Z.Mqa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQRC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQRC.Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkTt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkTt.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy8Z.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQRC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQRC.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QROt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QROt.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZxv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZxv.Mqo.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZxv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZxv.Mqm.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5m9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5m9.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5m9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5m9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5m9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5m9.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5m9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5m9.Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5m9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5m9.Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZxv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZxv.Mqn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzQg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzQg.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qe1A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qe1A.Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSsB.Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2TC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2TC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDkC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDkC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDkC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDkC.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qe1A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qe1A.Mqa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QULt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= Q6q3.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= Q6q3.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenX StepGenX2 GwCallee GwApply GwFold.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G Require Import GwFamMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rsysret_entry ralloc_slot_entry rvm_wait_entry : Z).
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
Hypothesis AL_rsysret_entry : gw_al rsysret_entry 4.
Hypothesis AL_ralloc_slot_entry : gw_al ralloc_slot_entry 4.
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rmmap_anon_post : ltac:(gw_rebind_ty (@Q8QT.Mq2.rmmap_anon_post segs RC__) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q8QT.Mq2.rmmap_anon_post segs RC__) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@Qe1A.Mqa.rmmap_anon_post segs RC__) (@rmmap_anon_post) (gw_ent (@Q8QT.Mq2.rmmap_anon_post segs RC__) (@rmmap_anon_post) gw_tbl_0)).
Definition rauxv_ok : ltac:(gw_rebind_ty (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QQRC.Mq8.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@Q8l1.Mq8.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QROt.Mq5.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QDkC.Mq0.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QDkC.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@Q2TC.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QSsB.Mq7.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@Qe1A.Mq6.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QzQg.Mq3.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QQRC.Mq4.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@Qy8Z.Mq1.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QDXD.Mq1.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QCa8.Mq5.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@Qe1A.Mqa.rauxv_ok segs RATP RC__) (@rauxv_ok) gw_tbl_1)))))))))))))).
Definition ralloc_fp : ltac:(gw_rebind_ty (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QQRC.Mq8.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@Q8l1.Mq8.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QROt.Mq5.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QDkC.Mq0.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QDkC.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@Q2TC.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QSsB.Mq7.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@Qe1A.Mq6.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QzQg.Mq3.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QQRC.Mq4.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@Qy8Z.Mq1.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QkTt.Mq5.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QCa8.Mq5.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@Qe1A.Mqa.ralloc_fp RATP) (@ralloc_fp) gw_tbl_2)))))))))))))).
Definition rmalloc_fp : ltac:(gw_rebind_ty (@QkTt.Mq5.rmalloc_fp RATP RC__) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@QkTt.Mq5.rmalloc_fp RATP RC__) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QQRC.Mq8.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@Q8l1.Mq8.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QROt.Mq5.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QDkC.Mq0.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QDkC.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@Q2TC.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QSsB.Mq7.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@Qe1A.Mq6.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QzQg.Mq3.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QQRC.Mq4.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@Qy8Z.Mq1.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QkTt.Mq5.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@Qe1A.Mqa.rmalloc_fp RATP RC__) (@rmalloc_fp) gw_tbl_3))))))))))))).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QzQg.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq9.rpres_except segs) (@rpres_except) (gw_ent (@QQRC.Mq9.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq7.rpres_except segs) (@rpres_except) (gw_ent (@QQRC.Mq8.rpres_except segs) (@rpres_except) (gw_ent (@Q8l1.Mq8.rpres_except segs) (@rpres_except) (gw_ent (@QROt.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QDkC.Mq0.rpres_except segs) (@rpres_except) (gw_ent (@QDkC.rpres_except segs) (@rpres_except) (gw_ent (@Q2TC.rpres_except segs) (@rpres_except) (gw_ent (@QSsB.Mq7.rpres_except segs) (@rpres_except) (gw_ent (@Qe1A.Mq6.rpres_except segs) (@rpres_except) (gw_ent (@QzQg.Mq3.rpres_except segs) (@rpres_except) (gw_ent (@QQRC.Mq4.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq3.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@Qe1A.Mqa.rpres_except segs) (@rpres_except) gw_tbl_4))))))))))))))))))))).
Definition rimplT : ltac:(gw_rebind_ty (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_5)).
#[global] Arguments rimplT {R}%_type_scope o t s Q%_function_scope ms.
Notation gw_tbl_6 := (gw_ent (@QzQg.rimplT segs RC__) (@rimplT) (gw_ent (@Qy8Z.Mq7.rimplT segs RC__) (@rimplT) (gw_ent (@QQRC.Mq8.rimplT segs RC__) (@rimplT) (gw_ent (@Q8l1.Mq8.rimplT segs RC__) (@rimplT) (gw_ent (@QROt.Mq5.rimplT segs RC__) (@rimplT) (gw_ent (@QDkC.Mq0.rimplT segs RC__) (@rimplT) (gw_ent (@QDkC.rimplT segs RC__) (@rimplT) (gw_ent (@Q2TC.rimplT segs RC__) (@rimplT) (gw_ent (@QSsB.Mq7.rimplT segs RC__) (@rimplT) (gw_ent (@Qe1A.Mq6.rimplT segs RC__) (@rimplT) (gw_ent (@QQRC.Mq4.rimplT segs RC__) (@rimplT) (gw_ent (@Qy8Z.Mq1.rimplT segs RC__) (@rimplT) (gw_ent (@QkTt.Mq3.rimplT segs RC__) (@rimplT) (gw_ent (@QCa8.Mq5.rimplT segs RC__) (@rimplT) (gw_ent (@Qe1A.Mqa.rimplT segs RC__) (@rimplT) gw_tbl_5))))))))))))))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@Q5m9.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@Q5m9.Mq8.rarea_rep segs) (@rarea_rep) (gw_ent (@QzQg.rarea_rep segs) (@rarea_rep) (gw_ent (@Q5m9.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq7.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq8.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8l1.Mq8.rarea_rep segs) (@rarea_rep) (gw_ent (@QROt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq7.rarea_rep segs) (@rarea_rep) (gw_ent (@QDkC.Mq0.rarea_rep segs) (@rarea_rep) (gw_ent (@QDkC.rarea_rep segs) (@rarea_rep) (gw_ent (@Q2TC.rarea_rep segs) (@rarea_rep) (gw_ent (@QSsB.Mq7.rarea_rep segs) (@rarea_rep) (gw_ent (@Qe1A.Mq6.rarea_rep segs) (@rarea_rep) (gw_ent (@QzQg.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QZxv.Mqn.rarea_rep segs) (@rarea_rep) (gw_ent (@Q5m9.Mq7.rarea_rep segs) (@rarea_rep) (gw_ent (@Q5m9.Mq6.rarea_rep segs) (@rarea_rep) (gw_ent (@Q5m9.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q5m9.rarea_rep segs) (@rarea_rep) (gw_ent (@Q5m9.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QZxv.Mqm.rarea_rep segs) (@rarea_rep) (gw_ent (@QZxv.Mqo.rarea_rep segs) (@rarea_rep) (gw_ent (@QROt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mqc.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qe1A.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_6))))))))))))))))))))))))))))))))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@Q5m9.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q5m9.Mq8.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QzQg.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q5m9.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq7.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq8.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8l1.Mq8.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QROt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq7.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDkC.Mq0.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDkC.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q2TC.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QSsB.Mq7.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qe1A.Mq6.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QzQg.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QZxv.Mqn.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q5m9.Mq7.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q5m9.Mq6.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q5m9.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q5m9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q5m9.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QZxv.Mqm.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QZxv.Mqo.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QROt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mqc.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qe1A.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_7))))))))))))))))))))))))))))))))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@Q5m9.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q5m9.Mq8.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QzQg.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q5m9.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq7.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq8.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8l1.Mq8.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QROt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq7.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDkC.Mq0.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDkC.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q2TC.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QSsB.Mq7.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qe1A.Mq6.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QzQg.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QZxv.Mqn.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q5m9.Mq7.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q5m9.Mq6.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q5m9.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q5m9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q5m9.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QZxv.Mqm.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QZxv.Mqo.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QROt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mqc.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qe1A.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_8))))))))))))))))))))))))))))))))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@Q5m9.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q5m9.Mq8.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QzQg.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q5m9.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq7.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq8.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8l1.Mq8.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QROt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq7.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDkC.Mq0.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDkC.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q2TC.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QSsB.Mq7.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qe1A.Mq6.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QzQg.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QZxv.Mqn.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q5m9.Mq7.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q5m9.Mq6.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q5m9.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q5m9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q5m9.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QZxv.Mqm.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QZxv.Mqo.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QROt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mqc.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qe1A.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_9))))))))))))))))))))))))))))))))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@Q5m9.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q5m9.Mq8.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QzQg.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q5m9.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq7.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq8.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8l1.Mq8.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QROt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq7.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDkC.Mq0.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDkC.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q2TC.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QSsB.Mq7.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qe1A.Mq6.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QzQg.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QZxv.Mqn.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q5m9.Mq7.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q5m9.Mq6.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q5m9.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q5m9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q5m9.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QZxv.Mqm.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QZxv.Mqo.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QROt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mqc.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qe1A.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_10))))))))))))))))))))))))))))))))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@Q5m9.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q5m9.Mq8.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QzQg.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q5m9.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq7.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq8.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8l1.Mq8.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QROt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq7.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDkC.Mq0.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDkC.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q2TC.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QSsB.Mq7.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qe1A.Mq6.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QzQg.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QZxv.Mqn.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q5m9.Mq7.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q5m9.Mq6.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q5m9.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q5m9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q5m9.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QZxv.Mqm.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QZxv.Mqo.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QROt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mqc.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qe1A.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_11))))))))))))))))))))))))))))))))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@Q5m9.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q5m9.Mq8.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QzQg.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q5m9.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq7.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq8.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8l1.Mq8.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QROt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq7.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDkC.Mq0.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDkC.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q2TC.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QSsB.Mq7.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qe1A.Mq6.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QzQg.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QZxv.Mqn.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q5m9.Mq7.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q5m9.Mq6.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q5m9.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q5m9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q5m9.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QZxv.Mqm.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QZxv.Mqo.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QROt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mqc.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qe1A.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_12))))))))))))))))))))))))))))))))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@Q5m9.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q5m9.Mq8.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QzQg.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q5m9.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq7.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq8.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8l1.Mq8.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QROt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq7.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDkC.Mq0.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDkC.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q2TC.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QSsB.Mq7.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qe1A.Mq6.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QzQg.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QZxv.Mqn.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q5m9.Mq7.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q5m9.Mq6.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q5m9.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q5m9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q5m9.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QZxv.Mqm.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QZxv.Mqo.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QROt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mqc.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qe1A.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_13))))))))))))))))))))))))))))))))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_14)).
Notation gw_tbl_15 := (gw_ent (@Q5m9.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q5m9.Mq8.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QzQg.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q5m9.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq7.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq8.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8l1.Mq8.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QROt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq7.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDkC.Mq0.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDkC.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q2TC.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QSsB.Mq7.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qe1A.Mq6.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QzQg.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QZxv.Mqn.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q5m9.Mq7.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q5m9.Mq6.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q5m9.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q5m9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q5m9.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QZxv.Mqm.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QZxv.Mqo.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QROt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mqc.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qe1A.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_14))))))))))))))))))))))))))))))))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_15)).
Notation gw_tbl_16 := (gw_ent (@Q5m9.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q5m9.Mq8.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QzQg.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q5m9.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq7.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq8.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8l1.Mq8.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QROt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq7.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDkC.Mq0.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDkC.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q2TC.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QSsB.Mq7.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qe1A.Mq6.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QzQg.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QZxv.Mqn.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q5m9.Mq7.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q5m9.Mq6.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q5m9.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q5m9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q5m9.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QZxv.Mqm.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QZxv.Mqo.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QROt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mqc.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qe1A.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_15))))))))))))))))))))))))))))))))))))))).
Definition rtailW : ltac:(gw_rebind_ty (@Q5m9.Mq4.rtailW RATP) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@Q5m9.Mq4.rtailW RATP) constr:(gw_tbl_16)).
Notation gw_tbl_17 := (gw_ent (@Q5m9.Mq4.rtailW RATP) (@rtailW) gw_tbl_16).
Definition rseqW : ltac:(gw_rebind_ty (@Q5m9.rseqW RATP) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@Q5m9.rseqW RATP) constr:(gw_tbl_17)).
Notation gw_tbl_18 := (gw_ent (@Q5m9.rseqW RATP) (@rseqW) gw_tbl_17).
Definition rmmc_post : ltac:(gw_rebind_ty (@Q5m9.Mq5.rmmc_post segs base) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@Q5m9.Mq5.rmmc_post segs base) constr:(gw_tbl_18)).
Notation gw_tbl_19 := (gw_ent (@Q5m9.Mq5.rmmc_post segs base) (@rmmc_post) gw_tbl_18).
Definition rta_frame : ltac:(gw_rebind_ty (@QROt.Mq3.rta_frame RC__) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QROt.Mq3.rta_frame RC__) constr:(gw_tbl_19)).
Notation gw_tbl_20 := (gw_ent (@QzQg.rta_frame RC__) (@rta_frame) (gw_ent (@QDkC.rta_frame RC__) (@rta_frame) (gw_ent (@Q2TC.rta_frame RC__) (@rta_frame) (gw_ent (@QSsB.Mq7.rta_frame RC__) (@rta_frame) (gw_ent (@Qe1A.Mq6.rta_frame RC__) (@rta_frame) (gw_ent (@QZxv.Mqn.rta_frame RC__) (@rta_frame) (gw_ent (@Q5m9.Mq7.rta_frame RC__) (@rta_frame) (gw_ent (@QZxv.Mqo.rta_frame RC__) (@rta_frame) (gw_ent (@QROt.Mq3.rta_frame RC__) (@rta_frame) gw_tbl_19))))))))).
Definition rFRM : ltac:(gw_rebind_ty (@Qe1A.Mq6.rFRM RC__) constr:(gw_tbl_20)) := ltac:(gw_rebind_tm (@Qe1A.Mq6.rFRM RC__) constr:(gw_tbl_20)).
Notation gw_tbl_21 := (gw_ent (@QDkC.rFRM RC__) (@rFRM) (gw_ent (@Q2TC.rFRM RC__) (@rFRM) (gw_ent (@QSsB.Mq7.rFRM RC__) (@rFRM) (gw_ent (@Qe1A.Mq6.rFRM RC__) (@rFRM) gw_tbl_20)))).
Definition rag_ctx : ltac:(gw_rebind_ty (@QSsB.Mq7.rag_ctx segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_21)) := ltac:(gw_rebind_tm (@QSsB.Mq7.rag_ctx segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_21)).
Notation gw_tbl_22 := (gw_ent (@QSsB.Mq7.rag_ctx segs RATP RGOT_SSP ref_reserved RC__) (@rag_ctx) gw_tbl_21).
Definition rcnt_state : ltac:(gw_rebind_ty (@QSsB.Mq7.rcnt_state segs base RATP RDEBRUIJN) constr:(gw_tbl_22)) := ltac:(gw_rebind_tm (@QSsB.Mq7.rcnt_state segs base RATP RDEBRUIJN) constr:(gw_tbl_22)).
Notation gw_tbl_23 := (gw_ent (@QSsB.Mq7.rcnt_state segs base RATP RDEBRUIJN) (@rcnt_state) gw_tbl_22).
Definition rHMM_stmt : ltac:(gw_rebind_ty (@QSsB.Mq7.rHMM_stmt segs base RATP RDEBRUIJN RGOT_SSP ref_reserved RC__) constr:(gw_tbl_23)) := ltac:(gw_rebind_tm (@QSsB.Mq7.rHMM_stmt segs base RATP RDEBRUIJN RGOT_SSP ref_reserved RC__) constr:(gw_tbl_23)).
#[global] Arguments rHMM_stmt {R}%_type_scope k%_function_scope bail o s Q%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope a1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F fc%_bv_scope m st0 st lo%_Z_scope sc%_Z_scope req%_Z_scope.
Notation gw_tbl_24 := (gw_ent (@QSsB.Mq7.rHMM_stmt segs base RATP RDEBRUIJN RGOT_SSP ref_reserved RC__) (@rHMM_stmt) gw_tbl_23).
Definition rlowW : ltac:(gw_rebind_ty (@QDkC.rlowW RATP RIMG_HI RC__) constr:(gw_tbl_24)) := ltac:(gw_rebind_tm (@QDkC.rlowW RATP RIMG_HI RC__) constr:(gw_tbl_24)).
Notation gw_tbl_25 := (gw_ent (@QDkC.rlowW RATP RIMG_HI RC__) (@rlowW) gw_tbl_24).
Definition rmetaW : ltac:(gw_rebind_ty (@QDkC.rmetaW RATP) constr:(gw_tbl_25)) := ltac:(gw_rebind_tm (@QDkC.rmetaW RATP) constr:(gw_tbl_25)).
Notation gw_tbl_26 := (gw_ent (@QDkC.rmetaW RATP) (@rmetaW) gw_tbl_25).
Definition rfailW : ltac:(gw_rebind_ty (@Q5m9.Mq7.rfailW RATP) constr:(gw_tbl_26)) := ltac:(gw_rebind_tm (@Q5m9.Mq7.rfailW RATP) constr:(gw_tbl_26)).
Notation gw_tbl_27 := (gw_ent (@QDkC.rfailW RATP) (@rfailW) (gw_ent (@Q5m9.Mq7.rfailW RATP) (@rfailW) gw_tbl_26)).
Definition ras_post2 : ltac:(gw_rebind_ty (@QQRC.Mq4.ras_post2 segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_27)) := ltac:(gw_rebind_tm (@QQRC.Mq4.ras_post2 segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_27)).
Notation gw_tbl_28 := (gw_ent (@QDkC.Mq0.ras_post2 segs RATP RGOT_SSP ref_reserved RC__) (@ras_post2) (gw_ent (@QDkC.ras_post2 segs RATP RGOT_SSP ref_reserved RC__) (@ras_post2) (gw_ent (@Q2TC.ras_post2 segs RATP RGOT_SSP ref_reserved RC__) (@ras_post2) (gw_ent (@QSsB.Mq7.ras_post2 segs RATP RGOT_SSP ref_reserved RC__) (@ras_post2) (gw_ent (@Qe1A.Mq6.ras_post2 segs RATP RGOT_SSP ref_reserved RC__) (@ras_post2) (gw_ent (@QQRC.Mq4.ras_post2 segs RATP RGOT_SSP ref_reserved RC__) (@ras_post2) gw_tbl_27)))))).

Hypothesis rmmap_anon_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q8QT.Mq2.gw_all) (@Q8QT.Mq2.rmmap_anon_spec) rvm_wait_entry)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_28))) in exact T).

Hypothesis rwrapper_munch_keeps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qe1A.Mqa.gw_all) (@Qe1A.Mqa.rwrapper_munch_keeps) (base + -880)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_28))) in let T := gw_fold_pcs T base (-880)%Z [0; 116; 152; 388; 396; 472; 500; 524; 600; 612; 664; 676; 696; 708; 712; 768; 784; 804; 816; 876]%Z in exact T).
Hypothesis land_m4096 : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QCa8.Mq3.gw_all) (@QCa8.Mq3.land_m4096) (base + 2212)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_28))) in let T := gw_fold_pcs T base (2212)%Z [0; 36; 64; 124; 184; 220]%Z in exact T).
Hypothesis le4_swrap_succ : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQRC.Mq7.gw_all) (@QQRC.Mq7.le4_swrap_succ) (base + -880)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_28))) in let T := gw_fold_pcs T base (-880)%Z [0; 152; 388; 396; 600; 612; 804]%Z in exact T).

Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).
Definition rreserved_disjoint1 : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint1) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint1)).
Definition rmrep_transport_high : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_transport_high) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_transport_high)).

Definition rimplT_undef : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_undef) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_undef)).
#[global] Arguments rimplT_undef {R}%_type_scope o w k%_function_scope s Q%_function_scope ms.
Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rimplT_mmap_rw : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_mmap_rw) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_mmap_rw)).
#[global] Arguments rimplT_mmap_rw {R}%_type_scope o len%_Z_scope k%_function_scope s P%_function_scope Q%_function_scope ms _ _%_function_scope.
Definition rauxv_ok_frame : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rauxv_ok_frame) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rauxv_ok_frame)).
Definition rpres_except_trans : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_trans) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_trans)).
Definition rpres_except_mono : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_mono) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_mono)).
Definition rpres_except_of_munch : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_of_munch) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_of_munch)).
Ltac riprefixT := apply rimplT_from_evt.

Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmeta_slot_bounds : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmeta_slot_bounds) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmeta_slot_bounds)).
Definition rpres_except_of_munch' : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rpres_except_of_munch') constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rpres_except_of_munch')).

Definition rmrep_new_region : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mqa.rmrep_new_region) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mqa.rmrep_new_region)).

Definition rmeta_chunk_facts : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rmeta_chunk_facts) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rmeta_chunk_facts)).
Definition rregion_facts : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rregion_facts) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rregion_facts)).
Definition rmalloc_fp_mono : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rmalloc_fp_mono) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rmalloc_fp_mono)).

Notation RAREACH := (AREACH_from ref_reserved rc_secret).
Notation RISTF := (@ISTF_g ref_reserved).

Definition rtail_walk : ltac:(gw_ctx_fold_ty2 (@Q5m9.Mq4.rtail_walk) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@Q5m9.Mq4.rtail_walk)).

Definition rmm_seq_walk : ltac:(gw_ctx_fold_ty2 (@Q5m9.rmm_seq_walk) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@Q5m9.rmm_seq_walk)).

Definition rmmc_walk : ltac:(gw_ctx_fold_ty2 (@Q5m9.Mq5.rmmc_walk) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@Q5m9.Mq5.rmmc_walk)).

Definition rmm_call_walk : ltac:(gw_ctx_fold_ty2 (@Q5m9.Mq6.rmm_call_walk) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@Q5m9.Mq6.rmm_call_walk)).
Definition rmm_ret_fail_walk : ltac:(gw_ctx_fold_ty2 (@Q5m9.Mq6.rmm_ret_fail_walk) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@Q5m9.Mq6.rmm_ret_fail_walk)).
Definition rmm_ret_ok_walk : ltac:(gw_ctx_fold_ty2 (@Q5m9.Mq6.rmm_ret_ok_walk) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@Q5m9.Mq6.rmm_ret_ok_walk)).

Definition rmrep_extW : ltac:(gw_ctx_fold_ty2 (@Q5m9.Mq7.rmrep_extW) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@Q5m9.Mq7.rmrep_extW)).
Definition rfailm2_walk : ltac:(gw_ctx_fold_ty2 (@Q5m9.Mq7.rfailm2_walk) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@Q5m9.Mq7.rfailm2_walk)).

Definition ras_ret0 : ltac:(gw_ctx_fold_ty2 (@QZxv.Mqn.ras_ret0) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@QZxv.Mqn.ras_ret0)).

Definition rauxv_ok_malloc_fp_ER : ltac:(gw_ctx_fold_ty2 (@QzQg.Mq3.rauxv_ok_malloc_fp_ER) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@QzQg.Mq3.rauxv_ok_malloc_fp_ER)).

Definition rerrno_lit5 : ltac:(gw_ctx_fold_ty2 (@Q2TC.rerrno_lit5) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@Q2TC.rerrno_lit5)).

Definition rfailW_shape : ltac:(gw_ctx_fold_ty2 (@QDkC.rfailW_shape) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@QDkC.rfailW_shape)).
Definition rfailW_low : ltac:(gw_ctx_fold_ty2 (@QDkC.rfailW_low) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@QDkC.rfailW_low)).
Definition rlowW_disjoint : ltac:(gw_ctx_fold_ty2 (@QDkC.rlowW_disjoint) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@QDkC.rlowW_disjoint)).
Definition rlowW_disjoint_img : ltac:(gw_ctx_fold_ty2 (@QDkC.rlowW_disjoint_img) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@QDkC.rlowW_disjoint_img)).

Definition rmrep_st_model : ltac:(gw_ctx_fold_ty2 (@QDkC.Mq0.rmrep_st_model) constr:(gw_tbl_28)) := ltac:(gw_ctx_fold_tm2 (@QDkC.Mq0.rmrep_st_model)).

#[using="RDEBRUIJN RGOT_SSP e_197bc rsysret_entry ralloc_slot_entry rvm_wait_entry rmmap_entry RATP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 D_114 E_114 D_116 E_116 D_121 E_121 D_122 E_122 D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 D_218 E_218 D_220 E_220 D_311 E_311 D_313 E_313 D_427 E_427 D_552 E_552 ANCH_15 ANCH_19 ANCH_116 ANCH_122 ANCH_131 ANCH_137 ANCH_149 ANCH_220 ANCH_313 LINK_427 LINK_552 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rsysret_entry AL_ralloc_slot_entry AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rmmap_entry rmmap_anon_spec rwrapper_munch_keeps land_m4096 le4_swrap_succ"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := first [clear - hs segs base w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_14 hi_18 hi_114 hi_121 hi_130 hi_136 hi_148 hi_218 hi_311 lo_15 lo_19 lo_116 lo_122 lo_131 lo_137 lo_149 lo_220 lo_313 joff_427 joff_552 RDEBRUIJN RGOT_SSP e_197bc rsysret_entry ralloc_slot_entry rvm_wait_entry rmmap_entry RATP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 D_114 E_114 D_116 E_116 D_121 E_121 D_122 E_122 D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 D_218 E_218 D_220 E_220 D_311 E_311 D_313 E_313 D_427 E_427 D_552 E_552 ANCH_15 ANCH_19 ANCH_116 ANCH_122 ANCH_131 ANCH_137 ANCH_149 ANCH_220 ANCH_313 LINK_427 LINK_552 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rsysret_entry AL_ralloc_slot_entry AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rmmap_anon_spec rwrapper_munch_keeps land_m4096 le4_swrap_succ | clear - hs segs base w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_14 hi_18 hi_114 hi_121 hi_130 hi_136 hi_148 hi_218 hi_311 lo_15 lo_19 lo_116 lo_122 lo_131 lo_137 lo_149 lo_220 lo_313 joff_427 joff_552 RDEBRUIJN RGOT_SSP e_197bc rsysret_entry ralloc_slot_entry rvm_wait_entry rmmap_entry RATP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 D_114 E_114 D_116 E_116 D_121 E_121 D_122 E_122 D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 D_218 E_218 D_220 E_220 D_311 E_311 D_313 E_313 D_427 E_427 D_552 E_552 ANCH_15 ANCH_19 ANCH_116 ANCH_122 ANCH_131 ANCH_137 ANCH_149 ANCH_220 ANCH_313 LINK_427 LINK_552 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rsysret_entry AL_ralloc_slot_entry AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay rmmap_anon_spec rwrapper_munch_keeps land_m4096 le4_swrap_succ].

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> QUZl.M R) (bail : QUZl.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : RAREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk segs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells segs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv segs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := QULt.Mq1.ist_facts_proof st0 LB st AR IS.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 joff_427 CODE BASE4 BASER D_427 E_427 LINK_427 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_ro_addr_false ref_wview_overlay ref_mrd_overlay rmmap_anon_spec rwrapper_munch_keeps land_m4096 le4_swrap_succ rmmap_entry A1 AR AUX CLO ER FIT HK LO MR RQ SC TP"] Lemma rhmm_ok : rHMM_stmt k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc req.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 joff_427 CODE BASE4 BASER D_427 E_427 LINK_427 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_ro_addr_false ref_wview_overlay ref_mrd_overlay rmmap_anon_spec rwrapper_munch_keeps land_m4096 le4_swrap_succ rmmap_entry A1 AR AUX CLO ER FIT HK LO MR RQ SC TP segs RATP ref_reserved R f k bail o s Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st0 st LB lo sc req errv IS AC TK UA BL ST ERR MI A0 F0. gw_expose_fam RATP. try gw_hide F0; try gw_hide A0; try gw_hide MI; try gw_hide ERR; try gw_hide ST; try gw_hide BL; try gw_hide UA; try gw_hide TK; try gw_hide AC; try gw_hide IS; first [clear errv | gw_hide errv | idtac]; try gw_hide req; try gw_hide sc; try gw_hide lo; try gw_hide LB; try gw_hide st; try gw_hide st0; try gw_hide m; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear t6 | gw_hide t6 | idtac]; first [clear t5 | gw_hide t5 | idtac]; first [clear t4 | gw_hide t4 | idtac]; first [clear t3 | gw_hide t3 | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; try gw_hide s9; try gw_hide s8; try gw_hide s7; try gw_hide s6; try gw_hide s5; try gw_hide s4; try gw_hide s3; try gw_hide s2; first [clear a7 | gw_hide a7 | idtac]; first [clear a6 | gw_hide a6 | idtac]; first [clear a5 | gw_hide a5 | idtac]; first [clear a4 | gw_hide a4 | idtac]; first [clear a3 | gw_hide a3 | idtac]; first [clear a2 | gw_hide a2 | idtac]; first [clear a1 | gw_hide a1 | idtac]; first [clear a0 | gw_hide a0 | idtac]; try gw_hide s1; try gw_hide s0; first [clear t2 | gw_hide t2 | idtac]; first [clear t1 | gw_hide t1 | idtac]; first [clear t0 | gw_hide t0 | idtac]; try gw_hide tp; try gw_hide gp; try gw_hide sp; try gw_hide ra; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; try gw_hide o; try gw_hide bail; try gw_hide k; first [clear f | gw_hide f | idtac].
clear A0 F0 IS AC TK UA BL ST MI ERR.
intros st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CT C1R BIGc.
destruct CT as (TF & TR & ACT0 & LF & IS2 & ER2 & AC2 & REL & G0 & MSL & MR3 & TK3 & UA3 & MI3 & ST3 & FR3 & ERR3 & AUX3 & PE03 & BL2 & PSM & PSF & PSO).
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. unfold alloc_ceiling in CLO'.
pose proof (rerrno_lit5 tp TP) as EA.
pose proof (QULt.Mq1.ist_facts_proof st0 LB st2 AR IS2) as F2. pose proof (isf_mf _ _ F2) as MF2.
pose proof (mf_usage _ _ MF2) as URall. change (fact_usage (strip st2)) with (fact_usage st2) in URall.
pose proof (mf_ctx _ _ MF2) as (FC1 & FC2 & FC3 & FC4 & FC5 & FC6).
change (ctx (strip st2)) with (ctx st2) in FC1, FC2, FC3, FC4. change (bounces (strip st2)) with (bounces st2) in FC5. change (unmap_seq (strip st2)) with (unmap_seq st2) in FC6.
pose proof (size_class_range sc SC) as SZR.
unfold rcnt_state.
replace (size_class sc * UNIT * cnt1) with (UNIT * size_class sc * cnt1) by lia.
replace (size_class sc * UNIT) with (UNIT * size_class sc) by lia.
set (size := UNIT * size_class sc) in *.
assert (SZ : 16 <= size < 2^18) by (subst size; unfold UNIT; lia).
rewrite A1. rewrite (ag_mmap_eq sc req k bail st2 mm cnt1).
set (stS := step_seq (account_bounce sc st2)).
set (nos := is_bouncing sc st2).
set (u1 := mm_usage1 stS sc (usage st2 sc)).
set (cR := mm_cnt_red sc size cnt1 u1 nos).
assert (CRR : 1 <= cR <= 32) by (subst cR; apply mm_cnt_red_range; gw_exact C1R).
destruct (mm_final size req u1 cR nos) as [c nd] eqn:EF.
destruct (mm_final_props size req u1 cR nos c nd CRR ltac:(lia) ltac:(lia) ltac:(subst size; unfold UNIT; lia) EF) as (CR & NDM & NDR & NDC).
assert (NDB : 16 <= nd < 2^40).
{ pose proof (round_up_pg_props (req + 20) ltac:(lia)). pose proof (round_up_pg_props (size * c + 16) ltac:(nia)).
assert (size * c <= 2^18 * 32) by nia. destruct NDC as [[Ec En]|[LE En]]; rewrite En; lia. }
cbv beta iota.

riprefixT.
eapply evt_cut. { eapply (rmm_seq_walk sc SC); [gw_exact MR3| gw_exact FC4| gw_exact FC5| gw_exact FC6| gw_exact MI3]. }
cbv beta. intros ms' (u0 & u1' & wa3 & wa6 & wa7 & m4 & -> & -> & MU4 & WM4 & MI4 & MR4).
fold nos stS in MR4 |- *.

destruct (stS_shape sc st2) as (fS & ES & HS). fold stS in ES.
assert (US : forall i, usage stS i = usage st2 i) by (intros i; unfold usage; rewrite ES; unfold ctx, upd_ctx; cbn; rewrite (proj1 (proj2 (HS _))); reflexivity).
eapply evt_cut.
{ replace (wz (size + 16)) with (wz (size + 16)) by first [reflexivity | (cbn; lia)].
eapply (rmmc_walk sc size req nos SC SZ RQ) with (st := stS) (m := m4); [gw_exact MR4| gw_exact C1R| apply URall| intros i; rewrite US; apply URall]. }
cbv beta. unfold rmmc_post. intros ms' (v0 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & ->).
fold u1. fold cR. rewrite ?EF. cbn [fst snd].

assert (FR4 : rw_cells segs m4 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
{ eapply rw_cells_transport; [gw_exact FR3| gw_exact MU4| gw_exact WM4|]. (gw_expose_fam RATP; unfold rseqW). cbn. lia. }
assert (ST4 : stk segs m4 lo (bv_unsigned sp + -144)).
{ eapply stk_transport_disjoint; [gw_exact ST3| gw_exact MU4| gw_exact WM4|]. (gw_expose_fam RATP; unfold rseqW). cbn. lia. }
assert (ERR4 : rw_cells segs m4 (errno_addr tp) [C4 errv']).
{ eapply rw_cells_transport; [gw_exact ERR3| gw_exact MU4| gw_exact WM4|]. rewrite EA. (gw_expose_fam RATP; unfold rseqW). cbn. lia. }
assert (PE04 : rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m4).
{ eapply rpres_except_trans; [gw_exact PE03|]. eapply rpres_except_of_munch; [gw_exact MU4| gw_exact WM4|].
intros a Ha NC. unfold rseqW. cbn. split; [|exact I]. intros X. apply NC. left. right. right. left. gw_expose_fam RATP. lia. }
assert (AUX4 : rauxv_ok m4 (bv_unsigned sp)).
{ eapply rauxv_ok_frame; [gw_exact AUX3| gw_exact MU4| gw_exact WM4|]. (gw_expose_fam RATP; unfold rseqW). constructor; [cbn; lia| constructor]. }
pose proof (rmeta_slot_bounds st2 m3 mm MR3 MSL) as (Gpos & GC & GI & _).

eapply evt_cut. { eapply rmm_call_walk. }
cbv beta. intros ms' ->.
apply evt_done.
set (sp' := Z_to_bv 64 (bv_unsigned sp + -144)).
assert (SP' : bv_unsigned sp' = bv_unsigned sp + -144) by (subst sp'; apply unsigned_lit; lia).
eapply rimplT_mmap_rw.
{ eapply (rmmap_anon_spec false) with (lo := lo) (avoid := []);
[ rewrite SP'; gw_exact ST4 | gw_exact ERR4 | gw_exact MI4 | reflexivity | reflexivity
| reflexivity | reflexivity | reflexivity | reflexivity | lia | rewrite SP'; lia | gw_exact CLO
| rewrite SP', EA; lia | rewrite TP; gw_expose_fam RATP; rewrite unsigned_lit by lia; lia ]. }
intros ans ms' PO.

assert (REGS : s_regions stS = s_regions st2) by (rewrite ES; reflexivity).
assert (SHS : s_shadow stS = s_shadow st2) by (rewrite ES; reflexivity).
assert (GRS : s_groups stS = s_groups st2) by (rewrite ES; reflexivity).
assert (ARS : s_areas stS = s_areas st2) by (rewrite ES; reflexivity).
assert (TKS' : s_tick stS = s_tick st2) by (rewrite ES; reflexivity).
assert (NRS : s_next_rid stS = s_next_rid st2) by (rewrite ES; reflexivity).
assert (RSS : s_reserved stS = s_reserved st2) by (rewrite ES; reflexivity).
assert (RECS : forall q, get_meta_rec stS q = get_meta_rec st2 q) by (intros q; rewrite ES; reflexivity).
assert (ACTS : forall c', active stS c' = active st2 c') by (intros c'; unfold active; rewrite ES; unfold ctx, upd_ctx; cbn; rewrite (proj1 (HS _)); reflexivity).
assert (BRKS : c_brk (ctx stS) = c_brk (ctx st2)) by (rewrite ES; unfold ctx, upd_ctx; cbn; apply (proj1 (proj2 (proj2 (HS _))))).
assert (CTRS : c_mmap_counter (ctx stS) = c_mmap_counter (ctx st2)) by (rewrite ES; unfold ctx, upd_ctx; cbn; apply (proj1 (proj2 (proj2 (proj2 (HS _)))))).
assert (FMHS : c_free_meta_head (ctx stS) = c_free_meta_head (ctx st2)) by (rewrite ES; unfold ctx, upd_ctx; cbn; apply (proj1 (proj2 (proj2 (proj2 (proj2 (HS _))))))).
assert (CONCS : forall q, conc stS q = conc st2 q) by (intros q; unfold conc, get_region; rewrite REGS; reflexivity).
assert (MSLS : meta_slot stS mm) by (eapply meta_slot_same_areas; [gw_exact ARS| gw_exact MSL]).
assert (TKS : ticks_ok stS) by (eapply ticks_ok_same; [gw_exact SHS| gw_exact TKS'| gw_exact TK3]).

assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
pose proof MR as (WF & _). pose proof WF as (RS0 & WR0 & DJ0 & _).
destruct ans as [e|xa].
-
cbn [rmmap_anon_post] in PO.
destruct PO as (v0' & v1 & v2 & v3 & v4' & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m6 & -> & MU6 & WM6 & MI6 & ST6 & ERR6 & He).
cbn [mmap_val]. unfold mm_after. fold stS. destruct (mmap_answer_ok_err (live_ranges stS) nd e ltac:(clear - He RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 joff_427 CODE BASE4 BASER D_427 E_427 LINK_427 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_ro_addr_false ref_wview_overlay ref_mrd_overlay rmmap_anon_spec rwrapper_munch_keeps land_m4096 le4_swrap_succ rmmap_entry segs RATP ref_reserved; lia)) as [-> ->]. cbn [negb].
rewrite as_free_meta_eq. cbn [as_kq].
rewrite SP' in MU6, ST6. rewrite EA in MU6.
try g_ret_pc_any.
assert (FR6 : rw_cells segs m6 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
{ eapply rw_cells_transport; [gw_exact FR4| gw_exact MU6| gw_exact WM6|]. cbn. lia. }
assert (MR6 : rmrep stS m6).
{ eapply (rwrapper_munch_keeps stS m4 m6 (bv_unsigned sp - 144) lo MR4); [| gw_exact WM6| unfold alloc_ceiling; lia].
eapply munch_weaken; [| gw_exact MU6]. intros y; cbn; lia. }

pose proof (lf_freelist _ (isf_lf _ _ F2)) as FFL. change (fact_freelist (strip st2)) with (fact_freelist st2) in FFL.
assert (FL : forall h, c_free_meta_head (ctx stS) = Some h ->
meta_slot stS h /\ h <> mm /\ exists p, m_prev (get_meta_rec stS h) = Some p /\ meta_slot stS p /\ p <> mm).
{ intros h Hh. rewrite FMHS in Hh. destruct (FFL h Hh) as (MSh & MEMh & NXh & p & HP & MSp & MEMp & NXp).
change (meta_slot (strip st2) h) in MSh. change (get_meta_rec (strip st2) h) with (get_meta_rec st2 h) in MEMh, NXh, HP.
change (meta_slot (strip st2) p) in MSp. change (get_meta_rec (strip st2) p) with (get_meta_rec st2 p) in MEMp, NXp.
split; [eapply meta_slot_same_areas; [gw_exact ARS| gw_exact MSh]|].
split; [intros ->; rewrite G0 in NXh; apply NXh; reflexivity|].
exists p. rewrite RECS. split; [gw_exact HP|]. split; [eapply meta_slot_same_areas; [gw_exact ARS| gw_exact MSp]|].
intros ->. rewrite G0 in NXp. apply NXp. reflexivity. }
riprefixT.
eapply evt_cut. { eapply rmm_ret_fail_walk. }
cbv beta. intros ms' ->.
eapply evt_cut. { rewrite <- (CONCS mm). subst sp'. unfold rFRM in FR6. eapply (rfailm2_walk stS mm MSLS FL); [gw_exact MR6| gw_exact MI6| gw_exact FR6| lia]. }
cbv beta. intros ms' (s6x & m7 & junk' & -> & FR7 & MU7 & WM7 & MI7 & MR7).
assert (LW : Forall (rlowW (bv_unsigned sp)) (rfailW stS mm (bv_unsigned sp))).
{ eapply (rfailW_low stS mm m6 _ MR6 MSLS). intros h Hh. destruct (FL h Hh) as (MSh & _ & p & HP & MSp & _).
split; [gw_exact MSh|]. intros p' Hp'. rewrite HP in Hp'. inversion Hp'; subst. gw_exact MSp. }
assert (ST7 : stk segs m7 lo (bv_unsigned sp + -144)).
{ eapply stk_transport_disjoint; [gw_exact ST6| gw_exact MU7| gw_exact WM7| apply (rlowW_disjoint (bv_unsigned sp)); [gw_exact LW| lia| lia]]. }
assert (ERR7 : rw_cells segs m7 (errno_addr tp) [C4 (Z_to_bv 64 (Q9A7.Mq0.mmap_fix_errno e))]).
{ eapply rw_cells_transport; [gw_exact ERR6| gw_exact MU7| gw_exact WM7|]. rewrite EA. apply (rlowW_disjoint_img (bv_unsigned sp)); [gw_exact LW| lia| cbn; lia| gw_expose_fam RATP; cbn; lia| lia]. }
eapply evt_cut. { eapply (ras_ret0 sp gp tp); [gw_exact MR7| gw_exact MI7| gw_exact FR7| gw_exact ST7| gw_exact CLO| lia]. }
cbv beta. intros ms' (a1y & a2y & -> & ST8). apply evt_done.

set (stF := as_fm_st stS mm) in *.
destruct (fm_proj stS mm) as (PF1 & PF2 & PF3 & PF4 & PF5 & PF6 & PF7 & PF8 & PF9 & PF10 & PF11 & PF12 & _). fold stF in PF1, PF2, PF3, PF4, PF5, PF6, PF7, PF8, PF9, PF10, PF11, PF12.
assert (FS : Forall (rmetaW (bv_unsigned sp) stS) (rfailW stS mm (bv_unsigned sp))).
{ apply (rfailW_shape stS mm _ MSLS). intros h Hh; destruct (FL h Hh) as (MSh & _ & p & HP & MSp & _); split; [gw_exact MSh|]; intros p' Hp'; rewrite HP in Hp'; inversion Hp'; subst; gw_exact MSp. }
assert (PE07 : rpres_except (rmalloc_fp st0 stF lo (bv_unsigned sp)) m m7).
{ eapply rpres_except_trans.
- eapply rpres_except_mono; [gw_exact PE04|]. intros a Ha. eapply rmalloc_fp_mono; [| gw_exact Ha]. intros rid r Hr. exists r. rewrite PF1, REGS. repeat split; auto; lia.
- eapply rpres_except_trans.
+ eapply rpres_except_of_munch; [gw_exact MU6| gw_exact WM6|]. intros a Ha NC. cbn. split; [|split; [|exact I]]; intros X; apply NC; left; [left; lia| right; left; rewrite unsigned_lit by lia; lia].
+ eapply rpres_except_of_munch'; [gw_exact MU7| gw_exact WM7|].
intros lo' hi' HI x Hx. pose proof (proj1 (Forall_forall _ _) FS _ HI) as [(q & MSq & E1 & E2)|[E|E]].
* cbn in E1, E2. subst lo' hi'. left. do 3 right.
assert (MSq' : meta_slot stF q) by (eapply meta_slot_same_areas; [rewrite PF4; reflexivity| gw_exact MSq]).
destruct (rmeta_chunk_facts stF m7 q MR7 MSq') as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')).
exists rid0, r0. split; [gw_exact H0|]. split; [gw_exact K0|].
assert (EC : conc stF q = conc stS q) by (unfold conc, get_region; rewrite PF1; reflexivity). rewrite EC in L0, H0'. lia.
* inversion E; subst. left. right. right. left. gw_expose_fam RATP. lia.
* inversion E; subst. left. left. lia. }
apply HK. unfold ras_post2.
do 14 eexists. exists m7, (Z_to_bv 64 (Q9A7.Mq0.mmap_fix_errno e)). split; [reflexivity|].
split; [gw_exact MI7|]. split; [gw_exact ST8|]. split; [gw_exact ERR7|].
split; [eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER stF m7); [gw_exact MR7| gw_exact AUX| gw_exact PE07| gw_exact CLO| lia]|].
split; [gw_exact MR7|].
split; [eapply ticks_ok_same; [rewrite PF2; gw_exact SHS| rewrite PF6; gw_exact TKS'| gw_exact TK3]|].
split. { eapply (unk_agree_xfer o st2 m3 stF m7 UA3).
- rewrite PF2. gw_exact SHS.
- intros rid r Hk Hr. rewrite PF1, REGS in Hr. gw_exact Hr.
- intros b. rewrite PF3, GRS. split; intros X; gw_exact X.
- intros rid r off h Hr Hk Ho Hc NG.
pose proof MR3 as (WF3 & _). pose proof WF3 as (_ & WR3 & DJ3 & _). destruct (WR3 _ _ Hr) as (R0 & _ & _ & RC & _). unfold alloc_ceiling in RC.
destruct (rregion_facts st2 m3 rid r MR3 Hr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
transitivity (m6 (wa (r_base r + off))).
{ apply MU7. rewrite wa_unsigned by lia. eapply (avoid_outside _ (fun y => y = r_base r + off)); [| reflexivity]. intros lo' hi' a' HI Ha ->.
pose proof (proj1 (Forall_forall _ _) FS _ HI) as [(q & MSq & E1 & E2)|[E|E]].
- cbn in E1, E2. subst lo' hi'. rewrite CONCS in Ha.
assert (MSq2 : meta_slot st2 q) by (eapply meta_slot_same_areas; [symmetry; gw_exact ARS| gw_exact MSq]).
destruct (rmeta_chunk_facts st2 m3 q MR3 MSq2) as (_ & _ & _ & _ & _ & GRG & _). destruct (GRG rid r Hr Hk); lia.
- inversion E; subst. gw_expose_fam RATP. lia.
- inversion E; subst. lia. }
transitivity (m4 (wa (r_base r + off))).
{ apply MU6. rewrite wa_unsigned by lia. cbn. lia. }
apply MU4. rewrite wa_unsigned by lia. (gw_expose_fam RATP; unfold rseqW). cbn. lia. }
split; [gw_exact PE07|].
split. { split; [| rewrite PF7, NRS, <- (tr_next _ _ _ TR); apply (amr_next_rid _ _ _ REL)| rewrite PF8, RSS, (amr_reserved _ _ _ REL); apply (tr_reserved _ _ _ TR)].
intros rid r Hr. rewrite <- REG1 in Hr. destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & B' & L' & _). exists r'. rewrite PF1, REGS. auto. }
split. { unfold brk_link_ps in *. rewrite PF11, BRKS. destruct (c_brk (ctx st2)) as [| |rid off]; auto.
unfold conc, get_region. rewrite PF1, REGS. gw_exact BL2. }
split; [gw_exact PSM|]. split; [gw_exact PSF|]. split; [gw_exact PSO|].
split. { constructor.
- intros c' Hc'. rewrite PF9, ACTS, (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
- intros a Ha. rewrite PF4, ARS. apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). gw_exact Ha.
- rewrite PF6, TKS', (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
- intros H; exfalso; lia.
- intros _ H; exfalso; lia. }
split; [rewrite PF12, CTRS; gw_exact FC1|].
left. split; [reflexivity| rewrite He; reflexivity].
-
cbn [rmmap_anon_post] in PO.
destruct PO as (v0' & v1 & v2 & v3 & v4' & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m6 & -> & MU6 & WM6 & MI6 & ST6 & ERR6 & AOK).
cbn [mmap_val]. unfold mm_after. fold stS.
destruct (mmap_answer_ok (live_ranges stS) nd xa) eqn:VOK. 2:{ cbn [negb]. apply rimplT_undef. }
cbn [negb].
destruct (mmap_answer_ok_addr (live_ranges stS) nd xa ltac:(lia) AOK VOK) as (X0 & XA & XC & XRF & ISE). rewrite ISE.
rewrite SP' in MU6, ST6.
assert (RU : round_up_pg nd = nd) by (unfold round_up_pg; change (PGSZ - 1) with (Z.ones 12); rewrite Z.land_ones by lia; change (2 ^ 12) with 4096; Z.div_mod_to_equations; lia).
rewrite RU in XC, XRF.
assert (FR6 : rw_cells segs m6 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
{ eapply rw_cells_transport; [gw_exact FR4| gw_exact MU6| gw_exact WM6|]. cbn. lia. }
assert (MR6 : rmrep stS m6).
{ eapply (rmrep_transport_high stS m4 m6); [gw_exact MR4| gw_exact MU6| gw_exact WM6| intros lo' hi' [E|[]]; inversion E; unfold alloc_ceiling; lia]. }

unfold new_region.
set (rid := s_next_rid stS). set (r0 := {| r_kind := RKGroup; r_base := xa; r_len := nd |}).
set (stN := set_next_rid (N.succ rid) (set_regions (<[rid:=r0]> (s_regions stS)) stS)).
assert (EstN : stN = fst (new_region RKGroup xa nd stS)) by first [reflexivity | (cbn; lia)].
pose proof (mf_ptrs _ _ MF2) as [PT0 FRESH0].
assert (PT1 : ptrs_in (fun r => r <> rid) stS).
{ rewrite ES. apply ptrs_in_upd_ctx_scalar; try (intros cc; pose proof (HS cc) as (?&?&?&?&?&?&?&?&?&?&?&?&?&?); assumption).
eapply ptrs_in_mono; [|gw_exact PT0]. intros r Hr. cbn in Hr. subst rid. rewrite NRS. intros ->. lia. }
destruct (FRESH0 rid ltac:(subst rid; rewrite NRS; lia)) as [FRr FRs].
unfold Q9A7.Mq0.mmap_raw in ST6 |- *. cbn [negb] in ST6 |- *. rewrite mmap_len_round_up, RU in ST6 |- *.
unfold alloc_ceiling in XC.
set (mz := apply_zeros m6 [(wa xa, Z_to_bv 64 nd)]) in *.
assert (ZO : forall a, 0 <= a < 2^64 -> (a < xa \/ xa + nd <= a) -> mz (wa a) = m6 (wa a)).
{ intros a Ha Ho. unfold mz. apply (zeros_outside m6 xa nd); rewrite ?wa_unsigned by lia; lia. }
assert (ZI : forall a, xa <= a < xa + nd -> mz (wa a) = Some (b8 0)).
{ intros a Ha. unfold mz. apply (zeros_inside m6 xa nd); rewrite ?wa_unsigned by lia; lia. }
assert (MRz : rmrep stN mz).
{ rewrite EstN. eapply (rmrep_new_region stS m6 mz xa nd RKGroup MR6 PT1 ltac:(rewrite SHS; gw_exact FRs) X0 XA ltac:(lia));
rewrite ?mmap_len_round_up, ?RU; [unfold alloc_ceiling; gw_exact XC| gw_exact XRF| gw_exact ZO| intros _; gw_exact ZI]. }
pose proof MR6 as (WF6 & _). pose proof WF6 as (RS6 & WR6 & DJ6 & _).
assert (XI : xa + nd <= 0x10000 \/ RIMG_HI <= xa).
{ assert (RFimg : ranges_free ref_reserved xa nd = true).
{ apply ranges_free_intro. intros b kk HI. apply (ranges_free_In _ _ _ _ _ XRF). unfold live_ranges. apply in_or_app. left. rewrite RS6. gw_exact HI. }
apply (rreserved_disjoint1 _ _ RFimg). lia. }
assert (MIz : mem_inv segs mz).
{ unfold mz. apply (mem_inv_zeros segs m6 xa nd); try lia; [gw_exact MI6|]. intros w Hw. apply ref_ro_addr_false. lia. }
assert (MUz : munch [(xa, xa + nd)] m6 mz) by (apply munch_of_pointwise; [lia| lia| gw_exact ZO]).
assert (WMz : wmono segs m6 mz) by (intros w Hw; unfold mz; apply (wview_zeros_mono segs m6 xa nd); try lia; gw_exact Hw).
assert (FRz : rw_cells segs mz (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
{ eapply rw_cells_transport; [gw_exact FR6| gw_exact MUz| gw_exact WMz|]. cbn. lia. }
assert (STz : stk segs mz lo (bv_unsigned sp + -144)) by gw_exact ST6.
assert (ERRz : rw_cells segs mz (errno_addr tp) [C4 errv']).
{ eapply rw_cells_transport; [gw_exact ERR6| gw_exact MUz| gw_exact WMz|]. rewrite EA. cbn. lia. }

assert (MSLN : meta_slot stN mm) by (eapply meta_slot_same_areas; [| gw_exact MSLS]; rewrite EstN; reflexivity).
assert (RECN : get_meta_rec stN mm = meta0) by (rewrite EstN; change (get_meta_rec (fst (new_region RKGroup xa nd stS)) mm) with (get_meta_rec stS mm); rewrite RECS; gw_exact G0).
assert (CTRN : c_mmap_counter (ctx stN) = c_mmap_counter (ctx st2)) by (rewrite EstN; change (ctx (fst (new_region RKGroup xa nd stS))) with (ctx stS); gw_exact CTRS).
assert (GCN : conc stN mm = conc st2 mm).
{ rewrite <- CONCS. rewrite EstN. apply nr_conc. cbn [fst].
destruct MSLS as (ar & arr & kk & Ha & Hk & ->). unfold aadd. cbn [fst]. intros E.
destruct PT1 as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 _ _ Ha) as [X _]. exact (X E). }
try g_ret_pc_any.
riprefixT.
eapply evt_cut.
{ rewrite <- GCN. subst sp'.
eapply (rmm_ret_ok_walk stN sc c size nd xa (c_mmap_counter (ctx st2)) mm SC ltac:(lia) SZ ltac:(lia) NDM X0 ltac:(unfold alloc_ceiling; lia) MSLN RECN CTRN FC1);
[gw_exact MRz| gw_exact MIz]. }
cbv beta. intros ms' (xa3 & xa4 & m8 & -> & MU8 & WM8 & MI8 & MR8 & CTR8).
set (stT := mm_st4 stN nd mm) in *.

assert (ND12 : Z.shiftr nd 12 = nd / 4096) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
assert (ML : 0 <= Z.shiftr nd 12 < 2^52) by (rewrite ND12; Z.div_mod_to_equations; lia).
assert (RECT : get_meta_rec stT mm = {| m_prev := None; m_next := None; m_mem := None; m_avail := 0; m_freed := 0; m_last_idx := 0; m_freeable := 0; m_sizeclass := 0; m_maplen := Z.shiftr nd 12 |}).
{ unfold stT, mm_st4. rewrite rec_upd_ctx. unfold upd_meta. rewrite get_meta_rec_put_same, RECN. unfold m_set_maplen, meta0. cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass].
f_equal. change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
assert (HrT : (s_regions stT) !! rid = Some r0) by (unfold stT, mm_st4, upd_meta; cbn; first [apply lookup_insert_eq | rewrite EstN; apply nr_lookup_new]).
assert (GNT : forall off, (s_groups stT) !! (rid, off) = None).
{ intros off. change (s_groups stT) with (s_groups stS). destruct ((s_groups stS) !! (rid, off)) as [gh|] eqn:E; [|reflexivity].
destruct PT1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
assert (SHT : (s_shadow stT) !! rid = None) by (change (s_shadow stT) with (s_shadow stS); rewrite SHS; gw_exact FRs).
assert (ACTT : active stT sc = None).
{ unfold stT, mm_st4. unfold active, ctx, upd_ctx, upd_meta. cbn. change (c_active (s_ctx stS) !! sc) with (active stS sc). rewrite ACTS, (amr_active _ _ _ REL). gw_exact ACT0. }
assert (TKT : ticks_ok stT).
{ eapply ticks_ok_same; [| | gw_exact TK3]; [change (s_shadow stT) with (s_shadow stS); gw_exact SHS| change (s_tick stT) with (s_tick stS); gw_exact TKS']. }
pose proof (mm_ai_range stN c size nd mm ltac:(lia) SZ) as AIR.
eapply evt_cut.
{ replace (Z_to_bv 64 xa) with (Z_to_bv 64 (conc stT (rid, 0))) by (rewrite (conc_region stT rid 0 r0 HrT); cbn [r_base r0]; f_equal; lia).
change (conc stN mm) with (conc stT mm).
eapply (rtail_walk stT sc c (mm_ai c size) (Z.shiftr nd 12) mm (rid, 0) r0 SC ltac:(lia) AIR ML);
[eapply meta_slot_same_areas; [| gw_exact MSLN]; reflexivity| gw_exact RECT| gw_exact HrT| reflexivity| cbn; lia| cbn; reflexivity
| cbn [snd r_len r0]; rewrite RU; lia| apply GNT
| intros b' gh Hb' Hf'; exfalso; destruct b' as [b1 b2]; cbn in Hf'; subst b1; rewrite GNT in Hb'; discriminate
| intros o' v t Ho Hc; exfalso; unfold get_shadow in Hc; rewrite SHT in Hc; cbn in Hc; rewrite lookup_empty in Hc; discriminate
| change (usage stT sc) with (usage stS sc); rewrite US; apply URall
| gw_exact ACTT| gw_exact TKT| gw_exact MR8| gw_exact MI8]. }
cbv beta. intros ms' (s0x & a1x & a2x & a3x & a4x & m9 & -> & MU9 & WM9 & MI9 & MR9 & TK9).
assert (GT : conc stT mm = conc st2 mm) by (change (conc stT mm) with (conc stN mm); gw_exact GCN).
assert (PT : conc stT (rid, 0) = xa) by (rewrite (conc_region stT rid 0 r0 HrT); cbn [r_base r0]; lia).

assert (FR9 : rw_cells segs m9 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
{ eapply rw_cells_transport; [| gw_exact MU9| gw_exact WM9| unfold rtailW; rewrite GT, PT; gw_expose_fam RATP; cbn; unfold alloc_ceiling in GC; lia].
eapply rw_cells_transport; [gw_exact FRz| gw_exact MU8| gw_exact WM8|]. rewrite GCN. gw_expose_fam RATP. cbn. unfold alloc_ceiling in GC. lia. }
assert (ST9 : stk segs m9 lo (bv_unsigned sp + -144)).
{ eapply stk_transport_disjoint; [| gw_exact MU9| gw_exact WM9| unfold rtailW; rewrite GT, PT; gw_expose_fam RATP; cbn; unfold alloc_ceiling in GC; lia].
eapply stk_transport_disjoint; [gw_exact STz| gw_exact MU8| gw_exact WM8| rewrite GCN; gw_expose_fam RATP; cbn; unfold alloc_ceiling in GC; lia]. }
eapply evt_cut. { unfold rFRM in FR9. eapply (ras_ret0 sp gp tp); [gw_exact MR9| gw_exact MI9| gw_exact FR9| gw_exact ST9| gw_exact CLO| lia]. }
cbv beta. intros ms' (a1y & a2y & -> & ST10). apply evt_done.
rewrite (ag_tail_kq_eq sc k bail stT mm (rid, 0) c (mm_ai c size)); [| rewrite RECT; reflexivity| rewrite RECT; reflexivity| gw_exact ACTT].
apply HK.

set (ai := mm_ai c size) in *. set (ml := Z.shiftr nd 12) in *.
set (stF := st_model stT sc c ai mm (rid, 0)).
assert (C32 : 1 <= c <= 32) by lia.
assert (EML : nd = 4096 * ml) by (subst ml; rewrite ND12; Z.div_mod_to_equations; lia).
assert (ML28 : 1 <= ml < 2^28) by lia.
assert (Hk0 : r_kind r0 = RKGroup) by first [reflexivity | (cbn; lia)].
assert (LEN0 : r_len r0 = nd) by first [reflexivity | (cbn; lia)].
assert (MST : meta_slot stT mm) by (eapply meta_slot_same_areas; [| gw_exact MSLN]; reflexivity).
assert (Esz : size = 16 * size_class sc) by first [reflexivity | (cbn; lia)].
assert (NDC' : c = 1 /\ nd < req + 20 + 4096 \/ 16 * size_class sc * c + 16 <= nd /\ nd < 16 * size_class sc * c + 16 + 4096).
{ pose proof (round_up_pg_props (req + 20) ltac:(lia)) as [R1 _]. pose proof (round_up_pg_props (size * c + 16) ltac:(nia)) as [N1 _].
rewrite <- Esz. destruct NDC as [[Ec En]|[LE En]]; [left; split; [gw_exact Ec| rewrite En; lia] | right; split; [gw_exact LE| rewrite En at 1; lia]]. }
destruct (sm_slot_ok stT sc c ai ml mm rid r0 SC C32 AIR ML28 RECT HrT Hk0 SHT GNT req nd RQ FIT LEN0 EML NDR ltac:(lia) NDC' MST) as (SO & STR & S16 & SND).
fold stF in SO, STR, S16, SND.
pose proof (sm_proj stT sc c ai mm rid) as (PF1 & PF2 & PF3 & PF4 & PF5 & PF6 & PF7 & PF8 & PF9 & PF10).
fold stF in PF1, PF2, PF3, PF4, PF5, PF6, PF7, PF8, PF9, PF10.
assert (MRF : rmrep stF m9) by (exact (rmrep_st_model stT sc c ai ml mm (rid, 0) SC C32 RECT ltac:(cbn; lia) m9 MR9)).
assert (TKF : ticks_ok stF) by (eapply ticks_ok_same; [| | gw_exact TK9]; reflexivity).
assert (MSF : meta_slot stF mm) by (apply (proj1 (sm_meta_slot stT sc c ai mm rid mm)); gw_exact MST).

assert (REGT : s_regions stT = <[rid:=r0]> (s_regions stS)) by first [reflexivity | (cbn; lia)].
assert (SHT' : s_shadow stT = s_shadow st2) by (transitivity (s_shadow stS); [reflexivity| gw_exact SHS]).
assert (GRT : s_groups stT = s_groups st2) by (transitivity (s_groups stS); [reflexivity| gw_exact GRS]).
assert (ART : s_areas stT = s_areas st2) by (transitivity (s_areas stS); [reflexivity| gw_exact ARS]).
assert (TKT' : s_tick stT = s_tick st2) by (transitivity (s_tick stS); [reflexivity| gw_exact TKS']).
assert (NRT : s_next_rid stT = N.succ rid) by first [reflexivity | (cbn; lia)].
assert (RST : s_reserved stT = s_reserved st2) by (transitivity (s_reserved stS); [reflexivity| gw_exact RSS]).
assert (BRKT : c_brk (ctx stT) = c_brk (ctx st2)) by (transitivity (c_brk (ctx stS)); [reflexivity| gw_exact BRKS]).
assert (ACTT' : forall c', active stT c' = active st2 c') by (intros c'; transitivity (active stS c'); [reflexivity| apply ACTS]).
assert (GF : conc stF mm = conc st2 mm) by (rewrite (sm_conc stT sc c ai mm rid); gw_exact GT).
assert (HOLD : forall q rq, (s_regions st2) !! q = Some rq -> (s_regions stF) !! q = Some rq /\ q <> rid).
{ intros q rq Hq. assert (NE : q <> rid) by (intros ->; rewrite FRr in Hq; discriminate).
split; [| gw_exact NE]. rewrite PF1, REGT, lookup_insert_ne, REGS by congruence. gw_exact Hq. }
assert (MREL0S : forall q rq, (s_regions st0) !! q = Some rq ->
exists r', (s_regions stS) !! q = Some r' /\ r_kind r' = r_kind rq /\ r_base r' = r_base rq /\ r_len rq <= r_len r').
{ intros q rq Hq. destruct (mrel_regions _ _ (er_mrel _ _ ER) q rq Hq) as (r1 & H1 & K1 & B1 & L1). rewrite <- REG1 in H1.
destruct (amr_regions _ _ _ REL q r1 H1) as (r2 & H2 & K2 & B2 & L2 & _). exists r2. rewrite REGS. repeat split; auto; try congruence. lia. }
assert (FRESH : forall a, xa <= a < xa + nd -> fresh_addr st0 a).
{ intros a Ha. eapply (fresh_addr_anti st0 stS); [| gw_exact MREL0S|].
- rewrite RS6, <- RS0. exact (mrel_reserved _ _ (er_mrel _ _ ER)).
- split; [unfold alloc_ceiling; lia|]. eapply (ranges_free_sub _ xa nd); [gw_exact XRF| lia| lia| lia]. }
assert (HFP2 : forall a, rmalloc_fp st0 st2 lo (bv_unsigned sp) a -> rmalloc_fp st0 stF lo (bv_unsigned sp) a).
{ intros a Ha. eapply rmalloc_fp_mono; [| gw_exact Ha]. intros q rq Hq. exists rq. split; [apply (proj1 (HOLD q rq Hq))|]. repeat split; auto. lia. }

assert (OLDW : forall q rq off, (s_regions st2) !! q = Some rq -> r_kind rq = RKGroup -> 0 <= off < round_up_pg (r_len rq) ->
m9 (wa (r_base rq + off)) = m3 (wa (r_base rq + off))).
{ intros q rq off Hq Hk Ho.
assert (HqS : (s_regions stS) !! q = Some rq) by (rewrite REGS; gw_exact Hq).
destruct (WR6 _ _ HqS) as (R0 & _ & _ & RC & _). unfold alloc_ceiling in RC.
destruct (rregion_facts st2 m3 q rq MR3 Hq) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
destruct (rmeta_chunk_facts st2 m3 mm MR3 MSL) as (_ & _ & _ & _ & _ & GRG & _). pose proof (GRG q rq Hq Hk) as GRq.
pose proof (In_live_ranges stS q rq HqS) as HIq. unfold region_live_range in HIq. rewrite Hk in HIq.
pose proof (ranges_free_In _ _ _ _ _ XRF HIq) as DJq.
pose proof (lr_lo_group rq Hk) as LRq.

transitivity (m8 (wa (r_base rq + off))). { apply MU9. rewrite wa_unsigned by (clear - Ho R0 RC RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 joff_427 CODE BASE4 BASER D_427 E_427 LINK_427 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_ro_addr_false ref_wview_overlay ref_mrd_overlay rmmap_anon_spec rwrapper_munch_keeps land_m4096 le4_swrap_succ rmmap_entry segs RATP ref_reserved; lia). unfold rtailW. rewrite GT, PT. cbn. gw_expose_fam RATP. clear - Ho R0 RC RI2 GRq DJq SC SND S16 RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 joff_427 CODE BASE4 BASER D_427 E_427 LINK_427 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_ro_addr_false ref_wview_overlay ref_mrd_overlay rmmap_anon_spec rwrapper_munch_keeps land_m4096 le4_swrap_succ rmmap_entry segs RATP ref_reserved; lia. }
transitivity (mz (wa (r_base rq + off))). { apply MU8. rewrite wa_unsigned by (clear - Ho R0 RC RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 joff_427 CODE BASE4 BASER D_427 E_427 LINK_427 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_ro_addr_false ref_wview_overlay ref_mrd_overlay rmmap_anon_spec rwrapper_munch_keeps land_m4096 le4_swrap_succ rmmap_entry segs RATP ref_reserved; lia). rewrite GCN. cbn. gw_expose_fam RATP. clear - Ho R0 RI2 GRq RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 joff_427 CODE BASE4 BASER D_427 E_427 LINK_427 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_ro_addr_false ref_wview_overlay ref_mrd_overlay rmmap_anon_spec rwrapper_munch_keeps land_m4096 le4_swrap_succ rmmap_entry segs RATP ref_reserved; lia. }
transitivity (m6 (wa (r_base rq + off))). { apply ZO; [clear - Ho R0 RC RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 joff_427 CODE BASE4 BASER D_427 E_427 LINK_427 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_ro_addr_false ref_wview_overlay ref_mrd_overlay rmmap_anon_spec rwrapper_munch_keeps land_m4096 le4_swrap_succ rmmap_entry segs RATP ref_reserved; lia | clear - Ho R0 DJq RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 joff_427 CODE BASE4 BASER D_427 E_427 LINK_427 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_ro_addr_false ref_wview_overlay ref_mrd_overlay rmmap_anon_spec rwrapper_munch_keeps land_m4096 le4_swrap_succ rmmap_entry segs RATP ref_reserved; lia]. }
transitivity (m4 (wa (r_base rq + off))). { apply MU6. rewrite wa_unsigned by (clear - Ho R0 RC RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 joff_427 CODE BASE4 BASER D_427 E_427 LINK_427 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_ro_addr_false ref_wview_overlay ref_mrd_overlay rmmap_anon_spec rwrapper_munch_keeps land_m4096 le4_swrap_succ rmmap_entry segs RATP ref_reserved; lia). cbn. clear - Ho R0 RC CLO' LO ASG RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 joff_427 CODE BASE4 BASER D_427 E_427 LINK_427 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_ro_addr_false ref_wview_overlay ref_mrd_overlay rmmap_anon_spec rwrapper_munch_keeps land_m4096 le4_swrap_succ rmmap_entry segs RATP ref_reserved; lia. }
apply MU4. rewrite wa_unsigned by (clear - Ho R0 RC RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 joff_427 CODE BASE4 BASER D_427 E_427 LINK_427 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_ro_addr_false ref_wview_overlay ref_mrd_overlay rmmap_anon_spec rwrapper_munch_keeps land_m4096 le4_swrap_succ rmmap_entry segs RATP ref_reserved; lia). (gw_expose_fam RATP; unfold rseqW). cbn. clear - Ho R0 RI2 RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 joff_427 CODE BASE4 BASER D_427 E_427 LINK_427 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_ro_addr_false ref_wview_overlay ref_mrd_overlay rmmap_anon_spec rwrapper_munch_keeps land_m4096 le4_swrap_succ rmmap_entry segs RATP ref_reserved; lia. }
assert (UAF : unk_agree stF o m9).
{ eapply (unk_agree_transfer st2 stF o m3 m9 UA3). intros q rq Hq Hk.
rewrite PF1, REGT, REGS in Hq.
destruct (N.eq_dec q rid) as [->|NE].
- right. rewrite lookup_insert_eq in Hq. inversion Hq; subst rq. cbn [r_len r_base]. intros off h Ho Hc.
rewrite (sm_cell_read stT sc c ai mm rid SHT off ltac:(lia)) in Hc.
destruct (off <? 12) eqn:T; [|discriminate]. apply Z.ltb_lt in T. apply (sm_grp_hdr_cov stT sc c ai mm rid SC). lia.
- left. rewrite lookup_insert_ne in Hq by congruence.
split; [gw_exact Hq|].
split. { rewrite (sm_shadow_other stT sc c ai mm rid q NE). unfold get_shadow. rewrite SHT'. reflexivity. }
split. { intros off X. apply (sm_grp_hdr_cov_old stT sc c ai mm rid GNT). eapply rgrp_hdr_cov_same; [gw_exact GRT| gw_exact X]. }
intros off h Ho Hc NG. exact (OLDW q rq off Hq Hk Ho). }
assert (PE09 : rpres_except (rmalloc_fp st0 stF lo (bv_unsigned sp)) m m9).
{ eapply rpres_except_trans. { eapply rpres_except_mono; [gw_exact PE04| gw_exact HFP2]. }
eapply rpres_except_trans. { eapply rpres_except_of_munch; [gw_exact MU6| gw_exact WM6|]. intros a Ha NC. cbn. split; [|exact I]. intros X; apply NC. left. left. lia. }
eapply rpres_except_trans. { eapply rpres_except_of_munch; [gw_exact MUz| gw_exact WMz|]. intros a Ha NC. cbn. split; [|exact I]. intros X; apply NC. do 4 right. apply FRESH. lia. }
eapply rpres_except_trans.
{ eapply rpres_except_of_munch; [gw_exact MU8| gw_exact WM8|]. intros a Ha NC. rewrite GCN. cbn. split; [|split; [|exact I]]; intros X; apply NC.
- left. do 3 right. destruct (rmeta_chunk_facts stF m9 mm MRF MSF) as (_ & _ & _ & _ & _ & _ & (rid0 & rr0 & H0 & K0 & L0 & H0')).
exists rid0, rr0. split; [gw_exact H0|]. split; [gw_exact K0|]. rewrite GF in L0, H0'. lia.
- left. right. right. left. gw_expose_fam RATP. lia. }
eapply rpres_except_of_munch; [gw_exact MU9| gw_exact WM9|]. intros a Ha NC. unfold rtailW. rewrite GT, PT. cbn.
split; [|split; [|split; [|split; [|exact I]]]]; intros X; apply NC.
- left. right. right. left. gw_expose_fam RATP. lia.
- left. do 3 right. destruct (rmeta_chunk_facts stF m9 mm MRF MSF) as (_ & _ & _ & _ & _ & _ & (rid0 & rr0 & H0 & K0 & L0 & H0')).
exists rid0, rr0. split; [gw_exact H0|]. split; [gw_exact K0|]. rewrite GF in L0, H0'. lia.
- do 4 right. apply FRESH. lia.
- left. right. right. left. gw_expose_fam RATP. lia. }
assert (ERR9 : rw_cells segs m9 (errno_addr tp) [C4 errv']).
{ eapply rw_cells_transport; [| gw_exact MU9| gw_exact WM9|].
- eapply rw_cells_transport; [gw_exact ERRz| gw_exact MU8| gw_exact WM8|]. rewrite EA, GCN. cbn. gw_expose_fam RATP. lia.
- unfold rtailW. rewrite GT, PT, EA. cbn. gw_expose_fam RATP. lia. }
unfold ras_post2.
do 14 eexists. exists m9, errv'. split; [reflexivity|].
split; [gw_exact MI9|]. split; [gw_exact ST10|]. split; [gw_exact ERR9|].
split; [eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER stF m9); [gw_exact MRF| gw_exact AUX| gw_exact PE09| gw_exact CLO| lia]|].
split; [gw_exact MRF|]. split; [gw_exact TKF|]. split; [gw_exact UAF|]. split; [gw_exact PE09|].
split. { split.
- intros q rq Hq. rewrite <- REG1 in Hq. destruct (amr_regions _ _ _ REL q rq Hq) as (r' & H' & K' & B' & L' & _).
exists r'. split; [apply (proj1 (HOLD q r' H'))|]. repeat split; auto.
- rewrite PF6, NRT. pose proof (amr_next_rid _ _ _ REL) as NX1. pose proof (tr_next _ _ _ TR) as NX0. subst rid. rewrite NRS. lia.
- rewrite PF7, RST, (amr_reserved _ _ _ REL). apply (tr_reserved _ _ _ TR). }
split. { unfold brk_link_ps in BL2 |- *. rewrite PF8, BRKT. destruct (c_brk (ctx st2)) as [| |brid boff] eqn:EB; auto.
rewrite (sm_conc stT sc c ai mm rid). rewrite <- (CONCS (brid, boff)) in BL2.
replace (conc stT (brid, boff)) with (conc stS (brid, boff)); [gw_exact BL2|].
change (conc stT (brid, boff)) with (conc stN (brid, boff)). rewrite EstN. symmetry. apply nr_conc. cbn [fst].
destruct PT1 as (_ & _ & _ & _ & _ & _ & P7 & _). rewrite BRKS in P7. first [rewrite EB in P7; gw_exact P7 | gw_exact P7]. }
split; [gw_exact PSM|]. split; [gw_exact PSF|]. split; [gw_exact PSO|].
split. { constructor.
- intros c' Hc'. rewrite (sm_active stT sc c ai mm rid). replace (c' =? sc) with false by (symmetry; apply Z.eqb_neq; lia).
rewrite ACTT', (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
- intros a Ha. rewrite PF4, ART. apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). gw_exact Ha.
- rewrite PF5, TKT', (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
- intros _ rid' S len RS o' v t Ho Hc. destruct (sm_ret_span stT sc c ai ml mm rid SC C32 RECT rid' S len RS) as [-> ->].
rewrite (sm_cells_none stT sc c ai mm rid SHT) in Hc. discriminate.
- intros _ _ rid' S len RS o' Ho. destruct (sm_ret_span stT sc c ai ml mm rid SC C32 RECT rid' S len RS) as [-> ->].
split; [apply (sm_cells_none stT sc c ai mm rid SHT)|].
split; [apply (sm_hav_none stT sc c ai mm rid SHT); lia| apply (sm_havp_none stT sc c ai mm rid SHT)]. }
split. { rewrite PF9, CTR8. unfold u32. Z.div_mod_to_equations. lia. }
right. split; [lia|]. exists mm, (rid, 0), r0.
split; [rewrite (sm_active stT sc c ai mm rid), Z.eqb_refl; reflexivity|]. split; [gw_exact SO|]. split.
+ intros a Ha. replace (r_base r0) with xa in Ha by first [reflexivity | (cbn; lia)]. cbn [fst snd] in Ha. do 4 right. apply FRESH. rewrite Z.mul_0_r in Ha. lia.
+ intros _. cbn [fst snd]. replace (0 + (16 + get_stride (get_meta_rec stF mm) * 0) + -3) with 13 by lia.
apply (sm_rdv stT sc c ai mm rid SHT).
Qed.
End LEVEL.

End RC__1.

End G.
