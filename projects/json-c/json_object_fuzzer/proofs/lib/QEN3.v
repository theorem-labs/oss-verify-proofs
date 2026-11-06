(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q5Rg Qfw3_c1 QWxq_c1 Qc3B QlEo_c1 Lib.GwApply QsjA QZAi Ql2m QqdR QYTG Lib.SepCache QnDM_c1 QVbl QQLG Q91D QQRC G.T_shp G.T_pe Qbz7 QFau Q8l1 QROt Lib.CodeAt Lib.StepGen Lib.StepGenX Lib.StepGenX2 Lib.GwCallee Lib.GwFold.
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

Import QROt.Mq0.
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

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 : Z).
Variables (hi_360 hi_543 : bv 20).
Variables (lo_362 lo_545 : bv 12).
Variables (G_102fd G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_fwritex : Z).
Hypothesis CODE : code_at segs base (printf_core_code w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 3632.
Hypothesis D_360 : decode_any (Z_to_bv 32 w_360) = Some (Auipc 11 hi_360, 4%Z).
Hypothesis E_360 : is_ecall (Z_to_bv 32 w_360) = false.
Hypothesis D_362 : decode_any (Z_to_bv 32 w_362) = Some (OpImm ALU_ADD 11 11 lo_362, 4%Z).
Hypothesis E_362 : is_ecall (Z_to_bv 32 w_362) = false.
Hypothesis D_543 : decode_any (Z_to_bv 32 w_543) = Some (Auipc 11 hi_543, 4%Z).
Hypothesis E_543 : is_ecall (Z_to_bv 32 w_543) = false.
Hypothesis D_545 : decode_any (Z_to_bv 32 w_545) = Some (OpImm ALU_ADD 17 11 lo_545, 4%Z).
Hypothesis E_545 : is_ecall (Z_to_bv 32 w_545) = false.
Hypothesis ANCH_362 : gw_anch (Z.shiftl (bv_signed hi_360) 12 + (base + 1440) + bv_signed lo_362)%Z G_102fd.
Hypothesis ANCH_545 : gw_anch (Z.shiftl (bv_signed hi_543) 12 + (base + 2172) + bv_signed lo_545)%Z G_102fd.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis RNG_GLOBALS_TOP : gw_br GLOBALS_TOP 8.
Hypothesis LAY_STATIC_SPLIT_got_ssp : gw_le (STATIC_SPLIT + 8) got_ssp.
Hypothesis LAY_got_ssp_ssp_guard : gw_le (got_ssp + 8) ssp_guard.
Hypothesis LAY_ssp_guard_GLOBALS_TOP : gw_le (ssp_guard + 8) GLOBALS_TOP.
Hypothesis RNG_G_102fd : gw_br G_102fd 12.
Hypothesis ROM_G_102fd : ro_bytes segs G_102fd [Z_to_bv 8 45; Z_to_bv 8 43; Z_to_bv 8 32; Z_to_bv 8 32; Z_to_bv 8 32; Z_to_bv 8 48; Z_to_bv 8 88; Z_to_bv 8 48; Z_to_bv 8 120; Z_to_bv 8 0; Z_to_bv 8 125; Z_to_bv 8 0].
Hypothesis LAY_G_102fd_STATIC_SPLIT : gw_le (G_102fd + 12) STATIC_SPLIT.
Hypothesis RNG_G_11778 : gw_br G_11778 224.

Local Definition gw_tbl_0 := tt.

Definition wfile : ltac:(gw_rebind_ty (@QQLG.Mq7.wfile segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QQLG.Mq7.wfile segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@QROt.Mq0.wfile segs) wfile (gw_ent (@Q8l1.Mq1.wfile segs) wfile (gw_ent (@Q91D.Mq2.wfile segs) wfile (gw_ent (@QQLG.Mq7.wfile segs) wfile gw_tbl_0)))).
Definition ssp_cells : ltac:(gw_rebind_ty (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QROt.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q8l1.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_1))).
Definition va_area : ltac:(gw_rebind_ty (@Q91D.Mq3.va_area segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q91D.Mq3.va_area segs) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@QROt.Mq0.va_area segs) va_area (gw_ent (@Q8l1.Mq1.va_area segs) va_area (gw_ent (@Q91D.Mq3.va_area segs) va_area gw_tbl_2))).
Definition sink_frame_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@QROt.Mq0.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@Q8l1.Mq1.sink_frame_stmt segs) sink_frame_stmt gw_tbl_3)).
#[global] Arguments sink_frame_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope.
Definition sink_flags_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@QROt.Mq0.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@Q8l1.Mq1.sink_flags_stmt segs) sink_flags_stmt gw_tbl_4)).
#[global] Arguments sink_flags_stmt {St}%_type_scope Fp%_Z_scope SINK%_function_scope.
Definition out_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QROt.Mq0.out_post segs got_ssp ssp_guard) out_post (gw_ent (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) out_post gw_tbl_5)).
#[global] Arguments out_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F fc%_bv_scope S%_Z_scope bs%_list_scope lo%_Z_scope canary%_bv_scope m%_function_scope _ _ _.
Definition out_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QROt.Mq0.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt gw_tbl_6)).
#[global] Arguments out_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope.
Definition POST : ltac:(gw_rebind_ty (@QROt.Mq0.POST segs got_ssp ssp_guard) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@QROt.Mq0.POST segs got_ssp ssp_guard) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QROt.Mq0.POST segs got_ssp ssp_guard) POST gw_tbl_7).
#[global] Arguments POST {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F m0%_function_scope lo%_Z_scope canary%_bv_scope AP%_Z_scope _%_Z_scope _ _.
Definition lo_cells : ltac:(gw_rebind_ty (@QROt.Mq0.lo_cells ssp_guard) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@QROt.Mq0.lo_cells ssp_guard) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QROt.Mq0.lo_cells ssp_guard) lo_cells gw_tbl_8).
Definition finv : ltac:(gw_rebind_ty (@QROt.Mq0.finv segs got_ssp ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QROt.Mq0.finv segs got_ssp ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QROt.Mq0.finv segs got_ssp ssp_guard) finv gw_tbl_9).
Definition arg_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QROt.Mq0.arg_ok segs) arg_ok (gw_ent (@Q8l1.Mq1.arg_ok segs) arg_ok gw_tbl_10)).
Definition args_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QROt.Mq0.args_ok segs) args_ok (gw_ent (@Q8l1.Mq1.args_ok segs) args_ok gw_tbl_11)).
Definition fpcall_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QROt.Mq0.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) fpcall_post gw_tbl_12)).
#[global] Arguments fpcall_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F lo%_Z_scope canary%_bv_scope m%_function_scope _%_Z_scope _ _.
Definition fpcall_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@QROt.Mq0.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt gw_tbl_13)).
#[global] Arguments fpcall_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUTFP%_function_scope c.
Definition S_HEAD : ltac:(gw_rebind_ty (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD gw_tbl_14).
#[global] Arguments S_HEAD {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope fuel%_nat_scope.
Definition S_FMTU : ltac:(gw_rebind_ty (@QROt.Mq0.S_FMTU segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_FMTU segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@QROt.Mq0.S_FMTU segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_FMTU gw_tbl_15).
#[global] Arguments S_FMTU {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_CV_D : ltac:(gw_rebind_ty (@QROt.Mq0.S_CV_D segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_CV_D segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@QROt.Mq0.S_CV_D segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_D gw_tbl_16).
#[global] Arguments S_CV_D {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
Definition pfx_sub : ltac:(gw_ctx_fold_ty (@QROt.Mq0.pfx_sub) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.pfx_sub)).
Definition implM_eq_ms : ltac:(gw_ctx_fold_ty (@QROt.Mq0.implM_eq_ms) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.implM_eq_ms)).
#[global] Arguments implM_eq_ms {St}%_type_scope {X}%_type_scope c s Q%_function_scope ms ms' _ _.
Definition sink_store : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_store) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_store)).
#[global] Arguments sink_store {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR m%_function_scope st a%_Z_scope bs%_list_scope _ _ _ _ _.
Definition sink_call : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_call) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_call)).
#[global] Arguments sink_call {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR Wc%_list_scope m%_function_scope m'%_function_scope st _ _ _ _ _.
Ltac zl := unfold zlength in *; cbn [length] in *; lia.
Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.
Ltac ienter := lazymatch goal with |- Ql2m.Mq3.implM _ _ _ _ _ => unfold Ql2m.Mq3.implM; apply impl_from_evt | |- QlEo_c1.Mq0.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.

Notation F_printf_core_common__S_CV_D := S_CV_D (only parsing).
Notation F_printf_core_common__S_FMTU := S_FMTU (only parsing).
Notation F_printf_core_common__finv := finv (only parsing).
Notation F_printf_core_common__implM_eq_ms := implM_eq_ms (only parsing).
Notation F_printf_core_common__lo_cells := lo_cells (only parsing).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).

#[using="G_102fd G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex CODE BASE4 BASER D_360 E_360 D_362 E_362 D_543 E_543 D_545 E_545 ANCH_362 ANCH_545 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd LAY_G_102fd_STATIC_SPLIT RNG_G_11778"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_360 hi_543 lo_362 lo_545 G_102fd G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex CODE BASE4 BASER D_360 E_360 D_362 E_362 D_543 E_543 D_545 E_545 ANCH_362 ANCH_545 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd LAY_G_102fd_STATIC_SPLIT RNG_G_11778.

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

Local Notation hi_cells := (QROt.Mq0.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (F_printf_core_common__lo_cells AP nla nlt).
Local Notation finv := (F_printf_core_common__finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).

Local Notation implM_eq_ms := (F_printf_core_common__implM_eq_ms (St:=St)).
Local Notation sink_store := (F_printf_core_common__sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common__sink_call (St:=St) Fp B BS SINK SFR).

Local Notation tregs := (QROt.Mq0.tregs Fp q gp tp A).

Local Notation S_FMTU := (F_printf_core_common__S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_D := (F_printf_core_common__S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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

Hypothesis HS_FMTU : S_FMTU.

#[using="Type"] Lemma fl_shl52 : forall fl, (0 <= fl < 131072)%Z ->
(Z.land (Z.shiftl fl 52) 18446744073709551615 < 9223372036854775808 <-> Z.land fl 2048 = 0)%Z.
Proof. clear - St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0 HS_FMTU.
clear. intros fl Hfl. rewrite Z.shiftl_mul_pow2 by lia.
change 2048%Z with (2^11)%Z. rewrite zb_land_pow2 by lia.
change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
split; intros H; Z.div_mod_to_equations; nia.
Qed.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_360 hi_543 lo_362 lo_545 G_102fd STATIC_SPLIT CODE D_360 E_360 D_362 E_362 D_543 E_543 D_545 E_545 ANCH_362 ANCH_545 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd LAY_G_102fd_STATIC_SPLIT BS0 GLO HA HAP HS_FMTU HVA LO QHI SEP_B SEP_F SFR"] Lemma L_CV_D : S_CV_D.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_360 hi_543 lo_362 lo_545 G_102fd STATIC_SPLIT CODE D_360 E_360 D_362 E_362 D_543 E_543 D_545 E_545 ANCH_362 ANCH_545 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd LAY_G_102fd_STATIC_SPLIT BS0 GLO HA HAP HS_FMTU HVA LO QHI SEP_B SEP_F SFR St Fp B BS SINK TOPOK OUT OUTFP SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF TQ FRM0 A0 VAHI.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp i pfx s2s za pl plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP Hi.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. gw_expose ssp_guard; unfold lo_cells in LOW.
stmt (HS_FMTU fuel HH) as NX.
pose proof (Z.mod_pos_bound i (2^64) ltac:(lia)) as RA.
set (argi := (i mod 2^64)%Z) in *.
unfold INTMAX_MAX, MARK_POS, PAD_POS.
ienter.
zs. zs. brf K1.
-
zs. zs. zs. zs. zs. zs. zs. zs.
replace (Z_to_bv 64 (0 - argi)) with (Z_to_bv 64 ((- argi) mod 2 ^ 64)) in * by (apply Z_to_bv_eqm; rewrite Z.mod_mod by lia; f_equal; lia).
replace (9223372036854775807 <? argi)%Z with true by (symmetry; apply Z.ltb_lt; lia).
pose proof (Z.mod_pos_bound (- argi) (2^64) ltac:(lia)) as RB.
(pose proof RNG_G_102fd as RNG_pfx_; pose proof LAY_G_102fd_STATIC_SPLIT as LAY_pfx_; unfold gw_br in RNG_pfx_; unfold gw_le in LAY_pfx_); jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := ((- argi) mod 2 ^ 64)%Z) (prefix := [45%Z]) (PFXA := G_102fd));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| intros mq MIq; (pose proof (pfx_sub mq 0 1 MIq ltac:(lia)) as H_pfx0; cbn [Z.of_nat skipn] in H_pfx0; rewrite Z.add_0_r in H_pfx0; exact H_pfx0) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
- replace (9223372036854775807 <? argi)%Z with false by (symmetry; apply Z.ltb_ge; lia).
zs. zs. zs. zs. zs. brf K2.
+
assert (HM : Z.land fl 2048 <> 0%Z) by (intros E; apply (proj2 (fl_shl52 fl Hfl)) in E; lia).
replace (Z.land fl 2048 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact HM). cbn [negb].
zs. zs. zs.
(pose proof RNG_G_102fd as RNG_pfx_; pose proof LAY_G_102fd_STATIC_SPLIT as LAY_pfx_; unfold gw_br in RNG_pfx_; unfold gw_le in LAY_pfx_); jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := argi) (prefix := [43%Z]) (PFXA := (G_102fd + 1)%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| intros mq MIq; exact (pfx_sub mq 1 1 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
+ assert (HM : Z.land fl 2048 = 0%Z) by (apply (proj1 (fl_shl52 fl Hfl)); lia).
replace (Z.land fl 2048 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact HM). cbn [negb].
zs. zs. zs. zs. zs.
pose proof (land_bound' fl 1 ltac:(lia) ltac:(lia)) as B1.
assert (C1 : (Z.land fl 1 = 0 \/ Z.land fl 1 = 1)%Z).
{ pose proof (Z.land_ones fl 1 ltac:(lia)) as E. change (Z.ones 1) with 1%Z in E. change (2^1)%Z with 2%Z in E. rewrite E.
pose proof (Z.mod_pos_bound fl 2 ltac:(lia)). lia. }
destruct C1 as [E1 | E1]; rewrite E1 in *.
*
cbn [Z.eqb negb Z.mul Z.add].
(pose proof RNG_G_102fd as RNG_pfx_; pose proof LAY_G_102fd_STATIC_SPLIT as LAY_pfx_; unfold gw_br in RNG_pfx_; unfold gw_le in LAY_pfx_); jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := argi) (prefix := []) (PFXA := G_102fd));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| intros mq MIq; (pose proof (pfx_sub mq 0 0 MIq ltac:(lia)) as H_pfx0; cbn [Z.of_nat skipn] in H_pfx0; rewrite Z.add_0_r in H_pfx0; exact H_pfx0) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
*
cbn [Z.eqb negb Z.mul Z.add].
(pose proof RNG_G_102fd as RNG_pfx_; pose proof LAY_G_102fd_STATIC_SPLIT as LAY_pfx_; unfold gw_br in RNG_pfx_; unfold gw_le in LAY_pfx_); jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := argi) (prefix := [32%Z]) (PFXA := (G_102fd + 2)%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| intros mq MIq; exact (pfx_sub mq 2 1 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
Qed.
End PrintfCore.

End G.
End Mq0.

Module Mq1.

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

Import QROt.Mq0.
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
Variables (hi_395 : bv 20).
Variables (lo_396 : bv 12).
Variables (joff_389 : bv 21).
Variables (G_102fd G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_fwritex e_2596c e_memchr : Z).
Hypothesis CODE : code_at segs base (printf_core_code w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 3632.
Hypothesis D_389 : decode_any (Z_to_bv 32 w_389) = Some (Jal 1 joff_389, 4%Z).
Hypothesis E_389 : is_ecall (Z_to_bv 32 w_389) = false.
Hypothesis D_395 : decode_any (Z_to_bv 32 w_395) = Some (Auipc 12 hi_395, 4%Z).
Hypothesis E_395 : is_ecall (Z_to_bv 32 w_395) = false.
Hypothesis D_396 : decode_any (Z_to_bv 32 w_396) = Some (OpImm ALU_ADD 12 12 lo_396, 4%Z).
Hypothesis E_396 : is_ecall (Z_to_bv 32 w_396) = false.
Hypothesis ANCH_396 : gw_anch (Z.shiftl (bv_signed hi_395) 12 + (base + 1580) + bv_signed lo_396)%Z G_102fd.
Hypothesis LINK_389 : gw_anch (base + 1556 + bv_signed joff_389)%Z (e_2596c + 0)%Z.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis RNG_GLOBALS_TOP : gw_br GLOBALS_TOP 8.
Hypothesis LAY_lo_GLOBALS_TOP : gw_le 65536 GLOBALS_TOP.
Hypothesis LAY_STATIC_SPLIT_got_ssp : gw_le (STATIC_SPLIT + 8) got_ssp.
Hypothesis LAY_got_ssp_ssp_guard : gw_le (got_ssp + 8) ssp_guard.
Hypothesis LAY_ssp_guard_GLOBALS_TOP : gw_le (ssp_guard + 8) GLOBALS_TOP.
Hypothesis RNG_G_102fd : gw_br G_102fd 12.
Hypothesis ROM_G_102fd : ro_bytes segs G_102fd [Z_to_bv 8 45; Z_to_bv 8 43; Z_to_bv 8 32; Z_to_bv 8 32; Z_to_bv 8 32; Z_to_bv 8 48; Z_to_bv 8 88; Z_to_bv 8 48; Z_to_bv 8 120; Z_to_bv 8 0; Z_to_bv 8 125; Z_to_bv 8 0].
Hypothesis LAY_G_102fd_STATIC_SPLIT : gw_le (G_102fd + 12) STATIC_SPLIT.
Hypothesis RNG_G_11778 : gw_br G_11778 224.

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
Definition S_HEAD : ltac:(gw_rebind_ty (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD gw_tbl_16).
#[global] Arguments S_HEAD {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope fuel%_nat_scope.
Definition S_TAIL : ltac:(gw_rebind_ty (@QROt.Mq0.S_TAIL segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_TAIL segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_17)).
Local Definition gw_tbl_18 := (gw_ent (@QROt.Mq0.S_TAIL segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_TAIL gw_tbl_17).
#[global] Arguments S_TAIL {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_CV_S : ltac:(gw_rebind_ty (@QROt.Mq0.S_CV_S segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_CV_S segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_18)).
Local Definition gw_tbl_19 := (gw_ent (@QROt.Mq0.S_CV_S segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_S gw_tbl_18).
#[global] Arguments S_CV_S {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Hypothesis strnlen_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q91D.Mq6.gw_all) (@Q91D.Mq6.strnlen_spec) e_2596c)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_19))) in exact T).

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
Definition pfx_sub : ltac:(gw_ctx_fold_ty (@QROt.Mq0.pfx_sub) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.pfx_sub)).
Definition implM_eq_ms : ltac:(gw_ctx_fold_ty (@QROt.Mq0.implM_eq_ms) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.implM_eq_ms)).
#[global] Arguments implM_eq_ms {St}%_type_scope {X}%_type_scope c s Q%_function_scope ms ms' _ _.
Definition sink_store : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_store) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_store)).
#[global] Arguments sink_store {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR m%_function_scope st a%_Z_scope bs%_list_scope _ _ _ _ _.
Definition sink_call : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_call) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_call)).
#[global] Arguments sink_call {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR Wc%_list_scope m%_function_scope m'%_function_scope st _ _ _ _ _.
Definition strnlen_callq : ltac:(gw_ctx_fold_ty (@QROt.Mq0.strnlen_callq) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.strnlen_callq)).
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
Ltac if_lit :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
let v := eval vm_compute in c in change c with v; cbv iota
end.
Ltac ienter := lazymatch goal with |- Ql2m.Mq3.implM _ _ _ _ _ => unfold Ql2m.Mq3.implM; apply impl_from_evt | |- QlEo_c1.Mq0.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
lazymatch goal with |- QlEo_c1.Mq0.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Ql2m.Mq3.implM segs c s Q ms) | _ => idtac end.

Notation F_printf_core_common__S_CV_S := S_CV_S (only parsing).
Notation F_printf_core_common__S_TAIL := S_TAIL (only parsing).
Notation F_printf_core_common__finv := finv (only parsing).
Notation F_printf_core_common__implM_eq_ms := implM_eq_ms (only parsing).
Notation F_printf_core_common__lo_cells := lo_cells (only parsing).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).
Notation F_printf_core_common__strnlen_callq := strnlen_callq (only parsing).

#[using="G_102fd G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex e_2596c e_memchr CODE BASE4 BASER D_389 E_389 D_395 E_395 D_396 E_396 ANCH_396 LINK_389 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd LAY_G_102fd_STATIC_SPLIT RNG_G_11778 strnlen_spec"] Lemma gw_all : True. Proof. exact I. Qed.

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

Local Notation hi_cells := (QROt.Mq0.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (F_printf_core_common__lo_cells AP nla nlt).
Local Notation finv := (F_printf_core_common__finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).

Local Notation implM_eq_ms := (F_printf_core_common__implM_eq_ms (St:=St)).
Local Notation sink_store := (F_printf_core_common__sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common__sink_call (St:=St) Fp B BS SINK SFR).

Local Notation strnlen_callq := (F_printf_core_common__strnlen_callq q gp tp lo LO GLO QHI).

Local Notation body_loc := (QROt.Mq0.body_loc Fp B BS q lo).
Local Notation S_TAIL := (F_printf_core_common__S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (QROt.Mq0.tregs Fp q gp tp A).

Local Notation S_CV_S := (F_printf_core_common__S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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

Hypothesis HS_TAIL : S_TAIL.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_395 lo_396 joff_389 G_102fd STATIC_SPLIT e_2596c CODE BASE4 BASER D_389 E_389 D_395 E_395 D_396 E_396 ANCH_396 LINK_389 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd LAY_G_102fd_STATIC_SPLIT strnlen_spec BS0 GLO HA HAP HS_TAIL HVA LO QHI SEP_B SEP_F SFR VAHI"] Lemma L_CV_S : S_CV_S.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_395 lo_396 joff_389 G_102fd STATIC_SPLIT e_2596c CODE BASE4 BASER D_389 E_389 D_395 E_395 D_396 E_396 ANCH_396 LINK_389 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd LAY_G_102fd_STATIC_SPLIT strnlen_spec BS0 GLO HA HAP HS_TAIL HVA LO QHI SEP_B SEP_F SFR VAHI St Fp B BS SINK TOPOK OUT OUTFP SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF TQ FRM0 A0.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p fl10 xp P s slack pfx s2s za pl plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP STR SRNG SPAD P0 SD1 SD2 SD3 E10.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. gw_expose ssp_guard; unfold lo_cells in LOW.
pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app, zb_length in SB. cbn [length] in SB.
assert (LSB : Z.of_nat (length (zb s ++ Z_to_bv 8 0 :: slack)) = (Z.of_nat (length s) + 1 + Z.of_nat (length slack))%Z)
by (rewrite length_app, zb_length; cbn [length]; lia).
pose proof (zb_nonul s SRNG) as NONUL. pose proof (zb_length s) as LZS.
pose proof (land_bound' fl 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB. rewrite (nzmask_eq fl) in FLB by lia.
assert (BRNG : forall n, Forall (fun c0 => 0 <= c0 < 256)%Z (firstn n s)).
{ intros n. rewrite <- (skipn_O s). apply Forall_sub. eapply Forall_impl; [|exact SRNG]. cbv beta. intros. lia. }
stmt (HS_TAIL fuel HH) as NX.
set (len := Z.of_nat (length s)) in *.
unfold ZERO_PAD.
ienter.
zs. zs. brf K0; [|exfalso; lia].
destruct XP as [[-> ->] | [-> Hp]].
-
cbn [Z.b2z]. change ((-1) <? 0)%Z with true. cbn [andb].
destruct (Z.leb_spec0 2147483647 len) as [BIG|SMALL]; [ileave; apply implM_unr_l|].
rewrite ?ift, ?iff.
zs. zs. if_lit. zs. zs. zs.
callx (eapply strnlen_callq with (buf := zb s ++ Z_to_bv 8 0 :: slack) (n := 2147483647%Z);
[ exact ST | exact STR | apply memchr_ok_cstr; [exact NONUL | rewrite zb_length; unfold zlength in *; lia] | exact MI
| rewrite length_app, zb_length; cbn [length]; unfold zlength in *; lia | lia | lia ]).
rewrite (strnlen_res_cstr 0) by exact NONUL. rewrite zb_length. fold len. replace (Z.min len 2147483647) with len by lia.
match goal with H : bytes_at _ ?mm P _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR1 end.
zs. zs. if_lit.
assert (NTH : nth_error (zb s ++ Z_to_bv 8 0 :: slack) (Z.to_nat len) = Some (Z_to_bv 8 0)).
{ rewrite nth_error_app2 by (rewrite zb_length; lia). rewrite zb_length. replace (Z.to_nat len - length s)%nat with 0%nat by lia. reflexivity. }
pose proof (u8ro_read segs _ P (zb s ++ Z_to_bv 8 0 :: slack) len (Z_to_bv 8 0) _ STR1 NTH ltac:(lia) eq_refl) as RD.
zs. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z. zs. if_lit. zs. zs. zs. zs. zs. zs. zs.
match goal with H : bytes_at _ ?mm P _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR2 end.
lazymatch type of STR2 with bytes_at _ ?mm _ _ => assert (SUB : bytes_at segs mm P (zb s)) end.
{ pose proof STR2 as STR3. apply bytes_at_app in STR3. exact (proj1 STR3). }
rewrite (@firstn_all2 Z (Z.to_nat len) s) by (unfold len; lia).
(pose proof RNG_G_102fd as RNG_pfx_; pose proof LAY_G_102fd_STATIC_SPLIT as LAY_pfx_; unfold gw_br in RNG_pfx_; unfold gw_le in LAY_pfx_); jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := Z.land fl (Z.lnot 65536)) (w := w) (p := len) (prefix := []) (body := s) (BA := P) (PFXA := G_102fd));
[ mk_finv | exact LOW | exact DIG | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact SUB | eapply Forall_impl; [|exact SRNG]; cbv beta; intros; lia
| unfold body_loc; zl | zl | unfold INT_MAX; zl
| intros mq MIq; (pose proof (pfx_sub mq 0 0 MIq ltac:(lia)) as H_pfx0; cbn [Z.of_nat skipn] in H_pfx0; rewrite Z.add_0_r in H_pfx0; exact H_pfx0) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
match goal with H : SINK ?mm _ |- SINK ?mm _ => exact H end.
-
replace (p <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb Z.b2z]. rewrite ?ift, ?iff.
zs. zs. brf K1; [ | zs ].

all: zs; zs.
all: callx (eapply strnlen_callq with (buf := zb s ++ Z_to_bv 8 0 :: slack);
[ exact ST | exact STR | apply memchr_ok_cstr; [exact NONUL | rewrite zb_length; unfold zlength in *; lia] | exact MI
| rewrite length_app, zb_length; cbn [length]; unfold zlength in *; lia | lia | lia ]).
all: rewrite (strnlen_res_cstr 0) by exact NONUL; rewrite zb_length; fold len.
all: zs; zs; (brf K2; [ | exfalso; lia ]); zs; zs; zs; zs; zs; zs; zs.
all: match goal with H : bytes_at _ ?mm ?PP (zb _ ++ _) |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR2 end.
all: lazymatch type of STR2 with bytes_at _ ?mm _ _ => assert (SUB : bytes_at segs mm P (zb (firstn (Z.to_nat (Z.min len p)) s)))
by (pose proof STR2 as STR3; rewrite <- (firstn_skipn (Z.to_nat (Z.min len p)) s) in STR3; rewrite zb_app, <- app_assoc in STR3; apply bytes_at_app in STR3; exact (proj1 STR3)) end.
all: assert (LF : zlength (firstn (Z.to_nat (Z.min len p)) s) = Z.min len p) by (unfold zlength; rewrite length_firstn; lia).
all: (pose proof RNG_G_102fd as RNG_pfx_; pose proof LAY_G_102fd_STATIC_SPLIT as LAY_pfx_; unfold gw_br in RNG_pfx_; unfold gw_le in LAY_pfx_); jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := Z.land fl (Z.lnot 65536)) (w := w) (p := Z.min len p) (prefix := []) (body := firstn (Z.to_nat (Z.min len p)) s) (BA := P) (PFXA := G_102fd));
[ mk_finv | exact LOW | exact DIG | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact SUB | apply BRNG
| unfold body_loc; rewrite LF; lia | rewrite LF; lia | rewrite LF; unfold INT_MAX; lia
| intros mq MIq; (pose proof (pfx_sub mq 0 0 MIq ltac:(lia)) as H_pfx0; cbn [Z.of_nat skipn] in H_pfx0; rewrite Z.add_0_r in H_pfx0; exact H_pfx0) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
all: match goal with H : SINK ?mm _ |- SINK ?mm _ => exact H end.
Qed.
End PrintfCore.

End G.
End Mq1.

Module Mq2.

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

Import QROt.Mq0.
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

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 : Z).
Variables (G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_fwritex : Z).
Hypothesis CODE : code_at segs base (printf_core_code w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 3632.
Hypothesis RNG_GLOBALS_TOP : gw_br GLOBALS_TOP 8.
Hypothesis LAY_lo_GLOBALS_TOP : gw_le 65536 GLOBALS_TOP.
Hypothesis RNG_G_11778 : gw_br G_11778 224.

Local Definition gw_tbl_0 := tt.

Definition wfile : ltac:(gw_rebind_ty (@QQLG.Mq7.wfile segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QQLG.Mq7.wfile segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@QROt.Mq0.wfile segs) wfile (gw_ent (@Q8l1.Mq1.wfile segs) wfile (gw_ent (@Q91D.Mq2.wfile segs) wfile (gw_ent (@QQLG.Mq7.wfile segs) wfile gw_tbl_0)))).
Definition ssp_cells : ltac:(gw_rebind_ty (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QROt.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q8l1.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_1))).
Definition va_area : ltac:(gw_rebind_ty (@Q91D.Mq3.va_area segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q91D.Mq3.va_area segs) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@QROt.Mq0.va_area segs) va_area (gw_ent (@Q8l1.Mq1.va_area segs) va_area (gw_ent (@Q91D.Mq3.va_area segs) va_area gw_tbl_2))).
Definition sink_frame_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@QROt.Mq0.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@Q8l1.Mq1.sink_frame_stmt segs) sink_frame_stmt gw_tbl_3)).
#[global] Arguments sink_frame_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope.
Definition sink_flags_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@QROt.Mq0.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@Q8l1.Mq1.sink_flags_stmt segs) sink_flags_stmt gw_tbl_4)).
#[global] Arguments sink_flags_stmt {St}%_type_scope Fp%_Z_scope SINK%_function_scope.
Definition out_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QROt.Mq0.out_post segs got_ssp ssp_guard) out_post (gw_ent (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) out_post gw_tbl_5)).
#[global] Arguments out_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F fc%_bv_scope S%_Z_scope bs%_list_scope lo%_Z_scope canary%_bv_scope m%_function_scope _ _ _.
Definition out_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QROt.Mq0.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt gw_tbl_6)).
#[global] Arguments out_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope.
Definition dloop_post : ltac:(gw_rebind_ty (@QROt.Mq0.dloop_post segs base) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@QROt.Mq0.dloop_post segs base) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QROt.Mq0.dloop_post segs base) dloop_post gw_tbl_7).
Definition S_DLOOP : ltac:(gw_rebind_ty (@QROt.Mq0.S_DLOOP segs base) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_DLOOP segs base) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QROt.Mq0.S_DLOOP segs base) S_DLOOP gw_tbl_8).

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Definition rw_CB_length : ltac:(gw_ctx_fold_ty (@QROt.Mq0.rw_CB_length) constr:(gw_tbl_9)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.rw_CB_length)).
Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_9)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
Definition sink_store : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_store) constr:(gw_tbl_9)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_store)).
#[global] Arguments sink_store {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR m%_function_scope st a%_Z_scope bs%_list_scope _ _ _ _ _.
Definition sink_call : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_call) constr:(gw_tbl_9)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_call)).
#[global] Arguments sink_call {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR Wc%_list_scope m%_function_scope m'%_function_scope st _ _ _ _ _.
Ltac zl := unfold zlength in *; cbn [length] in *; lia.
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.

Notation F_printf_core_common__S_DLOOP := S_DLOOP (only parsing).
Notation F_printf_core_common__dloop_post := dloop_post (only parsing).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).

#[using="G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex CODE BASE4 BASER RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP RNG_G_11778"] Lemma gw_all : True. Proof. exact I. Qed.

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

Local Notation sink_store := (F_printf_core_common__sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common__sink_call (St:=St) Fp B BS SINK SFR).

Local Notation tregs := (QROt.Mq0.tregs Fp q gp tp A).

Local Notation dloop_post := (F_printf_core_common__dloop_post q gp tp).
Local Notation S_DLOOP := (F_printf_core_common__S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Ltac hush := idtac.

Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).

Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal | (progress (rewrite ?Z.shiftl_0_l, ?Z.shiftr_0_l); lia) ].

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

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP GLO LO QHI"] Lemma L_DLOOP : S_DLOOP.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP GLO LO QHI St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
intros x1 x5 x6 x7 x8 x9 x11 x12 x13 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m x.
remember (Z.to_nat x) as nx eqn:Enx. revert x Enx x11 x12 x13 x23 m.
induction nx as [nx IH] using lt_wf_ind.
intros x Enx x11 x12 x13 x23 m j ds _ MI DIG Hx Hj ->.
gw_expose GLOBALS_TOP; unfold PC_DEPTH in LO, GLO.
pose proof (munch_refl [(q + -392, q + -368)]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (dec_digits_step x ltac:(lia)) as DS.
pose proof (Z.div_pos x 10 ltac:(lia) ltac:(lia)) as Q0.
pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as R0.
assert (Q1 : (x / 10 < 1844674407370955162)%Z) by (apply Z.div_lt_upper_bound; lia).
assert (LD : (2 <= zlength (dec_digits x))%Z).
{ rewrite DS. unfold zlength. rewrite length_app. cbn [length].
destruct (Z.lt_ge_cases (x / 10) 10).
- rewrite dec_digits_small by lia. cbn. lia.
- rewrite (dec_digits_step (x / 10)) by lia. rewrite length_app. cbn [length]. lia. }
pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
zs. zs. zs. zs. zs.
rewrite (land_W64_small (Z.shiftr (x * 14757395258967641293) 64)) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite div10_magic by lia. zs. zs. zs.
replace (bv_swrap 32 (x - x / 10 * 10)) with (x mod 10)%Z by (rewrite swrap32_small by lia; lia).
rewrite (land_W64_small (x mod 10)) by lia. rewrite lor48_digit by lia.
set (c := (48 + x mod 10)%Z) in *.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DIG) as DA.
pose proof (u8arr_store_ok segs _ _ _ (j - 1)%Z (wa (q + -392 + j + -1)) DA ltac:(rewrite LDS; lia) ltac:(f_equal; lia)) as SOK.
zs. zs. rewrite le1_small by lia. replace (q + -392 + j + -1)%Z with (q + -392 + (j - 1))%Z by lia.
pose proof (u8arr_write segs _ _ _ (j - 1)%Z (Z_to_bv 8 c) DA ltac:(rewrite LDS; lia)) as DA2. clear DA. store_done.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DIG1. rewrite upd_length, LDS in DIG1.
zs. zs. brf K.
-
eapply evt_mono.
{ eapply (IH (Z.to_nat (x / 10)) ltac:(lia) (x / 10)%Z eq_refl); [ exact MI | exact DIG1 | lia | | reflexivity ].
rewrite DS in Hj. unfold zlength in *. rewrite length_app in Hj. cbn [length] in Hj. lia. }
cbv beta. intros ms' P. destruct P as (a2' & a3' & xq & W' & m' & -> & MU' & WM' & MI' & DIG' & Hxq & HD & HW).
unfold dloop_post. exists a2', a3', xq, (W' ++ [c]), m'.
assert (EL : zlength (W' ++ [c]) = (zlength W' + 1)%Z) by (unfold zlength; rewrite length_app; cbn [length]; lia).
rewrite EL.
split; [ mseq | ].
split; [ eapply munch_trans; [exact MU | exact MU'] | ].
split; [ eapply wmono_trans; [exact WM | exact WM'] | ].
split; [ exact MI' | ].
split.
{ replace (firstn (Z.to_nat (j - (zlength W' + 1))) ds ++ zb (W' ++ [c]) ++ skipn (Z.to_nat j) ds)
with (firstn (Z.to_nat (j - 1 - zlength W')) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)) ++ zb W' ++ skipn (Z.to_nat (j - 1)) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c))); [exact DIG'|].
rewrite upd_firstn_part by (rewrite LDS; unfold zlength in *; lia). rewrite upd_skipn_at by (rewrite LDS; lia).
replace (Z.to_nat (j - 1 - zlength W')) with (Z.to_nat (j - (zlength W' + 1))) by lia.
replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia.
rewrite zb_app, <- !app_assoc. reflexivity. }
split; [ exact Hxq | ]. split; [ rewrite DS, HD; reflexivity | ]. unfold zlength in *. lia.
-
zs. apply evt_done.
unfold dloop_post. eexists (Z_to_bv 64 x), (Z_to_bv 64 c), (x / 10)%Z, [c], _.
split; [ mseq | ].
split; [ exact MU | ]. split; [ exact WM | ]. split; [ exact MI | ].
split.
{ replace (firstn (Z.to_nat (j - zlength [c])) ds ++ zb [c] ++ skipn (Z.to_nat j) ds) with (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)); [exact DIG1|].
rewrite upd_firstn_skipn by (rewrite LDS; lia). cbn [zb map app zlength length Z.of_nat Pos.of_succ_nat].
replace (Z.to_nat (j - 1)) with (Z.to_nat (j - 1)) by reflexivity.
replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia. reflexivity. }
split; [ lia | ]. split; [ rewrite DS, dec_digits_small by lia; reflexivity | ]. zl.
Qed.
End PrintfCore.

End G.
End Mq2.

Module Mq3.

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

Import QROt.Mq0.
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

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 : Z).
Variables (G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_fwritex : Z).
Hypothesis CODE : code_at segs base (printf_core_code w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 3632.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis RNG_GLOBALS_TOP : gw_br GLOBALS_TOP 8.
Hypothesis RNG_G_11778 : gw_br G_11778 224.

Local Definition gw_tbl_0 := tt.

Definition wfile : ltac:(gw_rebind_ty (@QQLG.Mq7.wfile segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QQLG.Mq7.wfile segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@QROt.Mq0.wfile segs) wfile (gw_ent (@Q8l1.Mq1.wfile segs) wfile (gw_ent (@Q91D.Mq2.wfile segs) wfile (gw_ent (@QQLG.Mq7.wfile segs) wfile gw_tbl_0)))).
Definition ssp_cells : ltac:(gw_rebind_ty (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QROt.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q8l1.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_1))).
Definition va_area : ltac:(gw_rebind_ty (@Q91D.Mq3.va_area segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q91D.Mq3.va_area segs) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@QROt.Mq0.va_area segs) va_area (gw_ent (@Q8l1.Mq1.va_area segs) va_area (gw_ent (@Q91D.Mq3.va_area segs) va_area gw_tbl_2))).
Definition sink_frame_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@QROt.Mq0.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@Q8l1.Mq1.sink_frame_stmt segs) sink_frame_stmt gw_tbl_3)).
#[global] Arguments sink_frame_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope.
Definition sink_flags_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@QROt.Mq0.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@Q8l1.Mq1.sink_flags_stmt segs) sink_flags_stmt gw_tbl_4)).
#[global] Arguments sink_flags_stmt {St}%_type_scope Fp%_Z_scope SINK%_function_scope.
Definition out_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QROt.Mq0.out_post segs got_ssp ssp_guard) out_post (gw_ent (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) out_post gw_tbl_5)).
#[global] Arguments out_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F fc%_bv_scope S%_Z_scope bs%_list_scope lo%_Z_scope canary%_bv_scope m%_function_scope _ _ _.
Definition out_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QROt.Mq0.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt gw_tbl_6)).
#[global] Arguments out_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope.
Definition finv : ltac:(gw_rebind_ty (@QROt.Mq0.finv segs got_ssp ssp_guard) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@QROt.Mq0.finv segs got_ssp ssp_guard) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QROt.Mq0.finv segs got_ssp ssp_guard) finv gw_tbl_7).
Definition S_FLAGS : ltac:(gw_rebind_ty (@QROt.Mq0.S_FLAGS segs base got_ssp ssp_guard) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_FLAGS segs base got_ssp ssp_guard) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QROt.Mq0.S_FLAGS segs base got_ssp ssp_guard) S_FLAGS gw_tbl_8).

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Definition flag_none : ltac:(gw_ctx_fold_ty (@QFau.flag_none) constr:(gw_tbl_9)) := ltac:(gw_ctx_fold_tm (@QFau.flag_none)).

Definition zbytes_read : ltac:(gw_ctx_fold_ty (@QROt.Mq0.zbytes_read) constr:(gw_tbl_9)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.zbytes_read)).
Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_9)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
Definition sink_store : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_store) constr:(gw_tbl_9)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_store)).
#[global] Arguments sink_store {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR m%_function_scope st a%_Z_scope bs%_list_scope _ _ _ _ _.
Definition sink_call : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_call) constr:(gw_tbl_9)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_call)).
#[global] Arguments sink_call {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR Wc%_list_scope m%_function_scope m'%_function_scope st _ _ _ _ _.
Ltac zl := unfold zlength in *; cbn [length] in *; lia.
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.

Notation F_printf_core_common__S_FLAGS := S_FLAGS (only parsing).
Definition F_printf_core_common__fmt_rng : ltac:(gw_ctx_fold_ty (@QROt.Mq0.fmt_rng) constr:(gw_tbl_9)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.fmt_rng)).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).

#[using="G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP RNG_G_11778"] Lemma gw_all : True. Proof. exact I. Qed.

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

Local Notation hi_cells := (QROt.Mq0.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).

Local Notation fmt_rng := (F_printf_core_common__fmt_rng fmt HF).

Local Notation sink_store := (F_printf_core_common__sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common__sink_call (St:=St) Fp B BS SINK SFR).

Local Notation S_FLAGS := (F_printf_core_common__S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Local Notation tregs := (QROt.Mq0.tregs Fp q gp tp A).

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

Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal | (progress (rewrite ?Z.shiftl_0_l, ?Z.shiftr_0_l); lia) ].
Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].

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

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP HF"] Lemma L_FLAGS : S_FLAGS.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP HF St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
intros x1 x6 x7 x10 x11 x12 x15 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q p k fl b w3 FL s1 _
FI Hp Hk Hpk Hw3 Hfl Hb PF NE HK.
remember (Z.to_nat (zlength fmt - (p + k))) as kk eqn:Hkk.
revert k fl b w3 x11 x12 x15 Hk Hpk Hw3 Hfl Hb PF HK Hkk.
induction kk as [|kk IH]; intros.
{  rewrite sfx_nil in PF by (unfold zlength in *; lia). cbn in PF. injection PF as _ <-. exfalso. apply NE. reflexivity. }
assert (Hlt : (p + k < zlength fmt)%Z) by (unfold zlength in *; lia).
pose proof FI as FI'. dest_finv FI.
zs. rd_fmt (p + k)%Z. zs. fix_u8 (p + k)%Z. zs. zs. rewrite Hw3. zs. brf K.
-
assert (NF : flag_bit (znth fmt (p + k)) = None).
{ destruct (flag_bit (znth fmt (p + k))) eqn:E; [|reflexivity]. exfalso.
pose proof (flag_bit_range (znth fmt (p + k)) ltac:(congruence)) as R.
pose proof (proj2 (sp_test (znth fmt (p + k)) RG) R). lia. }
rewrite (sfx_cons fmt (p + k)) in PF by (unfold zlength in *; lia). rewrite (parse_flags_cons_none _ _ _ NF) in PF.
injection PF as EFL Es1.
rewrite Z.lor_comm, EFL.
jump (eapply (HK (p + k)%Z (znth fmt (p + k))); try reflexivity; try assumption; try lia).
{ rewrite (sfx_cons fmt (p + k)) by (unfold zlength in *; lia). symmetry. exact Es1. }
rewrite <- EFL. apply lor_bound17; lia.
- assert (Hc : (32 <= znth fmt (p + k) < 64)%Z) by (apply (proj1 (sp_test _ RG)); exact K).
rewrite (land_M64_id (znth fmt (p + k) + -32)) in * by lia.
zs. zs. zs. zs. brf K2.
+
change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (p + k) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (p + k))) in K2.
destruct (flag_bit (znth fmt (p + k))) as [b'|] eqn:E.
2:{ exfalso. apply (proj2 (flag_none _ Hc)) in E. lia. }
pose proof (flag_some _ _ Hc E) as [Hfw Hb'].
rewrite (sfx_cons fmt (p + k)) in PF by (unfold zlength in *; lia). rewrite (parse_flags_cons_some _ _ _ _ E) in PF.
replace (A + p + k + 1)%Z with (A + p + (k + 1))%Z by lia.
rewrite Z.lor_comm.
eapply (IH (k + 1)%Z (Z.lor fl b) b'); try lia.
{ rewrite unsigned_lit_land. exact Hfw. }
{ apply lor_bound17; lia. }
{ replace (p + (k + 1))%Z with (p + k + 1)%Z by lia. exact PF. }
{ intros k' c' a3 a4 a5 Hk' Hs1 Hc' HN HFL. eapply HK; try eassumption; lia. }
all: unfold zlength in *; lia.
+
change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (p + k) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (p + k))) in K2.
assert (NF : flag_bit (znth fmt (p + k)) = None) by (apply (proj1 (flag_none _ Hc)); lia).
rewrite (sfx_cons fmt (p + k)) in PF by (unfold zlength in *; lia). rewrite (parse_flags_cons_none _ _ _ NF) in PF.
injection PF as EFL Es1.
rewrite Z.lor_comm, EFL.
jump (eapply (HK (p + k)%Z (znth fmt (p + k))); try reflexivity; try assumption; try lia).
{ rewrite (sfx_cons fmt (p + k)) by (unfold zlength in *; lia). symmetry. exact Es1. }
rewrite <- EFL. apply lor_bound17; lia.
Qed.
End PrintfCore.

End G.
End Mq3.

Module Mq4.

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

Import QROt.Mq0.
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

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 : Z).
Variables (G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_fwritex : Z).
Hypothesis CODE : code_at segs base (printf_core_code w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 3632.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis RNG_GLOBALS_TOP : gw_br GLOBALS_TOP 8.
Hypothesis LAY_STATIC_SPLIT_got_ssp : gw_le (STATIC_SPLIT + 8) got_ssp.
Hypothesis LAY_got_ssp_ssp_guard : gw_le (got_ssp + 8) ssp_guard.
Hypothesis LAY_ssp_guard_GLOBALS_TOP : gw_le (ssp_guard + 8) GLOBALS_TOP.
Hypothesis RNG_G_11778 : gw_br G_11778 224.

Local Definition gw_tbl_0 := tt.

Definition wfile : ltac:(gw_rebind_ty (@QQLG.Mq7.wfile segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QQLG.Mq7.wfile segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@QROt.Mq0.wfile segs) wfile (gw_ent (@Q8l1.Mq1.wfile segs) wfile (gw_ent (@Q91D.Mq2.wfile segs) wfile (gw_ent (@QQLG.Mq7.wfile segs) wfile gw_tbl_0)))).
Definition ssp_cells : ltac:(gw_rebind_ty (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QROt.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q8l1.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_1))).
Definition va_area : ltac:(gw_rebind_ty (@Q91D.Mq3.va_area segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q91D.Mq3.va_area segs) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@QROt.Mq0.va_area segs) va_area (gw_ent (@Q8l1.Mq1.va_area segs) va_area (gw_ent (@Q91D.Mq3.va_area segs) va_area gw_tbl_2))).
Definition sink_frame_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@QROt.Mq0.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@Q8l1.Mq1.sink_frame_stmt segs) sink_frame_stmt gw_tbl_3)).
#[global] Arguments sink_frame_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope.
Definition sink_flags_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@QROt.Mq0.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@Q8l1.Mq1.sink_flags_stmt segs) sink_flags_stmt gw_tbl_4)).
#[global] Arguments sink_flags_stmt {St}%_type_scope Fp%_Z_scope SINK%_function_scope.
Definition out_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QROt.Mq0.out_post segs got_ssp ssp_guard) out_post (gw_ent (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) out_post gw_tbl_5)).
#[global] Arguments out_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F fc%_bv_scope S%_Z_scope bs%_list_scope lo%_Z_scope canary%_bv_scope m%_function_scope _ _ _.
Definition out_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QROt.Mq0.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt gw_tbl_6)).
#[global] Arguments out_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope.
Definition POST : ltac:(gw_rebind_ty (@QROt.Mq0.POST segs got_ssp ssp_guard) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@QROt.Mq0.POST segs got_ssp ssp_guard) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QROt.Mq0.POST segs got_ssp ssp_guard) POST gw_tbl_7).
#[global] Arguments POST {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F m0%_function_scope lo%_Z_scope canary%_bv_scope AP%_Z_scope _%_Z_scope _ _.
Definition lo_cells : ltac:(gw_rebind_ty (@QROt.Mq0.lo_cells ssp_guard) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@QROt.Mq0.lo_cells ssp_guard) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QROt.Mq0.lo_cells ssp_guard) lo_cells gw_tbl_8).
Definition finv : ltac:(gw_rebind_ty (@QROt.Mq0.finv segs got_ssp ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QROt.Mq0.finv segs got_ssp ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QROt.Mq0.finv segs got_ssp ssp_guard) finv gw_tbl_9).
Definition arg_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QROt.Mq0.arg_ok segs) arg_ok (gw_ent (@Q8l1.Mq1.arg_ok segs) arg_ok gw_tbl_10)).
Definition args_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QROt.Mq0.args_ok segs) args_ok (gw_ent (@Q8l1.Mq1.args_ok segs) args_ok gw_tbl_11)).
Definition fpcall_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QROt.Mq0.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) fpcall_post gw_tbl_12)).
#[global] Arguments fpcall_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F lo%_Z_scope canary%_bv_scope m%_function_scope _%_Z_scope _ _.
Definition fpcall_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@QROt.Mq0.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt gw_tbl_13)).
#[global] Arguments fpcall_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUTFP%_function_scope c.
Definition S_HEAD : ltac:(gw_rebind_ty (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD gw_tbl_14).
#[global] Arguments S_HEAD {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope fuel%_nat_scope.
Definition dloop_post : ltac:(gw_rebind_ty (@QROt.Mq0.dloop_post segs base) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QROt.Mq0.dloop_post segs base) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@QROt.Mq0.dloop_post segs base) dloop_post gw_tbl_15).
Definition S_DLOOP : ltac:(gw_rebind_ty (@QROt.Mq0.S_DLOOP segs base) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_DLOOP segs base) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@QROt.Mq0.S_DLOOP segs base) S_DLOOP gw_tbl_16).
Definition S_FMTU2 : ltac:(gw_rebind_ty (@QROt.Mq0.S_FMTU2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_FMTU2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_17)).
Local Definition gw_tbl_18 := (gw_ent (@QROt.Mq0.S_FMTU2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_FMTU2 gw_tbl_17).
#[global] Arguments S_FMTU2 {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_FMTU : ltac:(gw_rebind_ty (@QROt.Mq0.S_FMTU segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_FMTU segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_18)).
Local Definition gw_tbl_19 := (gw_ent (@QROt.Mq0.S_FMTU segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_FMTU gw_tbl_18).
#[global] Arguments S_FMTU {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Definition rw_CB_length : ltac:(gw_ctx_fold_ty (@QROt.Mq0.rw_CB_length) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.rw_CB_length)).
Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
Definition implM_eq_ms : ltac:(gw_ctx_fold_ty (@QROt.Mq0.implM_eq_ms) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.implM_eq_ms)).
#[global] Arguments implM_eq_ms {St}%_type_scope {X}%_type_scope c s Q%_function_scope ms ms' _ _.
Definition sink_store : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_store) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_store)).
#[global] Arguments sink_store {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR m%_function_scope st a%_Z_scope bs%_list_scope _ _ _ _ _.
Definition sink_call : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_call) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_call)).
#[global] Arguments sink_call {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR Wc%_list_scope m%_function_scope m'%_function_scope st _ _ _ _ _.
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

Notation F_printf_core_common__POST := POST (only parsing).
Notation F_printf_core_common__S_DLOOP := S_DLOOP (only parsing).
Notation F_printf_core_common__S_FMTU := S_FMTU (only parsing).
Notation F_printf_core_common__S_FMTU2 := S_FMTU2 (only parsing).
Notation F_printf_core_common__finv := finv (only parsing).
Notation F_printf_core_common__implM_eq_ms := implM_eq_ms (only parsing).
Notation F_printf_core_common__lo_cells := lo_cells (only parsing).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).

#[using="G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_11778"] Lemma gw_all : True. Proof. exact I. Qed.

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

Local Notation POST := (F_printf_core_common__POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
Local Notation hi_cells := (QROt.Mq0.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (F_printf_core_common__lo_cells AP nla nlt).
Local Notation finv := (F_printf_core_common__finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).

Local Notation implM_eq_ms := (F_printf_core_common__implM_eq_ms (St:=St)).
Local Notation sink_store := (F_printf_core_common__sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common__sink_call (St:=St) Fp B BS SINK SFR).

Local Notation tregs := (QROt.Mq0.tregs Fp q gp tp A).

Local Notation S_DLOOP := (F_printf_core_common__S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU2 := (F_printf_core_common__S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU := (F_printf_core_common__S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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

Hypothesis HS_FMTU2 : S_FMTU2.
Hypothesis HS_DLOOP : S_DLOOP.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP BS0 GLO HA HAP HS_DLOOP HS_FMTU2 HVA LO SEP_B SEP_F SFR"] Lemma L_FMTU : S_FMTU.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP BS0 GLO HA HAP HS_DLOOP HS_FMTU2 HVA LO SEP_B SEP_F SFR St Fp B BS SINK TOPOK OUT OUTFP SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF QHI TQ FRM0 A0 VAHI.
intros fuel HH x1 x6 x7 x11 x12 x13 x15 x16 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp x prefix PFXA pfx s2s za plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hc XP Hx.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. gw_expose ssp_guard; unfold lo_cells in LOW.
pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
pose proof (dec_digits_length x) as LDX.
stmt (HS_FMTU2 fuel HH) as NX.
ienter.
zs. zs. zs. brf K.
-
zs.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := x) (d := x) (jj := 24%Z) (W := []) (prefix := prefix) (PFXA := PFXA) (pre := digs));
[ mk_finv | exact LOW | rewrite app_nil_r; exact DIG | zl | lia
| destruct (Z.eq_dec x 0) as [-> | NZ]; [left; split; [reflexivity|]; split; [reflexivity|]; apply dec_digits_0 | right; split; [lia|]; apply dec_digits_small; lia]
| exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
-
zs.
stmt HS_DLOOP as NL.
callx (eapply NL with (j := 24%Z) (ds := digs); [ exact MI | exact DIG | lia | unfold zlength; lia | f_equal; lia ]).
destruct_ands POST.
match goal with H : rw_cells _ _ (q + -392)%Z [CB 24 ?l] |- _ => rewrite (skipn_all2 digs) in H by (rewrite LDS; lia); rewrite app_nil_r in H; rename H into DIG' end.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := x) (prefix := prefix) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG' | unfold zlength in *; rewrite length_firstn, LDS; lia | unfold zlength in *; lia
| right; split; [assumption | assumption]
| exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
match goal with H : SINK _ _ |- _ => exact H end.
Qed.
End PrintfCore.

End G.
End Mq4.

Module Mq5.

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

Import QROt.Mq0.
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

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 : Z).
Variables (G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_fwritex : Z).
Hypothesis CODE : code_at segs base (printf_core_code w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 3632.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis LAY_lo_got_ssp : gw_le 65536 got_ssp.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis RNG_GLOBALS_TOP : gw_br GLOBALS_TOP 8.
Hypothesis LAY_lo_GLOBALS_TOP : gw_le 65536 GLOBALS_TOP.
Hypothesis LAY_STATIC_SPLIT_got_ssp : gw_le (STATIC_SPLIT + 8) got_ssp.
Hypothesis LAY_got_ssp_ssp_guard : gw_le (got_ssp + 8) ssp_guard.
Hypothesis LAY_ssp_guard_GLOBALS_TOP : gw_le (ssp_guard + 8) GLOBALS_TOP.
Hypothesis RNG_G_11778 : gw_br G_11778 224.

Local Definition gw_tbl_0 := tt.

Definition wfile : ltac:(gw_rebind_ty (@QQLG.Mq7.wfile segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QQLG.Mq7.wfile segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@QROt.Mq0.wfile segs) wfile (gw_ent (@Q8l1.Mq1.wfile segs) wfile (gw_ent (@Q91D.Mq2.wfile segs) wfile (gw_ent (@QQLG.Mq7.wfile segs) wfile gw_tbl_0)))).
Definition ssp_cells : ltac:(gw_rebind_ty (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QROt.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q8l1.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_1))).
Definition va_area : ltac:(gw_rebind_ty (@Q91D.Mq3.va_area segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q91D.Mq3.va_area segs) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@QROt.Mq0.va_area segs) va_area (gw_ent (@Q8l1.Mq1.va_area segs) va_area (gw_ent (@Q91D.Mq3.va_area segs) va_area gw_tbl_2))).
Definition sink_frame_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@QROt.Mq0.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@Q8l1.Mq1.sink_frame_stmt segs) sink_frame_stmt gw_tbl_3)).
#[global] Arguments sink_frame_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope.
Definition sink_flags_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@QROt.Mq0.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@Q8l1.Mq1.sink_flags_stmt segs) sink_flags_stmt gw_tbl_4)).
#[global] Arguments sink_flags_stmt {St}%_type_scope Fp%_Z_scope SINK%_function_scope.
Definition out_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QROt.Mq0.out_post segs got_ssp ssp_guard) out_post (gw_ent (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) out_post gw_tbl_5)).
#[global] Arguments out_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F fc%_bv_scope S%_Z_scope bs%_list_scope lo%_Z_scope canary%_bv_scope m%_function_scope _ _ _.
Definition out_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QROt.Mq0.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt gw_tbl_6)).
#[global] Arguments out_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope.
Definition POST : ltac:(gw_rebind_ty (@QROt.Mq0.POST segs got_ssp ssp_guard) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@QROt.Mq0.POST segs got_ssp ssp_guard) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QROt.Mq0.POST segs got_ssp ssp_guard) POST gw_tbl_7).
#[global] Arguments POST {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F m0%_function_scope lo%_Z_scope canary%_bv_scope AP%_Z_scope _%_Z_scope _ _.
Definition lo_cells : ltac:(gw_rebind_ty (@QROt.Mq0.lo_cells ssp_guard) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@QROt.Mq0.lo_cells ssp_guard) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QROt.Mq0.lo_cells ssp_guard) lo_cells gw_tbl_8).
Definition finv : ltac:(gw_rebind_ty (@QROt.Mq0.finv segs got_ssp ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QROt.Mq0.finv segs got_ssp ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QROt.Mq0.finv segs got_ssp ssp_guard) finv gw_tbl_9).
Definition arg_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QROt.Mq0.arg_ok segs) arg_ok (gw_ent (@Q8l1.Mq1.arg_ok segs) arg_ok gw_tbl_10)).
Definition args_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QROt.Mq0.args_ok segs) args_ok (gw_ent (@Q8l1.Mq1.args_ok segs) args_ok gw_tbl_11)).
Definition fpcall_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QROt.Mq0.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) fpcall_post gw_tbl_12)).
#[global] Arguments fpcall_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F lo%_Z_scope canary%_bv_scope m%_function_scope _%_Z_scope _ _.
Definition fpcall_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@QROt.Mq0.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt gw_tbl_13)).
#[global] Arguments fpcall_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUTFP%_function_scope c.
Definition S_HEAD : ltac:(gw_rebind_ty (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD gw_tbl_14).
#[global] Arguments S_HEAD {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope fuel%_nat_scope.
Definition S_INTC : ltac:(gw_rebind_ty (@QROt.Mq0.S_INTC segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_INTC segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@QROt.Mq0.S_INTC segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_INTC gw_tbl_15).
#[global] Arguments S_INTC {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_FMTU2 : ltac:(gw_rebind_ty (@QROt.Mq0.S_FMTU2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_FMTU2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@QROt.Mq0.S_FMTU2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_FMTU2 gw_tbl_16).
#[global] Arguments S_FMTU2 {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Definition rw_CB_length : ltac:(gw_ctx_fold_ty (@QROt.Mq0.rw_CB_length) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.rw_CB_length)).
Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
Definition bytes_at_nil : ltac:(gw_ctx_fold_ty (@QROt.Mq0.bytes_at_nil) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.bytes_at_nil)).
Definition implM_eq_ms : ltac:(gw_ctx_fold_ty (@QROt.Mq0.implM_eq_ms) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.implM_eq_ms)).
#[global] Arguments implM_eq_ms {St}%_type_scope {X}%_type_scope c s Q%_function_scope ms ms' _ _.
Definition sink_store : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_store) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_store)).
#[global] Arguments sink_store {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR m%_function_scope st a%_Z_scope bs%_list_scope _ _ _ _ _.
Definition sink_call : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_call) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_call)).
#[global] Arguments sink_call {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR Wc%_list_scope m%_function_scope m'%_function_scope st _ _ _ _ _.
Ltac zl := unfold zlength in *; cbn [length] in *; lia.
Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.
Ltac ienter := lazymatch goal with |- Ql2m.Mq3.implM _ _ _ _ _ => unfold Ql2m.Mq3.implM; apply impl_from_evt | |- QlEo_c1.Mq0.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.

Notation F_printf_core_common__S_FMTU2 := S_FMTU2 (only parsing).
Notation F_printf_core_common__S_INTC := S_INTC (only parsing).
Notation F_printf_core_common__finv := finv (only parsing).
Notation F_printf_core_common__implM_eq_ms := implM_eq_ms (only parsing).
Notation F_printf_core_common__lo_cells := lo_cells (only parsing).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).

#[using="G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex CODE BASE4 BASER RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_11778"] Lemma gw_all : True. Proof. exact I. Qed.

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

Local Notation hi_cells := (QROt.Mq0.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (F_printf_core_common__lo_cells AP nla nlt).
Local Notation finv := (F_printf_core_common__finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).

Local Notation implM_eq_ms := (F_printf_core_common__implM_eq_ms (St:=St)).
Local Notation sink_store := (F_printf_core_common__sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common__sink_call (St:=St) Fp B BS SINK SFR).

Local Notation tregs := (QROt.Mq0.tregs Fp q gp tp A).

Local Notation S_INTC := (F_printf_core_common__S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Local Notation S_FMTU2 := (F_printf_core_common__S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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

Hypothesis HS_INTC : S_INTC.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 CODE RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP BS0 GLO HA HAP HS_INTC HVA LO QHI SEP_B SEP_F SFR"] Lemma L_FMTU2 : S_FMTU2.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 CODE RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP BS0 GLO HA HAP HS_INTC HVA LO QHI SEP_B SEP_F SFR St Fp B BS SINK TOPOK OUT OUTFP SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF TQ FRM0 A0 VAHI.
intros fuel HH x1 x6 x7 x11 x12 x13 x14 x15 x16 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp x d jj W prefix PFXA pfx s2s za plp ahi j128 pre pad _
FI LOW DIG Hjj Hjj1 HD PAD HS APC Hk AOK FPC FRM FOK HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hc XP Hx.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. gw_expose ssp_guard; unfold lo_cells in LOW.
pose proof (rw_CB_length _ _ _ _ DIG) as LDS. rewrite length_app, zb_length in LDS.
pose proof (dec_digits_length x) as LDX.
stmt (HS_INTC fuel HH) as NX.
ienter.
zs. zs. brf K1.
-
destruct HD as [(Hd0 & -> & DX) | (Hd & DX)]; [|exfalso; lia].
rewrite app_nil_r in DIG.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := x) (prefix := prefix) (body := dec_digits x) (BA := (q + -368)%Z) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| rewrite DX; apply bytes_at_nil; lia | eapply Forall_impl; [|apply dec_digits_range]; cbv beta; intros; lia | rewrite DX; zl | rewrite DX; zl
| exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
-
destruct HD as [(Hd0 & -> & DX) | (Hd & DX)]; [exfalso; lia|].
assert (LW : (Z.of_nat (length W) + 1 <= 20)%Z) by (rewrite DX in LDX; cbn [length] in LDX; lia).
zs. rewrite lor48_digit by lia. zs.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DIG) as DA. clear DIG.
pose proof (u8arr_store_ok segs _ _ _ (jj - 1)%Z (wa (q + -392 + jj + -1)) DA ltac:(rewrite length_app, zb_length; unfold zlength in *; lia) ltac:(f_equal; lia)) as SOK.
zs. rewrite le1_small by lia. replace (q + -392 + jj + -1)%Z with (q + -392 + (jj - 1))%Z by lia.
pose proof (u8arr_write segs _ _ _ (jj - 1)%Z (Z_to_bv 8 (48 + d)) DA ltac:(rewrite length_app, zb_length; unfold zlength in *; lia)) as DA2. clear DA. store_done.
assert (EU : upd (pre ++ zb W) (Z.to_nat (jj - 1)) (Z_to_bv 8 (48 + d)) = firstn (Z.to_nat (jj - 1)) pre ++ zb ((48 + d)%Z :: W)).
{ rewrite upd_firstn_skipn by (rewrite length_app, zb_length; unfold zlength in *; lia).
rewrite firstn_app. replace (Z.to_nat (jj - 1) - length pre)%nat with 0%nat by (unfold zlength in *; lia). cbn [firstn]. rewrite app_nil_r.
replace (S (Z.to_nat (jj - 1))) with (length pre) by (unfold zlength in *; lia). rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. }
rewrite EU in DA2.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DIG.
replace (length (firstn (Z.to_nat (jj - 1)) pre ++ zb ((48 + d)%Z :: W))) with 24%nat in DIG
by (rewrite length_app, length_firstn, zb_length; cbn [length]; unfold zlength in *; lia).
pose proof (proj1 DA2) as BODY. apply bytes_at_app in BODY. destruct BODY as [_ BODY].
rewrite length_firstn in BODY. replace (Z.of_nat (Nat.min (Z.to_nat (jj - 1)) (length pre))) with (jj - 1)%Z in BODY by (unfold zlength in *; lia).
zs.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := x) (prefix := prefix) (body := dec_digits x) (BA := (q + -392 + (jj - 1))%Z) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| rewrite DX; exact BODY | eapply Forall_impl; [|apply dec_digits_range]; cbv beta; intros; lia | rewrite DX; zl | rewrite DX; zl
| exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
Qed.
End PrintfCore.

End G.
End Mq5.

Module Mq6.

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

Import QROt.Mq0.
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

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 : Z).
Variables (hi_22 : bv 20).
Variables (lo_25 : bv 12).
Variables (G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_fwritex : Z).
Hypothesis CODE : code_at segs base (printf_core_code w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 3632.
Hypothesis D_22 : decode_any (Z_to_bv 32 w_22) = Some (Auipc 10 hi_22, 4%Z).
Hypothesis E_22 : is_ecall (Z_to_bv 32 w_22) = false.
Hypothesis D_25 : decode_any (Z_to_bv 32 w_25) = Some (Load SZ8 true 12 10 lo_25, 4%Z).
Hypothesis E_25 : is_ecall (Z_to_bv 32 w_25) = false.
Hypothesis ANCH_25 : gw_anch (Z.shiftl (bv_signed hi_22) 12 + (base + 88) + bv_signed lo_25)%Z got_ssp.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis RNG_GLOBALS_TOP : gw_br GLOBALS_TOP 8.
Hypothesis LAY_STATIC_SPLIT_got_ssp : gw_le (STATIC_SPLIT + 8) got_ssp.
Hypothesis LAY_got_ssp_ssp_guard : gw_le (got_ssp + 8) ssp_guard.
Hypothesis LAY_ssp_guard_GLOBALS_TOP : gw_le (ssp_guard + 8) GLOBALS_TOP.
Hypothesis RNG_G_11778 : gw_br G_11778 224.

Local Definition gw_tbl_0 := tt.

Definition wfile : ltac:(gw_rebind_ty (@QQLG.Mq7.wfile segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QQLG.Mq7.wfile segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@QROt.Mq0.wfile segs) wfile (gw_ent (@Q8l1.Mq1.wfile segs) wfile (gw_ent (@Q91D.Mq2.wfile segs) wfile (gw_ent (@QQLG.Mq7.wfile segs) wfile gw_tbl_0)))).
Definition ssp_cells : ltac:(gw_rebind_ty (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QROt.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q8l1.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_1))).
Definition va_area : ltac:(gw_rebind_ty (@Q91D.Mq3.va_area segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q91D.Mq3.va_area segs) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@QROt.Mq0.va_area segs) va_area (gw_ent (@Q8l1.Mq1.va_area segs) va_area (gw_ent (@Q91D.Mq3.va_area segs) va_area gw_tbl_2))).
Definition sink_frame_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@QROt.Mq0.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@Q8l1.Mq1.sink_frame_stmt segs) sink_frame_stmt gw_tbl_3)).
#[global] Arguments sink_frame_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope.
Definition sink_flags_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@QROt.Mq0.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@Q8l1.Mq1.sink_flags_stmt segs) sink_flags_stmt gw_tbl_4)).
#[global] Arguments sink_flags_stmt {St}%_type_scope Fp%_Z_scope SINK%_function_scope.
Definition out_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QROt.Mq0.out_post segs got_ssp ssp_guard) out_post (gw_ent (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) out_post gw_tbl_5)).
#[global] Arguments out_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F fc%_bv_scope S%_Z_scope bs%_list_scope lo%_Z_scope canary%_bv_scope m%_function_scope _ _ _.
Definition out_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QROt.Mq0.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt gw_tbl_6)).
#[global] Arguments out_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope.
Definition lo_cells : ltac:(gw_rebind_ty (@QROt.Mq0.lo_cells ssp_guard) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@QROt.Mq0.lo_cells ssp_guard) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QROt.Mq0.lo_cells ssp_guard) lo_cells gw_tbl_7).
Definition finv : ltac:(gw_rebind_ty (@QROt.Mq0.finv segs got_ssp ssp_guard) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@QROt.Mq0.finv segs got_ssp ssp_guard) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QROt.Mq0.finv segs got_ssp ssp_guard) finv gw_tbl_8).
Definition S_PRO : ltac:(gw_rebind_ty (@QROt.Mq0.S_PRO segs base got_ssp ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_PRO segs base got_ssp ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QROt.Mq0.S_PRO segs base got_ssp ssp_guard) S_PRO gw_tbl_9).

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
Definition sink_store : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_store) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_store)).
#[global] Arguments sink_store {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR m%_function_scope st a%_Z_scope bs%_list_scope _ _ _ _ _.
Definition sink_call : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_call) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_call)).
#[global] Arguments sink_call {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR Wc%_list_scope m%_function_scope m'%_function_scope st _ _ _ _ _.
Ltac zl := unfold zlength in *; cbn [length] in *; lia.
Ltac c8ify H := lazymatch type of H with rw_cells _ ?m ?A ?cs =>
let rec go pre l := lazymatch l with
| CB 8 ?b :: ?post => apply (cb8_c8_in m A pre post b) in H; cbn [app] in H
| ?c :: ?l' => go constr:(pre ++ [c]) l'
| [] => idtac end in
go constr:(@nil cell) cs end.

Notation F_printf_core_common__S_PRO := S_PRO (only parsing).
Notation F_printf_core_common__finv := finv (only parsing).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).

#[using="G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex CODE BASE4 BASER D_22 E_22 D_25 E_25 ANCH_25 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_11778"] Lemma gw_all : True. Proof. exact I. Qed.

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

Local Notation hi_cells := (QROt.Mq0.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).

Local Notation finv := (F_printf_core_common__finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).

Local Notation sink_store := (F_printf_core_common__sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common__sink_call (St:=St) Fp B BS SINK SFR).

Local Notation tregs := (QROt.Mq0.tregs Fp q gp tp A).

Local Notation S_PRO := (F_printf_core_common__S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Ltac hush := idtac.

Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).

Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal | (progress (rewrite ?Z.shiftl_0_l, ?Z.shiftr_0_l); lia) ].

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

Ltac fix_rsegs := idtac.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal | (progress (rewrite ?Z.shiftl_0_l, ?Z.shiftr_0_l); lia) ].

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_22 lo_25 GLOBALS_TOP STATIC_SPLIT CODE D_22 E_22 D_25 E_25 ANCH_25 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP BS0 GLO HA HAP HVA LO QHI SEP_F"] Lemma L_PRO : S_PRO.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_22 lo_25 GLOBALS_TOP STATIC_SPLIT CODE D_22 E_22 D_25 E_25 ANCH_25 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP BS0 GLO HA HAP HVA LO QHI SEP_F St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF TQ FRM0 SEP_B A0 VAHI.
intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 f Q _ ST0 MI0 BY0 VAA0 SSP0 Hf CONT.
gw_expose GLOBALS_TOP; unfold PC_DEPTH in LO, GLO. unfold zlength in *.
destruct SSP0 as [SSP1 SSP2]. gw_expose got_ssp; gw_expose ssp_guard. fix_rsegs.
pose proof (zb_length fmt) as LZB. pose proof (u64s_length slots) as LU. unfold va_area in VAA0.
pose proof (munch_refl [(q + -544, q)]%Z m0) as MU. pose proof (wmono_refl segs m0) as WM.
pose proof ST0 as ST.
carve_frame 544%nat ST.
do 43 zs.

lazymatch type of FR with rw_cells _ _ _ (CB 40 ?ja :: _) => set (jA := ja) in FR; clearbody jA end.
lazymatch type of FR with rw_cells _ _ _ (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: CB 320 ?jb :: _) => set (jB := jb) in FR; clearbody jB end.
apply (proj1 (rw_cells_app segs _ _ [_;_;_;_;_;_;_;_;_;_;_] _)) in FR. destruct FR as [LOWa FRhi]. cbn [cells_size csize Nat.add app] in FRhi.
replace (q + -544 + Z.of_nat 432)%Z with (q + -112)%Z in FRhi by lia.
apply (rw_cells_split_CB segs _ _ [_;_;_;_;_;_;_;_;_;_] 320 _ [] [16; 24; 24; 256]%nat) in LOWa; [ | cbn; lia ].
cbn [mk_CB_cells app] in LOWa.
apply (rw_cells_split_CB segs _ _ [] 40 _ _ [8; 8; 8; 8; 8]%nat) in LOWa; [ | cbn; lia ].
cbn [mk_CB_cells app] in LOWa.
apply (rw_cells_split_CB segs _ _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_] 16 _ _ [8; 8]%nat) in LOWa; [ | cbn; lia ].
cbn [mk_CB_cells app] in LOWa.
do 7 c8ify LOWa.
apply (proj1 (rw_cells_app segs _ _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)) in LOWa. destruct LOWa as [LOW DP]. cbn [cells_size csize Nat.add app] in DP.
apply (proj1 (rw_cells_app segs _ _ [_] _)) in DP. destruct DP as [DIG PAD]. cbn [cells_size csize Nat.add app] in PAD.
replace (q + -544 + Z.of_nat 152)%Z with (q + -392)%Z in DIG by lia.
replace (q + -544 + Z.of_nat 152 + Z.of_nat 24)%Z with (q + -368)%Z in PAD by lia.
eapply CONT; [ | exact MU | exact LOW | exact DIG | exact PAD ].
gw_expose got_ssp; gw_expose ssp_guard; unfold finv, W, hi_cells, va_area.
split; [assumption|]. split; [eapply munch_weaken; [|exact MU]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM|].
split; [exact FRhi|]. split; [exact ST|]. split; [exact BY0|]. split; [exact VAA0|]. split; [exact SSP1|exact SSP2].
Qed.
End PrintfCore.

End G.
End Mq6.

Module Mq7.

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

Import QROt.Mq0.
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
Variables (joff_701 joff_722 : bv 21).
Variables (G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_197bc e_fwritex e_memset : Z).
Hypothesis CODE : code_at segs base (printf_core_code w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 3632.
Hypothesis D_701 : decode_any (Z_to_bv 32 w_701) = Some (Jal 1 joff_701, 4%Z).
Hypothesis E_701 : is_ecall (Z_to_bv 32 w_701) = false.
Hypothesis D_722 : decode_any (Z_to_bv 32 w_722) = Some (Jal 1 joff_722, 4%Z).
Hypothesis E_722 : is_ecall (Z_to_bv 32 w_722) = false.
Hypothesis LINK_701 : gw_anch (base + 2804 + bv_signed joff_701)%Z (e_memset + 0)%Z.
Hypothesis LINK_722 : gw_anch (base + 2888 + bv_signed joff_722)%Z (e_fwritex + 0)%Z.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis LAY_lo_got_ssp : gw_le 65536 got_ssp.
Hypothesis AL_got_ssp : gw_al got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis AL_ssp_guard : gw_al ssp_guard 8.
Hypothesis RNG_GLOBALS_TOP : gw_br GLOBALS_TOP 8.
Hypothesis LAY_lo_GLOBALS_TOP : gw_le 65536 GLOBALS_TOP.
Hypothesis LAY_STATIC_SPLIT_got_ssp : gw_le (STATIC_SPLIT + 8) got_ssp.
Hypothesis LAY_got_ssp_ssp_guard : gw_le (got_ssp + 8) ssp_guard.
Hypothesis LAY_ssp_guard_GLOBALS_TOP : gw_le (ssp_guard + 8) GLOBALS_TOP.
Hypothesis RNG_G_11778 : gw_br G_11778 224.

Local Definition gw_tbl_0 := tt.

Definition memset_postZ : ltac:(gw_rebind_ty (@Q91D.Mq2.memset_postZ segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q91D.Mq2.memset_postZ segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@Q91D.Mq2.memset_postZ segs) memset_postZ gw_tbl_0).
Definition wfile : ltac:(gw_rebind_ty (@QQLG.Mq7.wfile segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QQLG.Mq7.wfile segs) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QROt.Mq0.wfile segs) wfile (gw_ent (@Q8l1.Mq1.wfile segs) wfile (gw_ent (@Q91D.Mq2.wfile segs) wfile (gw_ent (@QQLG.Mq7.wfile segs) wfile gw_tbl_1)))).
Definition ssp_cells : ltac:(gw_rebind_ty (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@QROt.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q8l1.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_2))).
Definition va_area : ltac:(gw_rebind_ty (@Q91D.Mq3.va_area segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q91D.Mq3.va_area segs) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@QROt.Mq0.va_area segs) va_area (gw_ent (@Q8l1.Mq1.va_area segs) va_area (gw_ent (@Q91D.Mq3.va_area segs) va_area gw_tbl_3))).
Definition sink_frame_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@QROt.Mq0.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@Q8l1.Mq1.sink_frame_stmt segs) sink_frame_stmt gw_tbl_4)).
#[global] Arguments sink_frame_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope.
Definition sink_flags_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QROt.Mq0.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@Q8l1.Mq1.sink_flags_stmt segs) sink_flags_stmt gw_tbl_5)).
#[global] Arguments sink_flags_stmt {St}%_type_scope Fp%_Z_scope SINK%_function_scope.
Definition out_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QROt.Mq0.out_post segs got_ssp ssp_guard) out_post (gw_ent (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) out_post gw_tbl_6)).
#[global] Arguments out_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F fc%_bv_scope S%_Z_scope bs%_list_scope lo%_Z_scope canary%_bv_scope m%_function_scope _ _ _.
Definition out_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QROt.Mq0.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt gw_tbl_7)).
#[global] Arguments out_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope.
Definition POST : ltac:(gw_rebind_ty (@QROt.Mq0.POST segs got_ssp ssp_guard) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@QROt.Mq0.POST segs got_ssp ssp_guard) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QROt.Mq0.POST segs got_ssp ssp_guard) POST gw_tbl_8).
#[global] Arguments POST {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F m0%_function_scope lo%_Z_scope canary%_bv_scope AP%_Z_scope _%_Z_scope _ _.
Definition lo_cells : ltac:(gw_rebind_ty (@QROt.Mq0.lo_cells ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QROt.Mq0.lo_cells ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QROt.Mq0.lo_cells ssp_guard) lo_cells gw_tbl_9).
Definition finv : ltac:(gw_rebind_ty (@QROt.Mq0.finv segs got_ssp ssp_guard) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QROt.Mq0.finv segs got_ssp ssp_guard) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QROt.Mq0.finv segs got_ssp ssp_guard) finv gw_tbl_10).
Definition out_postq : ltac:(gw_rebind_ty (@QROt.Mq0.out_postq segs got_ssp ssp_guard) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@QROt.Mq0.out_postq segs got_ssp ssp_guard) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QROt.Mq0.out_postq segs got_ssp ssp_guard) out_postq gw_tbl_11).
#[global] Arguments out_postq {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope q%_Z_scope gp%_bv_scope tp%_bv_scope lo%_Z_scope canary%_bv_scope ra'%_bv_scope Ft fc%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope S%_Z_scope bs%_list_scope m%_function_scope _ _ _.
Definition arg_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QROt.Mq0.arg_ok segs) arg_ok (gw_ent (@Q8l1.Mq1.arg_ok segs) arg_ok gw_tbl_12)).
Definition args_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@QROt.Mq0.args_ok segs) args_ok (gw_ent (@Q8l1.Mq1.args_ok segs) args_ok gw_tbl_13)).
Definition fpcall_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@QROt.Mq0.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) fpcall_post gw_tbl_14)).
#[global] Arguments fpcall_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F lo%_Z_scope canary%_bv_scope m%_function_scope _%_Z_scope _ _.
Definition fpcall_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@QROt.Mq0.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt gw_tbl_15)).
#[global] Arguments fpcall_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUTFP%_function_scope c.
Definition S_HEAD : ltac:(gw_rebind_ty (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD gw_tbl_16).
#[global] Arguments S_HEAD {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope fuel%_nat_scope.
Definition tinv : ltac:(gw_rebind_ty (@QROt.Mq0.tinv segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@QROt.Mq0.tinv segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_17)).
Local Definition gw_tbl_18 := (gw_ent (@QROt.Mq0.tinv segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) tinv gw_tbl_17).
#[global] Arguments tinv {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope m%_function_scope st k%_Z_scope i4%_Z_scope args%_list_scope fuel%_nat_scope PFXA%_Z_scope fl%_Z_scope n%_Z_scope pl%_Z_scope pq%_Z_scope BA%_Z_scope prefix%_list_scope body%_list_scope alo%_bv_scope ahi%_bv_scope j128%_list_scope digs%_list_scope pad%_list_scope.
Definition S_T5 : ltac:(gw_rebind_ty (@QROt.Mq0.S_T5 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_T5 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_18)).
Local Definition gw_tbl_19 := (gw_ent (@QROt.Mq0.S_T5 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T5 gw_tbl_18).
#[global] Arguments S_T5 {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_T4 : ltac:(gw_rebind_ty (@QROt.Mq0.S_T4 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_T4 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_19)).
Local Definition gw_tbl_20 := (gw_ent (@QROt.Mq0.S_T4 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T4 gw_tbl_19).
#[global] Arguments S_T4 {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.

Hypothesis memset_callZ : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q91D.Mq2.gw_all) (@Q91D.Mq2.memset_callZ) (base + 3940)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_20))) in let T := gw_fold_pcs T base (3940)%Z [0; 168]%Z in exact T).

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
Definition c8_read4 : ltac:(gw_ctx_fold_ty (@QROt.Mq0.c8_read4) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.c8_read4)).
Definition implM_eq_ms : ltac:(gw_ctx_fold_ty (@QROt.Mq0.implM_eq_ms) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.implM_eq_ms)).
#[global] Arguments implM_eq_ms {St}%_type_scope {X}%_type_scope c s Q%_function_scope ms ms' _ _.
Definition sink_store : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_store) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_store)).
#[global] Arguments sink_store {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR m%_function_scope st a%_Z_scope bs%_list_scope _ _ _ _ _.
Definition sink_call : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_call) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_call)).
#[global] Arguments sink_call {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR Wc%_list_scope m%_function_scope m'%_function_scope st _ _ _ _ _.
Definition out_callq : ltac:(gw_ctx_fold_ty (@QROt.Mq0.out_callq) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.out_callq)).
#[global] Arguments out_callq {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope TOK HOUT q%_Z_scope gp%_bv_scope tp%_bv_scope lo%_Z_scope canary%_bv_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope LO GLO QHI TQ SEP_F SEP_B HAP BS0 ra'%_bv_scope t0%_bv_scope t1%_bv_scope t2%_bv_scope s0%_bv_scope s1%_bv_scope a3%_bv_scope a4%_bv_scope a5%_bv_scope a6%_bv_scope a7%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope t3%_bv_scope t4%_bv_scope t5%_bv_scope t6%_bv_scope Ft fc%_bv_scope m%_function_scope st S%_Z_scope L%_Z_scope bs%_list_scope _ _ _ _ _ _ _ _ _ _ _ _ _.
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
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
lazymatch goal with |- QlEo_c1.Mq0.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Ql2m.Mq3.implM segs c s Q ms) | _ => idtac end.

Notation F_printf_core_common__S_T4 := S_T4 (only parsing).
Notation F_printf_core_common__S_T5 := S_T5 (only parsing).
Notation F_printf_core_common__finv := finv (only parsing).
Notation F_printf_core_common__implM_eq_ms := implM_eq_ms (only parsing).
Notation F_printf_core_common__lo_cells := lo_cells (only parsing).
Notation F_printf_core_common__out_callq := out_callq (only parsing).
Notation F_printf_core_common__out_postq := out_postq (only parsing).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).
Notation F_printf_core_common__tinv := tinv (only parsing).

#[using="G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_197bc e_fwritex e_memset CODE BASE4 BASER D_701 E_701 D_722 E_722 LINK_701 LINK_722 RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard AL_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_11778 memset_callZ"] Lemma gw_all : True. Proof. exact I. Qed.

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

Local Notation hi_cells := (QROt.Mq0.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (F_printf_core_common__lo_cells AP nla nlt).
Local Notation finv := (F_printf_core_common__finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).

Local Notation implM_eq_ms := (F_printf_core_common__implM_eq_ms (St:=St)).
Local Notation sink_store := (F_printf_core_common__sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common__sink_call (St:=St) Fp B BS SINK SFR).

Local Notation out_postq := (F_printf_core_common__out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
Local Notation out_callq := (F_printf_core_common__out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).

Local Notation body_loc := (QROt.Mq0.body_loc Fp B BS q lo).

Local Notation tregs := (QROt.Mq0.tregs Fp q gp tp A).
Local Notation tinv := (F_printf_core_common__tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).

Local Notation S_T5 := (F_printf_core_common__S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T4 := (F_printf_core_common__S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
Ltac out_call :=
ileave; eapply implM_bind;
[ eapply out_callq;
[ match goal with H : SINK _ _ |- _ => exact H end
| | |
| match goal with H : stk _ _ _ _ |- _ => exact H end
| gw_expose got_ssp; gw_expose ssp_guard; unfold ssp_cells; split;
[ match goal with H : rw_cells _ _ got_ssp _ |- _ => exact H end
| match goal with H : rw_cells _ _ ssp_guard _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | | ]
| cbv beta ].
Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call segs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
(try g_ret_pc) end).
Ltac fix_rsegs := idtac.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal | (progress (rewrite ?Z.shiftl_0_l, ?Z.shiftr_0_l); lia) ].
Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
destruct H as (FI & LOW & DIG & PAD & HS & APC & Hk & AOK & FPC & BODY & BRNG & BLOC & BHI & Hn & HPFX & PRNG & PF0 & PF1 & Hpl & PL2 & Hi4 & Hfl & HnI & Hnp & Hplp);
pose proof FI as FI'; dest_finv FI; gw_expose ssp_guard; unfold lo_cells in LOW; unfold body_loc in BLOC; unfold INT_MAX in *;
pose proof (zb_length body) as LB; pose proof (zb_length prefix) as LP;
let BB := fresh "BB" in pose proof (bytes_at_bound _ _ _ _ BODY) as BB; rewrite LB in BB.
Ltac mk_tinv :=
lazymatch goal with |- tinv ?m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
unfold tinv, body_loc;
split; [mk_finv|];
split; [gw_expose ssp_guard; unfold lo_cells; first [hyp | hyp_cells] |];
split; [match goal with H : rw_cells _ m (q + -392)%Z _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m (q + -368)%Z _ |- _ => exact H end |];
split; [match goal with H : SINK m _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m AP _ |- _ => exact H end |];
split; [lia|];
split; [assumption|];
split; [assumption|];
split; [match goal with H : bytes_at _ m _ (zb _) |- _ => exact H end |];
repeat (split; [first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]
end.

Hypothesis HS_T5 : S_T5.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_701 joff_722 e_fwritex e_memset CODE BASE4 BASER D_701 E_701 D_722 E_722 LINK_701 LINK_722 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HS_T5 HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ"] Lemma L_T4 : S_T4.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_701 joff_722 e_fwritex e_memset CODE BASE4 BASER D_701 E_701 D_722 E_722 LINK_701 LINK_722 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HS_T5 HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ St Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF FRM0 A0 VAHI.
intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
TI FRM FOK Hc Hw Hwq Hcw.
pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
unfold mpad at 1. change (Z.land 0 (Z.lor LEFT_ADJ ZERO_PAD) =? 0)%Z with true. cbn [negb orb].
ienter.
pose proof (c8_read4 _ _ [C8 (Z_to_bv 64 PFXA); C8 (Z_to_bv 64 (Z.land fl 73728))] (Z_to_bv 64 n) _ _ LOW eq_refl) as RD4. cbn [cells_size csize Nat.add] in RD4.
zs. rewrite (sx32_lit n) by lia. zs. brf K2.
-
rewrite (proj2 (Z.leb_le _ _)) by lia.
stmt (HS_T5 fuel HH) as NX5.
jumpM (eapply NX5 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ exact TI' | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
- rewrite (proj2 (Z.leb_gt _ _)) by lia.
destruct (Z.leb_spec0 256 (pq - n)) as [|N256]; [ileave; apply implM_unr_l|].
set (n4 := (pq - n)%Z) in *.
zs. zs. zs. try rewrite (swrap32_small (pq - n)) by lia. fold n4.
zs. zs. zs. brf K3; [|exfalso; try rewrite unsigned_lit in K3 by lia; lia].
zs. zs.
apply (rw_cells_split_CB segs _ _ [] 256 _ [] [Z.to_nat n4; 256 - Z.to_nat n4]%nat) in PAD; [ | cbn; lia ].
cbn [mk_CB_cells app] in PAD.
apply (proj1 (rw_cells_app segs _ _ [_] _)) in PAD. destruct PAD as [PADa PADb].
cbn [cells_size csize] in PADb. rewrite Nat.add_0_r, Z2Nat.id in PADb by lia.
zs. callx (eapply memset_callZ; [exact PADa | exact MI | lia | lia | lia | lia]).
fix_rsegs. rename MI0 into MI.
match goal with H : rw_cells _ _ (q + -368)%Z [CB (Z.to_nat n4) (repeat _ _)] |- _ => rename H into PADa end.
rewrite (Z.mod_small 48 256) in PADa by lia.
zs. brf K4; [|exfalso; try rewrite unsigned_lit in K4 by lia; lia].
destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. zs. (brf K5; [ exfalso; lia | ]). clear FLC.
zs. zs. zs. zs.
pose proof (rw_cells_bytes_at' _ _ _ _ PADa) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
out_call.
1:{ unfold zb, zrepeat. rewrite map_repeat. exact SRC. }
1:{ unfold zrepeat. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. reflexivity. }
1:{ lia. } 1:{ lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.

match goal with Ha : rw_cells _ ?mm (q + -368)%Z [CB (Z.to_nat n4) ?l1], Hb : rw_cells _ ?mm (q + -368 + n4)%Z [CB _ ?l2] |- _ =>
assert (PAD : rw_cells segs mm (q + -368) ([] ++ [CB (Z.to_nat n4) l1; CB (256 - Z.to_nat n4) l2] ++ []));
[ cbn [app]; apply (proj2 (rw_cells_app segs _ _ [_] _)); split; [exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact Hb
| apply rw_cells_merge in PAD; cbn [cells_size cells_bytes csize cbytes app] in PAD; rewrite app_nil_r in PAD;
replace (Z.to_nat n4 + (256 - Z.to_nat n4 + 0))%nat with 256%nat in PAD by lia; clear Ha Hb ]
end.
stmt (HS_T5 fuel HH) as NX5.
jumpM (eapply NX5 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
Qed.
End PrintfCore.

End G.
End Mq7.

Module Mq8.

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

Import QROt.Mq0.
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

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 : Z).
Variables (hi_473 : bv 20).
Variables (lo_474 : bv 12).
Variables (G_107e0 G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_fwritex : Z).
Hypothesis CODE : code_at segs base (printf_core_code w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 3632.
Hypothesis D_473 : decode_any (Z_to_bv 32 w_473) = Some (Auipc 13 hi_473, 4%Z).
Hypothesis E_473 : is_ecall (Z_to_bv 32 w_473) = false.
Hypothesis D_474 : decode_any (Z_to_bv 32 w_474) = Some (OpImm ALU_ADD 13 13 lo_474, 4%Z).
Hypothesis E_474 : is_ecall (Z_to_bv 32 w_474) = false.
Hypothesis ANCH_474 : gw_anch (Z.shiftl (bv_signed hi_473) 12 + (base + 1892) + bv_signed lo_474)%Z G_107e0.
Hypothesis RNG_GLOBALS_TOP : gw_br GLOBALS_TOP 8.
Hypothesis LAY_lo_GLOBALS_TOP : gw_le 65536 GLOBALS_TOP.
Hypothesis RNG_G_107e0 : gw_br G_107e0 16.
Hypothesis ROM_G_107e0 : ro_bytes segs G_107e0 [Z_to_bv 8 48; Z_to_bv 8 49; Z_to_bv 8 50; Z_to_bv 8 51; Z_to_bv 8 52; Z_to_bv 8 53; Z_to_bv 8 54; Z_to_bv 8 55; Z_to_bv 8 56; Z_to_bv 8 57; Z_to_bv 8 65; Z_to_bv 8 66; Z_to_bv 8 67; Z_to_bv 8 68; Z_to_bv 8 69; Z_to_bv 8 70].
Hypothesis RNG_G_11778 : gw_br G_11778 224.

Local Definition gw_tbl_0 := tt.

Definition wfile : ltac:(gw_rebind_ty (@QQLG.Mq7.wfile segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QQLG.Mq7.wfile segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@QROt.Mq0.wfile segs) wfile (gw_ent (@Q8l1.Mq1.wfile segs) wfile (gw_ent (@Q91D.Mq2.wfile segs) wfile (gw_ent (@QQLG.Mq7.wfile segs) wfile gw_tbl_0)))).
Definition ssp_cells : ltac:(gw_rebind_ty (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QROt.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q8l1.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_1))).
Definition va_area : ltac:(gw_rebind_ty (@Q91D.Mq3.va_area segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q91D.Mq3.va_area segs) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@QROt.Mq0.va_area segs) va_area (gw_ent (@Q8l1.Mq1.va_area segs) va_area (gw_ent (@Q91D.Mq3.va_area segs) va_area gw_tbl_2))).
Definition sink_frame_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@QROt.Mq0.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@Q8l1.Mq1.sink_frame_stmt segs) sink_frame_stmt gw_tbl_3)).
#[global] Arguments sink_frame_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope.
Definition sink_flags_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@QROt.Mq0.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@Q8l1.Mq1.sink_flags_stmt segs) sink_flags_stmt gw_tbl_4)).
#[global] Arguments sink_flags_stmt {St}%_type_scope Fp%_Z_scope SINK%_function_scope.
Definition out_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QROt.Mq0.out_post segs got_ssp ssp_guard) out_post (gw_ent (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) out_post gw_tbl_5)).
#[global] Arguments out_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F fc%_bv_scope S%_Z_scope bs%_list_scope lo%_Z_scope canary%_bv_scope m%_function_scope _ _ _.
Definition out_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QROt.Mq0.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt gw_tbl_6)).
#[global] Arguments out_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope.
Definition xloop_post : ltac:(gw_rebind_ty (@QROt.Mq0.xloop_post segs base) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@QROt.Mq0.xloop_post segs base) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QROt.Mq0.xloop_post segs base) xloop_post gw_tbl_7).
Definition S_XLOOP : ltac:(gw_rebind_ty (@QROt.Mq0.S_XLOOP segs base) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_XLOOP segs base) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QROt.Mq0.S_XLOOP segs base) S_XLOOP gw_tbl_8).

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Definition rw_CB_length : ltac:(gw_ctx_fold_ty (@QROt.Mq0.rw_CB_length) constr:(gw_tbl_9)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.rw_CB_length)).
Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_9)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
Definition xdigits_read : ltac:(gw_ctx_fold_ty (@QROt.Mq0.xdigits_read) constr:(gw_tbl_9)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.xdigits_read)).
Definition sink_store : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_store) constr:(gw_tbl_9)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_store)).
#[global] Arguments sink_store {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR m%_function_scope st a%_Z_scope bs%_list_scope _ _ _ _ _.
Definition sink_call : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_call) constr:(gw_tbl_9)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_call)).
#[global] Arguments sink_call {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR Wc%_list_scope m%_function_scope m'%_function_scope st _ _ _ _ _.
Ltac zl := unfold zlength in *; cbn [length] in *; lia.
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.

Notation F_printf_core_common__S_XLOOP := S_XLOOP (only parsing).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).
Notation F_printf_core_common__xloop_post := xloop_post (only parsing).

#[using="G_107e0 G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex CODE BASE4 BASER D_473 E_473 D_474 E_474 ANCH_474 RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP RNG_G_107e0 ROM_G_107e0 RNG_G_11778"] Lemma gw_all : True. Proof. exact I. Qed.

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

Local Notation sink_store := (F_printf_core_common__sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common__sink_call (St:=St) Fp B BS SINK SFR).

Local Notation tregs := (QROt.Mq0.tregs Fp q gp tp A).

Local Notation xloop_post := (F_printf_core_common__xloop_post q gp tp).
Local Notation S_XLOOP := (F_printf_core_common__S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Ltac hush := idtac.

Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).

Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal | (progress (rewrite ?Z.shiftl_0_l, ?Z.shiftr_0_l); lia) ].

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

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_473 lo_474 G_107e0 GLOBALS_TOP CODE D_473 E_473 D_474 E_474 ANCH_474 RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP RNG_G_107e0 ROM_G_107e0 GLO LO QHI"] Lemma L_XLOOP : S_XLOOP.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_473 lo_474 G_107e0 GLOBALS_TOP CODE D_473 E_473 D_474 E_474 ANCH_474 RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP RNG_G_107e0 ROM_G_107e0 GLO LO QHI St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
intros x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m l x.
remember (Z.to_nat x) as nx eqn:Enx. revert x Enx x12 x13 x23 m.
induction nx as [nx IH] using lt_wf_ind.
intros x Enx x12 x13 x23 m j ds _ MI DIG Hx Hl Hj ->.
gw_expose GLOBALS_TOP; unfold PC_DEPTH in LO, GLO.
pose proof (munch_refl [(q + -392, q + -368)]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (hex_digits_step l x ltac:(lia)) as DS.
pose proof (Z.div_pos x 16 ltac:(lia) ltac:(lia)) as Q0.
pose proof (Z.mod_pos_bound x 16 ltac:(lia)) as R0.
assert (Q1 : (x / 16 < 1152921504606846976)%Z) by (apply Z.div_lt_upper_bound; lia).
assert (LD : (1 <= zlength (hex_digits l x))%Z) by (rewrite DS; unfold zlength; rewrite length_app; cbn [length]; lia).
pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
pose proof (hexchar_range 0 (x mod 16)%Z ltac:(lia) ltac:(lia)) as XR. rewrite Z.lor_0_r in XR.
pose proof (hexchar_range l (x mod 16)%Z Hl ltac:(lia)) as HR.
zs. zs. zs. zs.
replace (Z.land x 15) with (x mod 16)%Z in * by (change 15%Z with (Z.ones 4); rewrite Z.land_ones by lia; reflexivity).
pose proof (xdigits_read _ (x mod 16)%Z MI ltac:(lia)) as RD.
zs. cbv beta. rewrite (u8_lit (znth XDIGITS (x mod 16))) by lia.
zs. replace (Z.shiftr x 4) with (x / 16)%Z by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
zs. try rewrite (land_W64_small (znth XDIGITS (x mod 16))) by lia.
set (c := Z.lor (znth XDIGITS (x mod 16)) l) in *.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DIG) as DA.
pose proof (u8arr_store_ok segs _ _ _ (j - 1)%Z (wa (q + -392 + j + -1)) DA ltac:(rewrite LDS; lia) ltac:(f_equal; lia)) as SOK.
zs. rewrite le1_small by lia. replace (q + -392 + j + -1)%Z with (q + -392 + (j - 1))%Z by lia.
pose proof (u8arr_write segs _ _ _ (j - 1)%Z (Z_to_bv 8 c) DA ltac:(rewrite LDS; lia)) as DA2. clear DA. store_done.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DIG1. rewrite upd_length, LDS in DIG1.
zs. zs. brf K.
-
eapply evt_mono.
{ eapply (IH (Z.to_nat (x / 16)) ltac:(lia) (x / 16)%Z eq_refl) with (j := (j - 1)%Z); [ exact MI | exact DIG1 | lia | exact Hl | | f_equal; lia ].
rewrite DS in Hj. unfold zlength in *. rewrite length_app in Hj. cbn [length] in Hj. lia. }
cbv beta. intros ms' P. destruct P as (a2' & a3' & m' & -> & MU' & WM' & MI' & DIG' & HW).
unfold xloop_post. exists a2', a3', m'. cbv zeta.
assert (EL : zlength (hex_digits l x) = (zlength (hex_digits l (x / 16)) + 1)%Z) by (rewrite DS; unfold zlength; rewrite length_app; cbn [length]; lia).
rewrite EL.
split; [ mseq | ].
split; [ eapply munch_trans; [exact MU | exact MU'] | ].
split; [ eapply wmono_trans; [exact WM | exact WM'] | ].
split; [ exact MI' | ].
split.
{ replace (firstn (Z.to_nat (j - (zlength (hex_digits l (x / 16)) + 1))) ds ++ zb (hex_digits l x) ++ skipn (Z.to_nat j) ds)
with (firstn (Z.to_nat (j - 1 - zlength (hex_digits l (x / 16)))) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)) ++ zb (hex_digits l (x / 16)) ++ skipn (Z.to_nat (j - 1)) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c))); [exact DIG'|].
rewrite upd_firstn_part by (rewrite LDS; unfold zlength in *; lia). rewrite upd_skipn_at by (rewrite LDS; lia).
replace (Z.to_nat (j - 1 - zlength (hex_digits l (x / 16)))) with (Z.to_nat (j - (zlength (hex_digits l (x / 16)) + 1))) by lia.
replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia.
rewrite DS, zb_app, <- !app_assoc. reflexivity. }
unfold zlength in *. lia.
-
apply evt_done. unfold xloop_post. eexists _, _, _. cbv zeta.
assert (E0 : hex_digits l (x / 16) = []) by (replace (x / 16)%Z with 0%Z by lia; apply hex_digits_0).
assert (EL : zlength (hex_digits l x) = 1%Z) by (rewrite DS, E0; reflexivity).
rewrite EL.
split; [ mseq | ].
split; [ exact MU | ]. split; [ exact WM | ]. split; [ exact MI | ].
split.
{ replace (firstn (Z.to_nat (j - 1)) ds ++ zb (hex_digits l x) ++ skipn (Z.to_nat j) ds) with (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)); [exact DIG1|].
rewrite upd_firstn_skipn by (rewrite LDS; lia). rewrite DS, E0. cbn [zb map app].
replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia. reflexivity. }
lia.
Qed.
End PrintfCore.

End G.
End Mq8.

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
Import QlEo_c1.Mq0.Exc. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
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
Variables (joff_81 joff_381 joff_383 joff_389 joff_530 joff_627 joff_639 joff_648 joff_655 joff_668 joff_680 joff_689 joff_701 joff_713 joff_722 joff_729 joff_742 joff_754 joff_762 joff_798 joff_883 joff_907 : bv 21).
Variables (G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_194bc e_194c8 e_197bc e_fwritex e_memset e_2596c : Z).
Hypothesis CODE : code_at segs base (printf_core_code w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 3632.
Hypothesis D_81 : decode_any (Z_to_bv 32 w_81) = Some (Jal 1 joff_81, 4%Z).
Hypothesis E_81 : is_ecall (Z_to_bv 32 w_81) = false.
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
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis LAY_lo_ssp_guard : gw_le 65536 ssp_guard.
Hypothesis RNG_GLOBALS_TOP : gw_br GLOBALS_TOP 8.
Hypothesis LAY_lo_GLOBALS_TOP : gw_le 65536 GLOBALS_TOP.
Hypothesis LAY_STATIC_SPLIT_got_ssp : gw_le (STATIC_SPLIT + 8) got_ssp.
Hypothesis LAY_got_ssp_ssp_guard : gw_le (got_ssp + 8) ssp_guard.
Hypothesis LAY_ssp_guard_GLOBALS_TOP : gw_le (ssp_guard + 8) GLOBALS_TOP.
Hypothesis RNG_G_11778 : gw_br G_11778 224.

Local Definition gw_tbl_0 := tt.

Definition wfile : ltac:(gw_rebind_ty (@QQLG.Mq7.wfile segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QQLG.Mq7.wfile segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@QROt.Mq0.wfile segs) wfile (gw_ent (@Q8l1.Mq1.wfile segs) wfile (gw_ent (@Q91D.Mq2.wfile segs) wfile (gw_ent (@QQLG.Mq7.wfile segs) wfile gw_tbl_0)))).
Definition ssp_cells : ltac:(gw_rebind_ty (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QROt.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q8l1.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_1))).
Definition va_area : ltac:(gw_rebind_ty (@Q91D.Mq3.va_area segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q91D.Mq3.va_area segs) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@QROt.Mq0.va_area segs) va_area (gw_ent (@Q8l1.Mq1.va_area segs) va_area (gw_ent (@Q91D.Mq3.va_area segs) va_area gw_tbl_2))).
Definition sink_frame_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@QROt.Mq0.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@Q8l1.Mq1.sink_frame_stmt segs) sink_frame_stmt gw_tbl_3)).
#[global] Arguments sink_frame_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope.
Definition sink_flags_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@QROt.Mq0.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@Q8l1.Mq1.sink_flags_stmt segs) sink_flags_stmt gw_tbl_4)).
#[global] Arguments sink_flags_stmt {St}%_type_scope Fp%_Z_scope SINK%_function_scope.
Definition out_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QROt.Mq0.out_post segs got_ssp ssp_guard) out_post (gw_ent (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) out_post gw_tbl_5)).
#[global] Arguments out_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F fc%_bv_scope S%_Z_scope bs%_list_scope lo%_Z_scope canary%_bv_scope m%_function_scope _ _ _.
Definition out_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QROt.Mq0.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt gw_tbl_6)).
#[global] Arguments out_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope.
Definition POST : ltac:(gw_rebind_ty (@QROt.Mq0.POST segs got_ssp ssp_guard) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@QROt.Mq0.POST segs got_ssp ssp_guard) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QROt.Mq0.POST segs got_ssp ssp_guard) POST gw_tbl_7).
#[global] Arguments POST {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F m0%_function_scope lo%_Z_scope canary%_bv_scope AP%_Z_scope _%_Z_scope _ _.
Definition lo_cells : ltac:(gw_rebind_ty (@QROt.Mq0.lo_cells ssp_guard) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@QROt.Mq0.lo_cells ssp_guard) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QROt.Mq0.lo_cells ssp_guard) lo_cells gw_tbl_8).
Definition finv : ltac:(gw_rebind_ty (@QROt.Mq0.finv segs got_ssp ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QROt.Mq0.finv segs got_ssp ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QROt.Mq0.finv segs got_ssp ssp_guard) finv gw_tbl_9).
Definition out_postq : ltac:(gw_rebind_ty (@QROt.Mq0.out_postq segs got_ssp ssp_guard) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QROt.Mq0.out_postq segs got_ssp ssp_guard) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QROt.Mq0.out_postq segs got_ssp ssp_guard) out_postq gw_tbl_10).
#[global] Arguments out_postq {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope q%_Z_scope gp%_bv_scope tp%_bv_scope lo%_Z_scope canary%_bv_scope ra'%_bv_scope Ft fc%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope S%_Z_scope bs%_list_scope m%_function_scope _ _ _.
Definition S_SCAN : ltac:(gw_rebind_ty (@QROt.Mq0.S_SCAN segs base got_ssp ssp_guard) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_SCAN segs base got_ssp ssp_guard) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QROt.Mq0.S_SCAN segs base got_ssp ssp_guard) S_SCAN gw_tbl_11).
Definition S_DIR : ltac:(gw_rebind_ty (@QROt.Mq0.S_DIR segs base got_ssp ssp_guard) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_DIR segs base got_ssp ssp_guard) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QROt.Mq0.S_DIR segs base got_ssp ssp_guard) S_DIR gw_tbl_12).
Definition S_END : ltac:(gw_rebind_ty (@QROt.Mq0.S_END segs base got_ssp ssp_guard) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_END segs base got_ssp ssp_guard) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@QROt.Mq0.S_END segs base got_ssp ssp_guard) S_END gw_tbl_13).
#[global] Arguments S_END {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition arg_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@QROt.Mq0.arg_ok segs) arg_ok (gw_ent (@Q8l1.Mq1.arg_ok segs) arg_ok gw_tbl_14)).
Definition args_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@QROt.Mq0.args_ok segs) args_ok (gw_ent (@Q8l1.Mq1.args_ok segs) args_ok gw_tbl_15)).
Definition fpcall_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@QROt.Mq0.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) fpcall_post gw_tbl_16)).
#[global] Arguments fpcall_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F lo%_Z_scope canary%_bv_scope m%_function_scope _%_Z_scope _ _.
Definition fpcall_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_17)).
Local Definition gw_tbl_18 := (gw_ent (@QROt.Mq0.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt gw_tbl_17)).
#[global] Arguments fpcall_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUTFP%_function_scope c.
Definition S_HEAD : ltac:(gw_rebind_ty (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_18)).
Local Definition gw_tbl_19 := (gw_ent (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD gw_tbl_18).
#[global] Arguments S_HEAD {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope fuel%_nat_scope.
Definition S_CONV : ltac:(gw_rebind_ty (@QROt.Mq0.S_CONV segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_CONV segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_19)).
Local Definition gw_tbl_20 := (gw_ent (@QROt.Mq0.S_CONV segs base got_ssp GLOBALS_TOP ssp_guard) S_CONV gw_tbl_19).
#[global] Arguments S_CONV {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Definition zbytes_read : ltac:(gw_ctx_fold_ty (@QROt.Mq0.zbytes_read) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.zbytes_read)).
Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
Definition bytes_at_sub : ltac:(gw_ctx_fold_ty (@QROt.Mq0.bytes_at_sub) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.bytes_at_sub)).
Definition bytes_at_nil : ltac:(gw_ctx_fold_ty (@QROt.Mq0.bytes_at_nil) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.bytes_at_nil)).
Definition implM_eq_ms : ltac:(gw_ctx_fold_ty (@QROt.Mq0.implM_eq_ms) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.implM_eq_ms)).
#[global] Arguments implM_eq_ms {St}%_type_scope {X}%_type_scope c s Q%_function_scope ms ms' _ _.
Definition sink_store : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_store) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_store)).
#[global] Arguments sink_store {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR m%_function_scope st a%_Z_scope bs%_list_scope _ _ _ _ _.
Definition sink_call : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_call) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_call)).
#[global] Arguments sink_call {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR Wc%_list_scope m%_function_scope m'%_function_scope st _ _ _ _ _.
Definition out_callq : ltac:(gw_ctx_fold_ty (@QROt.Mq0.out_callq) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.out_callq)).
#[global] Arguments out_callq {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope TOK HOUT q%_Z_scope gp%_bv_scope tp%_bv_scope lo%_Z_scope canary%_bv_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope LO GLO QHI TQ SEP_F SEP_B HAP BS0 ra'%_bv_scope t0%_bv_scope t1%_bv_scope t2%_bv_scope s0%_bv_scope s1%_bv_scope a3%_bv_scope a4%_bv_scope a5%_bv_scope a6%_bv_scope a7%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope t3%_bv_scope t4%_bv_scope t5%_bv_scope t6%_bv_scope Ft fc%_bv_scope m%_function_scope st S%_Z_scope L%_Z_scope bs%_list_scope _ _ _ _ _ _ _ _ _ _ _ _ _.
Ltac zl := unfold zlength in *; cbn [length] in *; lia.
Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.
Ltac fixr := try (rewrite !swrap32_small by lia); try (rewrite !Z.add_0_r).
Ltac if_lit :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
let v := eval vm_compute in c in change c with v; cbv iota
end.
Ltac ienter := lazymatch goal with |- Ql2m.Mq3.implM _ _ _ _ _ => unfold Ql2m.Mq3.implM; apply impl_from_evt | |- QlEo_c1.Mq0.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
lazymatch goal with |- QlEo_c1.Mq0.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Ql2m.Mq3.implM segs c s Q ms) | _ => idtac end.

Notation F_printf_core_common__S_CONV := S_CONV (only parsing).
Notation F_printf_core_common__S_DIR := S_DIR (only parsing).
Notation F_printf_core_common__S_END := S_END (only parsing).
Notation F_printf_core_common__S_HEAD := S_HEAD (only parsing).
Notation F_printf_core_common__S_SCAN := S_SCAN (only parsing).
Notation F_printf_core_common__finv := finv (only parsing).
Definition F_printf_core_common__fmt_rng : ltac:(gw_ctx_fold_ty (@QROt.Mq0.fmt_rng) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.fmt_rng)).
Notation F_printf_core_common__implM_eq_ms := implM_eq_ms (only parsing).
Notation F_printf_core_common__lo_cells := lo_cells (only parsing).
Notation F_printf_core_common__out_callq := out_callq (only parsing).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).

#[using="G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_194bc e_194c8 e_197bc e_fwritex e_memset e_2596c CODE BASE4 BASER D_81 E_81 LINK_81 LINK_381 LINK_383 LINK_389 LINK_530 LINK_627 LINK_639 LINK_648 LINK_655 LINK_668 LINK_680 LINK_689 LINK_701 LINK_713 LINK_722 LINK_729 LINK_742 LINK_754 LINK_762 LINK_798 LINK_883 LINK_907 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_11778"] Lemma gw_all : True. Proof. exact I. Qed.

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

Local Notation hi_cells := (QROt.Mq0.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (F_printf_core_common__lo_cells AP nla nlt).
Local Notation finv := (F_printf_core_common__finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (F_printf_core_common__fmt_rng fmt HF).
Local Notation implM_eq_ms := (F_printf_core_common__implM_eq_ms (St:=St)).
Local Notation sink_store := (F_printf_core_common__sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common__sink_call (St:=St) Fp B BS SINK SFR).

Local Notation out_callq := (F_printf_core_common__out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).

Local Notation S_SCAN := (F_printf_core_common__S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Local Notation S_DIR := (F_printf_core_common__S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_END := (F_printf_core_common__S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_HEAD := (F_printf_core_common__S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CONV := (F_printf_core_common__S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Local Notation tregs := (QROt.Mq0.tregs Fp q gp tp A).

Notation sfx := (sfx fmt).

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

Hypothesis HS_SCAN : S_SCAN.
Hypothesis HS_DIR : S_DIR.
Hypothesis HS_CONV : S_CONV.
Hypothesis HS_END : S_END.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_81 joff_381 joff_383 joff_389 joff_530 joff_627 joff_639 joff_648 joff_655 joff_668 joff_680 joff_689 joff_701 joff_713 joff_722 joff_729 joff_742 joff_754 joff_762 joff_798 joff_883 joff_907 STATIC_SPLIT e_194bc e_194c8 e_197bc e_fwritex e_memset e_2596c CODE BASE4 BASER D_81 E_81 LINK_81 LINK_381 LINK_383 LINK_389 LINK_530 LINK_627 LINK_639 LINK_648 LINK_655 LINK_668 LINK_680 LINK_689 LINK_701 LINK_713 LINK_722 LINK_729 LINK_742 LINK_754 LINK_762 LINK_798 LINK_883 LINK_907 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP A0 BS0 GLO HA HAP HF HOUT HS_CONV HS_DIR HS_END HS_SCAN HVA LO QHI SEP_B SEP_F SFL TOK TQ VAHI"] Lemma L_HEAD : forall fuel, S_HEAD fuel.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_81 joff_381 joff_383 joff_389 joff_530 joff_627 joff_639 joff_648 joff_655 joff_668 joff_680 joff_689 joff_701 joff_713 joff_722 joff_729 joff_742 joff_754 joff_762 joff_798 joff_883 joff_907 STATIC_SPLIT e_194bc e_194c8 e_197bc e_fwritex e_memset e_2596c CODE BASE4 BASER D_81 E_81 LINK_81 LINK_381 LINK_383 LINK_389 LINK_530 LINK_627 LINK_639 LINK_648 LINK_655 LINK_668 LINK_680 LINK_689 LINK_701 LINK_713 LINK_722 LINK_729 LINK_742 LINK_754 LINK_762 LINK_798 LINK_883 LINK_907 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP A0 BS0 GLO HA HAP HF HOUT HS_CONV HS_DIR HS_END HS_SCAN HVA LO QHI SEP_B SEP_F SFL TOK TQ VAHI St Fp B BS SINK TOPOK OUT OUTFP SFR ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt FRM0.
induction fuel as [|fuel IH]; intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 Ft fc m st i cnt l k args pfx s2s za pl plp alo ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi Hcnt Hl Hcl.
{ cbn [printf_loop]. apply implM_unr. }
rewrite printf_loop_S. rewrite fp_calls_S in FPC.
destruct (sfx i) as [|c s'] eqn:Es. { apply implM_unr. }
destruct (sfx_cons_inv fmt i c s' Hi Es) as (Hilt & Ec & Es').
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. pose proof LOW as LOW'. gw_expose ssp_guard; unfold lo_cells in LOW.
pose proof (fmt_rng i ltac:(zl)) as RGi.
destruct (Z.eqb_spec c 0) as [C0|C0].
{
apply implM_ret.
zs. zs. zs. (brf K; [ exfalso; lia | ]). zs. rd_fmt i. zs. fix_u8 i. rewrite <- Ec, C0. zs. fixr. zs. if_lit.
stmt HS_END as NX. jump (eapply NX; [exact FI' | exact LOW' | exact DIG | exact PAD | exact HS | exact APC | exact FRM | exact FOK | unfold INT_MAX; lia]). }
rewrite <- Es in *. cbv zeta. cbv zeta in FPC.
pose proof (lit_run_sfx fmt i Hi) as (Hn & Hs1 & LIT & Hlit). cbv zeta in Hn, Hs1, LIT, Hlit. unfold zlength in *.
set (lit := lit_run (sfx i)) in *. set (n := Z.of_nat (length lit)) in *.
rewrite Hs1. rewrite Hs1 in FPC.
assert (Hn0 : (0 <= n)%Z) by (unfold n; lia).
destruct (sfx (i + n)) as [|c1 s2] eqn:Es1. { apply implM_unr. }
destruct (sfx_cons_inv fmt (i + n) c1 s2 ltac:(lia) Es1) as (Hin & Ec1 & Es2). unfold zlength in Hin.
match goal with |- context [if ?b then munr else _] => destruct b eqn:PCT; [apply implM_unr|] end.

assert (TERM : (znth fmt (i + n) = 0 \/ (znth fmt (i + n) = 37 /\ i + n + 1 < zlength fmt /\ znth fmt (i + n + 1) <> 37))%Z).
{ pose proof (lit_run_stop (sfx i) c1 s2 Hs1) as ST12. rewrite <- Ec1.
destruct ST12 as [E0|E37]; [left; exact E0 | right]. split; [exact E37|].
rewrite E37, Z.eqb_refl in PCT. cbn [andb] in PCT. destruct s2 as [|c2 s2q]; [discriminate|].
destruct (sfx_cons_inv fmt (i + n + 1) c2 s2q ltac:(lia) (eq_sym Es2)) as (Hin1 & Ec2 & Es2q).
split; [exact Hin1|]. rewrite <- Ec2. apply Z.eqb_neq. exact PCT. }
stmt HS_SCAN as NXS.
destruct (0 <? n) eqn:En; try rewrite En in FPC; [apply Z.ltb_lt in En; rename En into Npos | apply Z.ltb_ge in En; rename En into Nz].
-
destruct (Z.ltb_spec0 (2147483647 - (cnt + l)) n) as [|Hncl]; [apply implM_unr|].
ienter.
zs. zs. zs. (brf K; [ exfalso; lia | ]). zs. rd_fmt i. zs. fix_u8 i. zs. fixr. rewrite <- Ec. zs. (brf K0; [ exfalso; lia | ]). rewrite Ec.
jump (eapply NXS with (i := i) (n := n) (cnt' := (cnt + l)%Z); [exact FI' | lia | lia | zl | exact LIT | exact TERM | left; exact Npos | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
intros a1 a2.

zs. (brf K1; [ exfalso; lia | ]).
destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. (brf K2; [ exfalso; lia | ]). clear FLC.
zs. zs. zs. zs.
ileave. eapply implM_bind.
{ eapply out_callq; try exact HS; try exact ST; try exact MI.
- rewrite Hlit, zb_firstn. unfold sfx. rewrite zb_skipn. replace (A + i)%Z with (A + Z.of_nat (Z.to_nat i))%Z by lia. apply bytes_at_sub; [exact BY | zl].
- rewrite Hlit. unfold sfx. apply Forall_sub. exact HF.
- unfold n, zlength. reflexivity.
- gw_expose got_ssp; gw_expose ssp_guard; unfold ssp_cells. split; [exact SSP1 | exact SSP2].
- lia. - zl. - zl. - zl. - zl. - unfold INT_MAX in *; zl. }
cbv beta. intros [] st'. post_call segs m. rename MI0 into MI.
ienter. (try g_ret_pc).
zs. zs. (brf K3; [ exfalso; lia | ]).

rewrite <- Es1. rewrite <- Es1 in FPC.
stmt IH as NXH.
jumpM (eapply NXH with (i := (i + n)%Z) (cnt := (cnt + l)%Z) (l := n) (k := k));
[ mk_finv | gw_expose ssp_guard; unfold lo_cells; exact LOW | exact DIG | exact PAD | exact PC0 | exact APC | lia | exact AOK | exact FPC
| exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
-
assert (En0 : n = 0%Z) by lia. rewrite En0 in *.
assert (C37 : znth fmt i = 37%Z).
{ destruct TERM as [E0 | [E37 _]]; rewrite Z.add_0_r in *; [|exact E37]. exfalso. apply C0. rewrite Ec. exact E0. }
replace (i + 0 + 1)%Z with (i + 1)%Z in Es2 by lia.
destruct (parse_dir s2) as [[d s3]|] eqn:PD; [|apply implM_unr].
destruct args as [|a args']; [apply implM_unr|].
ienter.
zs. zs. zs. (brf K; [ exfalso; lia | ]). zs. rd_fmt i. zs. fix_u8 i. zs. fixr. rewrite <- Ec. zs. (brf K0; [ exfalso; lia | ]). rewrite Ec.
jump (eapply NXS with (i := i) (n := 0%Z) (cnt' := (cnt + l)%Z); [exact FI' | lia | lia | zl | intros j Hj; lia | rewrite !Z.add_0_r in TERM |- *; exact TERM | right; exact C37 | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
intros a1 a2.

zs. (brf K1; [ exfalso; lia | ]).
destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. (brf K2; [ exfalso; lia | ]). clear FLC.
zs. zs. zs. zs.
ileave. eapply implM_bind.
{ eapply out_callq; try exact HS; try exact ST; try exact MI.
- apply bytes_at_nil; zl.
- constructor.
- reflexivity.
- gw_expose got_ssp; gw_expose ssp_guard; unfold ssp_cells. split; [exact SSP1 | exact SSP2].
- lia. - zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; lia. }
cbv beta. intros [] st'. post_call segs m. rename MI0 into MI.
ienter. (try g_ret_pc).
zs. zs. (brf K3; [ | exfalso; lia ]).

stmt HS_DIR as NXD.
jump (eapply NXD with (i := i) (d := d) (rest := s3)); [mk_finv | gw_expose ssp_guard; unfold lo_cells; exact LOW | lia | zl | rewrite <- Es2; exact PD | ].
intros k4 a2' a3' a4' t1' Hk4 Hrest Ht Hfl Hw Hp. subst s3.

stmt (HS_CONV fuel IH) as NXC.
jumpM (eapply NXC with (i4 := k4) (k := k) (c := (cnt + l)%Z) (d := d) (a := a) (args := args'));
[ mk_finv | gw_expose ssp_guard; unfold lo_cells; exact LOW | exact DIG | exact PAD | exact PC0 | exact APC | lia | exact AOK
| | | exact FRM | exact FOK | lia | exact Ht | | lia | exact Hw | exact Hp | exact (parse_dir_xp _ _ _ PD) | unfold INT_MAX; lia ].
+ destruct a; try exact I. exact (Forall_inv FPC).
+ destruct a; try exact FPC. exact (Forall_inv_tail FPC).
+ exact (parse_dir_conv_type _ _ _ PD).
Qed.
End PrintfCore.

End G.
